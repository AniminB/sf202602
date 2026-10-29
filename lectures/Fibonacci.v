From CRIS.common Require Import CRIS.

Set Implicit Arguments.
Local Open Scope nat_scope.

(** A sequential memoization example for every natural-number input.
    A sparse memo table grows as results are computed; an absent entry
    represents the -1 sentinel.  Natural numbers avoid integer overflow. *)
Module Fibonacci.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      match n' with
      | 0 => 1
      | S n'' => fib n' + fib n''
      end
  end.

Definition fibonacci := fnsig "Fibonacci.fibonacci" (fntyp nat nat).
Definition scopes := ["Fibonacci"].
Definition memo := "Fibonacci" ↯ "memo".
Definition cache := gmap nat nat.

Definition cache_ok (xs : cache) : Prop :=
  forall n v, xs !! n = Some v -> v = fib n.

Lemma cache_ok_initial : cache_ok ∅.
Proof.
  intros n v Hlookup. rewrite lookup_empty in Hlookup. discriminate.
Qed.

Lemma cache_ok_insert xs n :
  cache_ok xs -> cache_ok (<[n := fib n]> xs).
Proof.
  intros Hvalues i v Hlookup.
  apply fin_maps.lookup_insert_Some in Hlookup.
  destruct Hlookup as [(-> & <-) | [_ Hlookup]].
  - reflexivity.
  - eapply Hvalues; exact Hlookup.
Qed.

Section Modules.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** The implementation reads the memo table before branching.  On a
      miss it makes ordinary recursive calls, then reads the current
      table again so that saving this result preserves recursive updates. *)
  Definition target_body (n : nat) : itree crisE nat :=
    'xs : cache <- cgetU memo;;
    match xs !! n with
    | Some v => Ret v
    | None =>
        v <- match n with
             | 0 => Ret 0
             | 1 => Ret 1
             | S (S m) =>
                 a <- ccallU fibonacci (S m);;
                 b <- ccallU fibonacci m;;
                 Ret (a + b)
             end;;
        ys <- cgetU memo;;
        cput memo (<[n := v]> (ys : cache));;;
        Ret v
    end.

  Definition source_body (n : nat) : itree crisE nat :=
    Ret (fib n).

  Definition target_fnsems : fnsemmap :=
    {[fid fibonacci # (msk_scp scopes msk_true,
      (None, cfunU fibonacci target_body))]}.

  Definition source_fnsems : fnsemmap :=
    {[fid fibonacci # (msk_scp scopes msk_true,
      (None, cfunU fibonacci source_body))]}.

  Program Definition target_smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := target_fnsems;
    SMod.initial_st := {[memo # (∅ : cache)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Program Definition source_smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := source_fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition target := SMod.to_mod ∅ target_smod.
  Definition source := SMod.to_mod ∅ source_smod.

  (** The source has no state.  Every entry in the target memo table
      contains the Fibonacci number at its own index. *)
  Definition Ist (STATE : stateGS Σ) : iProp Σ :=
    (∃ xs : cache, memo ↦tgt xs↑ ∗ ⌜cache_ok xs⌝)%I.

  Section Correctness.
    Context `{STATE : !stateGS Σ}.
    Context (R_s R_t : Type) (Ep : coPset * coPset).
    Context (g : forall R_s R_t,
      retr_type Σ R_s R_t -> bool -> bool ->
      itree crisE R_s -> itree crisE R_t -> iProp Σ).
    Context (RR : retr_type Σ R_s R_t).

    Local Notation sim :=
      (wsim (sandbox_fnsemmap source.(Mod.fnsems))
        (sandbox_fnsemmap target.(Mod.fnsems)) (Ist STATE)
        Ep g R_s R_t RR).

    (** A continuation form of correctness lets induction inline the two
        recursive target calls while the source stays at its return. *)
    Lemma sim_call n :
      forall ps pt (xs : cache) i_s (k_t : Any.t -> itree crisE R_t),
      cache_ok xs ->
      memo ↦tgt xs↑ -∗
      (∀ ys : cache, ⌜cache_ok ys⌝ -∗ memo ↦tgt ys↑ -∗
        sim ps true i_s (k_t (fib n)↑)) -∗
      sim ps pt i_s
        (r <- trigger (Call (fn_name fibonacci) n↑);; k_t r).
    Proof.
      induction n using (well_founded_induction lt_wf).
      intros ps pt xs i_s k_t Hxs.
      iIntros "MEM CONT".
      cInlineT. rewrite /cfunU /target_body.
      cStepsT. destruct (xs !! n) as [v|] eqn:Hentry.
      - rewrite (Hxs n v Hentry).
        cStepsT. iApply ("CONT" with "[] MEM"). done.
      - destruct n as [|[|m]]; cStepsT.
        + iApply ("CONT" with "[] MEM").
          iPureIntro. exact (cache_ok_insert 0 Hxs).
        + iApply ("CONT" with "[] MEM").
          iPureIntro. exact (cache_ok_insert 1 Hxs).
        + iApply (H (S m) ltac:(lia) ps true xs i_s _ Hxs with "MEM").
          iIntros (ys) "%Hys MEM". cStepsT.
          iApply (H m ltac:(lia) ps true ys i_s _ Hys with "MEM").
          iIntros (zs) "%Hzs MEM". cStepsT.
          iApply ("CONT" with "[] MEM"). iPureIntro.
          exact (cache_ok_insert (S (S m)) Hzs).
    Qed.
  End Correctness.

  Lemma sim_fibonacci :
    ⊢ ISim.sim_fun open source target Ist (fid fibonacci).
  Proof.
    cStartFunSim. rewrite /source_body /target_body.
    cStepsS.
    destruct (Any.downcast arg) as [n|] eqn:Harg;
      cStepsS; try contradiction.
    iDestruct "IST" as (xs) "(MEM & %Hxs)".
    cStepsT. rewrite Harg. cStepsT.
    destruct (xs !! n) as [v|] eqn:Hentry.
    - rewrite (Hxs n v Hentry). cStepsT.
      cStep. iSplit; first done. iExists xs. iFrame. done.
    - destruct n as [|[|m]]; cStepsT.
      + cStep. iSplit; first done.
        iExists _. iFrame. iPureIntro.
        exact (cache_ok_insert 0 Hxs).
      + cStep. iSplit; first done.
        iExists _. iFrame. iPureIntro.
        exact (cache_ok_insert 1 Hxs).
      + iApply (sim_call _ _ _ (S m) _ _ _ _ Hxs with "MEM").
        iIntros (ys) "%Hys MEM". cStepsT.
        iApply (sim_call _ _ _ m _ _ _ _ Hys with "MEM").
        iIntros (zs) "%Hzs MEM". cStepsT.
        cStep. iSplit; first done.
        iExists _. iFrame. iPureIntro.
        exact (cache_ok_insert (S (S m)) Hzs).
  Qed.

  Lemma sim : ⊢ ISim.t open source target Ist.
  Proof.
    cStartModSim.
    - iPoseProof (state_init_tgt_acc _ _ memo with "TGT") as
        (ov) "(%Hmemo & MEM & _)".
      { set_solver. }
      simpl_map. subst ov. iExists (∅ : cache). iFrame. iPureIntro.
      apply cache_ok_initial.
    - iApply sim_fibonacci.
  Qed.

  Theorem refinement : ⊢ ctx_refines target source.
  Proof.
    iApply main_adequacy. iApply sim.
  Qed.
End Modules.
End Fibonacci.
