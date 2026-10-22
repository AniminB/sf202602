Require Import String.

Variant SysEvent : Type -> Type :=
| sys_f (arg: nat) : SysEvent string
| sys_g (arg: string) : SysEvent nat
.  

(* SysEvent nat = { sys_g "", sys_g "gil", sys_g "hur", ... } *)
(* SysEvent string = { sys_f 3, sys_f 0, sys_f 7, ... } *)

CoInductive itree (E: Type ->Type) (R: Type): Type :=
| Ret (r: R)
| Tau (t: itree E R)
| Vis {A: Type} (e : E A) (k : A -> itree E R)
.

Arguments Ret {E R}.
Arguments Tau {E R}.
Arguments Vis {E R A}.

CoFixpoint bind {E: Type->Type} {R0 R: Type}
  (t: itree E R0) (s: R0 -> itree E R) : itree E R :=
  match t with
  | Ret r => s r
  | Tau t' => Tau (bind t' s)
  | @Vis _ _ A e k => Vis e (fun a => bind (k a) s)
  end.

CoFixpoint translate {E1 E2: Type -> Type} {R}
  (f: forall A, E1 A -> E2 A) (t: itree E1 R) : itree E2 R :=
  match t with
  | Ret r => Ret r
  | Tau t' => Tau (translate f t')
  | Vis e k => Vis (f _ e) (fun a => translate f (k a))
  end.

CoFixpoint interp {E: Type -> Type} {A R: Type}
  (body: A -> itree E (A + R)) (t: itree E (A + R))
  : itree E R
  :=
  match t with
  | Ret (inr r) => Ret r
  | Ret (inl a') => Tau (interp body (body a'))
  | Tau t => Tau (interp body t)
  | Vis e k => Vis e (fun a => interp body (k a))
  end.

(** State Monad **)

Variant StateEvent : Type -> Type :=
| Put (n: nat) : StateEvent unit
| Get : StateEvent nat
.

Definition sumE (E1 E2: Type -> Type) : Type -> Type :=
  fun A => (E1 A + E2 A)%type.

Definition put {E} (n: nat) : bool -> itree E (bool * unit) :=
  fun st =>
    Ret match n with
    | 0 => (false, tt)
    | _ => (true, tt)
    end.
  
Definition get {E} : bool -> itree E (bool * nat) :=
  fun st =>
    Ret (if st then (st, 1) else (st, 0)).

Definition interp_state E S R
  (puti: nat -> S -> itree E (S * unit))
  (geti: S -> itree E (S * nat))
  (t: itree (sumE E StateEvent) R)
  : itree E R.

  

   - key operations: bind, translate, iter, interp, state_monad



