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
| Vis {A: Type} (e : E A) (k : A ->itree E R)
.



