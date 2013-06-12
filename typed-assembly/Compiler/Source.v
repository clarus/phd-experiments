Require Import ZArith.

Set Implicit Arguments.
Local Open Scope Z_scope.

Module Source.
  Inductive t : (Z -> Prop) -> Type :=
  | const : forall (P : Z -> Prop) z, P z -> t P
  | uminus : forall (P1 P : Z -> Prop), t P1 ->
    (forall z1, P1 z1 -> P (- z1)) -> t P
  | plus : forall (P1 P2 P : Z -> Prop), t P1 -> t P2 ->
    (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 + z2)) -> t P
  | times : forall (P1 P2 P : Z -> Prop), t P1 -> t P2 ->
    (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 * z2)) -> t P.
  
  Fixpoint eval P (e : t P) {struct e} : {z : Z | P z}.
    destruct e as [P z H | P1 P e1 Hcast | P1 P2 P e1 e2 Hcast | P1 P2 P e1 e2 Hcast].
    - exists z; trivial.
    
    - destruct (eval _ e1) as (z1, H1).
      exists (- z1); auto.
    
    - destruct (eval _ e1) as (z1, H1).
      destruct (eval _ e2) as (z2, H2).
      exists (z1 + z2); auto.
    
    - destruct (eval _ e1) as (z1, H1).
      destruct (eval _ e2) as (z2, H2).
      exists (z1 * z2); auto.
  Defined.
  
  Module Test.
    Definition example (x : Z) (H : x >= 10) : {y : Z | y >= 20}.
      refine (
        let y := x + 12 in
        existT _ y _).
      abstract (unfold y; omega).
    Defined.
    
    (** For x >= 10, (x {>= 10} + 12 {= 12}) {>= 20}  *)
    Definition e (x : Z) (H : x >= 10) : t (fun y => y >= 20).
      refine (
        plus _ (const (fun x => x >= 10) x H) (const _ 12 eq_refl) _).
      abstract (intros; omega).
    Defined.
    
    Lemma geb_complete (m n : Z) :
      (if Z_ge_dec m n then true else false) = true -> m >= n.
      now destruct (Z_ge_dec m n).
    Qed.
    
    Definition e_15 := e (geb_complete 15 10 eq_refl).
    
    Check eq_refl : 27 = projT1 (eval e_15).
  End Test.
End Source.