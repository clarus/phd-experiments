(** The source language. *)
(** TODO:
    - let
    - if
    - ref
    - loop *)
Require Import ZArith.
Require Import List.

Set Implicit Arguments.
Import ListNotations.
Local Open Scope Z_scope.

Module UnOp.
  Inductive t : Set :=
  | uminus.
  
  Definition eval (op : t) (z1 : Z) : Z :=
    match op with
    | uminus => - z1
    end.
End UnOp.

Module BinOp.
  Inductive t : Set :=
  | plus
  | minus
  | times.
  
  Definition eval (op : t) (z1 z2 : Z) : Z :=
    match op with
    | plus => z1 + z2
    | minus => z1 - z2
    | times => z1 * z2
    end.
End BinOp.

Module Source.
  Inductive t : (Z -> Prop) -> Type :=
  | const : forall (P : Z -> Prop) z, P z -> t P
  | unop : forall (P1 P : Z -> Prop) (op : UnOp.t), t P1 ->
    (forall z1, P1 z1 -> P (UnOp.eval op z1)) -> t P
  | binop : forall (P1 P2 P : Z -> Prop) (op : BinOp.t), t P1 -> t P2 ->
    (forall z1 z2, P1 z1 -> P2 z2 -> P (BinOp.eval op z1 z2)) -> t P
  | _let : forall (P1 : Z -> Prop) (P2 : Z -> Z -> Prop) (P : Z -> Prop), t P1 -> (forall z1, t (P2 z1)) ->
    (forall z1 z2, P1 z1 -> P2 z1 z2 -> P z2) ->
    t P.
  
  Fixpoint eval P (e : t P) {struct e} : {z : Z | P z}.
    destruct e as [P z H | P1 P op e1 Hcast | P1 P2 P op e1 e2 Hcast | P1 P2 P e1 e2 Hcast].
    - exists z; trivial.
    
    - destruct (eval _ e1) as (z1, H1).
      exists (UnOp.eval op z1); auto.
    
    - destruct (eval _ e1) as (z1, H1).
      destruct (eval _ e2) as (z2, H2).
      exists (BinOp.eval op z1 z2); auto.
    
    - destruct (eval _ e1) as (z1, H1).
      destruct (eval _ (e2 z1)) as (z2, H2).
      exists z2.
      now apply Hcast with (z1 := z1).
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
        binop _ BinOp.plus (const (fun x => x >= 10) x H) (const _ 12 eq_refl) _).
      abstract (intros; simpl; omega).
    Defined.
    
    Lemma geb_complete (m n : Z) :
      (if Z_ge_dec m n then true else false) = true -> m >= n.
      now destruct (Z_ge_dec m n).
    Qed.
    
    Definition e_15 := e (geb_complete 15 10 eq_refl).
    
    Check eq_refl : 27 = projT1 (eval e_15).
  End Test.
End Source.