(** The source language. *)
Require Import ZArith.
Require Import List.

Set Implicit Arguments.
(*Import ListNotations.
Local Open Scope Z_scope.*)

Module Typ.
  Inductive t : Type :=
  | simple : Type -> t
  | app : forall (T1 : Type) (T2 : T1 -> Type), .
End Typ.

Module UnOp.
  Inductive t : Set :=
  | uminus.

  Module Typing.
    Inductive t : t -> Type -> Type -> Type :=
    | uminus : t uminus Z Z.
  End Typing.

  (* Definition eval (op : t) (z1 : Z) : Z :=
    match op with
    | uminus => - z1
    end. *)
End UnOp.

Module BinOp.
  Inductive t : Set :=
  | plus
  | minus
  | times.

  Module Typing.
    Inductive t : t -> Type -> Type -> Type -> Type :=
    | plus : t plus Z Z Z
    | minus : t plus Z Z Z
    | times : t plus Z Z Z.
  End Typing.

  (* Definition eval (op : t) (z1 z2 : Z) : Z :=
    match op with
    | plus => z1 + z2
    | minus => z1 - z2
    | times => z1 * z2
    end. *)
End BinOp.

Module Source.
  Inductive t (gvar : Type -> Type) : Type -> Type :=
  | const : forall T, T -> t gvar T
  | var : forall T, gvar T -> t gvar T
  | unop : forall (op : UnOp.t) (T1 T : Type), UnOp.Typing.t op T1 T ->
    t gvar T1 -> t gvar T
  | binop : forall (op : BinOp.t) (T1 T2 T : Type), BinOp.Typing.t op T1 T2 T ->
    t gvar T1 -> t gvar T2 -> t gvar T.
  | let_ : forall (T1 : Type) (T2 : gvar T1 -> Type),
    t gvar T1 -> (forall v1 : gvar T1, t gvar (T2 gvar v1)) -> t gvar (T2 id .

  (*| _let : forall (P1 : Z -> Prop) (P2 : Z -> Z -> Prop) (P : Z -> Prop), t P1 -> (forall z1, t (P2 z1)) ->
    (forall z1 z2, P1 z1 -> P2 z1 z2 -> P z2) ->
    t P*).

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
End Source.
