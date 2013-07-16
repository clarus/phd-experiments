(** Low-level source language. *)
Require Import List.
Require Import Memory.

Set Implicit Arguments.
Import ListNotations.

Module BinOp.
  Inductive t : Set :=
  | add | sub | mul
  | not | and | xor.
  
  Module BigStep.
    Parameter t : t -> Value.t -> Value.t -> Value.t -> Type.
  End BigStep.
End BinOp.

Module Operand.
  Inductive t (T : Type) : Type :=
  | imm : Value.t -> t T
  | var : T -> t T.
  
  Module BigStep.
    Inductive t : t Value.t -> Value.t -> Type :=
    | imm : forall (v : Value.t), t (imm _ v) v
    | var : forall (v : Value.t), t (var v) v.
  End BigStep.
End Operand.

Module Source.
  Inductive t (T : Type) : Type :=
  | final : Operand.t T -> t T
  | binop : BinOp.t -> Operand.t T -> Operand.t T -> (T -> t T) -> t T.
  
  Module BigStep.
    Inductive t : t Value.t -> Value.t -> Type :=
    | final : forall x v, Operand.BigStep.t x v -> t (final x) v
    | binop : forall op x y s v_x v_y v_z v,
      Operand.BigStep.t x v_x -> Operand.BigStep.t y v_y ->
      BinOp.BigStep.t op v_x v_y v_z ->
      t (s v_z) v -> t (binop op x y s) v.
  End BigStep.
End Source.