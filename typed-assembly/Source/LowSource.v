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
  | final (x : Operand.t T)
  | binop (op : BinOp.t) (x : Operand.t T) (y : Operand.t T) (s_next : T -> t T)
  | jcc (c : Operand.t T) (s_true : t T) (s_false : t T) (s_next : T -> t T)
  | iter (x : Operand.t T) (s_c : T -> t T) (s_f : T -> t T) (s_next : T -> t T).
  
  Module BigStep.
    Inductive t : t Value.t -> Value.t -> Type :=
    | final : forall x v, Operand.BigStep.t x v -> t (final x) v
    | binop : forall op x y s v_x v_y v_z v,
      Operand.BigStep.t x v_x -> Operand.BigStep.t y v_y ->
      BinOp.BigStep.t op v_x v_y v_z ->
      t (s v_z) v -> t (binop op x y s) v
    | jcc_true : forall c s_true s_false s_next v_true v,
      Operand.BigStep.t c (Value.bits 1) ->
      t s_true v_true -> t (s_next v_true) v ->
      t (jcc c s_true s_false s_next) v
    | jcc_false : forall c s_true s_false s_next v_false v,
      Operand.BigStep.t c (Value.bits 0) ->
      t s_false v_false -> t (s_next v_false) v ->
      t (jcc c s_true s_false s_next) v
    | iter_false : forall x s_c s_f s_next v_x v,
      Operand.BigStep.t x v_x ->
      t (s_c v_x) (Value.bits 0) -> t (s_next v_x) v ->
      t (iter x s_c s_f s_next) v
    | iter_true : forall x s_c s_f s_next v_x v_x' v,
      Operand.BigStep.t x v_x ->
      t (s_c v_x) (Value.bits 1) -> t (s_f v_x) v_x' -> t (iter (Operand.imm _ v_x') s_c s_f s_next) v ->
      t (iter x s_c s_f s_next) v.
  End BigStep.
End Source.