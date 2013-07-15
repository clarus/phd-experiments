(** Low-level source language. *)
Require Import List.
Require Import Memory.

Set Implicit Arguments.
Import ListNotations.

Module BinOp.
  Inductive t : Set :=
  | add | sub | mul
  | not | and | xor.
End BinOp.

Module Operand.
  Inductive t (T : Type) : Type :=
  | imm : Value.t -> t T
  | var : T -> t T.
  
  Module BigStep.
    Inductive t : Type :=
    | imm : forall 
  End BigStep.
End Operand.

Module Source.
  Inductive t (T : Type) : Type :=
  | final : Operand.t T -> t T
  | op : BinOp.t -> Operand.t T -> Operand.t T -> (T -> t T) -> t T.
  
  Module BigStep.
    Inductive t : Type :=
    | final : 
  End BigStep.
End Source.