Require Import List.
Require Import Memory.
Require Import Reifiable.

Set Implicit Arguments.
Import ListNotations.

(*Module BinOp.
End BinOp.*)

Module Source.
  Inductive t (T : forall A, Reifiable.t A -> Type) : forall A, Reifiable.t A -> Type :=
  | imm A (R : Reifiable.t A) (v : A) : t T R
  | var A (R : Reifiable.t A) (x : T A R) : t T R
  | def A B (RA : Reifiable.t A) (RB : Reifiable.t B) (e1 : t T RA) (e2 : T A RA -> t T RB) : t T RB.
(*  | binop (op : BinOp.t) (x : Operand.t T) (y : Operand.t T) (s_next : T -> t T)
  | jcc (c : Operand.t T) (s_true : t T) (s_false : t T) (s_next : T -> t T)
  | iter (x : Operand.t T) (s_c : T -> t T) (s_f : T -> t T) (s_next : T -> t T).*)
End Source.