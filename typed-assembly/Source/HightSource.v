Require Import List.
Require Import Memory.
Require Import Reifiable.

Set Implicit Arguments.
Import ListNotations.

Module BinOp.
End BinOp.

Module Source.
  Inductive t (T : forall A, Reifiable.t A -> Type) : forall A, Reifiable.t A -> Type :=
  | imm A (RA : Reifiable.t A) (v : A) : t T RA
  | var A (RA : Reifiable.t A) (x : T A RA) : t T RA
  | def A B (RA : Reifiable.t A) (RB : Reifiable.t B) (e1 : t T RA) (e2 : T A RA -> t T RB) : t T RB
  | convert A B (RA : Reifiable.t A) (RB : Reifiable.t B) (e : t T RA)
    : (forall v, Reifiable.invariant RA v -> Reifiable.invariant RB v) ->
      t T RB.
(*  | binop (op : BinOp.t) (x : Operand.t T) (y : Operand.t T) (s_next : T -> t T)
  | jcc (c : Operand.t T) (s_true : t T) (s_false : t T) (s_next : T -> t T)
  | iter (x : Operand.t T) (s_c : T -> t T) (s_f : T -> t T) (s_next : T -> t T).*)
End Source.