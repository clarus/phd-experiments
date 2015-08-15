(** Intermediate memory model. *)
Require Import List.
Require Import Lib.
Require Import Memory.

Set Implicit Arguments.
Import ListNotations.

Module Shape.
  Inductive t : Set :=
  | bits (n : nat)
  | array (n : nat) (content : t)
  | struct (fields : list t)
  | union (fields : list t)
  (*| pointer (target : t)*).

(*  Fixpoint check (s : t) (v : Value.t) : Prop :=
    match (s, v) with
    | (bits n, Value.bits bs) => length bs = n
    | (array n s, Value.array vs) => length vs = n /\ Forall (check s) vs
    | (struct ss, Value.struct vs) => Forall2 check ss vs
    | (union ss, Value.union i v) => exists s,
      nth_error ss i = Some s /\ check s v
    | _ => False
    end.*)

  Module Check.
    Inductive t : t -> Value.t -> Prop :=
    | bits : forall bs,
      t (bits (length bs)) (Value.bits bs)
    | array : forall vs s,
      Forall (t s) vs ->
      t (array (length vs) s) (Value.array vs)
    | struct : forall vs ss,
      Forall2 t ss vs ->
      t (struct ss) (Value.struct vs)
    | union : forall i v ss s,
      nth_error ss i = Some s ->
      t s v ->
      t (union ss) (Value.union i v).
  End Check.

  Module IsBits.
    Inductive t : Value.t -> Prop :=
    | intro : forall bs, t (Value.bits bs).
  End IsBits.
End Shape.
