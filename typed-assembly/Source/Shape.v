(** Intermediate memory model. *)
Require Import List.
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
End Shape.