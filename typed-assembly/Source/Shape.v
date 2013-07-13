(** Intermediate memory model. *)

Module Shape.
  Inductive t : Set :=
  | block (n : nat)
  | array (n : nat) (content : t)
  | struct (fields : list t)
  | union (fields : list t)
  | pointer (target : t).
End Shape.