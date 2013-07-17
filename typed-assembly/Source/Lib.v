(** Common functions. *)
Require Import List.

Set Implicit Arguments.
Import ListNotations.

(*Module List.
  Module ForAll.
    Inductive t (A : Type) (P : A -> Type) : list A -> Type :=
    | nil : t P nil
    | cons : forall x l, P x -> t P l -> t P (x :: l).
  End ForAll.
  
  Module ForAll2.
    Inductive t (A B : Type) (P : A -> B -> Type) : list A -> list B -> Type :=
    | nil : t P nil nil
    | cons : forall x y l1 l2, P x y -> t P l1 l2 -> t P (x :: l1) (y :: l2).
  End ForAll2.
End List.*)