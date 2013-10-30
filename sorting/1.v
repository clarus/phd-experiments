(** A bubble sort implementation. *)
Require Import List.
Require Import Omega.

Set Implicit Arguments.

Module SafeList.
  Fixpoint nth A (l : list A) (i : nat) (Hi : i < length l) : A.
    destruct l as [|x l].
    - simpl in Hi.
      omega.
    - destruct i as [|i].
      + exact x.
      + refine (nth _ l i _).
        simpl in Hi.
        omega.
  Defined.
End SafeList.

Module Array.
  Definition t := list.
  
  Definition has_length A (a : t A) (n : nat) : Prop :=
    length a = n.
  
  Definition nth A (n : nat) (a : t A) (Hn : has_length a n)
    (i : nat) (Hi : i < n) : A.
    refine (SafeList.nth a (i := i) _).
    abstract congruence.
  Defined.
  
(*   Definition swap A (x y : A) (a : t A) (Hx : ) :  *)
End Array.