(** A bubble sort implementation. *)
Require Import List.
Require Import Omega.

Set Implicit Arguments.

Module List.
  Module Index.
    Record t A (l : list A) : Set := new {
      i : nat;
      spec : i < length l}.
  End Index.
  
  Fixpoint read A (l : list A) (i : Index.t l) : A.
    destruct i as [i Hi].
    destruct l as [|x l].
    - simpl in Hi.
      clear read; abstract omega.
    - destruct i as [|i].
      + exact x.
      + refine (read _ l (Index.new l (i := i) _)).
        simpl in Hi.
        clear read; abstract omega.
  Defined.
  
  Fixpoint write A (l : list A) (i : Index.t l) (x : A) {struct l} : list A.
    admit.
  Defined.
  
  Axiom write_keeps_length : forall A (l : list A) (i : Index.t l) (x : A),
    length (write i x) = length l.
End List.

Module Array.
  Record t A (l : list A) (n : nat) : Type := new {
    spec : n = length l}.
  
  Module Index.
    Record t A (l : list A) n (a : t l n) : Set := new {
      i : nat;
      spec : i < n}.
    
    Definition to_list_index A (l : list A) n
      (a : Array.t l n) (i : t a) : List.Index.t l.
      destruct i as [i Hi].
      refine (List.Index.new l (i := i) _).
      abstract (destruct a; simpl; omega).
    Defined.
    
    Definition from_modified_array A (l l' : list A) n
      (a : Array.t l n) (a' : Array.t l' n) (i : t a) : t a'.
      destruct i as [i Hi].
      refine (new a' Hi).
    Defined.
  End Index.
  
  Definition read A (l: list A) n
    (a : t l n) (i : Index.t a) : A :=
    List.read (Index.to_list_index i).
  
  Definition write A (l : list A) n
    (a : t l n) (i : Index.t a) (x : A)
    : t (List.write (Index.to_list_index i) x) n.
    apply new.
    abstract (
      assert (H := List.write_keeps_length (Index.to_list_index i) x);
      destruct a;
      omega).
  Defined.
  
  Definition swap A (l : list A) n
    (a : t l n) (i j : Index.t a) : t _ n :=
    let x := read i in
    let y := read j in
    let a := write i y in
    let j := Index.from_modified_array a j in
    write j x.
End Array.