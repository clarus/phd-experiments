(** A bubble sort implementation. *)
Require Import List.
Require Import Omega.
Require Import Program.

Set Implicit Arguments.

Module Sig.
  Definition new := exist.
  Definition val := proj1_sig.
  Definition spec := proj1_sig.
End Sig.

Module List.
  Module Index.
    Definition t A (l : list A) := {i : nat | i < length l}.
    
    Definition new A (l : list A) i H : t l := exist _ i H.
    
    (*Definition from_new_list A (l l' : list A)
      (i : t l) (H : length l = length l') : t l'.
      refine (new l' (i := Index.i i) _).
      destruct i.
      abstract (simpl; omega).
    Defined.
    
    Definition dup A (l : list A) (i : t l)
      B (l' : list B) H : t l':=
      new l' (i := Index.i i) H.*)
  End Index.
  
  Ltac destruct_index_omega :=
    match goal with
    | [i : Index.t _ |- _] =>
      destruct i; simpl in *;
      omega
    end.
  
  Program Fixpoint read A (l : list A) (i : Index.t l) : A :=
    match l with
    | nil => !
    | cons x l =>
      match i with
      | O => x
      | S i => read i
      end
    end.
  Next Obligation.
    destruct_index_omega.
  Qed.
  Next Obligation.
    destruct_index_omega.
  Qed.
  
  Program Fixpoint write A (l : list A) (i : Index.t l) (x : A) : list A :=
    match l with
    | nil => !
    | cons x' l =>
      match i with
      | O => cons x l
      | S i => cons x (write i x)
      end
    end.
  Next Obligation.
    destruct_index_omega.
  Qed.
  Next Obligation.
    destruct_index_omega.
  Qed.
  
  Lemma write_keeps_length : forall A (l : list A) (i : Index.t l) (x : A),
    length (write i x) = length l.
    intros A l i x.
    induction l; simpl.
    - destruct_index_omega.
    - destruct i as [i]; destruct i; simpl; auto.
  Qed.
  
  Program Definition write_modifies_lemma : Prop :=
    forall A (l : list A) (i : Index.t l) (x : A),
      read (Index.new (i := i) (write i x) _) = x.
  Next Obligation.
    rewrite write_keeps_length.
    now destruct i.
  Qed.
  
  Lemma write_modifies : write_modifies_lemma.
    intros A l i x.
    induction l; simpl.
    - destruct_index_omega.
    - destruct i as [i]; destruct i; simpl; trivial.
      (* TODO *)
  Qed.
  
  Program Lemma write_modifies : forall A (l : list A) (i : Index.t l) (x : A),
    read (Sig.new _ (Sig.val i) _ : Index.t (write i x)) = x.
  
  Definition write_modifies_lemma : Prop.
    refine (forall A (l : list A) (i : Index.t l) (x : A),
      read (Index.dup i (write i x) _) = x).
  
  Axiom write_modifies : forall A (l : list A) (i : Index.t l) (x : A),
    read (from_new_list
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
    
    Definition from_new_array A (l l' : list A) n
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