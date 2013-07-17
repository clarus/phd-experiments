(** Reification to bonary values. *)
Require Import PArith.
Require Import List.
Require Import Memory.
Require Import Shape.

Set Implicit Arguments.
Import ListNotations.

Module Reifiable.
  Record t (T : Type) : Type := new {
    invariant : Value.t -> Prop;
    export : T -> {v : Value.t & invariant v};
    import : {v : Value.t & invariant v} -> T}.
  
  Definition involutive T (R : t T) : Prop :=
    forall (v : T), import R (export R v) = v.
End Reifiable.

Module Positive.
  Import Reifiable.
  
  Fixpoint export_aux p :=
    match p with
    | xH => []
    | xO p => false :: export_aux p
    | xI p => true :: export_aux p
    end.
  
  Fixpoint import_aux bs :=
    match bs with
    | nil => xH
    | false :: bs => xO (import_aux bs)
    | true :: bs => xI (import_aux bs)
    end.
  
  Definition r_positive : t positive.
    refine {|
    invariant := Shape.IsBits.t;
    export := fun p => existT _
      (Value.bits (export_aux p)) (Shape.IsBits.intro _);
    import := fun vP =>
      let (v, P) := vP in
      import_aux _ |}.
    destruct v; try exact bs;
      abstract (exfalso; inversion P).
  Defined.
  
  Lemma aux_is_involutive : forall p, import_aux (export_aux p) = p.
    induction p; simpl; congruence.
  Qed.
  
  Lemma r_positive_is_involutive : involutive r_positive.
    unfold involutive; simpl.
    exact aux_is_involutive.
  Qed.
End Positive.