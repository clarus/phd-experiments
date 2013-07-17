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
    export : T -> {v : Value.t | invariant v};
    import : {v : Value.t | invariant v} -> T}.
  
  Definition is_involutive T (R : t T) : Prop :=
    forall (x : T),
    let v := proj1_sig (export R x) in
    forall (H : invariant R v),
      import R (exist _ v H) = x.
  
  Definition subset_lift T (R : t T) (P : T -> Prop) (Hinvolutive : is_involutive R)
    : t {x : T | P x}.
    refine {|
      invariant := fun v =>
        {H : invariant R v | P (import R (exist _ v H))};
      export := fun (xP : {x : T | P x}) =>
        let (x, P) := xP in
        exist _ (proj1_sig (export R x)) _;
      import := fun vH =>
        let (v, H) := vH in
        let (Hinv, HP) := H in
        exist _ (import R (exist _ v Hinv)) HP |}.
    exists (proj2_sig (export R x)).
    now rewrite (Hinvolutive x (proj2_sig (export R x))).
  Defined.
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
      export := fun p => exist _
        (Value.bits (export_aux p)) (Shape.IsBits.intro _);
      import := fun vH =>
        let (v, H) := vH in
        import_aux _ |}.
    destruct v; try exact bs;
      abstract (exfalso; inversion H).
  Defined.
  
  Lemma aux_is_involutive : forall p, import_aux (export_aux p) = p.
    induction p; simpl; congruence.
  Qed.
  
  Lemma r_positive_is_involutive : is_involutive r_positive.
    unfold is_involutive; simpl.
    intros; apply aux_is_involutive.
  Qed.
End Positive.