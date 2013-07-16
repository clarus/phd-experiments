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
  
  Definition involutive T (R : t T) : Prop :=
    forall (v : T), import R (export R v) = v.
  
  Definition r_positive : t positive.
    refine {|
    invariant := Shape.IsBits.t;
    export := fun p =>
      let fix export p :=
        match p with
        | xH => []
        | xO p => false :: export p
        | xI p => true :: export p
        end in
      exist _ (Value.bits (export p)) _;
    import := fun v =>
      let fix import bs :=
        match bs with
        | nil => xH
        | false :: bs => xO (import bs)
        | true :: bs => xI (import bs)
        end in
      let (v, P) := v in
      _ |}.
    - constructor.
    
    - inversion P.
  
  Definition r_nat : t nat := {|
    invariant := fun _ => True;
    export := fix export n :=
      Pos.of_nat|}.
End Reifiable.