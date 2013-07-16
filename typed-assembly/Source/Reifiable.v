(** Reification to bonary values. *)
Require Import PArith.
Require Import List.
Require Import Memory.

Set Implicit Arguments.
Import ListNotations.

Module Reifiable.
  Record t (T : Type) : Type := new {
    invariant : Value.t -> Prop;
    export : T -> {v : Value.t | invariant v};
    import : {v : Value.t | invariant v} -> T}.
  
  Definition involutive T (R : t T) : Prop :=
    forall (v : T), import R (export R v) = v.
  
  (** We are little-endian. *)
  Definition r_positive : t positive := {|
    invariant := fun _ => True;
    export := fun p =>
      let fix export p :=
        match p with
        | xH => []
        | xO p => false :: export p
        | xI p => true :: export p
        end in
      exist _ (Value.bits (export p)) I
    import := fun v =>
      |}.
  
  Definition r_nat : t nat := {|
    invariant := fun _ => True;
    export := fix export n :=
      Pos.of_nat|}.
End Reifiable.