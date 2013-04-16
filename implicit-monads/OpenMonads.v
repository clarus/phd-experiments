(** Monads with an open structure to give more freedom to the run operations *)
Require Import String.

Set Implicit Arguments.

Class Monad : Type := {
  I : Type;
  E : Type;
  O : Type;
  O_of_I : I -> O}.

Module M.
  Inductive t {m : Monad} (A : Type) : Type :=
  | new : (I -> (A + E + t A) * O) -> t A.
  
  Definition open {m : Monad} A (x : t A) :=
    match x with
    | new x' => x'
    end.
End M.

Instance Id : Monad := {
  I := unit;
  E := Empty_set;
  O := unit;
  O_of_I := fun _ => tt}.

Definition ret {m : Monad} A (x : A) : M.t A :=
  M.new (fun i => (inl (inl x), O_of_I i)).

Fixpoint bind {m : Monad} A B (x : M.t A) (f : A -> M.t B) : M.t B :=
  M.new (fun i =>
    match (M.open x) i with
    | (inl xe, o) =>
      match xe with
      | inl x => (inr (f x), o)
      | inr e => (inl (inr e), o)
      end
    | (inr x, o) => (inr (bind x f), o)
    end).

Fixpoint run {m : Monad} A (x : M.t A) (I_of_O : O -> I) (i : I) : (A + E) * O :=
  match (M.open x) i with
  | (inl xe, o) => (xe, o)
  | (inr x, o) => run x I_of_O (I_of_O o)
  end.

Definition combine (m1 m2 : Monad) : Monad := {|
  I := @I m1 * @I m2;
  E := @E m1 + @E m2;
  O := @O m1 * @O m2;
  O_of_I := fun i =>
    let (i1, i2) := i in
    (O_of_I i1, O_of_I i2)|}.

Infix "++" := combine.

Instance Option : Monad := {
  I := unit;
  E := unit;
  O := unit;
  O_of_I := fun _ => tt}.

Definition option_none A : @M.t Option A :=
  M.new (fun _ => (inl (inr tt), tt)).

Definition option_run A (x : @M.t Option A) : option A :=
  match run x (fun _ => tt) tt with
  | (inl x', _) => Some x'
  | _ => None
  end.

Instance Error (E : Type) : Monad := {
  I := unit;
  E := E;
  O := unit;
  O_of_I := fun _ => tt}.

Instance Print : Monad := {
  I := list string;
  E := Empty_set;
  O := list string;
  O_of_I := fun i => i}.

Instance State (S : Type) : Monad := {
  I := S;
  E := Empty_set;
  O := S;
  O_of_I := fun i => i}.

Instance Loop : Monad := {
  I := nat;
  E := unit;
  O := nat;
  O_of_I := fun i => i}.