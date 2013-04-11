(** Monads with stronger hypothesis to simplify composition *)
Require Import String.

Set Implicit Arguments.

Class Monad : Type := {
  I : Type;
  E : Type;
  O : Type;
  M : Type -> Type :=
    fun A => I -> (A + E) * O;
  strong_ret : I -> O;
  strong_bind : O -> I;
  ret : forall A, A -> M A :=
    fun A x i =>
      (inl x, strong_ret i);
  bind : forall A B, M A -> (A -> M B) -> M B :=
    fun A B x f i =>
      match x i with
      | (inl x', o) => f x' (strong_bind o)
      | (inr e, o) => (inr e, o)
      end}.

Instance Id : Monad := {
  I := unit;
  E := Empty_set;
  O := unit;
  strong_ret := fun _ => tt;
  strong_bind := fun _ => tt}.

Instance Option : Monad := {
  I := unit;
  E := unit;
  O := unit;
  strong_ret := fun _ => tt;
  strong_bind := fun _ => tt}.

Instance Error (E : Type) : Monad := {
  I := unit;
  E := E;
  O := unit;
  strong_ret := fun _ => tt;
  strong_bind := fun _ => tt}.

Instance Print : Monad := {
  I := list string;
  E := Empty_set;
  O := list string;
  strong_ret := fun i => i;
  strong_bind := fun o => o}.

Instance State (S : Type) : Monad := {
  I := S;
  E := Empty_set;
  O := S;
  strong_ret := fun i => i;
  strong_bind := fun o => o}.

Instance Loop : Monad := {
  I := nat;
  E := unit;
  O := nat;
  strong_ret := fun i => i;
  strong_bind := fun o => o}.