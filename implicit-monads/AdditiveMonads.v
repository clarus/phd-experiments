(** Formalization of monads with a commutative sum operation to combine them.
    See StrongMonads.v for a better version. *)
Require Import String.

Set Implicit Arguments.

Class Monad : Type := {
  I : Type;
  O : Type;
  E : Type;
  M : Type -> Type :=
    fun A => I -> (A + E) * O;
  ret : forall A, A -> M A;
  bind : forall A B, M A -> (A -> M B) -> M B}.

Definition monadic_sum {m1 m2 : Monad} : Monad := {|
  I := @I m1 * @I m2;
  O := @O m1 * @O m2;
  E := @E m1 + @E m2;
  ret := fun _ x i =>
    let (i1, i2) := i in
    match (ret x i1, ret x i2) with
    | ((inl _, o1), (inl _, o2)) => (inl x, (o1, o2))
    | ((inl _, o1), (inr e2, o2)) => (inr (inr e2), (o1, o2))
    | ((inr e1, o1), (_, o2)) => (inr (inl e1), (o1, o2))
    end;
  bind := fun _ _ x f i =>
     match x i with
     | (inl x', (o1, o2)) =>
      let x1 := fun i1 => 
      end
     | (inr e, (o1, o2) => (inr e, (o1, o2))
     end |}.

Infix "·" := monadic_sum (at level 50, left associativity).

Instance Id : Monad := {
  I := unit;
  O := unit;
  E := Empty_set;
  ret := fun _ x _ => (inl x, tt)}.

Instance Option : Monad := {
  I := unit;
  O := unit;
  E := unit;
  ret := fun _ x _ => (inl x, tt)}.

Instance Error (E : Type) : Monad := {
  I := unit;
  O := unit;
  E := E;
  ret := fun _ x _ => (inl x, tt)}.

Instance Print : Monad := {
  I := unit;
  O := list string;
  E := Empty_set;
  ret := fun _ x _ => (inl x, nil)}.

Instance State (S : Type) : Monad := {
  I := S;
  O := S;
  E := Empty_set;
  ret := fun _ x s => (inl x, s)}.

Instance Loop : Monad := {
  I := nat;
  O := unit;
  E := unit;
  ret := fun _ x _ => (inl x, tt)}.