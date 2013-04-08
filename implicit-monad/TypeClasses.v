Require Import Classes.SetoidDec.

Set Implicit Arguments.

Class Monad (M : Type -> Type) : Type := {
  ret : forall A, A -> M A;
  bind : forall A B, M A -> (A -> M B) -> M B}.

Class Morphism (M1 M2 : Type -> Type) : Type := {
  lift : forall A, M1 A -> M2 A}.

Definition app {M1 M2 M3 M4 : Type -> Type}
  {monad1 : Monad M1} {monad2 : Monad M2} {monad3 : Monad M3} {monad4 : Monad M4}
  {f14 : Morphism M1 M4} {f24 : Morphism M2 M4} {f34 : Morphism M3 M4}
  (T1 T2 : Type) (e1 : M1 (T2 -> M3 T1)) (e2 : M2 T2)
  : M4 T1 :=
  bind _ (lift _ e1) (fun f =>
  bind _ (lift _ e2) (fun x =>
    lift _ (f x))).

Instance Id : Monad (fun A => A) := {
  ret A x := x;
  bind A B x f := f x }.

Instance Option : Monad option := {
  ret A x := Some x;
  bind A B x f :=
    match x with
    | Some x' => f x'
    | None => None
    end}.

Instance IdOfId : Morphism (fun A => A) (fun A => A) := {
  lift A x := x}.

Instance OptionOfOption : Morphism option option := {
  lift A x := x}.

Instance OptionOfId : Morphism (fun A => A) option := {
  lift A x := Some x}.

Definition gre :=
  app _ _
    (ret (M := fun A => A) (fun n => ret (M := option) (n + 1)))
    (ret (M := option) 23).

Compute gre.