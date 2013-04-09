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

Arguments app {M1 M2 M3 M4 monad1 monad2 monad3 monad4 f14 f24 f34} [T1 T2] e1 e2.

(* Definition let' {M1 M2 M3 : Type -> Type}
  {monad1 : Monad M1} {monad2 : Monad M2} {monad3 : Monad M3}
  {f13 : Morphism M1 M3} {f23 : Morphism M2 M3}
  (T1 T2 : Type) (e1 : M1 T1) (e2 : T1 -> M2 T2)
  : M3 T2 :=
  . *)

Definition id := fun (A : Type) => A.

Instance Id : Monad id := {
  ret A x := x;
  bind A B x f := f x }.

Instance Option : Monad option := {
  ret A x := Some x;
  bind A B x f :=
    match x with
    | Some x' => f x'
    | None => None
    end}.

Instance AnyOfId {M} {monad : Monad M} : Morphism id M := {
  lift A x := ret x}.

Instance AnyOfAny {M} {monad : Monad M} : Morphism M M := {
  lift A x := x}.

Definition bot A (x : A) : id A := ret (M := id) x.

(** Examples *)
Definition test1 := app (bot (fun n => Some (n + 1))) (Some 23).

Compute test1.

Definition decr (n : nat) : option nat :=
  match n with
  | O => None
  | S n' => Some n'
  end.

Definition test2 := fun n => app (bot decr) (app (bot decr) (bot n)).

Compute test2 12.
Compute test2 1.

Definition compose A B C (f : B -> C) (g : A -> B) x := f (g x).

Definition compose' {M} {monad : Monad M}
  (A B C : Type) (f : B -> M C) (g : A -> M B) (x : A) : M C :=
  app (bot f) (app (bot g) (bot x)).

Definition test3 :=
  app (M1 := id) (M2 := id) (M3 := id) (M4 := id)
    (app (M1 := id) (M2 := id) (compose' _) decr)
    decr.

Compute test3 12.
Compute test3 1.

Definition identity {M} {monad : Monad M} A (x : A) : M A := ret x.

Definition iapp (f : nat -> option nat) : option nat := f 12.

Definition test4 := app (M1 := id) (M2 := id) iapp (identity (A := _)).