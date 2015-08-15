(** Monads inference formalized using typeclasses *)
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

(** We experiment a general method to go from a function
    of type (A -> B) -> C to a function of type (A -> M B) -> M C *)

(** The continuation monad *)
Definition C (o : Type) := fun A => (A -> o) -> o.

Instance Continuation (o : Type) : Monad (C o) := {
  ret A x := fun k => k x;
  bind A B x f := fun k => x (fun x => f x k)}.

Definition callcc o A (f : (A -> o) -> o) : C o A :=
  f.

Definition run {M} {monad : Monad M} A (x : C (M A) A) : M A :=
  x (fun x => ret x).

Definition generalize {M} {monad : Monad M} T1 T2 T3
  (f : forall o, (T1 -> C o T2) -> C o T3)
  : (T1 -> M T2) -> M T3 :=
  fun g =>
    let g' := fun x => callcc (fun k => bind T3 (g x) k) in
    run (f _ g').

(** An example *)
Definition test5 (f : nat -> bool) : comparison :=
  if f 23 then
    Eq
  else
    Lt.

(** We do a monadic transform to the continuation monad *)
Definition monadic_test5 o (f : nat -> C o bool) : C o comparison :=
  bind _ (f 23) (fun b =>
  if b then
    ret Eq
  else
    ret Lt).

(** We get our generalized example *)
Definition test5' {M} {monad : Monad M} : (nat -> M bool) -> M comparison :=
  generalize monadic_test5.

Compute test5 (fun _ => true).
Compute test5 (fun _ => false).
Compute test5' (fun _ => Some true).
Compute test5' (fun _ => Some false).
Compute test5' (fun _ => None).

Definition generalize' {M} {monad : Monad M} T1 T2 T3
  (f : forall o o', (T1 o' -> C o (T2 o')) -> C o (T3 o'))
  : (T1 _ -> M (T2 _)) -> M (T3 _) :=
  fun g =>
    let g' := fun x => callcc (fun k => bind (T3 _) (g x) k) in
    run (f _ g').

Definition generalize' {M} {monad : Monad M} (T1 T2 : Type -> Type)
  (f : forall o, T1 o -> C o (T2 o))
  : T1 _ -> T2 _ :=
  fun g =>
    let g' := fun x => callcc (fun k => bind T3 (g x) k) in
    run (f _ g').

Definition gre {M} {monad : Monad M} (A B1 B2 R : Type)
  (f : forall o, (A -> C o (B1 -> C o B2)) -> C o R)
  (g : forall o, ) :=
  generalize (T2 := B1 -> C o B2) f.
