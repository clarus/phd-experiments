(** Monads with stronger hypothesis to simplify composition.
    See OpenMonads.v for a better system. *)
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

Definition sum (m1 m2 : Monad) : Monad := {|
  I := @I m1 * @I m2;
  E := @E m1 + @E m2;
  O := @O m1 * @O m2;
  strong_ret := fun i =>
    let (i1, i2) := i in
    (strong_ret i1, strong_ret i2);
  strong_bind := fun o =>
    let (o1, o2) := o in
    (strong_bind o1, strong_bind o2)|}.

Infix "++" := sum.

Class Le (m1 m2 : Monad) : Type := {
  lift : forall A, @M m1 A -> @M m2 A}.

Definition gret (m m' : Monad) A (x : @M m' A) : @M (m ++ m') A :=
  fun i =>
    let (i1, i2) := i in
    let o1 := strong_ret i1 in
    match x i2 with
    | (inl x', o2) => (inl x', (o1, o2))
    | (inr e, o2) => (inr (inr e), (o1, o2))
    end.

(*Definition gbind (m m' : Monad) A B
  (x : @M (m ++ m') A) (f : @M m' A -> @M m B)
  : @M m B :=
  fun i =>
    f (fun i' =>
      match x (i, i') with
      | 
      end)
    match x i with
    | (inl x', (o1, o2)) => (fun i2 => )
    end
    let (i1, i2) := i in
    let o1 := strong_ret i1 in
    match x i2 with
    | (inl x', o2) => (inl x', (o1, o2))
    | (inr e, o2) => (inr (inr e), (o1, o2))
    end.*)

Definition sum_id (m : Monad) A (x : @M (Id ++ m) A) : @M m A :=
  fun i =>
    match x (tt, i) with
    | (inl x', (_, o)) => (inl x', o)
    | (inr (inr e), (_, o)) => (inr e, o)
    | (inr (inl e), _) => match e with end
    end.

Definition sum_commut (m1 m2 : Monad) A (x : @M (m1 ++ m2) A)
  : @M (m2 ++ m1) A :=
  fun i =>
    let (i2, i1) := i in
    match x (i1, i2) with
    | (inl x', (o1, o2)) => (inl x', (o2, o1))
    | (inr e, (o1, o2)) =>
      (inr match e with
      | inl e1 => inr e1
      | inr e2 => inl e2
      end, (o2, o1))
    end.

Definition sum_assoc (m1 m2 m3 : Monad) A (x : @M ((m1 ++ m2) ++ m3) A)
  : @M (m1 ++ (m2 ++ m3)) A :=
  fun i =>
    match i with
    | (i1, (i2, i3)) =>
      match x ((i1, i2), i3) with
      | (inl x', ((o1, o2), o3)) => (inl x', (o1, (o2, o3)))
      | (inr e, ((o1, o2), o3)) =>
        let e := match e with
          | inl (inl e1) => inl e1
          | inl (inr e2) => inr (inl e2)
          | inr e3 => inr (inr e3)
          end in
        (inr e, (o1, (o2, o3)))
      end
    end.

Instance Option : Monad := {
  I := unit;
  E := unit;
  O := unit;
  strong_ret := fun _ => tt;
  strong_bind := fun _ => tt}.

Definition option_none A : @M Option A :=
  fun _ => (inr tt, tt).

Definition option_run A (x : @M Option A) : option A :=
  match x tt with
  | (inl x', _) => Some x'
  | _ => None
  end.

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

Definition app {m1 m2 m3 m4 : Monad}
  {f14 : Le m1 m4} {f24 : Le m2 m4} {f34 : Le m3 m4}
  (T1 T2 : Type) (e1 : @M m1 (T2 -> @M m3 T1)) (e2 : @M m2 T2)
  : @M m4 T1 :=
  bind (lift e1) (fun f =>
  bind (lift e2) (fun x =>
    lift (f x))).

Instance AnyOfId {m : Monad} : Le Id m := {
  lift A x :=
    match x tt with
    | (inl x', _) => ret x'
    | (inr e, _) => match e with end
    end}.

Instance AnyOfAny {m : Monad} : Le m m := {
  lift A x := x}.

(** Examples *)
Definition test0 := fun n => ret (Monad := Option) (n + 1).
Compute option_run (test0 12).

Definition test1 (m : Monad) := app (ret (fun n => ret (n + 1))) (ret 23).
Compute option_run (test1 _).

Definition decr (n : nat) : @M Option nat :=
  match n with
  | 0 => option_none _
  | S n' => ret n'
  end.

Definition test2 := fun n => app (ret decr) (app (ret decr) (ret n)).

Compute option_run (test2 12).
Compute option_run (test2 1).

Definition compose A B C (f : B -> C) (g : A -> B) x := f (g x).

Definition compose' {m : Monad}
  (A B C : Type) (f : B -> M C) (g : A -> M B) (x : A) : M C :=
  app (ret f) (app (ret g) (ret x)).

Definition test3 {m : Monad} :=
  app (app (ret (compose' (m := _) (C := _))) (ret decr)) (ret decr).

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



