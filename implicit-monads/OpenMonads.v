(** Monads with an open structure to give more freedom to the run operations *)
Require Import String.
Require Import List.

Import ListNotations.

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

Definition seq {m : Monad} A (x : M.t unit) (f : M.t A) : M.t A :=
  bind x (fun _ => f).

Fixpoint run {m : Monad} A (x : M.t A) (I_of_O : O -> I) (i : I) : (A + E) * O :=
  match (M.open x) i with
  | (inl xe, o) => (xe, o)
  | (inr x, o) => run x I_of_O (I_of_O o)
  end.

Fixpoint run_with_break {m : Monad} A (x : M.t A) (I_of_O : O -> option I) : M.t A :=
  M.new (fun i =>
    match (M.open x) i with
    | (inl xe, o) => (inl xe, o)
    | (inr x, o) =>
      match I_of_O o with
      | Some i' => (M.open (run_with_break x I_of_O)) i'
      | None => (inr x, o)
      end
    end).

Definition combine (m1 m2 : Monad) : Monad := {|
  I := @I m1 * @I m2;
  E := @E m1 + @E m2;
  O := @O m1 * @O m2;
  O_of_I := fun i =>
    let (i1, i2) := i in
    (O_of_I i1, O_of_I i2)|}.

Infix "++" := combine.

Fixpoint gret {m m' : Monad} A (x : @M.t m' A) : @M.t (m ++ m') A :=
  M.new (m := m ++ m') (fun i =>
    let (i1, i2) := i in
    let o1 := O_of_I i1 in
    match (M.open x) i2 with
    | (inl (inl x'), o2) => (inl (inl x'), (o1, o2))
    | (inl (inr e), o2) => (inl (inr (inr e)), (o1, o2))
    | (inr x', o2) => (inr (gret x'), (o1, o2))
    end).

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

(** Coroutines *)
Instance Waiter (m : Monad) (A B : Type) : Monad := {
  I := A -> @M.t m B;
  E := Empty_set;
  O := option (A -> @M.t m B);
  O_of_I := fun i => Some i}.

Module Coroutine.
  Definition t {m : Monad} (A B T : Type) := @M.t (Waiter m A B ++ m) T.
  
  (*Definition new {m : Monad} A B (x : @M.t (Waiter A ++ m) B) : t A B :=
    x.*)
  
  Definition forget {m : Monad} A B : t A B unit :=
    M.new (m := Waiter m A B ++ m) (fun i =>
      let (_, i_m) := i in
      (inl (inl tt), (None, O_of_I i_m))).
  
  Definition use_on {m : Monad} A B (a : A) : t A B B :=
    M.new (m := Waiter m A B ++ m) (fun i =>
      let (f, i_m) := i in
      match (M.open (f a)) i_m with
      | (inl (inl y), o_m) => (inl (inl y), (Some f, o_m))
      | (inl (inr y), o_m) => (inl (inr (inr y)), (Some f, o_m))
      | (inr y, o_m) => (inr (gret y), (Some f, o_m))
      end).
  
  Definition yield {m : Monad} A B (a : A) : t A B B :=
    seq (forget _ _) (use_on _ a).
  
  Fixpoint force {m : Monad} A B T (x : t A B T) (f : A -> M.t B) : M.t (T + t A B T) :=
    M.new (fun i_m =>
      match (M.open x) (f, i_m) with
      | (inl (inl x'), (_, o_m)) => (inl (inl (inl x')), o_m)
      | (inl (inr (inr e)), (_, o_m)) => (inl (inr e), o_m)
      | (inl (inr (inl e)), _) => match e with end
      | (inr x', (Some f, o_m)) => (inr (force x' f), o_m)
      | (inr x', (None, o_m)) => (inl (inl (inr x')), o_m)
      end).
  
  Fixpoint terminate {m : Monad} A B T (x : t A B T) (f : A -> M.t B) : M.t T :=
    M.new (fun i_m =>
      match (M.open x) (f, i_m) with
      | (inl (inl x'), (_, o_m)) => (inl (inl x'), o_m)
      | (inl (inr (inr e)), (_, o_m)) => (inl (inr e), o_m)
      | (inl (inr (inl e)), _) => match e with end
      | (inr x', (_, o_m)) => (inr (terminate x' f), o_m)
      end).
End Coroutine.

Fixpoint iter_list {m : Monad} A (l : list A) : Coroutine.t A unit unit :=
  match l with
  | nil => ret tt
  | x :: l' => seq (Coroutine.yield _ x) (iter_list l')
  end.




