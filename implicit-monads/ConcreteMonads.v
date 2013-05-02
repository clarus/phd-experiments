(** Something incomplete but simple to get a first concrete result *)
Require Import List.

Import ListNotations.

Set Implicit Arguments.

Module Result.
  Inductive t (A B : Type) : Type :=
  | Val : A -> t A B
  | Err : B -> t A B.
  
  Arguments Val [A] [B] _.
  Arguments Err [A] [B] _.
End Result.

Import Result.

Class Monad : Type := {
  S : Type;
  E : Type;
  M (A : Type) : Type :=
    S -> S * (t A E)}.

Definition ret {m : Monad} A (x : A) : M A :=
  fun i => (i, Val x).

Definition bind {m : Monad} A B (x : M A) (f : A -> M B) : M B :=
  fun i =>
    match x i with
    | (o, Val x) => f x o
    | (o, Err e) => (o, Err e)
    end.

Instance Id : Monad := {
  S := unit;
  E := Empty_set}.

Definition combine (m1 m2 : Monad) : Monad := {|
  S := @S m1 * @S m2;
  E := @E m1 + @E m2|}.

Infix "++" := combine.

Definition combine_id (m : Monad) A (x : @M (Id ++ m) A) : @M m A :=
  fun i =>
    match x (tt, i) with
    | ((_, o), Val x) => (o, Val x)
    | (_, Err (inl e)) => match e with end
    | ((_, o), Err (inr e)) => (o, Err e)
    end.

Definition combine_commut (m1 m2 : Monad) A (x : @M (m1 ++ m2) A)
  : @M (m2 ++ m1) A :=
  fun i =>
    let (i2, i1) := i in
    match x (i1, i2) with
    | ((o1, o2), Val x) => ((o2, o1), Val x)
    | ((o1, o2), Err (inl e)) => ((o2, o1), Err (inr e))
    | ((o1, o2), Err (inr e)) => ((o2, o1), Err (inl e))
    end.

Definition combine_assoc_left (m1 m2 m3 : Monad) A (x : @M ((m1 ++ m2) ++ m3) A)
  : @M (m1 ++ (m2 ++ m3)) A :=
  fun i =>
    match i with
    | (i1, (i2, i3)) =>
      match x ((i1, i2), i3) with
      | (((o1, o2), o3), Val x) => ((o1, (o2, o3)), Val x)
      | (((o1, o2), o3), Err e) =>
        let e := match e with
          | inl (inl e1) => inl e1
          | inl (inr e2) => inr (inl e2)
          | inr e3 => inr (inr e3)
          end in
        ((o1, (o2, o3)), Err e)
      end
    end.

Definition combine_assoc_right (m1 m2 m3 : Monad) A (x : @M (m1 ++ (m2 ++ m3)) A)
  : @M ((m1 ++ m2) ++ m3) A :=
  fun i =>
    match i with
    | ((i1, i2), i3) =>
      match x (i1, (i2, i3)) with
      | ((o1, (o2, o3)), Val x) => (((o1, o2), o3), Val x)
      | ((o1, (o2, o3)), Err e) =>
        let e := match e with
          | inl e1 => inl (inl e1)
          | inr (inl e2) => inl (inr e2)
          | inr (inr e3) => inr e3
          end in
        (((o1, o2), o3), Err e)
      end
    end.

Definition gret {m m' : Monad} A (x : @M m' A) : @M (m ++ m') A :=
  fun i =>
    let (i1, i2) := i in
    match x i2 with
    | (o2, Val x) => ((i1, o2), Val x)
    | (o2, Err e) => ((i1, o2), Err (inr e))
    end.

Instance Option : Monad := {
  S := unit;
  E := unit}.

Definition option_none A : @M Option A :=
  fun _ => (tt, Err tt).

Definition option_run A (x : @M Option A) : option A :=
  match x tt with
  | (_, Val x) => Some x
  | (_, Err _) => None
  end.

Instance Error (E : Type) : Monad := {
  S := unit;
  E := E}.

Definition raise E A (e : E) : @M (Error E) A :=
  fun _ => (tt, Err e).

Instance Print (A : Type) : Monad := {
  S := list A;
  E := Empty_set}.

Definition print A (x : A) : @M (Print A) unit :=
  fun i => (x :: i, Val tt).

Instance State (S : Type) : Monad := {
  S := S;
  E := Empty_set}.

Definition read (S : Type) : @M (State S) S :=
  fun s => (s, Val s).

Definition write (S : Type) (x : S) : @M (State S) unit :=
  fun _ => (x, Val tt).

Instance Loop : Monad := {
  S := nat;
  E := unit}.

Definition partial_run {m m' : Monad} A (x : @M (m ++ m') A) (i_m : @S m)
  : @M (Error (@E m) ++ m') A :=
  fun i =>
    let (_, i_m') := i in
    match x (i_m, i_m') with
    | ((_, o_2), r) => ((tt, o_2), r)
    end.
