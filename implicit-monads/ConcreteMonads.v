(** Something incomplete but simple to get a first concrete result *)
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