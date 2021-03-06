(** Something incomplete but simple to get a first concrete result.*)
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

Lemma monad_law1 {m : Monad} A B (x : A) (f : A -> M B)
  : bind (ret x) f = f x.
trivial.
Qed.

Lemma monad_law2 {m : Monad} A (x : M A)
  : forall i, bind x (ret (A := _)) i = x i.
  intro i.
  unfold bind, ret.
  destruct (x i).
  tauto.
Qed.

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

Definition lift {m m' : Monad} A (x : @M m' A) : @M (m ++ m') A :=
  fun i =>
    let (i1, i2) := i in
    match x i2 with
    | (o2, Val x) => ((i1, o2), Val x)
    | (o2, Err e) => ((i1, o2), Err (inr e))
    end.

(** Inference *)
Parameter I : list bool -> Type -> Type.

Definition l0 := [false; false; false; false; false].
Definition l1 := [false; false; true; false; true].
Definition l2 := [true; false; true; true; false].
Definition l3 := [true; false; true; true; true].

Fixpoint union (l1 l2 : list bool) : list bool :=
  match (l1, l2) with
  | ([], []) => []
  | (b1 :: l1, b2 :: l2) => orb b1 b2 :: union l1 l2
  | _ => []
  end.

Fixpoint is_le (l1 l2 : list bool) : bool :=
  match (l1, l2) with
  | ([], []) => true
  | (b1 :: l1, b2 :: l2) => andb (implb b1 b2) (is_le l1 l2)
  | _ => false
  end.

Definition L := list bool.

Definition Constraint := L -> bool.

Parameters C1 C2 : Constraint.
Parameter Cand : Constraint -> Constraint -> Constraint.

Parameters T1 T2 : L -> Type.

Parameter e1 : forall l, C1 l = true -> T1 l -> I l (T2 l).
Parameter e2 : forall l, C2 l = true -> I l (T1 l).

Parameter pi1 : forall l C1 C2, Cand C1 C2 l = true -> C1 l = true.
Parameter pi2 : forall l C1 C2, Cand C1 C2 l = true -> C2 l = true.

Parameter bind' : forall l A B, I l A -> (A -> I l B) -> I l B.

Definition app_e1_e2 := fun l c => bind' (@e2 l (pi2 c)) (@e1 l (pi1 c)).

Definition l' :=
  let l' := _ in (fun (_ : forall l, is_le l' l = true -> _) => l') app_e1_e2.
Compute l'.

Check app_e1_e2 l' eq_refl.

Check let n := 12 in let m := 12 in eq_refl : n = m.
Fail Check fun n => let m := 12 in eq_refl : n = m.

(** Inference (old) *)
Definition nb_monads : nat := 5.

(*Definition flags := { l : list bool | length l = nb_monads}. *)

Parameter I : list bool -> Monad.

Fixpoint union (f1 f2 : list bool) : list bool :=
  match (f1, f2) with
  | ([], []) => []
  | (b1 :: f1, b2 :: f2) => orb b1 b2 :: union f1 f2
  | _ => []
  end.

(** Tests *)
Definition f0 := [false; false; false; false; false].
Definition f1 := [false; false; true; false; true].
Definition f2 := [true; false; true; true; false].
Definition f3 := [true; false; true; true; true].

Definition f1f2 := union f1 f2.
Compute f1f2.

Definition f1' := fun b1 b2 => [false; b1; b2; false; true].
Compute fun b1 b2 => union (f1' b1 b2) f2.
Compute fun b1 b2 => union f2 (f1' b1 b2).

Check (fun _ : @M (I [false; false; true; false; true]) nat => tt)
  (ret (m := I (f1' _ _)) 0).

Fixpoint is_le (f1 f2 : list bool) : bool :=
  match (f1, f2) with
  | ([], []) => true
  | (b1 :: f1, b2 :: f2) => andb (implb b1 b2) (is_le f1 f2)
  | _ => false
  end.

Parameter lift' : forall (f1 f2 : list bool) A,
  is_le f1 f2 = true -> @M (I f1) A -> @M (I f2) A.

Check fun A (x : @M (I f1) A) =>
  lift' (f1 := f1) f3 eq_refl x.

Definition force_same_type A (_ _ : A) : unit := tt.

Check fun A =>
  fun x1 : forall f, @M (I (union f1 f)) A =>
  fun x2 : forall f, @M (I (union f2 f)) A =>
    force_same_type (x1 [_; _; _; _; _]) (x2 [_; _; _; _; _]).

Check fun A =>
  fun x1 : forall f, @M (I (union f1 f)) A =>
  fun x2 : @M (I f3) A =>
    force_same_type (x1 [_; _; _; _; _]) x2.

Parameter test_map : forall f, forall A B,
  (A -> @M (I (union f1 f)) B) ->
  @M (I (union f0 f)) (list B).

Parameter test_fun : forall f,
  nat -> @M (I (union f2 f)) bool.

Check test_map [_; _; _; _; _] (test_fun [_; _; _; _; _]).

Check fun A =>
  fun x1 : @M (I (union f1 [_; _; _; _; _])) A =>
  fun x2 : @M (I f3) A =>
    force_same_type x1 x2.

Check fun A =>
  let f := [_; _; _; _; _] in
  fun x1 : @M (I (union f1 f)) A =>
  fun x2 : @M (I f3) A =>
    force_same_type x1 x2.

Parameter F : list bool -> Type.

Check fun (x1 : F f1) (x2 : F (_ :: _)) => force_same_type x1 x2.

Parameter e1 : forall f, F (union f1 f).
Parameter e2 : F f2.
Parameter e3 : F f3.

Parameter liftF : forall f1 f2, is_le f1 f2 = true -> F f1 -> F (union f2.

Check let f := _ in liftF (f1 := f1) f eq_refl (e1 ) : F f3.

Class ListUnion (l1 l2 : list bool) := Union : list bool.

Instance UnionNil : ListUnion [] [] :=
  [].

Instance UnionCons b1 b2 l1 l2 : ListUnion (b1 :: l1) (b2 :: l2) :=
  (orb b1 b2) :: Union.

Check fun A =>
  let f := [_; _; _; _; _] in
  fun x1 : @M (I (Union (l1 := f1) (l2 := f))) A =>
  fun x2 : @M (I f2) A =>
    force_same_type x1 x2.

Require Import Vector.

Definition union' n := Vector.map2 (n := n) orb.

Parameter I' : Vector.t bool nb_monads -> Monad.

Definition f1v := Vector.of_list f1.
Definition f3v := Vector.of_list f3.

Check fun A =>
  fun x1 : @M (I' (union' f1v _)) A =>
  fun x2 : @M (I' f3v) A =>
    force_same_type x1 x2.
