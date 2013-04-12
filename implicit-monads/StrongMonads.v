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

Definition gret (m m' : Monad) A (x : @M m' A) : @M (m ++ m') A :=
  fun i =>
    let (i1, i2) := i in
    let o1 := strong_ret i1 in
    match x i2 with
    | (inl x', o2) => (inl x', (o1, o2))
    | (inr e, o2) => (inr (inr e), (o1, o2))
    end.

(*Definition gbind (m m' : Monad) A B
  (x : @M (m ++ m') A) (f : @M m' A -> @M (m ++ m') B)
  : @M (m ++ m') B :=
  fun i =>
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

Definition app {M1 M2 M3 M4 : Type -> Type}
  {monad1 : Monad M1} {monad2 : Monad M2} {monad3 : Monad M3} {monad4 : Monad M4}
  {f14 : Morphism M1 M4} {f24 : Morphism M2 M4} {f34 : Morphism M3 M4}
  (T1 T2 : Type) (e1 : M1 (T2 -> M3 T1)) (e2 : M2 T2)
  : M4 T1 :=
  bind _ (lift _ e1) (fun f =>
  bind _ (lift _ e2) (fun x =>
    lift _ (f x))).