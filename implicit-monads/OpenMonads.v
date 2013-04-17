(** Monads with an open structure to give more freedom to the run operations *)
Require Import Arith.
Require Import List.
Require Import String.

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

Definition seq {m : Monad} A B (x : M.t A) (f : M.t B) : M.t B :=
  bind x (fun _ => f).

Fixpoint run {m : Monad} A (x : M.t A) (I_of_O : O -> I) (i : I) : (A + E) * O :=
  match (M.open x) i with
  | (inl xe, o) => (xe, o)
  | (inr x, o) => run x I_of_O (I_of_O o)
  end.

(*Fixpoint run_with_break {m : Monad} A (x : M.t A) (I_of_O : O -> option I) : M.t A :=
  M.new (fun i =>
    match (M.open x) i with
    | (inl xe, o) => (inl xe, o)
    | (inr x, o) =>
      match I_of_O o with
      | Some i' => (M.open (run_with_break x I_of_O)) i'
      | None => (inr x, o)
      end
    end).*)

Definition combine (m1 m2 : Monad) : Monad := {|
  I := @I m1 * @I m2;
  E := @E m1 + @E m2;
  O := @O m1 * @O m2;
  O_of_I := fun i =>
    let (i1, i2) := i in
    (O_of_I i1, O_of_I i2)|}.

Infix "++" := combine.

(*Definition sum_id (m : Monad) A (x : @M (Id ++ m) A) : @M m A :=
  fun i =>
    match x (tt, i) with
    | (inl x', (_, o)) => (inl x', o)
    | (inr (inr e), (_, o)) => (inr e, o)
    | (inr (inl e), _) => match e with end
    end.*)

Fixpoint combine_commut (m1 m2 : Monad) A (x : @M.t (m1 ++ m2) A)
  : @M.t (m2 ++ m1) A :=
  M.new (m := m2 ++ m1) (fun i =>
    let (i2, i1) := i in
    match (M.open x) (i1, i2) with
    | (inl (inl x'), (o1, o2)) => (inl (inl x'), (o2, o1))
    | (inl (inr e), (o1, o2)) =>
      (inl (inr match e with
      | inl e1 => inr e1
      | inr e2 => inl e2
      end), (o2, o1))
    | (inr x', (o1, o2)) => (inr (combine_commut x'), (o2, o1))
    end).

(*Definition sum_assoc (m1 m2 m3 : Monad) A (x : @M ((m1 ++ m2) ++ m3) A)
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
    end.*)

Fixpoint gret {m m' : Monad} A (x : @M.t m' A) : @M.t (m ++ m') A :=
  M.new (m := m ++ m') (fun i =>
    let (i1, i2) := i in
    let o1 := O_of_I i1 in
    match (M.open x) i2 with
    | (inl (inl x'), o2) => (inl (inl x'), (o1, o2))
    | (inl (inr e), o2) => (inl (inr (inr e)), (o1, o2))
    | (inr x', o2) => (inr (gret x'), (o1, o2))
    end).

Fixpoint run_with_break {m m' : Monad} A
  (x : @M.t (m ++ m') A) (I_of_O : @O m -> @I m) (i_m : @I m)
  : @M.t m' (A + @M.t (m ++ m') A) :=
  M.new (fun i_m' =>
    match (M.open x) (i_m, i_m') with
    | (inl (inl x'), (_, o_m')) => (inl (inl (inl x')), o_m')
    | (inl (inr (inr e_m')), (_, o_m')) => (inl (inr e_m'), o_m')
    | (inl (inr (inl _)), (_, o_m')) => (inl (inl (inr x)), o_m')
    | (inr x', (o_m, o_m')) => (inr (run_with_break x' I_of_O (I_of_O o_m)), o_m')
    end).

Fixpoint run_with_break_n {m m' : Monad} A
  (x : @M.t (m ++ m') A) (I_of_O : @O m -> @I m) (i_m : @I m) (n : nat)
  : @M.t m' (A + @M.t (m ++ m') A) :=
  match n with
  | 0 => ret (inr x)
  | S n' => bind (run_with_break x I_of_O i_m) (fun x' =>
    match x' with
    | inl r => ret (inl r)
    | inr x' => run_with_break_n x' I_of_O i_m n'
    end)
  end.

Definition run_with_break_terminate {m m' : Monad} A
  (x : @M.t (m ++ m') A) (I_of_O : @O m -> @I m) (i_m : @I m)
  : @M.t m' (option A) :=
  let fix aux (x : @M.t (m ++ m') A) (i'_m : @I m) : @M.t m' (option A) :=
    M.new (fun i_m' =>
      match (M.open x) (i'_m, i_m') with
      | (inl (inl x'), (_, o_m')) => (inl (inl (Some x')), o_m')
      | (inl (inr (inr e_m')), (_, o_m')) => (inl (inr e_m'), o_m')
      | (inr x', (o_m, o_m')) => (inr (aux x' (I_of_O o_m)), o_m')
      | (inl (inr (inl _)), (_, o_m')) =>
        (* if the computation fails with restart with [i_m] instead of [i'_m] *)
        (inr (M.new (fun i_m' =>
          match (M.open x) (i_m, i_m') with
          | (inl (inl x'), (_, o_m')) => (inl (inl (Some x')), o_m')
          | (inl (inr (inr e_m')), (_, o_m')) => (inl (inr e_m'), o_m')
          | (inr x', (o_m, o_m')) => (inr (aux x' (I_of_O o_m)), o_m')
          | (inl (inr (inl _)), (_, o_m')) =>
            (* if the computation fails even with [i_m] we stop *)
            (inl (inl (None)), o_m')
          end)), o_m')
      end) in
  aux x i_m.

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

Instance Print (A : Type) : Monad := {
  I := list A;
  E := Empty_set;
  O := list A;
  O_of_I := fun i => i}.

Definition print A (x : A) : @M.t (Print A) unit :=
  M.new (m := Print A) (fun i =>
    (inl (inl tt), x :: i)).

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
  I := option (A -> @M.t m B);
  E := unit;
  O := option (A -> @M.t m B);
  O_of_I := fun i => i}.

Module Coroutine.
  Definition t {m : Monad} (A B T : Type) := @M.t (Waiter m A B ++ m) T.
  
  Definition yield {m : Monad} A B (a : A) : t A B B :=
    M.new (m := Waiter m A B ++ m) (fun i =>
      let (f, i_m) := i in
      match f with
      | Some f' =>
        match (M.open (f' a)) i_m with
        | (inl (inl y), o_m) => (inl (inl y), (None, o_m))
        | (inl (inr e_m), o_m) => (inl (inr (inr e_m)), (None, o_m))
        | (inr y, o_m) => (inr (gret y), (None, o_m))
        end
      | None => (inl (inr (inl tt)), O_of_I i)
      end).
  
  Definition force {m : Monad} A B T (x : t A B T) (f : A -> M.t B) : M.t (T + t A B T) :=
    run_with_break x (fun o => o) (Some f).
  
  Definition force_n {m : Monad} A B T (x : t A B T) (n : nat) (f : A -> M.t B) : M.t (T + t A B T) :=
    run_with_break_n x (fun o => o) (Some f) n.
  
  Definition terminate {m : Monad} A B T (x : t A B T) (f : A -> M.t B) : M.t (option T) :=
    run_with_break_terminate x (fun o => o) (Some f).
End Coroutine.

Fixpoint iter_list {m : Monad} A (l : list A) : Coroutine.t A unit unit :=
  match l with
  | nil => ret tt
  | x :: l' => seq (Coroutine.yield _ x) (iter_list l')
  end.

Definition test_it {m : Monad} := iter_list [1; 5; 7; 2].

Definition test1 := Coroutine.terminate test_it (fun x => print x).
Compute run test1 (fun o => o) nil.

Definition test2 := seq
  (Coroutine.force_n test_it 2 (fun x => print x))
  (ret tt).
Compute run test2 (fun o => o) nil.

Definition test3 := Coroutine.terminate test_it (fun x =>
  if eq_nat_dec x 7 then
    gret (m := Print nat) (option_none _)
  else
    combine_commut (gret (m := Option) (print x))).

Compute run test3 (fun o => o) (nil, tt).




