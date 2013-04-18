(** Monads with an open structure to give more freedom to the run operations *)
Require Import Arith.
Require Import List.
Require Import Streams.
Require Import String.

Import ListNotations.
Local Open Scope string_scope.

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

Definition combine (m1 m2 : Monad) : Monad := {|
  I := @I m1 * @I m2;
  E := @E m1 + @E m2;
  O := @O m1 * @O m2;
  O_of_I := fun i =>
    let (i1, i2) := i in
    (O_of_I i1, O_of_I i2)|}.

Infix "++" := combine.

Fixpoint sum_id (m : Monad) A (x : @M.t (Id ++ m) A) : @M.t m A :=
  M.new (fun i =>
    match M.open x (tt, i) with
    | (inl (inl x'), (_, o)) => (inl (inl x'), o)
    | (inl (inr (inr e)), (_, o)) => (inl (inr e), o)
    | (inl (inr (inl e)), _) => match e with end
    | (inr x, (_, o)) => (inr (sum_id x), o)
    end).

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

Definition raise E A (e : E) : @M.t (Error E) A :=
  M.new (m := Error E) (fun _ => (inl (inr e), tt)).

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

Fixpoint local_run {m m' : Monad} A
  (x : @M.t (m ++ m') A) (I_of_O : @O m -> @I m) (i_m : @I m)
  : @M.t (Error (@E m) ++ m') A :=
  M.new (m := Error (@E m) ++ m') (fun i =>
    let (_, i_m') := i in
    match M.open x (i_m, i_m') with
    | (inl xe, (o_m, o_m')) =>
      let o := (tt, o_m') in
      match xe with
      | inl x => (inl (inl x), o)
      | inr (inl e_m) => (inl (inr (inl e_m)), o)
      | inr (inr e_m') => (inl (inr (inr e_m')), o)
      end
    | (inr x, (o_m, o_m')) => (inr (local_run x I_of_O (I_of_O o_m)), (tt, o_m'))
    end).

Fixpoint local_run_with_break {m m' : Monad} A
  (x : @M.t (m ++ m') A) (I_of_O : @O m -> option (@I m)) (i_m : @I m)
  : @M.t (Error (@E m) ++ m') (A + @M.t (m ++ m') A) :=
  M.new (m := Error (@E m) ++ m') (fun i =>
    let (_, i_m') := i in
    match M.open x (i_m, i_m') with
    | (inl xe, (o_m, o_m')) =>
      let o := (tt, o_m') in
      match xe with
      | inl x => (inl (inl (inl x)), o)
      | inr (inl e_m) => (inl (inr (inl e_m)), o)
      | inr (inr e_m') => (inl (inr (inr e_m')), o)
      end
    | (inr x, (o_m, o_m')) =>
      let o := (tt, o_m') in
      match I_of_O o_m with
      | Some i'_m => (inr (local_run_with_break x I_of_O i'_m), o)
      | None => (inl (inl (inr x)), o)
      end
    end).

Fixpoint local_run_with_break_n {m m' : Monad} A
  (x : @M.t (m ++ m') A) (I_of_O : @O m -> option (@I m)) (i_m : @I m) (n : nat)
  : @M.t (Error (@E m) ++ m') (A + @M.t (m ++ m') A) :=
  match n with
  | 0 => ret (inr x)
  | S n' => bind (local_run_with_break x I_of_O i_m) (fun x =>
    match x with
    | inl r => ret (inl r)
    | inr x => local_run_with_break_n x I_of_O i_m n'
    end)
  end.

Definition local_run_with_break_terminate {m m' : Monad} A
  (x : @M.t (m ++ m') A) (I_of_O : @O m -> option (@I m)) (i_m : @I m)
  : @M.t (Error (@E m) ++ m') A :=
  let fix aux (x : @M.t (m ++ m') A) (i'_m : @I m) : @M.t (Error (@E m) ++ m') A :=
    M.new (m := Error (@E m) ++ m') (fun i =>
      let (_, i_m') := i in
      match (M.open x) (i'_m, i_m') with
      | (inl xe, (o_m, o_m')) =>
        let o := (tt, o_m') in
        match xe with
        | inl x => (inl (inl x), o)
        | inr (inl e_m) => (inl (inr (inl e_m)), o)
        | inr (inr e_m') => (inl (inr (inr e_m')), o)
        end
      | (inr x, (o_m, o_m')) =>
        let o := (tt, o_m') in
        match I_of_O o_m with
        | Some i'_m => (inr (aux x i'_m), o)
        | None => (inr (aux x i_m), o)
        end
      end) in
  aux x i_m.

(** Coroutines *)
Instance Waiter (m : Monad) (A B : Type) : Monad := {
  I := (A -> @M.t m B) * bool; (* the expected value and if it is fresh *)
  E := Empty_set;
  O := (A -> @M.t m B) * bool * bool; (* the last boolean is for breaking *)
  O_of_I := fun i => (i, false)}.

Module Coroutine.
  Definition t {m : Monad} (A B T : Type) := @M.t (Waiter m A B ++ m) T.
  
  Definition break_if_not_fresh {m : Monad} A B : t A B unit :=
     M.new (m := Waiter m A B ++ m) (fun i =>
      match i with
      | ((f, fresh), i_m) => (inl (inl tt), (((f, fresh), negb fresh), O_of_I i_m))
      end).
  
  Definition use_and_consume {m : Monad} A B (a : A) : t A B B :=
    M.new (m := Waiter m A B ++ m) (fun i =>
      match i with
      | ((f, fresh), i_m) =>
        let o_w := ((f, false), false) in
        match M.open (f a) i_m with
        | (inl (inl y), o_m) => (inl (inl y), (o_w, o_m))
        | (inl (inr e_m), o_m) => (inl (inr (inr e_m)), (o_w, o_m))
        | (inr y, o_m) => (inr (gret y), (o_w, o_m))
        end
      end).
  
  Definition yield {m : Monad} A B (a : A) : t A B B :=
    seq (break_if_not_fresh _ _) (use_and_consume _ a).
  
  Definition I_of_O {m : Monad} A B (o : @O (Waiter m A B)) : option (@I (Waiter m A B)) :=
    match o with
    | ((f, fresh), break) =>
      if break then
        None
      else
        Some (f, fresh)
    end.
  
  Definition force {m : Monad} A B T (x : t A B T) (f : A -> M.t B) : M.t (T + t A B T) :=
    sum_id (local_run_with_break x (I_of_O (B := _)) (f, true)).
  
  Definition force_n {m : Monad} A B T (x : t A B T) (n : nat) (f : A -> M.t B) : M.t (T + t A B T) :=
    sum_id (local_run_with_break_n x (I_of_O (B := _)) (f, true) n).
  
  Definition terminate {m : Monad} A B T (x : t A B T) (f : A -> M.t B) : M.t T :=
    sum_id (local_run_with_break_terminate x (I_of_O (B := _)) (f, true)).
End Coroutine.

Fixpoint iter_list {m : Monad} A (l : list A) : Coroutine.t A unit unit :=
  match l with
  | nil => ret tt
  | x :: l' => seq (Coroutine.yield _ x) (iter_list l')
  end.

Definition test_it {m : Monad} := iter_list [1; 5; 7; 2].

Definition test1 := Coroutine.terminate test_it (fun x => print x).
Compute run test1 (fun o => o) nil.

Definition test2 n := seq
  (Coroutine.force_n test_it n (fun x => print x))
  (ret tt).
Definition test2_run n := run (test2 n) (fun o => o) nil.
Compute test2_run 0.
Compute test2_run 1.
Compute test2_run 2.
Compute test2_run 3.
Compute test2_run 4.
Compute test2_run 5.

Definition test3 := Coroutine.terminate test_it (fun x =>
  if eq_nat_dec x 7 then
    gret (m := Print nat) (raise _ "x is equal to 7")
  else
    combine_commut (gret (m := Error string) (print x))).

Compute run test3 (fun o => o) (nil, tt).

(** Cooperative threads *)
Instance Breaker : Monad := {
  I := Stream bool;
  E := Empty_set;
  O := Stream bool * bool; (* if we did a break *)
  O_of_I := fun s => (s, false)}.

Definition break : @M.t Breaker unit :=
  M.new (fun s =>
    (inl (inl tt), (Streams.tl s, Streams.hd s))).

Fixpoint join_aux {m : Monad} A B (x : @M.t (Breaker ++ m) A) :=
  fix aux (y : @M.t (Breaker ++ m) B) (left_first : bool) : @M.t (Breaker ++ m) (A * B):=
    if left_first then
      M.new (fun i =>
        match (M.open x) i with
        | (inl xe, o) =>
          match xe with
          | inl x => (inr (bind y (fun y => ret (x, y))), o)
          | inr e => (inl (inr e), o)
          end
        | (inr x, ((s, breaking), o)) =>
          if breaking then
            (inr (join_aux _ x y false), ((s, false), o))
          else
            (inr (join_aux _ x y true), ((s, false), o))
        end)
    else
      M.new (fun i =>
        match (M.open y) i with
        | (inl ye, o) =>
          match ye with
          | inl y => (inr (bind x (fun x => ret (x, y))), o)
          | inr e => (inl (inr e), o)
          end
        | (inr y, ((s, breaking), o)) =>
          if breaking then
            (inr (aux y true), ((s, false), o))
          else
            (inr (aux y false), ((s, false), o))
        end).

Definition join {m : Monad} A B (x : @M.t (Breaker ++ m) A) (y : @M.t (Breaker ++ m) B)
  : @M.t (Breaker ++ m) (A * B) :=
  join_aux x y true.

(* join (print 12; break; print 13) (print 23; break; print 0) *)
Definition test4 := join
  (seq (gret (print 12)) (seq (combine_commut (gret break)) (gret (print 13))))
  (seq (gret (print 23)) (seq (combine_commut (gret break)) (gret (print 0)))).

Definition test4_run s :=
  run test4 (fun o => let (sb, o) := o in (fst sb, o)) (s, nil).

Compute test4_run (Streams.const false).
Compute test4_run (Streams.const true).







