(** Experiments for the "composable monads" project. *)
Require Import Arith.
Require Import List.
Require Import Streams.
Require Import String.

Import ListNotations.
Local Open Scope string_scope.

Set Implicit Arguments.

Module Result.
  Inductive t (A B C : Type) : Type :=
  | Val : A -> t A B C
  | Err : B -> t A B C
  | Mon : C -> t A B C.
  
  Arguments Val [A] [B] [C] _.
  Arguments Err [A] [B] [C] _.
  Arguments Mon [A] [B] [C] _.
End Result.

Import Result.

Module M.
  Inductive t (S : Type) (E : Type) (A : Type) : Type :=
  | make : (S -> Result.t A E (t S E A) * S) -> t S E A.
  
  Definition open S E A (x : t S E A) :=
    match x with
    | make x' => x'
    end.
End M.

Definition ret S E A (x : A) : M.t S E A :=
  M.make (fun s => (Val x, s)).

Fixpoint bind S E A B (x : M.t S E A) (f : A -> M.t S E B) : M.t S E B :=
  M.make (fun s =>
    match M.open x s with
    | (Val x, s) => (Mon (f x), s)
    | (Err e, s) => (Err e, s)
    | (Mon x, s) => (Mon (bind x f), s)
    end).

Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Fixpoint run_seq S E A (x : M.t S E A) (s : S) : (A + E) * S :=
  match M.open x s with
  | (Val x, s) => (inl x, s)
  | (Err e, s) => (inr e, s)
  | (Mon x, s) => run_seq x s
  end.

(*Fixpoint combine_id (m : Monad) A (x : @M.t (Id ++ m) A) : @M.t m A :=
  M.make (fun s =>
    match M.open x (tt, s) with
    | (Val x, (_, s)) => (Val x, s)
    | (Err (inr e), (_, s)) => (Err e, s)
    | (Err (inl e), _) => match e with end
    | (Mon x, (_, s)) => (Mon (combine_id x), s)
    end).

Fixpoint combine_commut (m1 m2 : Monad) A (x : @M.t (m1 ++ m2) A)
  : @M.t (m2 ++ m1) A :=
  M.make (m := m2 ++ m1) (fun s =>
    let (s2, s1) := s in
    match M.open x (s1, s2) with
    | (Val x, (s1, s2)) => (Val x, (s2, s1))
    | (Err e, (s1, s2)) =>
      (Err (match e with
      | inl e1 => inr e1
      | inr e2 => inl e2
      end), (s2, s1))
    | (Mon x', (s1, s2)) => (Mon (combine_commut x'), (s2, s1))
    end).

(** The canonical form of a list of additions should always be with right associativity. *)
Fixpoint combine_assoc_left (m1 m2 m3 : Monad) A (x : @M.t ((m1 ++ m2) ++ m3) A)
  : @M.t (m1 ++ m2 ++ m3) A :=
  M.make (m := m1 ++ (m2 ++ m3)) (fun s =>
    match s with
    | (s1, (s2, s3)) =>
      match M.open x ((s1, s2), s3) with
      | (Val x, ((s1, s2), s3)) => (Val x, (s1, (s2, s3)))
      | (Err e, ((s1, s2), s3)) =>
        let e := match e with
          | inl (inl e1) => inl e1
          | inl (inr e2) => inr (inl e2)
          | inr e3 => inr (inr e3)
          end in
        (Err e, (s1, (s2, s3)))
      | (Mon x, ((s1, s2), s3)) => (Mon (combine_assoc_left x), (s1, (s2, s3)))
      end
    end).

(** Should not be used. *)
Fixpoint combine_assoc_right (m1 m2 m3 : Monad) A (x : @M.t (m1 ++ m2 ++ m3) A)
  : @M.t ((m1 ++ m2) ++ m3) A :=
  M.make (m := (m1 ++ m2) ++ m3) (fun s =>
    match s with
    | ((s1, s2), s3) =>
      match M.open x (s1, (s2, s3)) with
      | (Val x, (s1, (s2, s3))) => (Val x, ((s1, s2), s3))
      | (Err e, (s1, (s2, s3))) =>
        let e := match e with
          | inl e1 => inl (inl e1)
          | inr (inl e2) => inl (inr e2)
          | inr (inr e3) => inr e3
          end in
        (Err e, ((s1, s2), s3))
      | (Mon x, (s1, (s2, s3))) => (Mon (combine_assoc_right x), ((s1, s2), s3))
      end
    end).*)

Fixpoint lift_state S S' E A (x : M.t S E A) : @M.t (S * S') E A :=
  M.make (fun (s : S * S') =>
    let (s1, s2) := s in
    match M.open x s1 with
    | (Val x, s1) => (Val x, (s1, s2))
    | (Err e, s1) => (Err e, (s1, s2))
    | (Mon x, s1) => (Mon (lift_state _ x), (s1, s2))
    end).

Fixpoint lift_error S E E' A (x : M.t S E A) : @M.t S (E + E') A :=
  M.make (fun s =>
    match M.open x s with
    | (Val x, s) => (Val x, s)
    | (Err e, s) => (Err (inl e), s)
    | (Mon x, s) => (Mon (lift_error _ x), s)
    end).

Module Option.
  Definition none A : M.t unit unit A :=
    M.make (fun _ => (Err tt, tt)).

  Definition run_seq A (x : M.t unit unit A) : option A :=
    match run_seq x tt with
    | (inl x, _) => Some x
    | _ => None
    end.
End Option.

Module Error.
  Definition raise E A (e : E) : M.t unit E A :=
    M.make (fun _ => (Err e, tt)).
End Error.

Module Print.
  Definition print A (x : A) : M.t (list A) Empty_set unit :=
    M.make (fun s => (Val tt, x :: s)).
End Print.

Module State.
  Definition read (S : Type) : M.t S Empty_set S :=
    M.make (fun s => (Val s, s)).

  Definition write (S : Type) (x : S) : M.t S Empty_set unit :=
    M.make (fun _ => (Val tt, x)).
End State.

(*(* Useful? *)
Fixpoint local_run {m m' : Monad} A (x : @M.t (m ++ m') A) (s_m : @S m)
  : @M.t (Error (@E m) ++ m') A :=
  M.make (m := Error (@E m) ++ m') (fun s =>
    let (_, s_m') := s in
    match M.open x (s_m, s_m') with
    | (r, (s_m, s_m')) =>
      let r := match r with
        | Val x => Val x
        | Err e => Err e
        | Mon x => Mon (local_run x s_m)
        end in
      (r, (tt, s_m'))
    end).*)

(*Fixpoint local_run_with_break {m m' : Monad} A
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
  aux x i_m.*)

(** Breaks *)
Instance Breaker : Monad := {
  S := bool;
  E := Empty_set }.

Definition break : @M.t Breaker unit :=
  M.make (fun _ => (Val tt, true)).

Fixpoint local_run_with_break {m : Monad} A (x : @M.t (Breaker ++ m) A)
  : @M.t m (A + @M.t (Breaker ++ m) A) :=
  M.make (m := m) (fun s =>
    match M.open x (false, s) with
    | (r, (true, s)) =>
      (Val (inr (M.make (m := Breaker ++ m) (fun i =>
        (r, (false, snd i))))), o)
    | (Val x, (false, s)) => (Val (inl x), s)
    | (Err e, (false, s)) =>
      match e with
      | inl e_break => match e_break with end
      | inr e_m => (Err e_m, s)
      end
    | (Mon x, (false, s)) => (Mon (local_run_with_break x), s)
    end).

Fixpoint local_run_with_break_n {m : Monad} A (x : @M.t (Breaker ++ m) A) (a : @M.t m unit) (n : nat)
  : @M.t m (A + @M.t (Breaker ++ m) A) :=
  match n with
  | 0 => ret (inr x)
  | S n' => bind (local_run_with_break x) (fun x =>
    match x with
    | inl x => ret (inl x)
    | inr x => seq a (local_run_with_break_n x a n')
    end)
  end.

Fixpoint local_run_with_break_terminate {m : Monad} A (x : @M.t (Breaker ++ m) A) (a : @M.t m unit)
  : @M.t m A :=
  M.make (m := m) (fun i =>
    match M.open x (tt, i) with
    | (Val x, (_, o)) => (Val x, o)
    | (Err e, (_, o)) =>
      match e with
      | inl e_break => match e_break with end
      | inr e_m => (Err e_m, o)
      end
    | (Mon x, (_, o)) => (Mon (seq a (local_run_with_break_terminate x a)), o)
    end).

(** Coroutines *)
Definition Waiter (m : Monad) (A B : Type) : Monad :=
  Breaker ++ State ((A -> @M.t m B) * bool).

Module Coroutine.
  Definition t {m : Monad} (A B T : Type) := @M.t (Waiter m A B ++ m) T.
  
  Definition break_if_not_fresh {m : Monad} A B : t A B unit :=
    combine_commut (gret (
      bind (m := Waiter m A B) (gret (read _)) (fun f_fresh =>
        let (_, fresh) := f_fresh in
        if fresh then
          ret tt
        else
          combine_commut (gret break)))).
  
  Definition use_and_consume {m : Monad} A B (a : A) : t A B B :=
    combine_assoc_right (gret (combine_commut (
      bind (m := m ++ State _) (gret (read _)) (fun f_fresh : _ * _ =>
        let (f, _) := f_fresh in
        seq (gret (write (f, false)))
          (combine_commut (gret (f a))))))).
  
  Definition yield {m : Monad} A B (a : A) : t A B B :=
    seq (break_if_not_fresh _ _) (use_and_consume _ a).
  
  (*Definition I_of_O {m : Monad} A B (o : @O (Waiter m A B)) : option (@I (Waiter m A B)) :=
    match o with
    | ((f, fresh), break) =>
      if break then
        None
      else
        Some (f, fresh)
    end.*)
  
  (*Definition inject_new_f {m : Monad} A B (f : A -> M.t B) : @M.t (State ((A -> @M.t m B) * bool)) unit :=
    write (f, true).*)
  
  (*Definition force {m : Monad} A B T (x : t A B T) (f : A -> M.t B) : M.t (T + t A B T) :=
    local_run (m' := m) (local_run_with_break x) (fun o => o) (f, true).
  
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
  M.make (fun s =>
    (inl (inl tt), (Streams.tl s, Streams.hd s))).

Fixpoint join_aux {m : Monad} A B (x : @M.t (Breaker ++ m) A) :=
  fix aux (y : @M.t (Breaker ++ m) B) (left_first : bool) : @M.t (Breaker ++ m) (A * B):=
    if left_first then
      M.make (fun i =>
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
      M.make (fun i =>
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
Compute test4_run (Streams.const true).*)