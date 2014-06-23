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

Module C.
  Inductive t (S : Type) (E : Type) (A : Type) : Type :=
  | make : (S -> Result.t A E (t S E A) * S) -> t S E A.
  
  Definition open S E A (x : t S E A) :=
    match x with
    | make x' => x'
    end.
End C.

Definition ret {S E A} (x : A) : C.t S E A :=
  C.make (fun s => (Val x, s)).

Fixpoint bind S E A B (x : C.t S E A) (f : A -> C.t S E B) : C.t S E B :=
  C.make (fun s =>
    match C.open x s with
    | (Val x, s) => (Mon (f x), s)
    | (Err e, s) => (Err e, s)
    | (Mon x, s) => (Mon (bind x f), s)
    end).

Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Fixpoint eval S E A (x : C.t S E A) (s : S) : (A + E) * S :=
  match C.open x s with
  | (Val x, s) => (inl x, s)
  | (Err e, s) => (inr e, s)
  | (Mon x, s) => eval x s
  end.

(*Fixpoint combine_id (m : Monad) A (x : @C.t (Id ++ m) A) : @C.t m A :=
  C.make (fun s =>
    match C.open x (tt, s) with
    | (Val x, (_, s)) => (Val x, s)
    | (Err (inr e), (_, s)) => (Err e, s)
    | (Err (inl e), _) => match e with end
    | (Mon x, (_, s)) => (Mon (combine_id x), s)
    end).

Fixpoint combine_commut (m1 m2 : Monad) A (x : @C.t (m1 ++ m2) A)
  : @C.t (m2 ++ m1) A :=
  C.make (m := m2 ++ m1) (fun s =>
    let (s2, s1) := s in
    match C.open x (s1, s2) with
    | (Val x, (s1, s2)) => (Val x, (s2, s1))
    | (Err e, (s1, s2)) =>
      (Err (match e with
      | inl e1 => inr e1
      | inr e2 => inl e2
      end), (s2, s1))
    | (Mon x', (s1, s2)) => (Mon (combine_commut x'), (s2, s1))
    end).

(** The canonical form of a list of additions should always be with right associativity. *)
Fixpoint combine_assoc_left (m1 m2 m3 : Monad) A (x : @C.t ((m1 ++ m2) ++ m3) A)
  : @C.t (m1 ++ m2 ++ m3) A :=
  C.make (m := m1 ++ (m2 ++ m3)) (fun s =>
    match s with
    | (s1, (s2, s3)) =>
      match C.open x ((s1, s2), s3) with
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
Fixpoint combine_assoc_right (m1 m2 m3 : Monad) A (x : @C.t (m1 ++ m2 ++ m3) A)
  : @C.t ((m1 ++ m2) ++ m3) A :=
  C.make (m := (m1 ++ m2) ++ m3) (fun s =>
    match s with
    | ((s1, s2), s3) =>
      match C.open x (s1, (s2, s3)) with
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

Fixpoint lift_state S1 S2 E A (x : C.t S1 E A) : @C.t (S1 * S2) E A :=
  C.make (fun (s : S1 * S2) =>
    let (s1, s2) := s in
    match C.open x s1 with
    | (Val x, s1) => (Val x, (s1, s2))
    | (Err e, s1) => (Err e, (s1, s2))
    | (Mon x, s1) => (Mon (lift_state _ x), (s1, s2))
    end).

(*Fixpoint lift_error S E E' A (x : C.t S E A) : @C.t S (E + E') A :=
  C.make (fun s =>
    match C.open x s with
    | (Val x, s) => (Val x, s)
    | (Err e, s) => (Err (inl e), s)
    | (Mon x, s) => (Mon (lift_error _ x), s)
    end).*)

Module Option.
  Definition none A : C.t unit unit A :=
    C.make (fun _ => (Err tt, tt)).
End Option.

Module Error.
  Definition raise E A (e : E) : C.t unit E A :=
    C.make (fun _ => (Err e, tt)).
End Error.

Module Log.
  Definition t := list.
  
  Definition log A (x : A) : C.t (t A) Empty_set unit :=
    C.make (fun s => (Val tt, x :: s)).
End Log.

Module State.
  Definition read (S : Type) : C.t S Empty_set S :=
    C.make (fun s => (Val s, s)).

  Definition write (S : Type) (x : S) : C.t S Empty_set unit :=
    C.make (fun _ => (Val tt, x)).
End State.

(** A source of information for a concurrent scheduler. *)
Module Entropy.
  Require Import BinNat.
  
  Definition t := Stream bool.
  
  Definition left : t := Streams.const true.
  
  Definition right : t := Streams.const false.
  
  Definition inverse (e : t) : t :=
    Streams.map negb e.
  
  Definition half : t :=
    let cofix aux b :=
      Streams.Cons b (aux (negb b)) in
    aux true.

  CoFixpoint random_naturals (n : N) : Stream N :=
    let n' := N.modulo (137 * n + 187) 256 in
    Streams.Cons n (random_naturals n').
  
  Definition random (seed : N) : t :=
    Streams.map (fun n => N.even (N.div n 64)) (random_naturals seed).
  
  Module Test.
    Fixpoint hds A (n : nat) (e : Stream A) : list A :=
      match n with
      | O => []
      | S n => Streams.hd e :: hds n (Streams.tl e)
      end.
    
    Compute hds 20 (random_naturals 0).
    Compute hds 20 (random 0).
    Compute hds 20 (random 12).
    Compute hds 20 (random 23).
  End Test.
End Entropy.

Module Concurrency.
  (** Executes [x] and [y] concurrently, using a boolean stream as source of entropy. *)
  Fixpoint par S E A B
    (x : C.t (S * Entropy.t) E A) (y : C.t (S * Entropy.t) E B) {struct x}
    : C.t (S * Entropy.t) E (A * B) :=
    let fix par_aux y {struct y} : C.t (S * Entropy.t) E (A * B) :=
      C.make (fun (s : S * Entropy.t) =>
        match s with
        | (s, Streams.Cons b bs) =>
          if b then
            let (r, ss) := C.open x (s, bs) in
            (match r with
            | Val x => Mon (let! y := y in ret (x, y))
            | Err e => Err e
            | Mon x => Mon (par x y)
            end, ss)
          else
            let (r, ss) := C.open y (s, bs) in
            (match r with
            | Val y => Mon (let! x := x in ret (x, y))
            | Err e => Err e
            | Mon y => Mon (par_aux y)
            end, ss)
        end) in
    C.make (fun (s : S * Entropy.t) =>
      match s with
      | (s, Streams.Cons b bs) =>
        if b then
          let (r, ss) := C.open x (s, bs) in
          (match r with
          | Val x => Mon (let! y := y in ret (x, y))
          | Err e => Err e
          | Mon x => Mon (par x y)
          end, ss)
        else
          let (r, ss) := C.open y (s, bs) in
          (match r with
          | Val y => Mon (let! x := x in ret (x, y))
          | Err e => Err e
          | Mon y => Mon (par_aux y)
          end, ss)
      end).
  
  (** Make [x] atomic. *)
  Fixpoint atomic S E A (x : C.t S E A) : C.t S E A :=
    C.make (fun (s : S) =>
      match C.open x s with
      | (Val _, _) as y | (Err _, _) as y => y
      | (Mon x, s) => C.open (atomic x) s
      end).
End Concurrency.

Module List.
  Fixpoint iter_seq S E A (f : A -> C.t S E unit) (l : list A) : C.t S E unit :=
    match l with
    | [] => ret tt
    | x :: l =>
      let! _ := f x in
      iter_seq f l
    end.
  
  Fixpoint iter_par S E A (f : A -> C.t (S * Entropy.t) E unit) (l : list A)
    : C.t (S * Entropy.t) E unit :=
    match l with
    | [] => ret tt
    | x :: l =>
      let! _ := Concurrency.par (f x) (iter_par f l) in
      ret tt
    end.
End List.

Module Event.
  Definition t := list.
  
  Definition loop_seq S E A (f : A -> C.t S E unit) : C.t (S * t A) E unit :=
    C.make (fun (s : S * t A) =>
      let (s, events) := s in
      (Mon (lift_state (t A) (List.iter_seq f events)), (s, []))).
  
  Definition loop_par S E A (f : A -> C.t (S * Entropy.t) E unit)
    : C.t (S * Entropy.t * t A) E unit :=
    C.make (fun (s : S * Entropy.t * t A) =>
      let (s, events) := s in
      (Mon (lift_state (t A) (List.iter_par f events)), (s, []))).
End Event.

Module Test.
  Definition eval_seq (x : C.t (list nat) Empty_set unit) :=
    snd (eval x []).
  
  Definition eval_par (x : C.t (list nat * Entropy.t) Empty_set unit) (e : Entropy.t) :=
    snd (snd (eval x ([], e))).
  
  (** Two threads are printing concurrently two lists of numbers. *)
  Module PrintList.
    Fixpoint print_before (n : nat) : C.t (Log.t nat) Empty_set unit :=
      match n with
      | O => ret tt
      | S n =>
        let! _ := Log.log n in
        print_before n
      end.
    
    Definition two_prints_seq (n : nat) : C.t (Log.t nat) Empty_set unit :=
      let! _ := print_before n in
      print_before (2 * n).
    
    Definition print_before_par (n : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
      lift_state (Entropy.t) (print_before n).
    
    Definition two_prints_par (n : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
      let! _ := Concurrency.par (print_before_par n) (print_before_par (2 * n)) in
      ret tt.
    
    Compute eval_seq (print_before 12).
    Compute eval_seq (two_prints_seq 12).
    
    Compute eval_par (print_before_par 12) Entropy.half.
    Compute eval_par (two_prints_par 12) Entropy.left.
    Compute eval_par (two_prints_par 12) Entropy.right.
    Compute eval_par (two_prints_par 12) Entropy.half.
    Compute eval_par (two_prints_par 12) (Entropy.random 0).
  End PrintList.
  
  (** A list of threads are printing a number each. *)
  Module ListOfPrints.
    Definition print_seq_seq (n k : nat) : C.t (Log.t nat) Empty_set unit :=
      List.iter_seq (Log.log (A := nat)) (List.seq n k).
    
    Definition print_seq_par (n k : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
      List.iter_par (fun n => lift_state _ (Log.log n)) (List.seq n k).
    
    Compute eval_seq (print_seq_seq 10 20).
    Compute eval_par (print_seq_par 10 20) Entropy.left.
    Compute eval_par (print_seq_par 10 20) Entropy.right.
    Compute eval_par (print_seq_par 10 20) (Entropy.random 12).
  End ListOfPrints.
  
  Module Events.
    Module UiInput.
      Inductive t : Set :=
      | Add : string -> t
      | Remove : nat -> t.
    End UiInput.
    
    Module UiOutput.
      Definition t := list string.
    End UiOutput.
    
    Module ServerInput.
      Definition t := list string.
    End ServerInput.
    
    Module ServerOutput.
      Definition t := list string.
    Module ServerOutput.
    
    Module Model.
      Definition t := list string.
    End Model.
    
    Parameter handle_ui : UiInput.t -> C.t (Log.t UiOutput.t * Model.t) Empty_set unit.
    Parameter handle_server : ServerInput.t -> C.t (Log.t ServerOutput.t * Model.t) Empty_set unit.
    
    (*Definition todo :=
      let! _ := Concurrency.par (Event.loop_par (fun  => )) in
      ret tt.*)
  End Events.
End Test.