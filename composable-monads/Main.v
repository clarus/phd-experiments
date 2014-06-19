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

Fixpoint run_seq S E A (x : C.t S E A) (s : S) : (A + E) * S :=
  match C.open x s with
  | (Val x, s) => (inl x, s)
  | (Err e, s) => (inr e, s)
  | (Mon x, s) => run_seq x s
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

Fixpoint lift_state S1 S2 E A (x : C.t S2 E A) : @C.t (S1 * S2) E A :=
  C.make (fun (s : S1 * S2) =>
    let (s1, s2) := s in
    match C.open x s2 with
    | (Val x, s2) => (Val x, (s1, s2))
    | (Err e, s2) => (Err e, (s1, s2))
    | (Mon x, s2) => (Mon (lift_state _ x), (s1, s2))
    end).

Fixpoint lift_error S E E' A (x : C.t S E A) : @C.t S (E + E') A :=
  C.make (fun s =>
    match C.open x s with
    | (Val x, s) => (Val x, s)
    | (Err e, s) => (Err (inl e), s)
    | (Mon x, s) => (Mon (lift_error _ x), s)
    end).

Module Option.
  Definition none A : C.t unit unit A :=
    C.make (fun _ => (Err tt, tt)).

  Definition run_seq A (x : C.t unit unit A) : option A :=
    match run_seq x tt with
    | (inl x, _) => Some x
    | _ => None
    end.
End Option.

Module Error.
  Definition raise E A (e : E) : C.t unit E A :=
    C.make (fun _ => (Err e, tt)).
End Error.

Module Print.
  Definition print A (x : A) : C.t (list A) Empty_set unit :=
    C.make (fun s => (Val tt, x :: s)).
End Print.

Module State.
  Definition read (S : Type) : C.t S Empty_set S :=
    C.make (fun s => (Val s, s)).

  Definition write (S : Type) (x : S) : C.t S Empty_set unit :=
    C.make (fun _ => (Val tt, x)).
End State.

Module Concurrency.
  Fixpoint par S E A B
    (x : C.t (Stream bool * S) E A) (y : C.t (Stream bool * S) E B) {struct x}
    : C.t (Stream bool * S) E (A * B) :=
    let fix par_aux y {struct y} : C.t (Stream bool * S) E (A * B) :=
      C.make (fun (s : Stream bool * S) =>
        match s with
        | (Streams.Cons b bs, s) =>
          if b then
            let (r, ss) := C.open x (bs, s) in
            (match r with
            | Val x => Mon (let! y := y in ret (x, y))
            | Err e => Err e
            | Mon x => Mon (par x y)
            end, ss)
          else
            let (r, ss) := C.open y (bs, s) in
            (match r with
            | Val y => Mon (let! x := x in ret (x, y))
            | Err e => Err e
            | Mon y => Mon (par_aux y)
            end, ss)
        end) in
    C.make (fun (s : Stream bool * S) =>
      match s with
      | (Streams.Cons b bs, s) =>
        if b then
          let (r, ss) := C.open x (bs, s) in
          (match r with
          | Val x => Mon (let! y := y in ret (x, y))
          | Err e => Err e
          | Mon x => Mon (par x y)
          end, ss)
        else
          let (r, ss) := C.open y (bs, s) in
          (match r with
          | Val y => Mon (let! x := x in ret (x, y))
          | Err e => Err e
          | Mon y => Mon (par_aux y)
          end, ss)
      end).
End Concurrency.