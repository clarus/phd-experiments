(** Sequential monads with temporal logic support. *)
Require Import List.

Import ListNotations.

Set Implicit Arguments.

Module Effect.
  Definition t := Type.
End Effect.

Module Property.
  Definition t (e : Effect.t) (A : Type) :=
    option A -> list e -> Prop.

  Inductive seq e A B (PA : t e A) (PB : t e B) : t e B :=
  | seq_intro : forall x y s tx ty,
    PA x (s :: tx) -> PB y (last tx s :: ty) -> seq PA PB y (s :: tx ++ ty).
End Property.

Module M.
  Definition t (S : Type) (A : Type) (P : option A -> list S -> Prop) : Type :=
    forall (s : S),
      {x : option A & {t : list S | P x (s :: t)}}.
End M.

Definition ret S A (x : A) : M.t S A (fun _ _ => True) :=
  fun _ => existT _ (Some x) (exist _ [] I).

Definition bind S A B (PA PB : _ -> _ -> Prop)
  (Hsome : forall x y s tx ty,
    PA (Some x) (s :: tx) -> PB y (last tx s :: ty) -> PB y (s :: tx ++ ty))
  (Hnone : forall t,
    PA None t -> PB None t)
  (x : M.t S A PA) (f : A -> M.t S B PB)
  : M.t S B PB.
  intro s.
  destruct (x s) as (x', (tx, Hx)).
  destruct x' as [x' |].
  - destruct (f x' (last tx s)) as (y, (ty, Hy)).
    exists y.
    exists (tx ++ ty).
    now apply Hsome with (x := x').

  - exists None.
    exists tx.
    now apply Hnone.
Defined.

Definition combine S1 S2 A P1 P2

Infix "++" := combine.
