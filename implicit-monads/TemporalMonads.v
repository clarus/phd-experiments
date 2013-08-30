(** Sequential monads with temporal logic support. *)
Require Import List.

Import ListNotations.

Module M.
  Definition t (S : Type) (A : Type) (P : option A -> list S -> Prop) : Type :=
    forall (s : S),
      {x : option A & {t : list S | P x (s :: t)}}.
End M.

Set Implicit Arguments.

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
intuition.
    
  unfold M.t.
  
  refine (
  fun s =>
    let (x, txHx) := x s in
    let (tx, Hx) := txHx in
    match x with
    | None => existT _ None (exist _ tx _)
    | Some x' =>
      let s' := last tx s in
      let (y, tyHy) := f x' s' in
      let (ty, Hy) := tyHy in
      existT _ y (exist _ (tx ++ ty) (Hsome x' y s tx ty Hx))
    end).
    apply Hsome with (x := x1).
    match x s t with
    | existT 
    end.