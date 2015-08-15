Require Import List.

Import ListNotations.

Set Implicit Arguments.

Module Gamma.
  Definition t := list Type.
End Gamma.

Module Env.
  Inductive t : Gamma.t -> Type :=
  | nil : t nil
  | cons : forall T G, T -> t G -> t (T :: G).

  Fixpoint get G (e : t G) (n : nat) : List.nth n G unit :=
    match e with
    | nil =>
      match n with
      | O => tt
      | S _ => tt
      end
    | cons x e =>
      match n with
      | O => x
      | S n => get e n
      end
    end.
End Env.

Inductive M (G : Gamma.t) (A : Type) : Type :=
| new : (Env.t G -> A + {T : Type & T & M (T :: G) A}) -> M G A.

Definition open G A (x : M G A) :=
  match x with
  | new x' => x'
  end.

Definition next A G T (x : T) (k : M (T :: G) A) : {T : Type & T & M (T :: G) A} :=
  existT2 (fun T => T) _ T x k.

Fixpoint eval G A (x : M G A) (e : Env.t G) : A :=
  match open x e with
  | inl x => x
  | inr (existT2 _ _ _ t x) => eval x (Env.cons t e)
  end.

Definition eval_closed A (x : M [] A) : A :=
  eval x Env.nil.

Definition test1 :=
  let x := 12 in
  let y := 23 in
  x + y.

Compute test1.

Definition test1' : M [] nat :=
  new (fun _ => inr (
  next 12 (new (fun _ => inr (
  next 23 (new (fun (e : Env.t [nat : Type; nat : Type]) => inl (
  Env.get e 0 + Env.get e 1)))))))).

Compute eval_closed test1'.

Definition test2 :=
  let f := fun n => n + 2 in
  f 12.

Compute test2.

Definition test2' : M [] nat :=
  new (fun (_ : Env.t []) => inr (
  next ((fun n => new (fun (e : Env.t [nat : Type]) =>
    inl 0)) : nat -> M [nat : Type] nat) (new (fun (e : Env.t [nat -> M [nat : Type] nat]) =>
  inl 0)))).
