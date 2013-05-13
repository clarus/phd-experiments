Require Import List.

Import ListNotations.

Set Implicit Arguments.

(*Module Gamma.
  Inductive t : Type :=
  | nil : t
  | cons : Type ->
End Gamma.*)

Module Gamma.
  Definition t := list Type.
End Gamma.

Module Env.
  Inductive t : Gamma.t -> Type :=
  | nil : t nil
  | cons : forall T G, T -> t G -> t (T :: G).
End Env.

Inductive M (G : Gamma.t) (A : Type) : Type :=
| new : (Env.t G -> A + {T : Type & M (T :: G) A}) -> M G A.