(** Quite complicated, I will come back to it later *)
Set Implicit Arguments.

Module Trace.
  Inductive t (A : Type) : Type :=
  | one : A -> t A
  | next : A -> t A -> t A.

  Definition head A (tr : t A) : A :=
    match tr with
    | one s => s
    | next s _ => s
    end.

  Fixpoint append A (tr1 : list A) (tr2 : t A) : t A :=
    match tr1 with
    | nil => tr2
    | cons s tr1 => next s (append tr1 tr2)
    end.
End Trace.

Infix "::" := Trace.next.
Infix "++" := Trace.append.

Module Spec.
  Definition t S A := Trace.t S -> A -> Prop.

  Definition true S A : t S A := fun _ _ => True.
End Spec.

Module M.
  Inductive t (S : Type) (A : Type) (P : Spec.t S A) (tr : Trace.t S) : Type :=
  | new :
    ((exists tr' x, P (tr' ++ tr) x) ->
      {s : S & (({x : A | P (s :: tr) x} + (forall tr', t P (tr' ++ s :: tr))) % type)})
    -> t P tr.

  Definition open S A (P : Spec.t S A) tr (x : t P tr) :=
    match x with
    | new _ x => x
    end.
End M.

Definition bind (S A B : Type) (Px : Spec.t S A) (Pf : Spec.t S B)
  (x : forall tr, M.t Px tr) (f : A -> forall tr, M.t Pf tr) : forall (tr : Trace.t S), M.t (Spec.true (A := B)) tr.
    refine (fun tr =>
      M.new tr (fun pre =>
        match M.open (x tr) pre with
        | existT _ s (inl (exist _ x post)) => existT _ s (inr (fun tr' => M.open (f x _) _))
        | existT _ s (inr x) => _
        end)).
