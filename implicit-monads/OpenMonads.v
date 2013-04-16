(** Monads with an open structure to give more freedom to the run operations *)

Set Implicit Arguments.

Class Monad : Type := {
  I : Type;
  E : Type;
  O : Type;
  O_of_I : I -> O}.

Module M.
  Inductive t {m : Monad} (A : Type) : Type :=
  | new : (I -> (A + E + t A) * O) -> t A.
End M.

Definition ret {m : Monad} A (x : A) : M.t A :=
  M.new (fun i => (inl (inl x), O_of_I i)).

Fixpoint bind {m : Monad} A B (x : M.t A) (f : A -> M.t B) : M.t B :=
  M.new (fun i =>
    match x with
    | M.new x =>
      match x i with
      | (inl xe, o) =>
        match xe with
        | inl x => (inr (f x), o)
        | inr e => (inl (inr e), o)
        end
      | (inr x, o) => (inr (bind x f), o)
      end
    end).

Fixpoint run {m : Monad} A (x : M.t A) (I_of_O : O -> I) (i : I) : (A + E) * O :=
  match x with
  | M.new x =>
    match x i with
    | (inl xe, o) => (xe, o)
    | (inr x, o) => run x I_of_O (I_of_O o)
    end
  end.