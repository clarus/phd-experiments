(** Monads with stronger hypothesis to simplify composition *)
Set Implicit Arguments.

Class Monad : Type := {
  I : Type;
  E : Type;
  O : Type;
  M : Type -> Type :=
    fun A => I -> (A + E) * O;
  strong_ret : I -> O;
  strong_bind : I -> O -> I;
  ret : forall A, A -> M A :=
    fun A x i =>
      (inl x, strong_ret i);
  bind : forall A B, M A -> (A -> M B) -> M B :=
    fun A B x f i =>
      match x i with
      | (inl x', o) => f x' (strong_bind i o)
      | (inr e, o) => (inr e, o)
      end}.
