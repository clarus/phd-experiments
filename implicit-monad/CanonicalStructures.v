(** Not working for now *)
Set Implicit Arguments.

Record Monad (M : Type -> Type) : Type := {
  ret : forall A, A -> M A;
  bind : forall A B, M A -> (A -> M B) -> M B}.

Record Morphism (M1 M2 : Type -> Type) : Type := {
  lift : forall A, M1 A -> M2 A}.

Definition app (M1 M2 M3 M4 : Type -> Type) (T1 T2 : Type)
  (monad1 : Monad M1) (monad2 : Monad M2) (monad3 : Monad M3) (monad4 : Monad M4)
  (f14 : Morphism M1 M4) (f24 : Morphism M2 M4) (f34 : Morphism M3 M4)
  (e1 : M1 (T2 -> M3 T1)) (e2 : M2 T2)
  : M4 T1 :=
  bind monad4 _ (lift f14 _ e1) (fun f =>
  bind monad4 _ (lift f24 _ e2) (fun x =>
    lift f34 _ (f x))).

Definition Id : Monad (fun A => A) := {|
  ret A x := x;
  bind A B x f := f x |}.

Definition Option : Monad option := {|
  ret A x := Some x;
  bind A B x f :=
    match x with
    | Some x' => f x'
    | None => None
    end |}.

Definition identity_morphism (M : Type -> Type) : Morphism M M := {|
  lift A x := x |}.

Definition IdOfId := identity_morphism (fun A => A).

Definition OptionOfOption := identity_morphism option.

Definition OptionOfId : Morphism (fun A => A) option := {|
  lift A x := Some x |}.

Canonical Structure Id.
Canonical Structure Option.

Canonical Structure IdOfId.
Canonical Structure OptionOfOption.
Canonical Structure OptionOfId.

(** Inference does not seem to work for us with canonical structures *)
Definition gre :=
  app (M1 := fun A => A) (M2 := option) (M3 := option) (M4 := option)
    nat nat
    Id Option Option Option
    OptionOfId OptionOfOption OptionOfOption
    (ret Id (fun n => ret Option n)) (ret Option 23).