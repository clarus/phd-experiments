Require Import List.

Import ListNotations.

Set Implicit Arguments.

Module Body.
  Inductive t : Type -> Type -> Type :=
  | op : forall H H' H'', (H -> H') -> t H' H'' -> t H H''
  | jcc : forall H H', (H -> bool) -> t H H' -> t H H' -> t H H'
  | call : forall A B H H' H'', (H -> A) -> (B -> H') -> t A B -> t H' H'' -> t H H''
  | ret : forall H, t H H.
  
  Fixpoint eval H H' (b : t H H') (i : H) {struct b} : H'.
    destruct b as [H H' H'' f b | H H' c b1 b2 | A B H H' H'' x y f b | H].
      exact (eval _ _ b (f i)).
      
      exact (if c i then eval _ _ b1 i else eval _ _ b2 i).
      
      exact (eval _ _ b (y (eval _ _ f (x i)))).
      
      exact i.
  Defined.
End Body.

Import Body.

Definition test1 : t unit nat :=
  op (fun _ => 12) (
  op (fun n => n + 1) (
  ret _)).

Compute eval test1 tt.