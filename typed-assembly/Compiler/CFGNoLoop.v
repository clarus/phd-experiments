(** Control flow graphs without loops. *)
Require Import ZArith.
Require Import List.

Set Implicit Arguments.
Import ListNotations.
Local Open Scope Z_scope.

Module CFG.
  Inductive t (S : Set) : (S -> Type) -> (S -> Type) -> Type :=
  | nop : forall L,
    t L L
  | op : forall Lin L Lout,
    (forall s, {s' : S & Lin s -> L s'}) ->
    t L Lout -> t Lin Lout
  | jcc : forall Lin Lin_true Lin_false Lmerge Lout,
    (forall s, (Lin s -> Lin_true s) + (Lin s -> Lin_false s)) ->
    t Lin_true Lmerge -> t Lin_false Lmerge -> t Lmerge Lout ->
    t Lin Lout.
  
  Fixpoint eval (S : Set) Lin Lout (p : t Lin Lout)
    (s : S) (l : Lin s) {struct p} : {s' : S & Lout s'}.
    destruct p as
      [ L
      | Lin L Lout f p
      | Lin Lin_true Lin_false Lmerge Lout f p_true p_false p].
    - exact (existT _ _ l).
    
    - exact (
        let (_, fl) := f s in
        eval _ _ _ p _ (fl l)).
    
    - exact (
        match f s with
        | inl fl_true =>
          let (s, l) := eval _ _ _ p_true _ (fl_true l) in
          eval _ _ _ p _ l
        | inr fl_false =>
          let (s, l) := eval _ _ _ p_false _ (fl_false l) in
          eval _ _ _ p _ l
        end).
  Defined.
  
  Module Test.
    Require Import Arith.Compare_dec.
    Local Open Scope nat_scope.
    
    Definition L1 (n : nat) := 3 <= n.
    Definition L2 (n : nat) := 5 <= n.
    
    Definition g1 : CFG.t L1 L2.
      refine (
        op _ (fun s => existT _ (s + 2) (fun l => _))
        (@nop _ _)); abstract (
      unfold L1, L2 in *;
      omega).
    Defined.
    
    Check eq_refl : 6 = projT1 (eval g1 4 (leb_complete 3 4 eq_refl)).
  End Test.
End CFG.