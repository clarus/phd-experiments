(** Control flow graphs without loops. *)
Require Import List.
Require Import Compiler.Linear.

Set Implicit Arguments.
Import ListNotations.

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
  
  Fixpoint eval (S : Set) Lin Lout (g : t Lin Lout)
    (s : S) (l : Lin s) {struct g} : {s' : S & Lout s'}.
    destruct g as
      [ L
      | Lin L Lout f g
      | Lin Lin_true Lin_false Lmerge Lout f g_true g_false g].
    - exact (existT _ _ l).
    
    - exact (
        let (_, fl) := f s in
        eval _ _ _ g _ (fl l)).
    
    - exact (
        match f s with
        | inl fl_true =>
          let (s, l) := eval _ _ _ g_true _ (fl_true l) in
          eval _ _ _ g _ l
        | inr fl_false =>
          let (s, l) := eval _ _ _ g_false _ (fl_false l) in
          eval _ _ _ g _ l
        end).
  Defined.
  
  Fixpoint length (S : Set) (Lin Lout : S -> Type) (g : t Lin Lout) : nat :=
    match g with
    | nop _ => 0
    | op _ _ g => 1 + (length g)
    | jcc _ _ g_true g_false g => length g_true + length g_false + length g
    end.
  
  Module Test.
    Require Import Arith.Plus.
    Require Import Arith.Compare_dec.
    Local Open Scope nat_scope.
    
    Definition L1 (n : nat) := 3 <= n.
    Definition L2 (n : nat) := 5 <= n.
    
    Definition g1 : CFG.t L1 L2.
      refine (
        op _ (fun s => existT _ (s + 2) (fun l => _))
        (@nop _ _)).
      unfold L1, L2 in *.
      replace 5 with (3 + 2); trivial.
      now apply plus_le_compat_r.
    Defined.
    
    Check eq_refl : 6 = projT1 (eval g1 4 (leb_complete 3 4 eq_refl)).
  End Test.
End CFG.

Module Compile.
  Require Import Arith.Wf_nat.
  Import CFG.
  
  Fixpoint Laux (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout)
    (ip : nat) : (S -> Type) + nat :=
    match g with
    | nop _ => inr ip
    | op _ _ g =>
      match ip with
      | O => inl Lin
      | Datatypes.S ip => Laux g ip
      end
    | jcc _ _ g_true g_false  g =>
      match ip with
      | O => inl Lin
      | Datatypes.S ip =>
        match Laux g_true ip with
        | inl L => inl L
        | inr ip =>
          match Laux g_false ip with
          | inl L => inl L
          | inr ip => Laux g ip
          end
        end
      end
    end.
  
  Definition L (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout)
    (ip : nat) : S -> Type :=
    match Laux g ip with
    | inl L => L
    | inr _ => Lout
    end.
  
  Definition lt (S : Set) (L : nat -> S -> Type) : Instr.lt_type L :=
    fun x y =>
    projT1 x < projT1 y.
  
  Lemma lt_wf (S : Set) (L : nat -> S -> Type) : well_founded (lt L).
    apply well_founded_ltof.
  Defined.
  
  (*Fixpoint compile (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout)
    : Program.t (lt (L g)) 0.*)
End Compile.





