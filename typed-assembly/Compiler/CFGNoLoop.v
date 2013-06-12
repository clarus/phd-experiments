(** Control flow graphs without loops. *)
Require Import ZArith.
Require Import List.
Require Import Compiler.MacroAsm.

Set Implicit Arguments.
Local Open Scope Z_scope.
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

Module Op.
  Inductive t : Set :=
  | const (z : Z) | uminus | plus | times.
  
  Definition eval (o : t) (s : list Z) : list Z :=
    match o with
    | const z => z :: s
    | uminus =>
      match s with
      | z1 :: s => (- z1) :: s
      | _ => s
      end
    | plus =>
      match s with
      | z1 :: z2 :: s => (z1 + z2) :: s
      | _ => s
      end
    | times =>
      match s with
      | z1 :: z2 :: s => (z1 * z2) :: s
      | _ => s
      end
    end.
  
  Definition compile (i : Instr.t) : t :=
    match i with
    | Instr.const _ (exist _ z _) => const z
    | Instr.uminus _ _ _ => uminus
    | Instr.plus _ _ _ _ => plus
    | Instr.times _ _ _ _ => times
    end.
End Op.

Module Compile.
  Import CFG.
  
  Definition S := list Z.
  
  Module L.
    Inductive t : Sig.t -> S -> Type :=
    | nil : t [] []
    | cons : forall sig s z (P : Z -> Prop), P z -> t sig s -> t (P :: sig) (z :: s).
    
    Fixpoint extract_stack sig (stack : Stack.t sig) : {s : S & t sig s}.
      destruct stack as [| P (z, H) sig stack].
      - exact (existT _ [] nil).
      
      - refine (let (s, l) := extract_stack _ stack in _).
        exact (existT _ (z :: s) (cons z P H l)).
    Defined.
    
    Fixpoint make_stack sig (s : S) (l : t sig s) : Stack.t sig.
      destruct l as [| sig s z P H l].
      - exact Stack.nil.
      
      - exact (Stack.cons P (existT _ z H) (make_stack _ _ l)).
    Defined.
  End L.
  
  Fixpoint compile (P : Z -> Prop) (sig : Sig.t) (p : Program.t P sig)
    : CFG.t (L.t sig) (L.t [P]).
    destruct p as [|i context p].
    - exact (@nop _ _).
    
    - refine (op _ (fun s => existT _ (Op.eval (Op.compile i) s) (fun l => _)) (compile _ _ p)).
      destruct i as [P' z | P1 P' Hcast | P1 P2 P' Hcast | P1 P2 P' Hcast]; simpl in *.
      + destruct z as (z, H).
        now apply L.cons.
      
      + inversion_clear l.
        apply L.cons; auto.
      
      + inversion_clear l as [|sig s' z1 Pz1 Hz1 l'].
        inversion_clear l' as [|sig s'' z2 Pz2 Hz2 l''].
        apply L.cons; auto.
      
      + inversion_clear l as [|sig s' z1 Pz1 Hz1 l'].
        inversion_clear l' as [|sig s'' z2 Pz2 Hz2 l''].
        apply L.cons; auto.
  Defined.
  
  Module Test.
    Require Import Compiler.Source.
    
    Check eq_refl : [27] = projT1 (CFG.eval (compile (MacroAsm.Program.compile Source.Test.e_15))
      [] L.nil).
  End Test.
End Compile.