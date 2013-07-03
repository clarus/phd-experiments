(** A hight-level assembler manipulating both data and proofs. *)
Require Import ZArith.
Require Import List.
Require Import Compiler.Source.

Set Implicit Arguments.
Import ListNotations.
Local Open Scope Z_scope.

Module Sig.
  Definition t := list (Z -> Prop).
End Sig.

Module Stack.
  Inductive t : Sig.t -> Type :=
  | nil : t nil
  | cons : forall P, {z : Z | P z} -> forall sig, t sig -> t (P :: sig).
End Stack.

Module Instr.
  Inductive t : Type :=
  | const : forall (P : Z -> Prop),
    {z : Z | P z} -> t
  | unop : forall (P1 P : Z -> Prop) (op : UnOp.t),
    (forall z1, P1 z1 -> P (UnOp.eval op z1)) -> t
  | binop : forall (P1 P2 P : Z -> Prop) (op : BinOp.t),
    (forall z1 z2, P1 z1 -> P2 z2 -> P (BinOp.eval op z1 z2)) -> t.
  
  Definition input_sig (i : t) (context : Sig.t) : Sig.t :=
    match i with
    | const _ _ => context
    | unop P1 _ _ _ => P1 :: context
    | binop P1 P2 _ _ _ => P1 :: P2 :: context
    end.
  
  Definition output_sig (i : t) (context : Sig.t) : Sig.t :=
    match i with
    | const P _ | unop _ P _ _ | binop _ _ P _ _ => P :: context
    end.
  
  Definition eval (i : t) (context : Sig.t) (s : Stack.t (input_sig i context))
    : Stack.t (output_sig i context).
    destruct i as [P z | P1 P op Hcast | P1 P2 P op Hcast]; simpl in *.
    - exact (Stack.cons P z s).
    
    - inversion_clear s as [|P' z1 sig s'].
      destruct z1 as (z1, H1).
      exact (Stack.cons P (existT _ (UnOp.eval op z1) (Hcast z1 H1)) s').
    
    - inversion_clear s as [|P' z1 sig s']; inversion_clear s' as [|P' z2 sig s''].
      destruct z1 as (z1, H1); destruct z2 as (z2, H2).
      exact (Stack.cons P (existT _ (BinOp.eval op z1 z2) (Hcast z1 z2 H1 H2)) s'').
  Defined.
End Instr.

Module Program.
  Inductive t (P : Z -> Prop) : Sig.t -> Type :=
  | nil : t P [P]
  | cons : forall (i : Instr.t) context,
    t P (Instr.output_sig i context) -> t P (Instr.input_sig i context).
  
  Fixpoint length P input_sig (p : t P input_sig) : nat :=
    match p with
    | nil _ => 0
    | cons _ _ p => S (length p)
    end.
  
  Fixpoint eval_aux P input_sig (p : t P input_sig) (s : Stack.t input_sig)
    : {z : Z | P z}.
    destruct p as [|i context p].
    - inversion_clear s as [|P' z sig s'].
      exact z.
    
    - exact (
      let s := Instr.eval i context s in
      eval_aux _ _ p s).
  Defined.
  
  Definition eval P (p : t P []) : {z : Z | P z} :=
    eval_aux p Stack.nil.
  
  Module Test.
    Definition P (z : Z) := True.
    
    (** const 12 *)
    Definition p1 :=
      cons (Instr.const P (existT _ 12 I)) _ (
      nil P).
    
    (** const 12; uminus *)
    Definition p2 :=
      cons (Instr.const P (existT _ 12 I)) _ (
      cons (Instr.unop _ _ UnOp.uminus (fun _ _ => I)) _ (
      nil P)).
    
    (** const 12; const 5; plus *)
    Definition p3 :=
      cons (Instr.const P (existT _ 12 I)) _ (
      cons (Instr.const P (existT _ 5 I)) _ (
      cons (Instr.binop _ _ _ BinOp.plus (fun _ _ _ _ => I)) _ (
      nil P))).
    
    Check eq_refl : 12 = projT1 (eval p1).
    Check eq_refl : - 12 =  projT1 (eval p2).
    Check eq_refl : 17 =  projT1 (eval p3).
  End Test.
End Program.