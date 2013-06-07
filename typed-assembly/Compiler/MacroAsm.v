Require Import ZArith.
Require Import List.
Require Import Source.

Set Implicit Arguments.
Local Open Scope Z_scope.
Import ListNotations.

Module MacroAsm.
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
    | const : forall (P : Z -> Prop), {z : Z | P z} -> t
    | uminus : forall (P1 P : Z -> Prop), (forall z1, P1 z1 -> P (- z1)) -> t
    | plus : forall (P1 P2 P : Z -> Prop), (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 + z2)) -> t
    | times : forall (P1 P2 P : Z -> Prop), (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 * z2)) -> t.
    
    Definition input_sig (i : t) (context : Sig.t) : Sig.t :=
      match i with
      | const _ _ => context
      | uminus P1 _ _ => P1 :: context
      | plus P1 P2 _ _ | times P1 P2 _ _ => P1 :: P2 :: context
      end.
    
    Definition output_sig (i : t) (context : Sig.t) : Sig.t :=
      match i with
      | const P _ | uminus _ P _ | plus _ _ P _ | times _ _ P _ => P :: context
      end.
    
    Definition eval (i : t) (context : Sig.t) (s : Stack.t (input_sig i context))
      : Stack.t (output_sig i context).
      destruct i as [P z | P1 P Hcast | P1 P2 P Hcast | P1 P2 P Hcast]; simpl in *.
      - exact (Stack.cons P z s).
      
      - inversion_clear s as [|P' z1 sig s'].
        destruct z1 as (z1, H1).
        exact (Stack.cons P (existT _ (- z1) (Hcast z1 H1)) s').
      
      - inversion_clear s as [|P' z1 sig s']; inversion_clear s' as [|P' z2 sig s''].
        destruct z1 as (z1, H1); destruct z2 as (z2, H2).
        exact (Stack.cons P (existT _ (z1 + z2) (Hcast z1 z2 H1 H2)) s'').
      
      - inversion_clear s as [|P' z1 sig s']; inversion_clear s' as [|P' z2 sig s''].
        destruct z1 as (z1, H1); destruct z2 as (z2, H2).
        exact (Stack.cons P (existT _ (z1 * z2) (Hcast z1 z2 H1 H2)) s'').
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
  End Program.
  
  Module Compile.
    Import Instr Program.
    
    Fixpoint compile_aux context P P' (e : Source.t P) (k : Program.t P' (P :: context))
      : Program.t P' context.
      destruct e as [P z H | P1 P e1 Hcast | P1 P2 P e1 e2 Hcast | P1 P2 P e1 e2 Hcast].
      - exact (cons (const P (existT _ z H)) context k).
      
      - exact (
        compile_aux _ P1 P' e1 (
        cons (uminus P1 P Hcast) _ k)).
      
      - exact (
        compile_aux _ P2 P' e2 (
        compile_aux _ P1 P' e1 (
        cons (plus P1 P2 P Hcast) _ k))).
      
      - exact (
        compile_aux _ P2 P' e2 (
        compile_aux _ P1 P' e1 (
        cons (times P1 P2 P Hcast) _ k))).
    Defined.
    
    Definition compile P (e : Source.t P) : Program.t P [] :=
      compile_aux e (Program.nil _).
  End Compile.
  
  Module Test.
    Import Instr Program.
    
    Definition P (z : Z) := True.
    
    (** const 12 *)
    Definition p1 :=
      cons (const P (existT _ 12 I)) _ (
      nil P).
    
    (** const 12; uminus *)
    Definition p2 :=
      cons (const P (existT _ 12 I)) _ (
      cons (uminus _ _ (fun _ _ => I)) _ (
      nil P)).
    
    (** const 12; const 5; plus *)
    Definition p3 :=
      cons (const P (existT _ 12 I)) _ (
      cons (const P (existT _ 5 I)) _ (
      cons (plus _ _ _ (fun _ _ _ _ => I)) _ (
      nil P))).
    
    Compute projT1 (eval p1).
    Compute projT1 (eval p2).
    Compute projT1 (eval p3).
    
    Definition p4 := Compile.compile (Source.Test.e
      (Source.Test.geb_complete 15 10 eq_refl)).
    
    Check eq_refl : 27 = projT1 (eval p4).
  End Test.
End MacroAsm.