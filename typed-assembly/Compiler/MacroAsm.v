Require Import ZArith.
Require Import List.
Require Import Compiler.CFGNoLoop.

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

Module RawInstr.
  Inductive t : Set :=
  | const (z : Z) | uminus | plus | times.
  
  Definition eval (i : t) (s : list Z) : list Z :=
    match i with
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
End RawInstr.

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
      cons (Instr.uminus _ _ (fun _ _ => I)) _ (
      nil P)).
    
    (** const 12; const 5; plus *)
    Definition p3 :=
      cons (Instr.const P (existT _ 12 I)) _ (
      cons (Instr.const P (existT _ 5 I)) _ (
      cons (Instr.plus _ _ _ (fun _ _ _ _ => I)) _ (
      nil P))).
    
    Check eq_refl : 12 = projT1 (eval p1).
    Check eq_refl : - 12 =  projT1 (eval p2).
    Check eq_refl : 17 =  projT1 (eval p3).
  End Test.
End Program.

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
    
    - refine (op _ (fun s => existT _ (RawInstr.eval (RawInstr.compile i) s) (fun l => _)) (compile _ _ p)).
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
End Compile.