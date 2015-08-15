Require Import ZArith.
Require Import List.
Require Import Compiler.Source.
Require Import Compiler.MacroAsm.
Require Import Compiler.CFG.

Set Implicit Arguments.
Import ListNotations CFG.
Local Open Scope Z_scope.

Module RawInstr.
  Inductive t : Set :=
  | const (z : Z) | unop (op : UnOp.t) | binop (op : BinOp.t).

  Definition eval (i : t) (s : list Z) : list Z :=
    match i with
    | const z => z :: s
    | unop o =>
      match s with
      | z1 :: s => (UnOp.eval o z1) :: s
      | _ => s
      end
    | binop o =>
      match s with
      | z1 :: z2 :: s => (BinOp.eval o z1 z2) :: s
      | _ => s
      end
    end.

  Definition compile (i : Instr.t) : t :=
    match i with
    | Instr.const _ (exist _ z _) => const z
    | Instr.unop _ _ o _ => unop o
    | Instr.binop _ _ _ o _ => binop o
    end.
End RawInstr.

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

(** This compilation step does the extraction. *)
Fixpoint compile (P : Z -> Prop) (sig : Sig.t) (p : Program.t P sig)
  : CFG.t (L.t sig) (L.t [P]).
  destruct p as [|i context p].
  - exact (@nop _ _).

  - refine (op _ (fun s => existT _ (RawInstr.eval (RawInstr.compile i) s) (fun l => _)) (compile _ _ p)).
    destruct i as [P' z | P1 P' op Hcast | P1 P2 P' op Hcast]; simpl in *.
    + destruct z as (z, H).
      now apply L.cons.

    + inversion_clear l.
      apply L.cons; auto.

    + inversion_clear l as [|sig s' z1 Pz1 Hz1 l'].
      inversion_clear l' as [|sig s'' z2 Pz2 Hz2 l''].
      apply L.cons; auto.
Defined.
