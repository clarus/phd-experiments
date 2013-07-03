Require Import ZArith.
Require Import List.
Require Import Compiler.Source.
Require Import Compiler.MacroAsm.

Set Implicit Arguments.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint compile_aux context P P' (e : Source.t P) (k : Program.t P' (P :: context))
  : Program.t P' context.
  destruct e as [P z H | P1 P op e1 Hcast | P1 P2 P op e1 e2 Hcast | P1 P2 P e1 e2 Hcast].
  - exact (Program.cons (Instr.const P (existT _ z H)) context k).
  
  - exact (
    compile_aux _ P1 P' e1 (
    Program.cons (Instr.unop P1 P op Hcast) _ k)).
  
  - exact (
    compile_aux _ P2 P' e2 (
    compile_aux _ P1 P' e1 (
    Program.cons (Instr.binop P1 P2 P op Hcast) _ k))).
  
  - 
Defined.

Definition compile P (e : Source.t P) : Program.t P [] :=
  compile_aux e (Program.nil _).