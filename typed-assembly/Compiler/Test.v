(** Test of the compilation pipeline. *)
Require Import ZArith.
Require Import List.
Require Import Compiler.Source.
Require Import Compiler.SourceToMacroAsm.
Require Import Compiler.MacroAsm.
Require Import Compiler.MacroAsmToCFG.
Require Import Compiler.CFG.

Set Implicit Arguments.
Import ListNotations.
Local Open Scope Z_scope.

Definition P (z : Z) := z >= 20.

Definition e0 : Source.t P :=
  Source.Test.e_15.

Definition e1 : Program.t P [] :=
  SourceToMacroAsm.compile e0.

Definition e2 : CFG.t (MacroAsmToCFG.L.t []) (MacroAsmToCFG.L.t [P]) :=
  MacroAsmToCFG.compile e1.

Check eq_refl : 27 = projT1 (Source.eval e0).
Check eq_refl : 27 = projT1 (Program.eval e1).
Check eq_refl : [27] = projT1 (CFG.eval e2 [] MacroAsmToCFG.L.nil).