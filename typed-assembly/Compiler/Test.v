Require Import ZArith.
Require Import List.
Require Import Compiler.Source.
Require Import Compiler.MacroAsm.
Require Import Compiler.CFGNoLoop.

Set Implicit Arguments.
Import ListNotations.
Local Open Scope Z_scope.

Definition P (z : Z) := z >= 20.

Definition e0 : Source.t P :=
  Source.Test.e_15.

Definition e1 : Program.t P [] :=
  Source.compile e0.

Definition e2 : CFG.t (MacroAsm.Compile.L.t []) (MacroAsm.Compile.L.t [P]) :=
  MacroAsm.Compile.compile e1.

Check eq_refl : 27 = projT1 (Source.eval e0).
Check eq_refl : 27 = projT1 (Program.eval e1).
Check eq_refl : [27] = projT1 (CFG.eval e2 [] MacroAsm.Compile.L.nil).