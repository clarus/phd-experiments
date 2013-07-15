(** Low-level source language using indexed variables. *)
Require Import List.
Require Import Memory.
Require Import LowSource.

Set Implicit Arguments.
Import ListNotations.

Module Operand.
  Inductive t : Set :=
  | imm : Value.t -> t
  | var : nat -> t.
  
  Definition of_phoas (op : LowSource.Operand.t nat) : t :=
    match op with
    | LowSource.Operand.imm _ v => imm v
    | LowSource.Operand.var x => var x
    end.
End Operand.

Module Source.
  Inductive t : Set :=
  | final : Operand.t -> t
  | op : BinOp.t -> Operand.t -> Operand.t -> t -> t.
  
  Definition of_phoas (s : LowSource.Source.t nat) : t :=
    let fix aux s i :=
      match s with
      | LowSource.Source.final x => final (Operand.of_phoas x)
      | LowSource.Source.op o x y s => op o (Operand.of_phoas x) (Operand.of_phoas y) (aux (s i) (S i))
      end in
    aux s 0.
End Source.

Module Example.
  Module OfPhoas.
    Import LowSource.Operand.
    Import LowSource.Source.
    
    Definition ex1 T : t T :=
      final (imm _ (Value.bits [true])).
    
    Definition ex2 T : t T :=
      op BinOp.add (imm _ (Value.bits [true])) (imm _ (Value.bits [false])) (fun x =>
      op BinOp.and (imm _ (Value.bits [false; true])) (imm _ (Value.bits [])) (fun y =>
      final (var x))).
    
    Compute Source.of_phoas (ex1 nat).
    Compute Source.of_phoas (ex2 nat).
  End OfPhoas.
End Example.