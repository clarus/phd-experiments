(** First source language. *)
Require Import List.
Require Import Memory.

Set Implicit Arguments.
Import ListNotations.

Module Op.
  Inductive t : Set :=
  | add | sub | mul
  | not | and | xor.
End Op.

Module Source.
  Inductive t (T : Type) : Type :=
  | imm : Value.t -> t T
  | var : T -> t T
  | op : Op.t -> t T -> (T -> t T) -> t T.
End Source.

Module BareSource.
  Inductive t : Set :=
  | imm : Value.t -> t
  | var : nat -> t
  | op : Op.t -> t -> t -> t.
  
  Definition instanciate_variables (s : forall T, Source.t T) : t :=
    let fix aux s i0 :=
      match s with
      | Source.imm _ v => imm v
      | Source.var i => var i
      | Source.op o x s => op o (aux x i0) (aux (s i0) (S i0))
      end in
    aux (s nat) 0.
End BareSource.

Module Example.
  Import Source.
  
  Definition ex1 T : Source.t T :=
    imm _ (Value.bits [true]).
  
  Definition ex2 T : Source.t T :=
    op Op.add (imm _ (Value.bits [true])) (fun x =>
    op Op.and (imm _ (Value.bits [false])) (fun y =>
    var x)).
  
  Compute BareSource.instanciate_variables ex1.
  Compute BareSource.instanciate_variables ex2.
End Example.
