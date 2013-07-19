(** Primitive binary operators. *)
Require Import List.
Require Import Memory.
Require Import Shape.

Set Implicit Arguments.
Import ListNotations.

Module BinOp.
  Inductive t : Set :=
  | and (n : nat)
  | or (n : nat)
  | xor (n : nat).
  
  Definition size (op : t) : nat :=
    match op with
    | and n | or n | xor n => n
    end.
  
  Definition shape (op : t) : Shape.t :=
    Shape.bits (size op).
  
  Definition type (op : t) : Set :=
    {v : Value.t | Shape.Check.t (shape op) v}.
  
  Definition eval_aux (op : t) (x y : list bool) : list bool :=
    let apply (f : bool -> bool -> bool) :=
      map (fun (b1b2 : bool * bool) =>
        let (b1, b2) := b1b2 in
        andb b1 b2)
        (combine x y) in
    match op with
    | and _ => apply andb
    | or _ => apply orb
    | xor _ => apply xorb
    end.
  
  Lemma eval_aux_keeps_length op x y :
    length (eval_aux op x y) = min (length x) (length y).
    destruct op; simpl;
      rewrite map_length;
      now rewrite combine_length.
  Qed.
  
  Definition eval (op : t) (x y : type op) : type op.
    unfold type, shape in *; simpl in *.
    destruct x as [x Hx]; destruct y as [y Hy].
    destruct x as [xs | | |];
      try now (exfalso; abstract inversion Hx).
    destruct y as [ys | | |];
      try now (exfalso; abstract inversion Hy).
    exists (Value.bits (eval_aux op xs ys)).
    abstract (
      replace (size op) with (length (eval_aux op xs ys)); [
        apply Shape.Check.bits |
        
        rewrite eval_aux_keeps_length;
        replace (length xs) with (size op);
          [| now inversion Hx];
        replace (length ys) with (size op);
          [| now inversion Hy];
        now apply min_l]).
  Defined.
End BinOp.