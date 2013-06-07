(** Experiments to find a nice representation of an annoted control-flow graph *)
Require Import Wellfounded.

Set Implicit Arguments.

Module WellFounded.
  Record t (A : Type) : Type := new {
    lt : A -> A -> Prop;
    Hwf : well_founded lt}.
End WellFounded.

(*Module Context.
  Module T.
    Inductive t (S : Set) : Type :=
    | nil
    | cons (A : Type) (WF : WellFounded.t A) (C : t S).
    
    Fixpoint append S (C1 C2 : t S) : t S :=
      match C1 with
      | nil _ => C2
      | cons WF C1 => cons WF (append C1 C2)
      end.
  End T.
  
  Module I.
    Inductive t (S : Set) : T.t S -> Type :=
    | nil : t (T.nil S)
    | cons : forall A WF (C : T.t S) (a : A) (c : t C), t (T.cons (A := A) WF C).
  End I.
  
  Inductive lt S : {C : T.t S & I.t C} -> {C : T.t S & I.t C} -> Prop :=
  | lt_nil : forall A WF a C c,
    lt (existT _ _ (I.cons (A := A) WF (C := C) a c))
       (existT _ _ (I.nil S))
  | lt_head_lt : forall A WF a1 a2 C1 C2 c1 c2,
    WellFounded.lt WF a1 a2 ->
    lt (existT _ _ (I.cons (A := A) WF (C := C1) a1 c1))
       (existT _ _ (I.cons (A := A) WF (C := C2) a2 c2))
  | lt_head_eq : forall A WF a C1 C2 c1 c2,
    lt (existT _ _ c1)
       (existT _ _ c2) ->
    lt (existT _ _ (I.cons (A := A) WF (C := C1) a c1))
       (existT _ _ (I.cons (A := A) WF (C := C2) a c2)).
  
  Lemma lt_wf (S : Set) : well_founded (lt (S := S)).
    intro x.
    constructor; intros y H.
  Admitted.
End Context.*)

(** The shape of positions of the loop entry points *)
Module Shape.
  Inductive t : Type :=
  | nil
  | loop (A : Type) (WF : WellFounded.t A) (shape_in shape_next : t)
  | jcc (shape_true shape_false shape_next : t).
End Shape.

(** A state of the program's loop variants. This type has a well-founded order. *)
Module Path.
  Inductive t : Shape.t -> Type :=
  | nil :
    t Shape.nil
  | loop_in : forall A WF shape_in shape_next (a : A) (path : t shape_in),
    t (Shape.loop (A := A) WF shape_in shape_next)
  | loop_next : forall A WF shape_in shape_next (a : A) (path : t shape_next),
    t (Shape.loop (A := A) WF shape_in shape_next)
  | jcc_true : forall shape_true shape_false shape_next (path : t shape_true),
    t (Shape.jcc shape_true shape_false shape_next)
  | jcc_false : forall shape_true shape_false shape_next (path : t shape_false),
    t (Shape.jcc shape_true shape_false shape_next)
  | jcc_next : forall shape_true shape_false shape_next (path : t shape_next),
    t (Shape.jcc shape_true shape_false shape_next).
End Path.

(** The stack of the loop entry points a program is depending on. *)
Module Context.
  Inductive t (S : Set) : Type :=
  | nil
  | cons (A : Type) (WF : WellFounded.t A) (L : S -> Type) (context : t S).
  
  Fixpoint append S (C1 C2 : t S) : t S :=
    match C1 with
    | nil _ => C2
    | cons WF L C1 => cons WF L (append C1 C2)
    end.
End Context.

Module CFG.
  Inductive t (S : Set) : Context.t S -> Shape.t -> (S -> Type) -> (S -> Type) -> Type :=
  | nop : forall context L,
    t context Shape.nil L L
  | op : forall context shape Lin L Lout,
    (forall s, {s' : S & Lin s -> L s'}) ->
    t context shape L Lout ->
    t context shape Lin Lout
  | jcc : forall context shape_true shape_false shape_next
      Lin Lin_true Lin_false Lmerge Lout,
    (forall s, (Lin s -> Lin_true s) + (Lin s -> Lin_false s)) ->
    t context shape_true Lin_true Lmerge -> t context shape_false Lin_false Lmerge -> t context shape_next Lmerge Lout ->
    t context (Shape.jcc shape_true shape_false shape_next) Lin Lout
  | loop : forall context shape_in shape_next Lin L Lout A WF,
    t (Context.cons (A := A) WF Lin context) shape_in Lin L -> t context shape_next L Lout ->
    t context (Shape.loop (A := A) WF shape_in shape_next) Lin Lout
  | goto : forall context1 A WF context2 Lin L Lout,
    t (Context.append context1 (Context.cons (A := A) WF L context2)) Shape.nil Lin Lout.
  
  (*Inductive t (S : Set) : (S -> Type) -> (S -> Type) -> Type :=
  | op : forall (f : S -> S) (Lin L Lout : S -> Type)
    (fl : forall s, Lin s -> L (f s)),
    t S L Lout ->
    t S Lin Lout
  | jcc : forall (c : S -> bool) (Lin Lin_true Lin_false Lmerge Lout : S -> Type)
    (fl : forall s, if c s then Lin s -> Lin_true s else Lin s -> Lin_false s),
    t S Lin_true Lmerge -> t S Lin_false Lmerge -> t S Lmerge Lout ->
    t S Lin Lout.*)
  
  Fixpoint eval S Lin Lout (p : t S Lin Lout)
    (s : S) (l : Lin s) {struct p} : {s' : S & Lout s'}.
    destruct p as [Lin L Lout f p
      | Lin Lin_true Lin_false Lmerge Lout f p_true p_false p].
    - exact (
        let (_, fl) := f s in
        eval _ _ _ p _ (fl l)).
    
    - exact (
        match f s with
        | inl fl_true =>
          let (s, l) := eval _ _ _ p_true _ (fl_true l) in
          eval _ _ _ p _ l
        | inr fl_false =>
          let (s, l) := eval _ _ _ p_false _ (fl_false l) in
          eval _ _ _ p _ l
        end).
  Defined.
End CFG.