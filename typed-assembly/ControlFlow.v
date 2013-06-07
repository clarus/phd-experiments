(** Experiments to find a nice representation of an annoted control-flow graph *)
Require Import Wellfounded.

Set Implicit Arguments.

Module WellFounded.
  Record t (A : Type) : Type := new {
    lt : A -> A -> Prop;
    Hwf : well_founded lt}.
End WellFounded.

Module Context.
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
End Context.

Module CFG.
  Inductive t (S : Set) : Context.t S -> (S -> Type) -> (S -> Type) -> Type :=
  | nop : forall C L,
    t C L L
  | op : forall C Lin L Lout,
    (forall s, {s' : S & Lin s -> L s'}) ->
    t C L Lout ->
    t C Lin Lout
  | jcc : forall C Lin Lin_true Lin_false Lmerge Lout,
    (forall s, (Lin s -> Lin_true s) + (Lin s -> Lin_false s)) ->
    t C Lin_true Lmerge -> t C Lin_false Lmerge -> t C Lmerge Lout ->
    t C Lin Lout
  | label : forall C Lin L Lout (WF : WellFounded.t (sigT Lin)),
    t (Context.cons WF C) Lin L -> t C L Lout ->
    t C Lin Lout
  | goto : forall C1 C2 Lin L Lout (WF : WellFounded.t (sigT Lin)),
    
    t (Context.append C1 (Context.cons WF C2)) Lin Lout.
  
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