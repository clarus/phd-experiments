(** Control flow graphs without loops. *)
Set Implicit Arguments.

Module CFG.
  Inductive t (S : Set) : (S -> Type) -> (S -> Type) -> Type :=
  | nop : forall L,
    t L L
  | op : forall Lin L Lout,
    (forall s, {s' : S & Lin s -> L s'}) ->
    t L Lout -> t Lin Lout
  | jcc : forall Lin Lin_true Lin_false Lmerge Lout,
    (forall s, (Lin s -> Lin_true s) + (Lin s -> Lin_false s)) ->
    t Lin_true Lmerge -> t Lin_false Lmerge -> t Lmerge Lout ->
    t Lin Lout.
  
  Fixpoint eval (S : Set) Lin Lout (p : t Lin Lout)
    (s : S) (l : Lin s) {struct p} : {s' : S & Lout s'}.
    destruct p as
      [ L
      | Lin L Lout f p
      | Lin Lin_true Lin_false Lmerge Lout f p_true p_false p].
    - exact (existT _ _ l).
    
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