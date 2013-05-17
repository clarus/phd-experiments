(** An assembly language with a static code segment. *)
Require Import Arith.
Require Import Wellfounded.
Require Import Relation_Operators.

Set Implicit Arguments.

Fixpoint valid_nth A (l : list A) (n : nat) (H : n < length l) : A.
  destruct n as [|n]; destruct l as [| x l];
    try destruct (lt_n_0 _ H).
    exact x.
    
    refine (valid_nth _ l n _).
    now apply lt_S_n.
Defined.

Module Instr.
  Inductive t (S : Set) (L : S -> Type)
    (lt : sigT L -> sigT L -> Prop) (Hwf : well_founded lt)
    (size : nat) : Type :=
  | op : forall (f : S -> S),
    (forall s (l : L s), {l' : L (f s) | lt (existT _ _ l') (existT _ _ l) }) -> t Hwf size
  | jcc : (forall s, option {n : nat & forall (l : L s), n <= size}) ->
    (forall s (l : L s), {l' : L s | lt (existT _ _ l') (existT _ _ l) }) -> t Hwf size.
End Instr.

Module Program.
  Definition t (S : Set) (L : S -> Type)
    (lt : sigT L -> sigT L -> Prop) (Hwf : well_founded lt)
    (size : nat) : Type :=
    list (Instr.t Hwf size).
  
  Definition eval (S : Set) (L : S -> Type)
    (lt_L : sigT L -> sigT L -> Prop) (Hwf : well_founded lt_L)
    (size : nat) (p : t Hwf size) (Hp_valid : size = length p)
    : forall (input : {s : S & L s}) (ip : nat) (Hip_valid : ip <= size),
      {s : S & L s}.
    refine (well_founded_induction_type Hwf _ _).
    intros input eval ip Hip_valid.
    destruct input as [s l].
    destruct ip as [|ip].
      (* [ip] is null, the program is terminated. *)
      exact (existT _ _ l).
      
      refine (let i := valid_nth p (n := ip) _ in _).
        rewrite Hp_valid in Hip_valid.
        apply lt_S_n.
        now apply le_lt_n_Sm.
      destruct i as [f fl | ptr fl].
        (* The current instruction is an [op]. *)
        refine (
          let (l', Hl'_lt_l) := fl s l in
          eval (existT _ _ l') Hl'_lt_l ip _).
          now apply le_Sn_le.
        
        (* The current instruction is a [jcc]. *)
        destruct (ptr s) as [(next_ip, Hptr)|].
          (* The jump is occuring. *)
          exact (
            let (l', Hl'_lt_l) := fl s l in
            eval (existT _ _ l') Hl'_lt_l next_ip (Hptr l)).
          
          (* The jump is not occuring. *)
          refine (
            let (l', Hl'_lt_l) := fl s l in
            eval (existT _ _ l') Hl'_lt_l ip _).
          now apply le_Sn_le.
  Defined.
End Program.