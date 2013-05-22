(** An assembly language with a static code segment. *)
Require Import Arith.
Require Import List.
Require Import Wellfounded.
Require Import Relation_Operators.

Import ListNotations.

Set Implicit Arguments.

(** A complete version of [nth] for lists given the right pre-condition. *)
Fixpoint valid_nth A (l : list A) (n : nat) (H : n < length l) : A.
  destruct n as [|n]; destruct l as [| x l];
    try destruct (lt_n_0 _ H).
    exact x.
    
    refine (valid_nth _ l n _).
    now apply lt_S_n.
Defined.

Module Instr.
  Inductive t (S : Set) (L : S -> Type)
    (lt : (nat * sigT L) -> (nat * sigT L) -> Prop) (Hwf : well_founded lt)
    (size : nat) : Type :=
  | op :
    (forall s, {s' : S & forall (l : L s), {l' : L s' |
      forall ip, lt (ip, existT _ _ l') (Datatypes.S ip, existT _ _ l) }}) -> t Hwf size
  | jcc :
    (forall s, {next_ip : nat & forall (l : L s), (next_ip <= size) * {l' : L s |
      forall ip, lt (next_ip, existT _ _ l') (ip, existT _ _ l) }}) -> t Hwf size.
End Instr.

Module Program.
  Definition t (S : Set) (L : S -> Type)
    (lt : (nat * sigT L) -> (nat * sigT L) -> Prop) (Hwf : well_founded lt)
    (size : nat) : Type :=
    list (Instr.t Hwf size).
  
  (** The instruction pointer [ip] is decrementing during the evaluation, down to zero. *)
  Definition eval (S : Set) (L : S -> Type)
    (lt_L : (nat * sigT L) -> (nat * sigT L) -> Prop) (Hwf : well_founded lt_L)
    (size : nat) (p : t Hwf size) (Hp_valid : size = length p)
    : forall (input : nat * {s : S & L s}) (Hip_valid : fst input <= size),
      {s : S & L s}.
    refine (well_founded_induction_type Hwf _ _).
    intros input eval Hip_valid.
    destruct input as (ip, (s, l)).
    destruct ip as [|ip].
      (* [ip] is null, the program is terminated. *)
      exact (existT _ _ l).
      
      (* [ip] is not null, one instruction is executed. *)
      refine (let i := valid_nth p (n := ip) _ in _).
        rewrite Hp_valid in Hip_valid.
        apply lt_S_n.
        now apply le_lt_n_Sm.
      destruct i as [f | f].
        (* The current instruction is an [op]. *)
        refine (
          let (s', fl) := f s in
          let (l', Hl'_lt_l) := fl l in
          eval (ip, existT _ _ l') (Hl'_lt_l _) _).
          now apply le_Sn_le.
        
        (* The current instruction is a [jcc]. *)
          exact (
            let (next_ip, fl) := f s in
            let (Hnext_ip, l'_Hl'_lt_l) := fl l in
            let (l', Hl'_lt_l) := l'_Hl'_lt_l in
            eval (next_ip, existT _ _ l') (Hl'_lt_l _) Hnext_ip).
  Defined.
End Program.

Module Test1.
  Import Instr.
  
  Definition S := prod nat nat.
  
  Definition L : S -> Prop := fun s =>
    let (n, ip) := s in
    3 <= n /\ ip <> 0.
  
  Definition measure (x : {s : S & L s}) : nat :=
    match x with
    | existT _ (_, ip) _ => ip
    end.
  
  Definition lt (x y : sigT L) : Prop :=
    measure x < measure y.
  
  Lemma lt_wf : well_founded lt.
    apply well_founded_ltof.
  Qed.
  
  Definition size := 2.
  
  Definition dec_ip (f : nat -> nat) (s : S) : S :=
    let (n, ip) := s in
    (f n, pred ip).
  
  (** A program where the state is a single natural number, and the logical world
      a proof that it is greater or equal to three. *)
  Definition test1 : Program.t lt_wf size.
    refine [
      op lt_wf size (dec_ip (fun n => n + 1)) _;
      op lt_wf size (dec_ip (fun _ => 12)) _]; intros s l.
      
      eapply exist.
    auto with *.
  Defined.
End Test1.