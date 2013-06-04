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
  Definition t (S : Set) (L : S -> Type)
    (lt : (nat * sigT L) -> (nat * sigT L) -> Prop) (Hwf : well_founded lt)
    (size : nat) : Type :=
    forall s ip, {s'_next_ip : S * nat &
      let (s', next_ip) := s'_next_ip in
      forall (l : L s), Datatypes.S ip <= size -> (next_ip <= size) * {l' : L s' |
      lt (next_ip, existT _ _ l') (Datatypes.S ip, existT _ _ l) }}.
  
  (** Simple eval of just one instruction (for tests) *)
  Definition eval (S : Set) (L : S -> Type)
    (lt : (nat * sigT L) -> (nat * sigT L) -> Prop) (Hwf : well_founded lt)
    (size : nat) (i : t Hwf size)
    (ip : nat) (s : S) (l : L s) (Hip_valid : Datatypes.S ip <= size)
    : {next_ip : nat | next_ip <= size} * {s' : S & L s'}.
    destruct (i s ip) as ((s', next_ip), fl).
    destruct (fl l Hip_valid) as (Hnext_ip_valid, (l', _)).
    exact (exist _ next_ip Hnext_ip_valid, existT _ s' l').
  Defined.
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
      destruct (i s ip) as ((s', next_ip), fl).
      destruct (fl l Hip_valid) as (Hnext_ip_valid, (l', Hl'_lt_l)).
      exact (eval (next_ip, existT _ _ l') Hl'_lt_l Hnext_ip_valid).
  Defined.
End Program.

Module Test1.
  Import Instr.
  
  Definition S := nat.
  
  Definition L (n : S) : Prop :=
    3 <= n.
  
  Definition lt (x y : nat * sigT L) : Prop :=
    fst x < fst y.
  
  (** Has to be transparent to reduce the well-founded recursion. *)
  Lemma lt_wf : well_founded lt.
    apply well_founded_ltof.
  Defined.
  
  Definition size := 2.
  
  (** A program where the state is a single natural number, and the logical world
      a proof that it is greater or equal to three. *)
  Definition progr : Program.t lt_wf size.
    refine [
      (fun n ip => existT _ (n + 1, ip) _);
      (fun _ ip => existT _ (12, ip) _)];
      unfold S, L, lt; intros l Hip_valid;
      (split; [now apply le_Sn_le |]);
      [assert (H : L (n + 1)) | assert (H : 3 <= 12)]; unfold L; auto with arith;
      apply exist with (x := H); auto.
  Defined.
  
  Definition input : nat * {s : S & L s}.
    refine (2, existT _ 23 _).
    unfold L; auto with *.
  Defined.
  
  Lemma input_is_valid : fst input <= size.
    trivial.
  Qed.
  
  Definition first_op : Instr.t lt_wf size.
    unfold t.
    refine (fun n ip => existT _ (n + 1, ip) _).
    unfold S, L, lt; intros l Hip_valid.
    split; [now apply le_Sn_le |].
    assert (H : L (n + 1)); unfold L; auto with arith.
    apply exist with (x := H); auto.
  Defined.
  
  Compute Instr.eval first_op (ip := 1) 23
    (leb_complete 3 23 eq_refl) (leb_complete 2 2 eq_refl).
  
  Definition progr_small : Program.t lt_wf 1.
    refine [
      fun n ip => existT _ (n + 1, ip) _];
      unfold S, L, lt; intros l Hip_valid;
      (split; [now apply le_Sn_le |]);
      [assert (H : L (n + 1))]; unfold L; auto with arith;
      apply exist with (x := H); auto.
  Defined.
  
  Compute projT1 (Program.eval progr_small eq_refl
    (1, existT _ 23 (leb_complete 3 23 eq_refl)) (leb_complete 1 1 eq_refl)).
  
  Compute projT1 (Program.eval progr eq_refl input input_is_valid).
End Test1.

Module ArithAsm.
  Require Import ZArith.
  
  Local Open Scope Z_scope.
  
  Inductive t : Set :=
  | const (n : Z) | uminus | plus | minus | times.
  
  Definition S := list Z.
  
  Definition L (s : S) := unit.
  
  Definition lt (x y : nat * sigT L) : Prop :=
    Peano.lt (fst x) (fst y).
  
  Lemma lt_wf : well_founded lt.
    apply well_founded_ltof.
  Defined.
  
  Definition instr_of_state_update size (f : S -> S) : Instr.t lt_wf size.
    unfold Instr.t.
    refine (fun s ip =>
      existT _ (f s, ip) _).
    intros l Hip_valid.
    split; [now apply le_Sn_le |].
    exists tt.
    unfold lt; auto.
  Defined.
  
  Definition instr_of_unop size (f : Z -> Z) : Instr.t lt_wf size :=
    instr_of_state_update size (fun s =>
      match s with
      | n :: s => f n :: s
      | _ => s
      end).
  
  Definition instr_of_binop size (f : Z -> Z -> Z) : Instr.t lt_wf size :=
    instr_of_state_update size (fun s =>
      match s with
      | n1 :: n2 :: s => f n1 n2 :: s
      | _ => s
      end).
  
  Definition to_instr size (i : t) : Instr.t lt_wf size :=
    match i with
    | const n => instr_of_state_update size (fun s => n :: s)
    | uminus => instr_of_unop size (fun n => - n)
    | plus => instr_of_binop size (fun n1 n2 => n1 + n2)
    | minus => instr_of_binop size (fun n1 n2 => n1 - n2)
    | times => instr_of_binop size (fun n1 n2 => n1 * n2)
    end.
  
  Definition compile (p : list t) : Program.t lt_wf (length p) :=
    List.map (to_instr (length p)) p.
  
  Lemma compile_is_valid : forall (p : list t),
    length (compile p) = length p.
    intro; apply map_length.
  Qed.
  
  Definition eval (p : list t) : S.
    refine (projT1 (Program.eval (compile p) _ (length p, existT _ nil tt) _));
      trivial.
    now rewrite compile_is_valid.
  Defined.
  
  Module Test.
    Definition p1 := [const 12].
    Definition p2 := [uminus; const 12].
    Definition p3 := [plus; const 12; times; const 5; const 2].
    
    Compute eval p1.
    Compute eval p2.
    Compute eval p3.
  End Test.
End ArithAsm.











