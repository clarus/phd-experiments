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

(*Module Ip.
  Definition t : Set := nat.
  
  Definition tl (size : nat) : Set := {ip : nat | ip < size}.
  
  (*Definition is_valid (ip : t) (size : nat) :=
    match ip with
    | None => True
    | Some ip => ip < size
    end.*)
End Ip.*)

Module Instr.
  Open Local Scope type.
  
  Definition lt_type (S : Set) (L : nat -> S -> Type) :=
    {ip : nat & {s : S & L ip s}} -> {ip : nat & {s : S & L ip s}} -> Prop.
  
  Definition t (S : Set) (L : nat -> S -> Type) (lt : lt_type L) (Hwf : well_founded lt)
    : Type :=
    {ip : nat & forall s, {ip' : nat & {s' : S &
      forall (l : L ip s), {l' : L ip' s' |
        lt (existT _ _ (existT _ _ l')) (existT _ _ (existT _ _ l)) }}}}.
  
  (** Simple eval of just one instruction (for tests) *)
  Definition eval (S : Set) (L : nat -> S -> Type) (lt : lt_type L) (Hwf : well_founded lt)
    (i : t Hwf) (s : S) (l : L (projT1 i) s)
    : {ip' : nat & {s' : S & L ip' s'}}.
    destruct i as (ip, f); simpl in l.
    destruct (f s) as (ip', (s', fl)).
    destruct (fl l) as (l', _).
    now exists ip'; exists s'.
  Defined.
End Instr.

Module Program.
  Definition t (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    : Type :=
    list (Instr.t Hwf).
  
  (*Definition is_valid (S : Set) (L : nat -> S -> Type)
    (lt : {ip : nat & {s : S & L ip s}} -> {ip : nat & {s : S & L ip s}} -> Prop) (Hwf : well_founded lt)
    (p : t L Hwf) : Prop :=
    let fix aux p (ip : nat) : Prop :=
      match p with
      | nil => True
      | existT _ ip' _ :: p => ip' = ip /\ aux p (Datatypes.S ip)
      end in
    aux p 0.
  
  Lemma is_valid_nth (S : Set) (L : nat -> S -> Type)
    (lt : {ip : nat & {s : S & L ip s}} -> {ip : nat & {s : S & L ip s}} -> Prop) (Hwf : well_founded lt)
    (p : t L Hwf) (H : is_valid p)
    : forall (ip : nat) (Hip : ip < length p), projT1 (valid_nth p Hip) = ip.
    induction p; intros ip Hip; simpl in H.
      admit.
      
      destruct ip as [|ip]; simpl.
        unfold is_valid in H.
        destruct a as (ip', f); simpl in *.
        tauto.
        
        unfold is_valid in H.
        simpl.
        unfold is_valid in H; simpl in H.
  Admitted.*)
  
  Definition is_valid (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t Hwf) : Prop :=
    forall (ip : nat) (H : ip < length p), projT1 (valid_nth p H) = ip.
  
  Definition is_valid_aux (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t Hwf) (ip0 : nat) : Prop :=
    forall (ip : nat) (H : ip < length p), projT1 (valid_nth p H) = ip0 + ip.
  
  (** All sub-proofs are made transparent for reduction. *)
  Fixpoint decide_is_valid_aux (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t Hwf) (ip0 : nat) : option (is_valid_aux p ip0).
    destruct p as [|i p].
      refine (Some _); unfold is_valid; intros ip H.
      unfold Peano.lt in H.
      simpl in H.
      inversion H.
      
      destruct i as (ip', f).
      destruct (eq_nat_dec ip0 ip') as [Hip0_ip' | _]; [| exact None].
      destruct (decide_is_valid_aux _ _ _ _ p (1 + ip0)) as [Hp |]; [| exact None].
      refine (Some _); unfold is_valid; intros ip H.
      destruct ip as [|ip]; simpl in *.
        now rewrite Hip0_ip'.
        
        unfold is_valid_aux in Hp.
        assert (Haux : forall n m, n + Datatypes.S m = Datatypes.S n + m).
          intros n m; induction n; trivial.
          simpl; now rewrite IHn.
        rewrite Haux.
        apply Hp.
  Defined.
  
  Definition decide_is_valid (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t Hwf) : option (is_valid p) :=
    decide_is_valid_aux p 0.
  
  Definition reflexive_is_valid (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t Hwf) (H : (if decide_is_valid p then true else false) = true) : is_valid p.
    now destruct (decide_is_valid p) as [Hvalid |].
  Defined.
  
  Definition eval (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t Hwf) (Hp_valid : is_valid p) (s : S) (l : L 0 s)
    : {ip' : nat & {s' : S & L ip' s'}}.
    refine (let aux : {ip' : nat & {s' : S & L ip' s'}} -> _ := _ in
      aux (existT _ _ (existT _ _ l))).
    clear s l.
    refine (well_founded_induction_type Hwf _ _).
    intros input eval.
    destruct input as (ip, (s, l)).
    destruct (le_lt_dec (length p) ip) as [Hge | Hlt].
      (* ip >= length p, the program is terminated. *)
      exact (existT _ _ (existT _ _ l)).
      
      (* ip < length p, one instruction is executed. *)
      assert (Hip'_ip := Hp_valid ip Hlt).
      destruct (valid_nth p Hlt) as (ip', f); simpl in Hip'_ip.
      rewrite Hip'_ip in f; clear Hip'_ip ip'.
      destruct (f s) as (ip', (s', fl)).
      destruct (fl l) as (l', Hl'_lt_l).
      exact (eval (existT _ _ (existT _ _ l')) Hl'_lt_l).
  Defined.
End Program.

Module Test1.
  Import Instr.
  
  Definition S := nat.
  
  Definition L (ip : nat) (n : S) : Prop :=
    3 <= n.
  
  Definition size := 2.
  
  Definition f_lt T (x : {ip : nat & T ip}) : nat :=
    if leb size (projT1 x) then
      0
    else
      (projT1 x) + 1.
  
  Definition lt : Instr.lt_type L := fun x y =>
    f_lt _ x < f_lt _ y.
  
  (** Has to be transparent to reduce the well-founded recursion. *)
  Lemma lt_wf : well_founded lt.
    apply well_founded_ltof.
  Defined.
  
  (** A program where the state is a single natural number, and the logical world
      a proof that it is greater or equal to three. *)
  Definition progr : Program.t lt_wf.
    refine [
      existT _ 0 (fun n => existT _ size (existT _ (n + 1) _)); (* n := n + 1 *)
      existT _ 1 (fun n => existT _ 0 (existT _ 12 _))]; (* n := 12 *)
      unfold L, lt, f_lt; intro l;
      [assert (H : 3 <= n + 1) | assert (H : 3 <= 12)]; unfold L; auto with arith;
      exists H; auto.
  Defined.
  
  Definition progr_is_valid : Program.is_valid progr :=
    Program.reflexive_is_valid progr eq_refl.
  
  Definition progr_is_valid' : Program.is_valid progr.
  Admitted.
  
  Compute projT1 (Program.eval progr_is_valid 23 (leb_complete 3 23 eq_refl)).
  Compute projT1 (Program.eval progr_is_valid' 23 (leb_complete 3 23 eq_refl)).
  
  (*Definition input : nat * {s : S & L s}.
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
    (1, existT _ 23 (leb_complete 3 23 eq_refl)) (leb_complete 1 1 eq_refl)).*)
End Test1.

(** A language with arithmetic expressions and assertions *)
Module Arith.
  Require Import ZArith.
  
  Local Open Scope Z_scope.
  
(*   Definition subZ P := {z : Z | P z}. *)
  
  Inductive t : (Z -> Prop) -> Type :=
  | const : forall (P : Z -> Prop) z, P z -> t P
  | uminus : forall (P1 P : Z -> Prop), t P1 ->
    (forall z, P1 z -> P (- z)) -> t P
  | plus : forall (P1 P2 P : Z -> Prop), t P1 -> t P2 ->
    (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 + z2)) -> t P
  | times : forall (P1 P2 P : Z -> Prop), t P1 -> t P2 ->
    (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 * z2)) -> t P.
  
  Fixpoint eval P (e : t P) {struct e} : {z : Z | P z}.
    destruct e as [P z H | P1 P e1 Hcast | P1 P2 P e1 e2 Hcast | P1 P2 P e1 e2 Hcast].
    - exists z; trivial.
    
    - destruct (eval _ e1) as (z1, H1).
      exists (- z1); auto.
    
    - destruct (eval _ e1) as (z1, H1).
      destruct (eval _ e2) as (z2, H2).
      exists (z1 + z2); auto.
    
    - destruct (eval _ e1) as (z1, H1).
      destruct (eval _ e2) as (z2, H2).
      exists (z1 * z2); auto.
  Defined.
  
  Module Test.
    Definition example (x : Z) (H : x >= 10) : {y : Z | y >= 20}.
      refine (
        let y := x + 12 in
        existT _ y _).
      abstract (unfold y; omega).
    Defined.
    
    Definition e (x : Z) (H : x >= 10) : t (fun y => y >= 20).
      refine (
        plus _ (const (fun x => x >= 10) x H) (const _ 12 eq_refl) _).
      abstract (intros; omega).
    Defined.
    
    Lemma ge15 : 15 >= 10.
      omega.
    Qed.
    
    Compute projT1 (eval (e ge15)).
  End Test.
End Arith.

Module ArithAsm.
  Require Import ZArith.
  
  Local Open Scope Z_scope.
  
  Definition S := list Z.
  
  Definition lt (L : S -> Type) (x y : nat * sigT L) : Prop :=
    Peano.lt (fst x) (fst y).
  
  Lemma lt_wf : forall L, well_founded (@lt L).
    intro; apply well_founded_ltof.
  Defined.
  
  Definition instr_of_state_update L size
    (f : S -> S) (fl : forall s, L s -> L (f s))
    : Instr.t (@lt_wf L) size.
    unfold Instr.t.
    refine (fun s ip =>
      existT _ (f s, ip) _).
    intros l Hip_valid.
    split; [now apply le_Sn_le |].
    exists (fl s l).
    unfold lt; auto.
  Defined.
  
  Definition instr_of_unop L size (f : Z -> Z) : Instr.t (@lt_wf L) size :=
    instr_of_state_update L size (fun s =>
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
  
  Inductive t (L : S -> Type) : Set :=
  | const (n : Z) | uminus | plus | minus | times.
  
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















