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
  Open Local Scope type.

  Definition lt_type (S : Set) (L : nat -> S -> Type) :=
    {ip : nat & {s : S & L ip s}} -> {ip : nat & {s : S & L ip s}} -> Prop.

  Definition t (S : Set) (L : nat -> S -> Type) (lt : lt_type L) (ip : nat) : Type :=
    forall s, {ip' : nat & {s' : S &
      forall (l : L ip s), {l' : L ip' s' |
        lt (existT _ _ (existT _ _ l')) (existT _ _ (existT _ _ l)) }}}.
End Instr.

Module Program.
  Inductive t (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (ip0 : nat) :=
  | nil
  | cons (i : Instr.t lt ip0) (p : t lt (Datatypes.S ip0)).

  (** Sub-proofs are made transparent to allow reductions. *)
  Fixpoint nth (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L)
    (ip0 : nat) (p : t lt ip0) (n : nat) : option (Instr.t lt (ip0 + n)).
    destruct p as [|i p].
      exact None.

      destruct n as [|n].
        assert (Haux : forall a, a + 0 = a).
          induction a; simpl; trivial.
          now rewrite IHa.
        rewrite Haux.
        exact (Some i).

        assert (Haux : forall a b, a + Datatypes.S b = Datatypes.S a + b).
          intros a b; induction a; simpl; trivial.
          simpl; now rewrite IHa.
        rewrite Haux.
        exact (nth _ _ _ _ p _).
  Defined.

  Definition eval (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t lt 0) (ip : nat) (s : S) (l : L ip s)
    : {ip' : nat & {s' : S & L ip' s'}}.
    refine (let aux : {ip' : nat & {s' : S & L ip' s'}} -> _ := _ in
      aux (existT _ _ (existT _ _ l))).
    clear ip s l.
    refine (well_founded_induction_type Hwf _ _).
    intros input eval.
    destruct input as (ip, (s, l)).
    destruct (nth p ip) as [i|].
      (* ip < length p, one instruction is executed. *)
      destruct (i s) as (ip', (s', fl)).
      destruct (fl l) as (l', Hl'_lt_l).
      exact (eval (existT _ _ (existT _ _ l')) Hl'_lt_l).

      (* ip >= length p, the program is terminated. *)
      exact (existT _ _ (existT _ _ l)).
  Defined.
End Program.

Module Test1.
  Import Program.

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
  Definition progr : Program.t lt 0.
    refine (
      cons (fun n => existT _ size (existT _ (n + 1) _)) ( (* n := n + 1 *)
      cons (fun n => existT _ 0 (existT _ 12 _)) ( (* n := 12 *)
      (nil _ _))));
      unfold L, lt, f_lt; intro l;
      [assert (H : 3 <= n + 1) | assert (H : 3 <= 12)]; unfold L; auto with arith;
      exists H; auto.
  Defined.

  Compute projT1 (projT2 (eval lt_wf progr 1 23 (leb_complete 3 23 eq_refl))).
End Test1.

(** A language with arithmetic expressions and assertions. *)
Module ArithLang.
  Require Import ZArith.

  Local Open Scope Z_scope.

  Module Source.
    Inductive t : (Z -> Prop) -> Type :=
    | const : forall (P : Z -> Prop) z, P z -> t P
    | uminus : forall (P1 P : Z -> Prop), t P1 ->
      (forall z1, P1 z1 -> P (- z1)) -> t P
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

      (** For x >= 10, (x {>= 10} + 12 {= 12}) {>= 20}  *)
      Definition e (x : Z) (H : x >= 10) : t (fun y => y >= 20).
        refine (
          plus _ (const (fun x => x >= 10) x H) (const _ 12 eq_refl) _).
        abstract (intros; omega).
      Defined.

      Lemma geb_complete (m n : Z) :
        (if Z_ge_dec m n then true else false) = true -> m >= n.
        now destruct (Z_ge_dec m n).
      Qed.

      Compute projT1 (eval (e (geb_complete 15 10 eq_refl))).
    End Test.
  End Source.

  Module MacroAsm.
    Module Sig.
      Definition t := list (Z -> Prop).
    End Sig.

    Module Stack.
      Inductive t : Sig.t -> Type :=
      | nil : t nil
      | cons : forall P, {z : Z | P z} -> forall sig, t sig -> t (P :: sig).
    End Stack.

    Module Instr.
      Inductive t : Type :=
      | const : forall (P : Z -> Prop), {z : Z | P z} -> t
      | uminus : forall (P1 P : Z -> Prop), (forall z1, P1 z1 -> P (- z1)) -> t
      | plus : forall (P1 P2 P : Z -> Prop), (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 + z2)) -> t
      | times : forall (P1 P2 P : Z -> Prop), (forall z1 z2, P1 z1 -> P2 z2 -> P (z1 * z2)) -> t.

      Definition input_sig (i : t) (context : Sig.t) : Sig.t :=
        match i with
        | const _ _ => context
        | uminus P1 _ _ => P1 :: context
        | plus P1 P2 _ _ | times P1 P2 _ _ => P1 :: P2 :: context
        end.

      Definition output_sig (i : t) (context : Sig.t) : Sig.t :=
        match i with
        | const P _ | uminus _ P _ | plus _ _ P _ | times _ _ P _ => P :: context
        end.

      Definition eval (i : t) (context : Sig.t) (s : Stack.t (input_sig i context))
        : Stack.t (output_sig i context).
        destruct i as [P z | P1 P Hcast | P1 P2 P Hcast | P1 P2 P Hcast]; simpl in *.
        - exact (Stack.cons P z s).

        - inversion_clear s as [|P' z1 sig s'].
          destruct z1 as (z1, H1).
          exact (Stack.cons P (existT _ (- z1) (Hcast z1 H1)) s').

        - inversion_clear s as [|P' z1 sig s']; inversion_clear s' as [|P' z2 sig s''].
          destruct z1 as (z1, H1); destruct z2 as (z2, H2).
          exact (Stack.cons P (existT _ (z1 + z2) (Hcast z1 z2 H1 H2)) s'').

        - inversion_clear s as [|P' z1 sig s']; inversion_clear s' as [|P' z2 sig s''].
          destruct z1 as (z1, H1); destruct z2 as (z2, H2).
          exact (Stack.cons P (existT _ (z1 * z2) (Hcast z1 z2 H1 H2)) s'').
      Defined.
    End Instr.

    Module Program.
      Inductive t (P : Z -> Prop) : Sig.t -> Type :=
      | nil : t P [P]
      | cons : forall (i : Instr.t) context,
        t P (Instr.output_sig i context) -> t P (Instr.input_sig i context).

      Fixpoint length P input_sig (p : t P input_sig) : nat :=
        match p with
        | nil _ => 0
        | cons _ _ p => S (length p)
        end.

      Fixpoint eval_aux P input_sig (p : t P input_sig) (s : Stack.t input_sig)
        : {z : Z | P z}.
        destruct p as [|i context p].
        - inversion_clear s as [|P' z sig s'].
          exact z.

        - exact (
          let s := Instr.eval i context s in
          eval_aux _ _ p s).
      Defined.

      Definition eval P (p : t P []) : {z : Z | P z} :=
        eval_aux p Stack.nil.
    End Program.

    Module Compile.
      Import Instr Program.

      Fixpoint compile_aux context P P' (e : Source.t P) (k : Program.t P' (P :: context))
        : Program.t P' context.
        destruct e as [P z H | P1 P e1 Hcast | P1 P2 P e1 e2 Hcast | P1 P2 P e1 e2 Hcast].
        - exact (cons (const P (existT _ z H)) context k).

        - exact (
          compile_aux _ P1 P' e1 (
          cons (uminus P1 P Hcast) _ k)).

        - exact (
          compile_aux _ P2 P' e2 (
          compile_aux _ P1 P' e1 (
          cons (plus P1 P2 P Hcast) _ k))).

        - exact (
          compile_aux _ P2 P' e2 (
          compile_aux _ P1 P' e1 (
          cons (times P1 P2 P Hcast) _ k))).
      Defined.

      Definition compile P (e : Source.t P) : Program.t P [] :=
        compile_aux e (Program.nil _).
    End Compile.

    Module Test.
      Import Instr Program.

      Definition P (z : Z) := True.

      (** const 12 *)
      Definition p1 :=
        cons (const P (existT _ 12 I)) _ (
        nil P).

      (** const 12; uminus *)
      Definition p2 :=
        cons (const P (existT _ 12 I)) _ (
        cons (uminus _ _ (fun _ _ => I)) _ (
        nil P)).

      (** const 12; const 5; plus *)
      Definition p3 :=
        cons (const P (existT _ 12 I)) _ (
        cons (const P (existT _ 5 I)) _ (
        cons (plus _ _ _ (fun _ _ _ _ => I)) _ (
        nil P))).

      Compute projT1 (eval p1).
      Compute projT1 (eval p2).
      Compute projT1 (eval p3).

      Definition p4 := Compile.compile (Source.Test.e
        (Source.Test.geb_complete 15 10 eq_refl)).

      Check eq_refl : 27 = projT1 (eval p4).
    End Test.
  End MacroAsm.

  Module ConcreteAsm.
    Module Stack.
      Definition t : Set := list Z.

      Inductive is_extraction : forall (sig : MacroAsm.Sig.t), t -> MacroAsm.Stack.t sig -> Prop :=
      | nil : is_extraction [] MacroAsm.Stack.nil
      | cons : forall z (P : Z -> Prop) sig s (s' : MacroAsm.Stack.t sig) (H : P z),
        is_extraction s s' -> is_extraction (z :: s) (MacroAsm.Stack.cons P (existT _ z H) s').
    End Stack.

    Module RawInstr.
      Inductive t : Set :=
      | const (z : Z) | uminus | plus | times.

      Definition eval (i : t) (s : Stack.t) : Stack.t :=
        match i with
        | const z => z :: s
        | uminus =>
          match s with
          | z1 :: s => (- z1) :: s
          | _ => s
          end
        | plus =>
          match s with
          | z1 :: z2 :: s => (z1 + z2) :: s
          | _ => s
          end
        | times =>
          match s with
          | z1 :: z2 :: s => (z1 * z2) :: s
          | _ => s
          end
        end.
    End RawInstr.

    Module AnnotedInstr.
      Definition f_lt T size (x : {ip : nat & T ip}) : nat :=
        size - projT1 x.

      Definition lt (L : nat -> Stack.t -> Type) size : Instr.lt_type L := fun x y =>
        (f_lt _ size x < f_lt _ size y) % nat.

      Lemma lt_wf L size : well_founded (lt L size).
        apply well_founded_ltof.
      Defined.

      Definition t (L : nat -> Stack.t -> Type) (size ip : nat) : Type :=
        Instr.t (lt L size) ip.

      Definition lift (L : nat -> Stack.t -> Type) (size : nat)
        (i : RawInstr.t) (ip : nat) (Hip : (ip < size) % nat)
        (fl : forall s, L ip s -> L (S ip) (RawInstr.eval i s))
        : t L size ip.
        unfold t, Instr.t.
        intro s.
        exists (S ip).
        exists (RawInstr.eval i s).
        intro l.
        exists (fl s l).
        unfold lt, f_lt.
        simpl; omega.
      Defined.
    End AnnotedInstr.

    Module Program.
      Fixpoint sigs_of_program (P : Z -> Prop) (sig : MacroAsm.Sig.t) (p : MacroAsm.Program.t P sig)
        : list MacroAsm.Sig.t :=
        match p with
        | MacroAsm.Program.nil _ => []
        | MacroAsm.Program.cons _ sig p => sig :: sigs_of_program p
        end.

      Definition L P input_sig (p : MacroAsm.Program.t P input_sig) (context : list MacroAsm.Sig.t)
        (ip : nat) (s : Stack.t) : Type :=
        let sigs := context ++ sigs_of_program p in
        let size := length sigs in
        let sig :=
          match le_lt_dec size ip with
          | left _ => [P]
          | right Hlt => valid_nth sigs Hlt
          end in
        {s' : MacroAsm.Stack.t sig | Stack.is_extraction s s'}.

      Definition lt P input_sig (p : MacroAsm.Program.t P input_sig) (context : list MacroAsm.Sig.t)
        : Instr.lt_type (L p context) :=
        AnnotedInstr.lt _

      Fixpoint compile_aux P input_sig (p : MacroAsm.Program.t P input_sig) (context : list MacroAsm.Sig.t)
        : {L : nat -> Stack.t -> Type & {lt : Instr.lt_type L & Program.t lt ip0}}.
        destruct p as [|i p].
        - exists (fun _ s => ).

      Definition compile_aux (P : Z -> Prop) (sig : MacroAsm.Sig.t) (p : MacroAsm.Program.t P sig) (ip0 : nat)
        : Program.t (S := Stack.t) (L := L p) (AnnotedInstr.lt _ (MacroAsm.Program.length p)) ip0.

      Fixpoint extract_sig_aux (sigs : list MacroAsm.Sig.t) (ip0 : nat)
        : nat -> Stack.t -> Type :=
        .
    End Program.
  End ConcreteAsm.

  (*Definition compile_aux (p : list t) : Program.t lt_wf (length p) :=

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
  End Test.*)
End ArithLang.
