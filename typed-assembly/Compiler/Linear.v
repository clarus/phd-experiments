(** The low-level assember. *)
Require Import Arith.

Set Implicit Arguments.

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
  
  Fixpoint length (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L)
    (ip0 : nat) (p : t lt ip0) : nat :=
    match p with
    | nil _ _ => 0
    | cons _ p => 1 + length p
    end.
  
  (** Sub-proofs are made transparent to allow reductions. *)
  Fixpoint nth (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L)
    (ip0 : nat) (p : t lt ip0) (n : nat) (H : n < length p)
    : Instr.t lt (ip0 + n).
    destruct p as [|i p]; simpl in H.
    - destruct (lt_n_0 _ H).
    
    - destruct n as [|n].
        assert (Haux : forall a, a + 0 = a).
          induction a; simpl; trivial.
          now rewrite IHa.
        rewrite Haux.
        exact i.
        
        assert (Haux : forall a b, a + Datatypes.S b = Datatypes.S a + b).
          intros a b; induction a; simpl; trivial.
          simpl; now rewrite IHa.
        rewrite Haux.
        refine (nth _ _ _ _ p _ _).
        now apply lt_S_n.
  Defined.
  
  Definition eval (S : Set) (L : nat -> S -> Type) (lt : Instr.lt_type L) (Hwf : well_founded lt)
    (p : t lt 0) (ip : nat) (s : S) (l : L ip s)
    : {ip' : nat & {s' : S & ((length p <= ip') * L ip' s') % type}}.
    refine (let aux : {ip' : nat & {s' : S & L ip' s'}} -> _ := _ in
      aux (existT _ _ (existT _ _ l))).
    clear ip s l.
    refine (well_founded_induction_type Hwf _ _).
    intros input eval.
    destruct input as (ip, (s, l)).
    destruct (le_lt_dec (length p) ip) as [Hle | Hlt].
    - (* ip >= length p, the program is terminated. *)
      exact (existT _ _ (existT _ _ (Hle, l))).
    
    - (* ip < length p, one instruction is executed. *)
      refine (let i := nth p Hlt in _).
      destruct (i s) as (ip', (s', fl)).
      destruct (fl l) as (l', Hl'_lt_l).
      exact (eval (existT _ _ (existT _ _ l')) Hl'_lt_l).
  Defined.
  
  Module Test.
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
    
    Check eq_refl : 13 = projT1 (projT2 (eval lt_wf progr 1 23 (leb_complete 3 23 eq_refl))).
  End Test.
End Program.