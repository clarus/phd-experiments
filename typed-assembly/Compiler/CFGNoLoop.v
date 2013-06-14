(** Control flow graphs without loops. *)
Require Import List.
Require Import Compiler.Linear.

Set Implicit Arguments.
Import ListNotations.

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
  
  Fixpoint eval (S : Set) Lin Lout (g : t Lin Lout)
    (s : S) (l : Lin s) {struct g} : {s' : S & Lout s'}.
    destruct g as
      [ L
      | Lin L Lout f g
      | Lin Lin_true Lin_false Lmerge Lout f g_true g_false g].
    - exact (existT _ _ l).
    
    - exact (
        let (_, fl) := f s in
        eval _ _ _ g _ (fl l)).
    
    - exact (
        match f s with
        | inl fl_true =>
          let (s, l) := eval _ _ _ g_true _ (fl_true l) in
          eval _ _ _ g _ l
        | inr fl_false =>
          let (s, l) := eval _ _ _ g_false _ (fl_false l) in
          eval _ _ _ g _ l
        end).
  Defined.
  
  Fixpoint length (S : Set) (Lin Lout : S -> Type) (g : t Lin Lout) : nat :=
    match g with
    | nop _ => 0
    | op _ _ g => 1 + (length g)
    | jcc _ _ g_true g_false g => 1 + length g_true + length g_false + length g
    end.
  
  Module Test.
    Require Import Arith.Plus.
    Require Import Arith.Compare_dec.
    Local Open Scope nat_scope.
    
    Definition L1 (n : nat) := 3 <= n.
    Definition L2 (n : nat) := 5 <= n.
    
    Definition g1 : CFG.t L1 L2.
      refine (
        op _ (fun s => existT _ (s + 2) (fun l => _))
        (@nop _ _)).
      unfold L1, L2 in *.
      replace 5 with (3 + 2); trivial.
      now apply plus_le_compat_r.
    Defined.
    
    Check eq_refl : 6 = projT1 (eval g1 4 (leb_complete 3 4 eq_refl)).
  End Test.
End CFG.

(*Module Compile.
  Require Import Arith.
  Import CFG.
  
  (*Module AnnotedProgram.
    Inductive t (S : Set) (Lin Lout : S -> Type) : Type :=
    | new (L : nat -> S -> Type).
    
    Fixpoint concat (S : Set) (L1 L2 L3 : S -> Type) (p1 : t L1 L2) (p2 : t L2 L3)
  End AnnotedProgram.*)
  
  Definition f_lt T size (x : {ip : nat & T ip}) : nat :=
      if leb size (projT1 x) then
        0
      else
        size - projT1 x.
  
  Definition lt (S : Set) (L : nat -> S -> Type) (size : nat) : Instr.lt_type L :=
    fun x y =>
      f_lt _ size x < f_lt _ size y.
  
  Lemma lt_wf (S : Set) (L : nat -> S -> Type) size : well_founded (lt L size).
    apply well_founded_ltof.
  Defined.
  
  (*Definition lift_L (S : Set) (Lpre Lpost L : nat -> S -> Type) (ip0 length : nat)
    (ip : nat) : S -> Type :=
    match nat_compare ip ip0 with
    | Lt => Lpre ip
    | _ =>
      match nat_compare ip (ip0 + length) with
      | Lt => L ip
      | _ => Lpost ip
      end
    end.*)
  
  Definition lift_L (S : Set) (Lin Lout : S -> Type) (L : nat -> S -> Type) (ip0 length : nat)
    (ip : nat) : S -> Type :=
    if beq_nat ip ip0 then
      Lin
    else if beq_nat ip (ip0 + length) then
      Lout
    else
      L ip.
  
  Fixpoint compile_aux (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout) (ip0 : nat)
    : { L : nat -> S -> Type & Program.t (lt (lift_L Lin Lout L ip0 (length g)) (length g)) ip0 }.
    destruct g as
      [ L
      | Lin L Lout f g
      | Lin Lin_true Lin_false Lmerge Lout f g_true g_false g].
    - exists (fun _ => L).
      exact (Program.nil _ _).
    
    - destruct (compile_aux _ _ _ g (1 + ip0)) as (Lg, p).
      exists (fun ip =>
        if beq_nat ip (1 + ip0) then
          L
        else
          Lg ip).
      refine (Program.cons _ _).
      + intro s.
        exists (1 + ip0).
        destruct (f s) as (s', fl).
        exists s'.
        unfold lt, f_lt; simpl.
        intro l.
        unfold lift_L in l.
        rewrite (proj2 (beq_nat_true_iff ip0 ip0) eq_refl) in l.
        constructor.
        * unfold lift_L.
          assert (H1 : (Datatypes.S ip0) <> ip0); [auto |].
          rewrite (proj2 (beq_nat_false_iff _ _) H1).
          rewrite (proj2 (beq_nat_true_iff _ _) eq_refl).
          destruct g; rewrite plus_comm; simpl.
            rewrite (proj2 (beq_nat_true_iff _ _) eq_refl).
            exact (fl l).
            
            assert (H2 : ip0 <> (Datatypes.S (length g + ip0)));
              [apply succ_plus_discr |].
            rewrite (proj2 (beq_nat_false_iff _ _) H2).
            exact (fl l).
            
            assert (H2 : ip0 <> (Datatypes.S (length g1 + length g2 + length g3 + ip0)));
              [apply succ_plus_discr |].
            rewrite (proj2 (beq_nat_false_iff _ _) H2).
            exact (fl l).
        
        * destruct (le_lt_dec (length g) ip0) as [Hle | Hlt].
            rewrite (leb_correct _ _ Hle).
            destruct ip0.
intuition. destruct ip0; simpl; auto.
          destruct ip0.
intuition.
            rewrite <- minus_n_O; auto.
            
            
            
intuition.
            
intuition. 
            rewrite plus_comm.
          refine (let size := length g in _).
          inversion size.
        
        
        assert (l' := fl l).
        
        unfold lift_L at 1.
        assert (H : (Datatypes.S ip0) <> ip0); [auto |].
        rewrite (proj2 (beq_nat_false_iff _ _) H).
        
        unfold lift_L.
        induction ip0.
        * simpl.
          intro l.
          unfold 
        
        induction ip0; intro l; simpl.
        
        unfold lift_L at 1.
        rewrite (proj2 (beq_nat_true_iff ip0 ip0) eq_refl).
        intro l.
        unfold lift_L at 1.
        assert (H : (1 + ip0) <> ip0); [auto |].
        simpl in l.
        assert (l' := fl l).
        rewrite (proj2 (beq_nat_false_iff (1 + ip0) ip0) H).
        
        exists (fl l).
      simpl.
        if beq_nat ip ip0 then
          Lin
        else
          Lg ip).
  
  Fixpoint compile_aux (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout) (ip0 : nat)
    (Lpre Lpost : nat -> S -> Type) {struct g}
    : { L : nat -> S -> Type & { length : nat & { p : Program.t (lt (lift_L Lpre Lpost L ip0 length)) ip0 |
      length = Program.length p /\ L ip0 = Lin /\ L (ip0 + length) = Lout }}}.
    destruct g as
      [ L
      | Lin L Lout f g
      | Lin Lin_true Lin_false Lmerge Lout f g_true g_false g].
    - exists (fun _ => L).
      exists 0.
      exists (Program.nil _ _).
      tauto.
    
    - refine (let Lpre' := fun ip => if beq_nat ip ip0 then Lin else Lpre ip in _).
      destruct (compile_aux _ _ _ g (1 + ip0) Lpre' Lpost) as (Lg, (length, (p, (Hlength, (HLout, HLpost))))).
      exists (fun ip => if leb ip ip0 then Lin else Lg ip).
      exists (1 + length).
      refine (let i : Instr.t (lt ) ip0 := _ in _).
    
    
    
    
    
    - exists (fun ip =>
        match nat_compare ip ip0 with
        | Lt => Lpre ip
        | Eq => L
        | Gt => Lpost ip
        end).
      exists (Program.nil _ _).
      repeat split; simpl; try rewrite <- plus_n_O.
      + intros ip H.
        now rewrite (proj1 (nat_compare_lt _ _) H).
      
      + now rewrite (proj2 (nat_compare_eq_iff _ _) eq_refl).
      
      + now rewrite (proj2 (nat_compare_eq_iff _ _) eq_refl).
      
      + intros ip H.
        now rewrite (proj1 (nat_compare_gt _ _) H).
    
    - refine (let Lpre' := fun ip => if beq_nat ip ip0 then Lin else Lpre ip in _).
      destruct (compile_aux _ _ _ g (1 + ip0) Lpre' Lpost) as (Lg, (p, (HLpre, (HL, (HLout, HLpost))))).
      exists Lg.
      refine (let i : Instr.t (lt Lg) ip0 := _ in _).
        intro s.
        exists (1 + ip0).
        destruct (f s) as (s', fl).
        exists s'.
        intro l.
        assert (Lg ip0 = Lin).
          assert (H := HLpre ip0 (lt_n_Sn _)).
          unfold Lpre' in H.
          now rewrite <- beq_nat_refl in H.
        rewrite H in l.
        refine (let l' := fl l in _).
        rewrite HL.
      exists (Program.cons () p).
      exists (fun ip => if leb ip ip0 then Lin else Lg ip).
      exists (Program.cons () p).
  
  Fixpoint Laux (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout)
    (ip : nat) : (S -> Type) + nat :=
    match g with
    | nop _ => inr ip
    | op _ _ g =>
      match ip with
      | O => inl Lin
      | Datatypes.S ip => Laux g ip
      end
    | jcc _ _ g_true g_false  g =>
      match ip with
      | O => inl Lin
      | Datatypes.S ip =>
        match Laux g_true ip with
        | inl L => inl L
        | inr ip =>
          match Laux g_false ip with
          | inl L => inl L
          | inr ip => Laux g ip
          end
        end
      end
    end.
  
  Definition L (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout)
    (ip : nat) : S -> Type :=
    match Laux g ip with
    | inl L => L
    | inr _ => Lout
    end.
  
  (*Fixpoint compile (S : Set) (Lin Lout : S -> Type) (g : CFG.t Lin Lout)
    : Program.t (lt (L g)) 0.*)
End Compile.*)