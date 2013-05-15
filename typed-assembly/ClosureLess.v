Require Import List.

Import ListNotations.

Set Implicit Arguments.

Module Asm.
  Inductive t (S : Set) (L : S -> Type) : Type :=
  | op :
    forall (f : S -> S), (forall s, L s -> L (f s)) ->
    t L -> t L
  | jcc :
    (S -> bool) -> (forall s, L s -> L s) ->
    t L -> t L -> t L
  | call :
    forall (fx : S -> S), (forall s, L s -> L (fx s)) ->
    forall (fy : S -> S), (forall s, L s -> L (fy s)) ->
    t L -> t L -> t L
  | ret :
    t L.
  
  Fixpoint eval (S : Set) (L : S -> Type) (a : t L) (s : S) (l : L s) {struct a} : {s : S & L s}.
    destruct a as [fs fl n | c fl nnc n | xs xl ys yl f n | ].
      exact (
        let l := fl s l in
        let s := fs s in
        eval _ _ n s l).
      
      exact (
        let l := fl s l in
        if c s then
          eval _ _ n s l
        else
          let (s, l) := eval _ _ nnc s l in
          eval _ _ n s l).
      
      exact (
        let l := xl s l in
        let s := xs s in
        let (s, l) := eval _ _ f s l in
        let l := yl s l in
        let s := ys s in
        eval _ _ n s l).
      
      exact (existT _ s l).
  Defined.
End Asm.

Import Asm.
Require Import Arith.Compare_dec.

Definition test1 : t (fun n => 3 <= n).
  refine (
    op (fun _ => 12) (fun n _ => _) (
    op (fun n => n + 1) (fun n h => _) (
    ret _)));
  auto with *.
Defined.

Compute eval test1 3 (leb_complete 3 3 eq_refl).