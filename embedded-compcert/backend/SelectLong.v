(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Instruction selection for 64-bit integer operations *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.

Open Local Scope cminorsel_scope.

(** Some operations on 64-bit integers are transformed into calls to
  runtime library functions.  The following record type collects
  the names of these functions. *)

Record helper_functions : Type := mk_helper_functions {
  i64_dtos: ident;                      (**r float -> signed long *)
  i64_dtou: ident;                      (**r float -> unsigned long *)
  i64_stod: ident;                      (**r signed long -> float *)
  i64_utod: ident;                      (**r unsigned long -> float *)
  i64_neg: ident;                       (**r opposite *)
  i64_add: ident;                       (**r addition *)
  i64_sub: ident;                       (**r subtraction *)
  i64_mul: ident;                       (**r multiplication 32x32->64 *)
  i64_sdiv: ident;                      (**r signed division *)
  i64_udiv: ident;                      (**r unsigned division *)
  i64_smod: ident;                      (**r signed remainder *)
  i64_umod: ident;                      (**r unsigned remainder *)
  i64_shl: ident;                       (**r shift left *)
  i64_shr: ident;                       (**r shift right unsigned *)
  i64_sar: ident                        (**r shift right signed *)
}.

Definition sig_l_l := mksignature (Tlong :: nil) (Some Tlong).
Definition sig_l_f := mksignature (Tlong :: nil) (Some Tfloat).
Definition sig_f_l := mksignature (Tfloat :: nil) (Some Tlong).
Definition sig_ll_l := mksignature (Tlong :: Tlong :: nil) (Some Tlong).
Definition sig_li_l := mksignature (Tlong :: Tint :: nil) (Some Tlong).
Definition sig_ii_l := mksignature (Tint :: Tint :: nil) (Some Tlong).

Section SELECT.

Variable hf: helper_functions.

Definition makelong (h l: expr): expr :=
  Eop Omakelong (h ::: l ::: Enil).

(** Original definition:
<<
Nondetfunction splitlong (e: expr) (f: expr -> expr -> expr) :=
  match e with
  | Eop Omakelong (h ::: l ::: Enil) => f h l
  | _ => Elet e (f (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil)))
  end.
>>
*)

Inductive splitlong_cases: forall (e: expr) , Type :=
  | splitlong_case1: forall h l, splitlong_cases (Eop Omakelong (h ::: l ::: Enil))
  | splitlong_default: forall (e: expr) , splitlong_cases e.

Definition splitlong_match (e: expr)  :=
  match e as zz1 return splitlong_cases zz1 with
  | Eop Omakelong (h ::: l ::: Enil) => splitlong_case1 h l
  | e => splitlong_default e
  end.

Definition splitlong (e: expr) (f: expr -> expr -> expr) :=
  match splitlong_match e with
  | splitlong_case1 h l => (* Eop Omakelong (h ::: l ::: Enil) *) 
      f h l
  | splitlong_default e =>
      Elet e (f (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil)))
  end.


(** Original definition:
<<
Nondetfunction splitlong2 (e1 e2: expr) (f: expr -> expr -> expr -> expr -> expr) :=
  match e1, e2 with
  | Eop Omakelong (h1 ::: l1 ::: Enil), Eop Omakelong (h2 ::: l2 ::: Enil) =>
      f h1 l1 h2 l2
  | Eop Omakelong (h1 ::: l1 ::: Enil), t2 =>
      Elet t2 (f (lift h1) (lift l1)
                 (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil)))
  | t1, Eop Omakelong (h2 ::: l2 ::: Enil) =>
      Elet t1 (f (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil))
                 (lift h2) (lift l2))
  | _, _ =>
      Elet e1 (Elet (lift e2)
        (f (Eop Ohighlong (Eletvar 1 ::: Enil)) (Eop Olowlong (Eletvar 1 ::: Enil))
           (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil))))
  end.
>>
*)

Inductive splitlong2_cases: forall (e1 e2: expr) , Type :=
  | splitlong2_case1: forall h1 l1 h2 l2, splitlong2_cases (Eop Omakelong (h1 ::: l1 ::: Enil)) (Eop Omakelong (h2 ::: l2 ::: Enil))
  | splitlong2_case2: forall h1 l1 t2, splitlong2_cases (Eop Omakelong (h1 ::: l1 ::: Enil)) (t2)
  | splitlong2_case3: forall t1 h2 l2, splitlong2_cases (t1) (Eop Omakelong (h2 ::: l2 ::: Enil))
  | splitlong2_default: forall (e1 e2: expr) , splitlong2_cases e1 e2.

Definition splitlong2_match (e1 e2: expr)  :=
  match e1 as zz1, e2 as zz2 return splitlong2_cases zz1 zz2 with
  | Eop Omakelong (h1 ::: l1 ::: Enil), Eop Omakelong (h2 ::: l2 ::: Enil) => splitlong2_case1 h1 l1 h2 l2
  | Eop Omakelong (h1 ::: l1 ::: Enil), t2 => splitlong2_case2 h1 l1 t2
  | t1, Eop Omakelong (h2 ::: l2 ::: Enil) => splitlong2_case3 t1 h2 l2
  | e1, e2 => splitlong2_default e1 e2
  end.

Definition splitlong2 (e1 e2: expr) (f: expr -> expr -> expr -> expr -> expr) :=
  match splitlong2_match e1 e2 with
  | splitlong2_case1 h1 l1 h2 l2 => (* Eop Omakelong (h1 ::: l1 ::: Enil), Eop Omakelong (h2 ::: l2 ::: Enil) *) 
      f h1 l1 h2 l2
  | splitlong2_case2 h1 l1 t2 => (* Eop Omakelong (h1 ::: l1 ::: Enil), t2 *) 
      Elet t2 (f (lift h1) (lift l1) (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil)))
  | splitlong2_case3 t1 h2 l2 => (* t1, Eop Omakelong (h2 ::: l2 ::: Enil) *) 
      Elet t1 (f (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil)) (lift h2) (lift l2))
  | splitlong2_default e1 e2 =>
      Elet e1 (Elet (lift e2) (f (Eop Ohighlong (Eletvar 1 ::: Enil)) (Eop Olowlong (Eletvar 1 ::: Enil)) (Eop Ohighlong (Eletvar O ::: Enil)) (Eop Olowlong (Eletvar O ::: Enil))))
  end.


(** Original definition:
<<
Nondetfunction lowlong (e: expr) :=
  match e with
  | Eop Omakelong (e1 ::: e2 ::: Enil) => e2
  | _ => Eop Olowlong (e ::: Enil)
  end.
>>
*)

Inductive lowlong_cases: forall (e: expr), Type :=
  | lowlong_case1: forall e1 e2, lowlong_cases (Eop Omakelong (e1 ::: e2 ::: Enil))
  | lowlong_default: forall (e: expr), lowlong_cases e.

Definition lowlong_match (e: expr) :=
  match e as zz1 return lowlong_cases zz1 with
  | Eop Omakelong (e1 ::: e2 ::: Enil) => lowlong_case1 e1 e2
  | e => lowlong_default e
  end.

Definition lowlong (e: expr) :=
  match lowlong_match e with
  | lowlong_case1 e1 e2 => (* Eop Omakelong (e1 ::: e2 ::: Enil) *) 
      e2
  | lowlong_default e =>
      Eop Olowlong (e ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction highlong (e: expr) :=
  match e with
  | Eop Omakelong (e1 ::: e2 ::: Enil) => e1
  | _ => Eop Ohighlong (e ::: Enil)
  end.
>>
*)

Inductive highlong_cases: forall (e: expr), Type :=
  | highlong_case1: forall e1 e2, highlong_cases (Eop Omakelong (e1 ::: e2 ::: Enil))
  | highlong_default: forall (e: expr), highlong_cases e.

Definition highlong_match (e: expr) :=
  match e as zz1 return highlong_cases zz1 with
  | Eop Omakelong (e1 ::: e2 ::: Enil) => highlong_case1 e1 e2
  | e => highlong_default e
  end.

Definition highlong (e: expr) :=
  match highlong_match e with
  | highlong_case1 e1 e2 => (* Eop Omakelong (e1 ::: e2 ::: Enil) *) 
      e1
  | highlong_default e =>
      Eop Ohighlong (e ::: Enil)
  end.


Definition longconst (n: int64) : expr :=
  makelong (Eop (Ointconst (Int64.hiword n)) Enil)
           (Eop (Ointconst (Int64.loword n)) Enil).

(** Original definition:
<<
Nondetfunction is_longconst (e: expr) :=
  match e with
  | Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) =>
      Some(Int64.ofwords h l)
  | _ =>
      None
  end.
>>
*)

Inductive is_longconst_cases: forall (e: expr), Type :=
  | is_longconst_case1: forall h l, is_longconst_cases (Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil))
  | is_longconst_default: forall (e: expr), is_longconst_cases e.

Definition is_longconst_match (e: expr) :=
  match e as zz1 return is_longconst_cases zz1 with
  | Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) => is_longconst_case1 h l
  | e => is_longconst_default e
  end.

Definition is_longconst (e: expr) :=
  match is_longconst_match e with
  | is_longconst_case1 h l => (* Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) *) 
      Some(Int64.ofwords h l)
  | is_longconst_default e =>
      None
  end.


Definition is_longconst_zero (e: expr) :=
  match is_longconst e with
  | Some n => Int64.eq n Int64.zero
  | None => false
  end.

Definition intoflong (e: expr) := lowlong e.

Definition longofint (e: expr) :=
  Elet e (makelong (shrimm (Eletvar O) (Int.repr 31)) (Eletvar O)).

Definition longofintu (e: expr) :=
  makelong (Eop (Ointconst Int.zero) Enil) e.

Definition negl (e: expr) :=
  match is_longconst e with
  | Some n => longconst (Int64.neg n)
  | None => Ebuiltin (EF_builtin hf.(i64_neg) sig_l_l) (e ::: Enil)
  end.

Definition notl (e: expr) :=
  splitlong e (fun h l => makelong (notint h) (notint l)).

Definition longoffloat (arg: expr) := 
  Eexternal hf.(i64_dtos) sig_f_l (arg ::: Enil).
Definition longuoffloat (arg: expr) :=
  Eexternal hf.(i64_dtou) sig_f_l (arg ::: Enil).
Definition floatoflong (arg: expr) :=
  Eexternal hf.(i64_stod) sig_l_f (arg ::: Enil).
Definition floatoflongu (arg: expr) :=
  Eexternal hf.(i64_utod) sig_l_f (arg ::: Enil).

Definition andl (e1 e2: expr) :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 => makelong (and h1 h2) (and l1 l2)).

Definition orl (e1 e2: expr) :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 => makelong (or h1 h2) (or l1 l2)).

Definition xorl (e1 e2: expr) :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 => makelong (xor h1 h2) (xor l1 l2)).

Definition shllimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  if Int.ltu n Int.iwordsize then
   splitlong e1 (fun h l =>
     makelong (or (shlimm h n) (shruimm l (Int.sub Int.iwordsize n)))
              (shlimm l n))
  else if Int.ltu n Int64.iwordsize' then
    makelong (shlimm (lowlong e1) (Int.sub n Int.iwordsize))
             (Eop (Ointconst Int.zero) Enil)
  else
    Eexternal hf.(i64_shl) sig_li_l (e1 ::: Eop (Ointconst n) Enil ::: Enil).

Definition shrluimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  if Int.ltu n Int.iwordsize then
    splitlong e1 (fun h l =>
      makelong (shruimm h n)
               (or (shruimm l n) (shlimm h (Int.sub Int.iwordsize n))))
  else if Int.ltu n Int64.iwordsize' then
    makelong (Eop (Ointconst Int.zero) Enil)
             (shruimm (highlong e1) (Int.sub n Int.iwordsize))
  else
    Eexternal hf.(i64_shr) sig_li_l (e1 ::: Eop (Ointconst n) Enil ::: Enil).

Definition shrlimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  if Int.ltu n Int.iwordsize then
    splitlong e1 (fun h l =>
      makelong (shrimm h n)
               (or (shruimm l n) (shlimm h (Int.sub Int.iwordsize n))))
  else if Int.ltu n Int64.iwordsize' then
    Elet (highlong e1)
      (makelong (shrimm (Eletvar 0) (Int.repr 31))
                (shrimm (Eletvar 0) (Int.sub n Int.iwordsize)))
  else
    Eexternal hf.(i64_sar) sig_li_l (e1 ::: Eop (Ointconst n) Enil ::: Enil).

Definition is_intconst (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Some n
  | _ => None
  end.

Definition shll (e1 e2: expr) :=
  match is_intconst e2 with
  | Some n => shllimm e1 n
  | None => Eexternal hf.(i64_shl) sig_li_l (e1 ::: e2 ::: Enil)
  end.

Definition shrlu (e1 e2: expr) :=
  match is_intconst e2 with
  | Some n => shrluimm e1 n
  | None => Eexternal hf.(i64_shr) sig_li_l (e1 ::: e2 ::: Enil)
  end.

Definition shrl (e1 e2: expr) :=
  match is_intconst e2 with
  | Some n => shrlimm e1 n
  | None => Eexternal hf.(i64_sar) sig_li_l (e1 ::: e2 ::: Enil)
  end.

Definition addl (e1 e2: expr) :=
  let default := Ebuiltin (EF_builtin hf.(i64_add) sig_ll_l) (e1 ::: e2 ::: Enil) in
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 => longconst (Int64.add n1 n2)
  | Some n1, _ => if Int64.eq n1 Int64.zero then e2 else default
  | _, Some n2 => if Int64.eq n2 Int64.zero then e1 else default
  | _, _ => default
  end.

Definition subl (e1 e2: expr) :=
  let default := Ebuiltin (EF_builtin hf.(i64_sub) sig_ll_l) (e1 ::: e2 ::: Enil) in
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 => longconst (Int64.sub n1 n2)
  | Some n1, _ => if Int64.eq n1 Int64.zero then negl e2 else default
  | _, Some n2 => if Int64.eq n2 Int64.zero then e1 else default
  | _, _ => default
  end.

Definition mull_base (e1 e2: expr) :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 =>
    Elet (Ebuiltin (EF_builtin hf.(i64_mul) sig_ii_l) (l1 ::: l2 ::: Enil))
      (makelong
        (add (add (Eop Ohighlong (Eletvar O ::: Enil))
                  (mul (lift l1) (lift h2)))
             (mul (lift h1) (lift l2)))
        (Eop Olowlong (Eletvar O ::: Enil)))).

Definition mullimm (e: expr) (n: int64) :=
  if Int64.eq n Int64.zero then longconst Int64.zero else
  if Int64.eq n Int64.one then e else
  match Int64.is_power2 n with
  | Some l => shllimm e (Int.repr (Int64.unsigned l))
  | None   => mull_base e (longconst n)
  end.

Definition mull (e1 e2: expr) :=
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 => longconst (Int64.mul n1 n2)
  | Some n1, _ => mullimm e2 n1
  | _, Some n2 => mullimm e1 n2
  | _, _ => mull_base e1 e2
  end.

Definition binop_long (id: ident) (sem: int64 -> int64 -> int64) (e1 e2: expr) :=
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 => longconst (sem n1 n2)
  | _, _ => Eexternal id sig_ll_l (e1 ::: e2 ::: Enil)
  end.

Definition divl := binop_long hf.(i64_sdiv) Int64.divs.
Definition modl := binop_long hf.(i64_smod) Int64.mods.

Definition divlu (e1 e2: expr) :=
  let default := Eexternal hf.(i64_udiv) sig_ll_l (e1 ::: e2 ::: Enil) in
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 => longconst (Int64.divu n1 n2)
  | _, Some n2 =>
      match Int64.is_power2 n2 with
      | Some l => shrluimm e1 (Int.repr (Int64.unsigned l))
      | None   => default
      end
  | _, _ => default
  end.

Definition modlu (e1 e2: expr) :=
  let default := Eexternal hf.(i64_umod) sig_ll_l (e1 ::: e2 ::: Enil) in
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 => longconst (Int64.modu n1 n2)
  | _, Some n2 =>
      match Int64.is_power2 n2 with
      | Some l => andl e1 (longconst (Int64.sub n2 Int64.one))
      | None   => default
      end
  | _, _ => default
  end.

Definition cmpl_eq_zero (e: expr) :=
  splitlong e (fun h l => comp Ceq (or h l) (Eop (Ointconst Int.zero) Enil)).

Definition cmpl_ne_zero (e: expr) :=
  splitlong e (fun h l => comp Cne (or h l) (Eop (Ointconst Int.zero) Enil)).

Definition cmplu_gen (ch cl: comparison) (e1 e2: expr) :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 =>
    Econdition (CEcond (Ccomp Ceq) (h1:::h2:::Enil))
               (Eop (Ocmp (Ccompu cl)) (l1:::l2:::Enil))
               (Eop (Ocmp (Ccompu ch)) (h1:::h2:::Enil))).

Definition cmplu (c: comparison) (e1 e2: expr) :=
  match c with
  | Ceq =>
      if is_longconst_zero e2
      then cmpl_eq_zero e1
      else cmpl_eq_zero (xorl e1 e2)
  | Cne =>
      if is_longconst_zero e2
      then cmpl_ne_zero e1
      else cmpl_ne_zero (xorl e1 e2)
  | Clt =>
      cmplu_gen Clt Clt e1 e2
  | Cle =>
      cmplu_gen Clt Cle e1 e2
  | Cgt =>
      cmplu_gen Cgt Cgt e1 e2
  | Cge =>
      cmplu_gen Cgt Cge e1 e2
  end.

Definition cmpl_gen (ch cl: comparison) (e1 e2: expr) :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 =>
    Econdition (CEcond (Ccomp Ceq) (h1:::h2:::Enil))
               (Eop (Ocmp (Ccompu cl)) (l1:::l2:::Enil))
               (Eop (Ocmp (Ccomp ch)) (h1:::h2:::Enil))).

Definition cmpl (c: comparison) (e1 e2: expr) :=
  match c with
  | Ceq =>
      if is_longconst_zero e2
      then cmpl_eq_zero e1
      else cmpl_eq_zero (xorl e1 e2)
  | Cne =>
      if is_longconst_zero e2
      then cmpl_ne_zero e1
      else cmpl_ne_zero (xorl e1 e2)
  | Clt =>
      if is_longconst_zero e2
      then comp Clt (highlong e1) (Eop (Ointconst Int.zero) Enil)
      else cmpl_gen Clt Clt e1 e2
  | Cle =>
      cmpl_gen Clt Cle e1 e2
  | Cgt =>
      cmpl_gen Cgt Cgt e1 e2
  | Cge =>
      if is_longconst_zero e2
      then comp Cge (highlong e1) (Eop (Ointconst Int.zero) Enil)
      else cmpl_gen Cgt Cge e1 e2
  end.

End SELECT.

(** Setting up the helper functions *)

Require Import Errors.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Parameter get_helper: Cminor.genv -> String.string -> signature -> res ident.
Parameter get_builtin: String.string -> signature -> res ident.

Definition get_helpers (ge: Cminor.genv): res helper_functions :=
  do i64_dtos <- get_helper ge "__i64_dtos" sig_f_l ;
  do i64_dtou <- get_helper ge "__i64_dtou" sig_f_l ;
  do i64_stod <- get_helper ge "__i64_stod" sig_l_f ;
  do i64_utod <- get_helper ge "__i64_utod" sig_l_f ;
  do i64_neg <- get_builtin "__builtin_negl" sig_l_l ;
  do i64_add <- get_builtin "__builtin_addl" sig_ll_l ;
  do i64_sub <- get_builtin "__builtin_subl" sig_ll_l ;
  do i64_mul <- get_builtin "__builtin_mull" sig_ll_l ;
  do i64_sdiv <- get_helper ge "__i64_sdiv" sig_ll_l ;
  do i64_udiv <- get_helper ge "__i64_udiv" sig_ll_l ;
  do i64_smod <- get_helper ge "__i64_smod" sig_ll_l ;
  do i64_umod <- get_helper ge "__i64_umod" sig_ll_l ;
  do i64_shl <- get_helper ge "__i64_shl" sig_li_l ;
  do i64_shr <- get_helper ge "__i64_shr" sig_li_l ;
  do i64_sar <- get_helper ge "__i64_sar" sig_li_l ;
  OK (mk_helper_functions
     i64_dtos i64_dtou i64_stod i64_utod
     i64_neg i64_add i64_sub i64_mul i64_sdiv i64_udiv i64_smod i64_umod
     i64_shl i64_shr i64_sar).
