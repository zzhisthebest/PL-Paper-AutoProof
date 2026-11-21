From Coq Require Import Lia List MSets PeanoNat String FunInd.

From Mctt.Core Require Import Base.

From Mctt.Core.Syntactic Require Import Syntax.

Open Scope string_scope.

Module StrSet := Make String_as_OT.

Module StrSProp := MSetProperties.Properties StrSet.

Notation "s [<=] t" := (StrSet.Subset s t) (at level 70, no associativity).

Fixpoint lookup (s : string) (ctx : list string) : option nat :=
  match ctx with
  | nil => None
  | c::cs =>
      if string_dec c s
      then Some 0
      else
        match lookup s cs with
        | Some n => Some (n + 1)%nat
        | None => None
        end
  end
.

Fixpoint elaborate (cst : Cst.obj) (ctx : list string) : option exp :=
  match cst with
  | Cst.var s =>
      match lookup s ctx with
      | Some n => Some (a_var n)
      | None => None
      end
  | Cst.typ n => Some (a_typ n)
  | Cst.nat => Some a_nat
  | Cst.zero => Some a_zero
  | Cst.succ c =>
      match elaborate c ctx with
      | Some a => Some (a_succ a)
      | None => None
      end
  | Cst.natrec n mx m z sx sr s =>
      match elaborate m (mx :: ctx), elaborate z ctx, elaborate s (sr :: sx :: ctx), elaborate n ctx with
      | Some m, Some z, Some s, Some n => Some (a_natrec m z s n)
      | _, _, _, _ => None
      end
  | Cst.pi s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_pi t a)
      | _, _ => None
      end
  | Cst.fn s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_fn t a)
      | _, _ => None
      end
  | Cst.app c1 c2 =>
      match elaborate c1 ctx, elaborate c2 ctx with
      | None, _ => None
      | _, None => None
      | Some a1, Some a2 => Some (a_app a1 a2)
      end
  | Cst.sigma s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_sigma t a)
      | _, _ => None
      end
  | Cst.pair c1 t1 c2 s t2 =>
      match elaborate c1 ctx,  elaborate t1 ctx, elaborate c2 ctx, elaborate t2 (s::ctx) with
      | Some a1, Some b1, Some a2, Some b2 => Some (a_pair a1 b1 a2 b2)
      | _, _, _, _ => None
      end
  | Cst.fst c =>
      match elaborate c ctx with
      | Some a => Some (a_fst a)
      | None => None
      end
  | Cst.snd c =>
      match elaborate c ctx with
      | Some a => Some (a_snd a)
      | None => None
      end
  | Cst.prop_eq c1 t c2 =>
      match elaborate c1 ctx, elaborate t ctx, elaborate c2 ctx with
      | Some a1, Some t, Some a2 => Some (a_eq t a1 a2)
      | _, _, _ => None
      end
  | Cst.refl t c =>
      match elaborate t ctx, elaborate c ctx with
      | Some t, Some a => Some (a_refl t a)
      | _, _ => None
      end
  | Cst.eqrec n mx my mz m rx r c1 t c2 =>
      match elaborate n ctx, elaborate m (mz :: my :: mx :: ctx), elaborate r (rx :: ctx), elaborate c1 ctx, elaborate t ctx, elaborate c2 ctx with
      | Some n, Some m, Some r, Some a1, Some t, Some a2 => Some (a_eqrec t m r a1 a2 n)
      | _, _, _, _, _, _ => None
      end
  end
.

Generalizable All Variables.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp (a_typ i) )
| user_exp_nat :
  `( user_exp a_nat )
| user_exp_zero :
  `( user_exp a_zero )
| user_exp_succ :
  `( user_exp M ->
     user_exp (a_succ M) )
| user_exp_natrec :
  `( user_exp A ->
     user_exp MZ ->
     user_exp MS ->
     user_exp M ->
     user_exp (a_natrec A MZ MS M) )
| user_exp_pi :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_pi A B) )
| user_exp_fn :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_fn A M) )
| user_exp_app :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_app M N) )
| user_exp_sigma :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_sigma A B) )
| user_exp_pair :
  `( user_exp M ->
     user_exp A ->
     user_exp N ->
     user_exp B ->
     user_exp (a_pair M A N B) )
| user_exp_fst :
  `( user_exp M ->
     user_exp (a_fst M) )
| user_exp_snd :
  `( user_exp M ->
     user_exp (a_snd M) )
| user_exp_eq :
  `( user_exp A ->
     user_exp M1 ->
     user_exp M2 ->
     user_exp (a_eq A M1 M2) )
| user_exp_refl :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_refl A M) )
| user_exp_eqrec :
  `( user_exp A ->
     user_exp B ->
     user_exp BR ->
     user_exp M1 ->
     user_exp M2 ->
     user_exp N ->
     user_exp (a_eqrec A B BR M1 M2 N) )
| user_exp_vlookup :
  `( user_exp (a_var x) ).

Fixpoint cst_variables (cst : Cst.obj) : StrSet.t :=
 match cst with
  | Cst.var s => StrSet.singleton s
  | Cst.typ n => StrSet.empty
  | Cst.nat => StrSet.empty
  | Cst.zero => StrSet.empty
  | Cst.succ c => cst_variables c
  | Cst.natrec n mx m z sx sy s => StrSet.union (StrSet.union (cst_variables n) (StrSet.remove mx (cst_variables m))) (StrSet.union (cst_variables z) (StrSet.remove sx (StrSet.remove sy (cst_variables s))))
  | Cst.pi s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.fn s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.app c1 c2 => StrSet.union (cst_variables c1) (cst_variables c2)
  | Cst.sigma s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.pair c1 t1 c2 s t2 => StrSet.union (StrSet.union (cst_variables c1) (cst_variables t1)) (StrSet.union (cst_variables c2) (StrSet.remove s (cst_variables t2)))
  | Cst.fst c => cst_variables c
  | Cst.snd c => cst_variables c
  | Cst.prop_eq c1 t c2 => StrSet.union (cst_variables c1) (StrSet.union (cst_variables t) (cst_variables c2))
  | Cst.refl t c => StrSet.union (cst_variables t) (cst_variables c)
  | Cst.eqrec n mx my mz m rx r c1 t c2 => StrSet.union (cst_variables n) (StrSet.union (StrSet.remove mx (StrSet.remove my (StrSet.remove mz (cst_variables m)))) (StrSet.union (StrSet.remove rx (cst_variables r)) (StrSet.union (cst_variables c1) (StrSet.union (cst_variables t) (cst_variables c2)))))
 end
.

Inductive closed_at : exp -> nat -> Prop :=
 | ca_var : `( x < n -> closed_at (a_var x) n )
 | ca_type : `( closed_at (a_typ m) n )
 | ca_nat : `( closed_at (a_nat) n )
 | ca_zero : `( closed_at (a_zero) n )
 | ca_succ : `( closed_at a n -> closed_at (a_succ a) n )
 | ca_natrec : `( closed_at n l -> closed_at m (1+l) -> closed_at z l -> closed_at s (2+l) -> closed_at (a_natrec m z s n) l )
 | ca_pi : `( closed_at t n -> closed_at b (1+n) -> closed_at (a_pi t b) n )
 | ca_lam : `( closed_at t n -> closed_at b (1+n) -> closed_at (a_fn t b) n )
 | ca_app : `( closed_at a1 n -> closed_at a2 n -> closed_at (a_app a1 a2) n )
 | ca_sigma : `( closed_at t n -> closed_at b (1+n) -> closed_at (a_sigma t b) n )
 | ca_pair : `( closed_at a1 n -> closed_at b1 n -> closed_at a2 n -> closed_at b2 (1+n) -> closed_at (a_pair a1 b1 a2 b2) n )
 | ca_fst : `( closed_at a n -> closed_at (a_fst a) n )
 | ca_snd : `( closed_at a n -> closed_at (a_snd a) n )
 | ca_eq : `( closed_at t n -> closed_at a1 n -> closed_at a2 n -> closed_at (a_eq t a1 a2) n )
 | ca_refl : `( closed_at t n -> closed_at a n -> closed_at (a_refl t a) n )
 | ca_eqrec : `( closed_at a l -> closed_at m (3+l) -> closed_at r (1+l) -> closed_at m1 l -> closed_at m2 l -> closed_at n l -> closed_at (a_eqrec a m r m1 m2 n) l )
.

Import StrSProp.Dec.
