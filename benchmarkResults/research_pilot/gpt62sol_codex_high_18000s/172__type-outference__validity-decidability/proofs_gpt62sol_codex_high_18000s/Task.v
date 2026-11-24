(* Copyright 2025 Ross Tate
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(* Benchmark adaptation: proof bodies and proof-only declarations were removed;
   the syntax needed by the supplied interfaces was updated for Rocq 9.1. *)

Set Uniform Inductive Parameters.

Set Primitive Projections.

Set Printing Projections.

Inductive Squash {P: Prop}: SProp
:= squash: P -> Squash.

Arguments Squash : clear implicits.

Inductive Box {P: SProp}: Prop
:= box: P -> Box.

Arguments Box : clear implicits.

Inductive exSP {P: SProp} {P': P -> Prop}: Prop
:= ex_introSP (p: P) (p': P' p).

Arguments exSP [_] _.

Notation "'existsSP' x .. y , p" := (exSP (fun x => .. (exSP (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsSP' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Inductive exTS {T: Type} {P: T -> SProp}: SProp
:= ex_introTS (t: T) (p: P t).

Arguments exTS [_] _.

Notation "'existsTS' x .. y , p" := (exTS (fun x => .. (exTS (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsTS' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Record exSS {P: SProp} {P': P -> SProp}: SProp := ex_introSS
{ proj1_exSS: P;
  proj2_exSS: P' proj1_exSS;
}.

Arguments exSS [_] _.

Notation "'existsSS' x .. y , p" := (exSS (fun x => .. (exSS (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsSS' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Inductive exTSS {T: Type} {P1: T -> SProp} {P2: T -> SProp}: SProp
:= ex_introSSS (t: T) (p1: P1 t) (p2: P2 t).

Arguments exTSS [_] _ _.

Notation "'existsTSS' x , p & q" := (exTSS (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.

Notation "'existsTSS' x : A , p & q" := (@exTSS A (fun x => p) (fun x => q))
  (at level 200, x name, A at level 200, p at level 200, right associativity,
    format "'[' 'existsTSS' '/ ' x : A , '/ ' '[' p & '/' q ']' ']'")
  : type_scope.

Inductive exTSP {T: Type} {P1: T -> SProp} {P2: T -> Prop}: Prop
:= ex_introTSP (t: T) (p1: P1 t) (p2: P2 t).

Arguments exTSP [_] _ _.

Notation "'existsTSP' x , p & q" := (exTSP (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.

Notation "'existsTSP' x : A , p & q" := (@exTSP A (fun x => p) (fun x => q))
  (at level 200, x name, A at level 200, p at level 200, right associativity,
    format "'[' 'existsTSP' '/ ' x : A , '/ ' '[' p & '/' q ']' ']'")
  : type_scope.

Record sigS {T: Type} {P: T -> SProp}: Type := existS
{ proj1_sigS: T;
  proj2_sigS: P proj1_sigS;
}.

Arguments sigS [_] _.

Record sigSdT {A: Type} {P: A -> SProp} {B: forall a: A, P a -> Type}: Type := existSdT
{ proj1_sigSdT: A;
  proj2_sigSdT: P proj1_sigSdT;
  proj3_sigSdT: B proj1_sigSdT proj2_sigSdT;
}.

Arguments sigSdT [_] _ _.

Arguments existSdT {_ _ _} _ _ _.

Inductive FalseS: SProp
:=.

Definition falseSe {T: Type} (f: FalseS): T
:= match f with end.

Definition false_falseS (f: False): FalseS
:= match f with end.

Definition falseS_false: FalseS -> False
:= falseSe.

Inductive TrueS: SProp
:= trueS.

Record AndS {F S: SProp}: SProp := conjS
{ proj1_AndS: F;
  proj2_AndS: S;
}.

Arguments AndS : clear implicits.

Inductive OrS {L R: SProp}: SProp
:= oleftS (l: L)
 | orightS (r: R).

Arguments OrS : clear implicits.

Inductive eqS {T: Type} (t: T): T -> SProp
:= eqS_refl: eqS t.

Arguments eqS [_] _ _.

Inductive eqSProp {P: SProp} (p: P): P -> Prop
:= eqSProp_refl: eqSProp p.

Definition eqSProp_total {P: SProp} (p p': P): eqSProp p p' := eqSProp_refl p.

Definition compose {T T' T'': Type} (f: T -> T') (f': T' -> T'') (t: T): T''
:= f' (f t).

Definition Unit: Type := unit.

Inductive empty: Prop
:=.

Definition Empty: Type
:= empty.

Definition emptye {T: Type} (empty: Empty): T
:= match empty with end.

Definition emptyde {T: Empty -> Type} (empty: Empty): T empty
:= match empty with end.

Definition emptydSe {T: Empty -> SProp} (empty: Empty): T empty
:= match empty with end.

Definition optione {A: Type} {K: Type} (kn: K) (ks: A -> K) (o: option A): K
:= match o with
   | None => kn
   | Some a => ks a
   end.

Definition OptionS {A: Type} (P: A -> SProp): option A -> SProp
:= optione TrueS P.

Definition sume {L R: Type} {K: Type} (kl: L -> K) (kr: R -> K) (s: sum L R): K
:= match s with
   | inl l => kl l
   | inr r => kr r
   end.

Definition sum_mapr {L R R': Type} (rmap: R -> R') (s: sum L R): sum L R'
:= match s with
   | inl l => inl l
   | inr r => inr (rmap r)
   end.

Require Import List.

Inductive ListContains {T: Type} {t: T}: list T -> SProp
:= lchead (tail: list T): ListContains (cons t tail)
 | lctail (head: T) (tail: list T): ListContains tail -> ListContains (cons head tail).

Arguments ListContains {_} _ _.

Definition ListForallS {T: Type} (P: T -> SProp): list T -> SProp
:= fix ListForallS (l: list T): SProp
:= match l with
   | nil => TrueS
   | cons t l => AndS (P t) (ListForallS l)
   end.

Definition PairListContains {A B: Type} (l: list (prod A B)) (a: A) (b: B): SProp
:= ListContains (pair a b) l.

Inductive SumBoolS {P P': SProp}: Type
:= sbleftS (p: P)
 | sbrightS (p': P').

Arguments SumBoolS : clear implicits.

Definition DeciderS (P: SProp): Type
:= SumBoolS P (P -> FalseS).

Inductive Sign: Type
:= negative | positive.

Definition negate (sign: Sign): Sign
:= match sign with
   | negative => positive
   | positive => negative
   end.

Definition multiply (sign: Sign): Sign -> Sign
:= match sign with
   | negative => negate
   | positive => fun sign => sign
   end.

Definition Signed {A: Type} (R: A -> A -> SProp) (sign: Sign): A -> A -> SProp
:= match sign with
   | negative => fun a a' => R a' a
   | positive => R
   end.

Inductive ISigned {A: Type} {R: A -> A -> SProp}: Sign -> A -> A -> SProp
:= isnegative (a a': A): R a' a -> ISigned negative a a'
 | ispositive (a a': A): R a a' -> ISigned positive a a'.

Arguments ISigned {_} _ _ _ _.

Class DecidableS (P: SProp): Type
:= decidableS: DeciderS P.

Arguments decidableS _ {_}.

Definition K {T: Type} (t: T): Prop
:= forall e: t = t, eq_refl = e.

Definition projT1_eq {A: Type} {T: A -> Type} {s s': sigT T} (e : s = s'): projT1 s = projT1 s'
:= match e with eq_refl => eq_refl (projT1 s) end.

Definition projT2_eq {A: Type} {T: A -> Type} {s s': sigT T} (e : s = s'): match projT1_eq e in _ = a' return T a' with eq_refl => projT2 s end = projT2 s'
:= match e as e in _ = s' return match projT1_eq e in _ = a' return T a' with eq_refl => projT2 s end = projT2 s' with eq_refl => eq_refl (projT2 s) end.

Definition k_inj_projT2 {A: Type} {T: A -> Type} {a: A} (k: K a) [t t': T a] (e : existT T a t = existT T a t'): t = t'
:= match k (projT1_eq e) in _ = e' return match e' in _ = a' return T a' with eq_refl => t end = t' -> t = t' with eq_refl => fun e => e end (projT2_eq e).

Definition proj1_sigSdT_eq {A: Type} {P: A -> SProp} {T: forall a: A, P a -> Type} {s s': sigSdT P T} (e : s = s'): proj1_sigSdT s = proj1_sigSdT s'
:= match e with eq_refl => eq_refl s.(proj1_sigSdT) end.

Definition proj3_sigSdT_eq {A: Type} {P: A -> SProp} {T: forall a: A, P a -> Type} {s s': sigSdT P T} (e : s = s'): match proj1_sigSdT_eq e as e in _ = a' return T a' (match e with eq_refl => s.(proj2_sigSdT) end) with eq_refl => s.(proj3_sigSdT) end = s'.(proj3_sigSdT)
:= match e as e in _ = s' return match proj1_sigSdT_eq e as e in _ = a' return T a' (match e with eq_refl => s.(proj2_sigSdT) end) with eq_refl => s.(proj3_sigSdT) end = s'.(proj3_sigSdT) with eq_refl => eq_refl s.(proj3_sigSdT) end.

Definition k_inj_proj3_sigSdT {A: Type} {P: A -> SProp} {T: forall a: A, P a -> Type} {a: A} {p: P a} (k: K a) [t t': T a p] (e : existSdT a p t = existSdT a p t'): t = t'
:= match k (proj1_sigSdT_eq e) in _ = e' return match e' in _ = a' return T a' (match e' with eq_refl => p end) with eq_refl => t end = t' -> t = t' with eq_refl => fun e => e end (proj3_sigSdT_eq e).

Class HSet (T: Type): Prop
:= uip (t: T): K t.

Definition hset_inj_projT2 {A: Type} `{HSet A} {T: A -> Type} {a: A}: forall [t t': T a], (existT T a t = existT T a t') -> t = t'
:= k_inj_projT2 (uip a).

Class HSetS {T: Type} (P: T -> SProp): Prop
:= uipS (t: T) (p: P t): K t.

Definition hsetS_inj_proj3_sigSdT {A: Type} {P: A -> SProp} `{HSetS A P} {T: forall a: A, P a -> Type} {a: A} {p: P a}: forall [t t': T a p], (existSdT a p t = existSdT a p t') -> t = t'
:= k_inj_proj3_sigSdT (uipS a p).

Class SSet (T: Type): Prop
:= eqS_eq [t t': T] (e: eqS t t'): eq t t'.

Definition convert {A: Type} `{SSet A} {a: A} {a': A} (e: eqS a a') (B: A -> Type) (b: B a): B a'
:= match eqS_eq e with eq_refl => b end.

Definition convertS {A: Type} `{SSet A} {a: A} {a': A} (e: eqS a a') (P: A -> SProp) (p: P a): P a'
:= match eqS_eq e with eq_refl => p end.

Class DecEq (T: Type): Type
:= dec_eq (t t': T): {t = t'} + {t = t' -> False}.

#[local] Instance DecEq_SSet (T: Type) `{DecEq T}: SSet T :=
  fun t t' e =>
    match dec_eq t t' with
    | left q => q
    | right ne => falseSe
        ((match e in eqS _ u return (t = u -> False) -> FalseS with
          | eqS_refl _ => fun k => false_falseS (k eq_refl)
          end) ne)
    end.

Definition inj_DecEq {A: Type} {B: Type} `{deB: DecEq B} (f: A -> B) (finj: forall [a a': A], f a = f a' -> a = a'): DecEq A
:= fun a a' => match dec_eq (f a) (f a') with
               | left e => left (finj e)
               | right ne => right (fun e => ne (match e in _ = a' return f a = f a' with eq_refl => eq_refl (f a) end))
               end.

Inductive BPath: Type
:= bend
 | bfirst (path: BPath)
 | bsecond (path: BPath).

Scheme Equality for BPath.

#[local] Instance BPath_DecEq: DecEq BPath := BPath_eq_dec.

Fixpoint bpath_pair (first: BPath): BPath -> BPath
:= match first with
   | bend => bfirst
   | bfirst first => fun second => bsecond (bfirst (bpath_pair first second))
   | bsecond first => fun second => bsecond (bsecond (bpath_pair first second))
   end.

Fixpoint bpath_fst (path: BPath): BPath
:= match path with
   | bfirst path => bend
   | bsecond (bfirst path) => bfirst (bpath_fst path)
   | bsecond (bsecond path) => bsecond (bpath_fst path)
   | _ => bend
   end.

Fixpoint bpath_snd (path: BPath): BPath
:= match path with
   | bfirst path => path
   | bsecond (bfirst path) => bpath_snd path
   | bsecond (bsecond path) => bpath_snd path
   | _ => bend
   end.

Class SubCountable (T: Type) :=
{ scpath: T -> BPath;
  scpath_inj: forall [t t': T], scpath t = scpath t' -> eq t t'
}.

#[local] Instance SubCountable_DecEq (T: Type) `{SubCountable T}: DecEq T
:= inj_DecEq scpath scpath_inj.

Class SubCountableS {T: Type} (P: T -> SProp) :=
{ scpathS: forall t: T, P t -> BPath;
  scpathS_inj: forall [t t': T], forall [p : P t], forall [p': P t'], scpathS t p = scpathS t' p' -> eq t t'
}.

Definition inj_SubCountable {A: Type} {B: Type} {scB: SubCountable B} (f: A -> B) (finj: forall [a a': A], f a = f a' -> a = a'): SubCountable A :=
{| scpath a := scpath (f a);
   scpath_inj a a' e := finj (scpath_inj e)
|}.

Definition inj_SubCountableS {A: Type} {P: A -> SProp} {B: Type} {P': B -> SProp} {scP': SubCountableS P'} (f: forall a: A, P a -> B) (fp: forall a: A, forall p: P a, P' (f a p)) (finj: forall [a a': A], forall p: P a, forall p': P a', f a p = f a' p' -> a = a'): SubCountableS P :=
{| scpathS a p := scpathS (f a p) (fp a p);
   scpathS_inj a a' p p' e := finj p p' (scpathS_inj e)
|}.

Class Projective (T: Type): SProp
:= projective (T': Type) (R: T -> T' -> SProp): (forall t: T, existsTS t': T', R t t') -> existsTS t': T -> T', forall t: T, R t (t' t).

Class ProjectiveS {T: Type} (P: T -> SProp): SProp
:= projectiveS (T': Type) (R: T -> T' -> SProp): (forall t: T, P t -> existsTS t': T', R t t') -> existsTS t': forall t: T, P t -> T', forall t: T, forall p: P t, R t (t' t p).

Arguments projectiveS {_} _ {_}.

Inductive Optional: Type
:= oabsent
 | opresent.

Definition PresentS (o: Optional): SProp
:= match o with oabsent => FalseS | opresent => TrueS end.

Inductive BTrunk: Type
:= bleaf
 | bbranch (head: Optional) (first second: BTrunk).

Fixpoint BTContains (trunk: BTrunk): BPath -> SProp
:= match trunk with
   | bleaf => fun _ => FalseS
   | bbranch head first second => fun path => match path with
                                              | bend => PresentS head
                                              | bfirst path => BTContains first path
                                              | bsecond path => BTContains second path
                                              end
   end.

Fixpoint btrunk_pair (first: BTrunk): (forall path: BPath, BTContains first path -> BTrunk) -> BTrunk
:= match first as first return (forall path: BPath, BTContains first path -> BTrunk) -> BTrunk with
   | bleaf => fun _ => bleaf
   | bbranch head first second => fun second' => bbranch oabsent
                                                         (match head as head return (PresentS head -> BTrunk) -> BTrunk with
                                                         | oabsent => fun _ => bleaf
                                                         | opresent => fun second => second trueS
                                                         end (second' bend))
                                                         (bbranch oabsent
                                                                  (btrunk_pair first (fun path => second' (bfirst path)))
                                                                  (btrunk_pair second (fun path => second' (bsecond path))))
   end.

Class SubFinite (T: Type): Type :=
{ SubFinite_SubCountable :: SubCountable T;
  sftrunk: BTrunk;
  sfcontains: forall t: T, BTContains sftrunk (scpath t)
}.

Arguments sftrunk _ {_}.

Class SubFiniteS {T: Type} (P: T -> SProp): Type :=
{ SubFiniteS_SubCountableS :: SubCountableS P;
  sftrunkS: BTrunk;
  sfcontainsS: forall t: T, forall p: P t, BTContains sftrunkS (scpathS t p)
}.

Arguments sftrunkS {_} _ {_}.

Definition inj_SubFinite {A: Type} {B: Type} {sfB: SubFinite B} (f: A -> B) (finj: forall [a a': A], f a = f a' -> a = a'): SubFinite A :=
{| sftrunk := sftrunk B;
   sfcontains a := (sfcontains (f a)): BTContains (sftrunk B) ((inj_SubCountable f finj).(scpath) a)
|}.

Definition inj_SubFiniteS {A: Type} {P: A -> SProp} {B: Type} {P': B -> SProp} {sfP': SubFiniteS P'} (f: forall a: A, P a -> B) {fp: forall a: A, forall p: P a, P' (f a p)} {finj: forall [a a': A], forall p: P a, forall p': P a', f a p = f a' p' -> a = a'}: SubFiniteS P :=
{| sftrunkS := sftrunkS P';
   sfcontainsS a p := (sfcontainsS (f a p) (fp a p)): BTContains (sftrunkS P') ((inj_SubCountableS f fp finj).(scpathS) a p)
|}.

Class Finite (T: Type): Type :=
{ Finite_SubFinite :: SubFinite T;
  fpath (path: BPath) (contains: BTContains (sftrunk T) path): T;
  fpath_eqS (path: BPath) (contains: BTContains (sftrunk T) path): eqS path (scpath (fpath path contains))
}.

Arguments fpath _ {_} _ _.

Class FiniteS {T: Type} (P: T -> SProp): Type :=
{ FiniteS_SubFiniteS :: SubFiniteS P;
  fpathS (path: BPath) (contains: BTContains (sftrunkS P) path): T;
  fpathSP (path: BPath) (contains: BTContains (sftrunkS P) path): P (fpathS path contains);
  fpathS_eqS (path: BPath) (contains: BTContains (sftrunkS P) path): eqS path (scpathS (fpathS path contains) (fpathSP path contains));
}.

Arguments fpathS {_} _ {_} _ _.

Arguments fpathSP {_} _ {_} _ _.

Definition btappend {T: Type}: forall trunk: BTrunk, (forall path: BPath, BTContains trunk path -> list T) -> list T
:= fix btappend (trunk: BTrunk): (forall path: BPath, BTContains trunk path -> list T) -> list T
:= match trunk with
   | bleaf => fun _ => nil
   | bbranch head first second => fun f => app (match head as head return (PresentS head -> list T) -> list T with
                                                | oabsent => fun _ => nil
                                                | opresent => fun head => head trueS
                                                end (f bend))
                                          (app (btappend first (fun path => f (bfirst path)))
                                               (btappend second (fun path => f (bsecond path))))
   end.

Definition fappend {A: Type} `{Finite A} `{B: Type} (f: A -> list B): list B
:= btappend (sftrunk A) (fun path contains => f (fpath A path contains)).

Definition flist {A: Type} `{Finite A} `{B: Type} (f: A -> B): list B
:= fappend (fun a => cons (f a) nil).

Inductive SplitS {A: Type} {P: A -> SProp} {P': SProp}: Type
:= split_exists (a: A): P a -> SplitS
 | split_forall: P' -> SplitS.

Arguments SplitS {_} _ _.

Inductive CoAcc {T: Type} {R: T -> T -> Prop} | {t: T}: Prop
:= coacc: (forall t': T, R t t' -> CoAcc (t := t')) -> CoAcc.

Arguments CoAcc {_} _ _.

Record BEntry {K: Type} {V: K -> Type} {P: K -> SProp}: Type := bentry
{ bekey: K;
  bekeyP: P bekey;
  bevalue: V bekey;
}.

Arguments BEntry : clear implicits.

Inductive BTree {K: Type} {V: K -> Type} | {P: BPath -> K -> SProp}: Type
:= bempty
 | bnode (head: option (BEntry K V (P bend))) (first: BTree (P := fun path => P (bfirst path))) (second: BTree (P := fun path => P (bsecond path))).

Arguments BTree : clear implicits.

Definition BContainsPath {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, BTree K V P -> BPath -> SProp
:= fix BContainsPath {P: BPath -> K -> SProp} (tree: BTree K V P): BPath -> SProp
:= match tree with
   | bempty => fun _ => FalseS
   | bnode head first second => fun path => match path with
                                            | bend => optione FalseS (fun _ => TrueS) head
                                            | bfirst path => BContainsPath first path
                                            | bsecond path => BContainsPath second path
                                            end
   end.

Definition btree_trunk {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, BTree K V P -> BTrunk
:= fix btree_trunk {P: BPath -> K -> SProp} (tree: BTree K V P): BTrunk
:= match tree with
   | bempty => bleaf
   | bnode entry tree1 tree2 => bbranch (match entry with None => oabsent | Some _ => opresent end) (btree_trunk tree1) (btree_trunk tree2)
   end.

Definition bget_contained {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall tree: BTree K V P, forall path: BPath, BContainsPath tree path -> BEntry K V (P path)
:= fix bget_contained {P: BPath -> K -> SProp} (tree: BTree K V P): forall path: BPath, BContainsPath tree path -> BEntry K V (P path)
:= match tree with
   | bempty => fun _ => falseSe
   | bnode head first second => fun path => match path with
                                            | bend => match head with
                                                      | Some head => fun _ => head
                                                      | None => falseSe
                                                      end
                                            | bfirst path => bget_contained first path
                                            | bsecond path => bget_contained second path
                                            end
   end.

Definition bget {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall tree: BTree K V P, forall path: BPath, option (BEntry K V (P path))
:= fix bget {P: BPath -> K -> SProp} (tree: BTree K V P): forall path: BPath, option (BEntry K V (P path))
:= match tree with
   | bempty => fun _ => None
   | bnode head first second => fun path => match path with
                                            | bend => head
                                            | bfirst path => bget first path
                                            | bsecond path => bget second path
                                            end
   end.

Definition bsingleton {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall path: BPath, BEntry K V (P path) -> BTree K V P
:= fix bsingleton {P: BPath -> K -> SProp} (path: BPath): BEntry K V (P path) -> BTree K V P
:= match path with
   | bend => fun entry => bnode (Some entry) bempty bempty
   | bfirst path => fun entry => bnode None (bsingleton path entry) bempty
   | bsecond path => fun entry => bnode None bempty (bsingleton path entry)
   end.

Inductive BExtends {K: Type} {V: K -> Type} | {P: BPath -> K -> SProp}: BTree K V P -> forall path: BPath, BEntry K V (P path) -> BTree K V P -> Prop
:= beempty (path: BPath) (entry: BEntry K V (P path)): BExtends bempty path entry (bsingleton path entry)
 | beend (entry: BEntry K V (P bend)) (head: option (BEntry K V (P bend))) (tree1: BTree K V (fun path => P (bfirst path))) (tree2: BTree K V (fun path => P (bsecond path))): BExtends (bnode head tree1 tree2) bend entry (bnode (Some entry) tree1 tree2)
 | befirst (path: BPath) (entry: BEntry K V (P (bfirst path))) (head: option (BEntry K V (P bend))) (tree1 tree1': BTree K V (fun path => P (bfirst path))) (tree2: BTree K V (fun path => P (bsecond path))): BExtends tree1 path entry tree1' -> BExtends (bnode head tree1 tree2) (bfirst path) entry (bnode head tree1' tree2)
 | besecond (path: BPath) (entry: BEntry K V (P (bsecond path))) (head: option (BEntry K V (P bend))) (tree1: BTree K V (fun path => P (bfirst path))) (tree2 tree2': BTree K V (fun path => P (bsecond path))): BExtends tree2 path entry tree2' -> BExtends (bnode head tree1 tree2) (bsecond path) entry (bnode head tree1 tree2').

Definition bupdate {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall tree: BTree K V P, forall path: BPath, (SumBoolS (BContainsPath tree path) (BContainsPath tree path -> FalseS) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P))
:= fix bupdate {P: BPath -> K -> SProp} (tree: BTree K V P): forall path: BPath, (SumBoolS (BContainsPath tree path) (BContainsPath tree path -> FalseS) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P))
:= match tree as tree return forall path: BPath, (DeciderS (BContainsPath tree path) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P)) with
   | bempty => fun path update => option_map (option_map (bsingleton path)) (update (sbrightS (fun f => f)))
   | bnode entry tree1 tree2 => fun path => match path as path return (DeciderS (BContainsPath (bnode entry tree1 tree2) path) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P)) with
                                            | bend => match entry as entry return (DeciderS (BContainsPath (bnode entry tree1 tree2) bend) -> option (option (BEntry K V (P bend)))) -> option (option (BTree K V P)) with
                                                      | None => fun update => option_map (option_map (fun entry => bnode (Some entry) tree1 tree2)) (update (sbrightS (fun f => f)))
                                                      | Some _ => fun update => option_map (option_map (fun entry => bnode (Some entry) tree1 tree2)) (update (sbleftS trueS))
                                                      end
                                            | bfirst path => fun update => option_map (option_map (fun tree1 => bnode entry tree1 tree2)) (bupdate tree1 path update)
                                            | bsecond path => fun update => option_map (option_map (fun tree2 => bnode entry tree1 tree2)) (bupdate tree2 path update)
                                            end
   end.

Definition bentries' {K: Type} {V: K -> Type} {P: BPath -> K -> SProp}: forall f: BPath -> BPath, BTree K V (compose f P) -> list (sigT (fun path => BEntry K V (P path)))
:= fix bentries' (f: BPath -> BPath) (tree: BTree K V (compose f P)): list (sigT (fun path => BEntry K V (P path)))
:= match tree with
   | bempty => nil
   | bnode head tree1 tree2 => match head with
                               | None => app (bentries' (compose bfirst f) tree1) (bentries' (compose bsecond f) tree2)
                               | Some entry => cons (existT _ (f bend) entry) (app (bentries' (compose bfirst f) tree1) (bentries' (compose bsecond f) tree2))
                               end
   end.

Definition bentries {K: Type} {V: K -> Type} {P: BPath -> K -> SProp}: BTree K V P -> list (sigT (fun path => BEntry K V (P path)))
:= bentries' (fun path => path).

Definition BTreeContains {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P) (path: BPath) (entry: BEntry K V (P path)): SProp
:= existsSS contains: BContainsPath tree path, eqS (bget_contained tree path contains) entry.

Definition BTreeForallS {K: Type} {V: K -> Type} (R: forall key: K, V key -> SProp): forall {P: BPath -> K -> SProp}, BTree K V P -> SProp
:= fix BTreeForallS {P: BPath -> K -> SProp} (tree: BTree K V P): SProp
:= match tree with
   | bempty => TrueS
   | bnode head ltree rtree => AndS (OptionS (fun entry => R entry.(bekey) entry.(bevalue)) head)
                                    (AndS (BTreeForallS ltree) (BTreeForallS rtree))
   end.

Definition SCMap (K: Type) `{SubCountable K} (V: K -> Type): Type
:= BTree K V (fun path k => eqS (scpath k) path).

Definition SCMapContains {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K): SProp
:= BContainsPath map (scpath k).

Definition scmempty {K: Type} `{SubCountable K} {V: K -> Type}: SCMap K V
:= bempty.

Definition SCMExtends {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K) (v: V k) (map': SCMap K V): Prop
:= BExtends map (scpath k) {| bekey := k; bevalue := v; bekeyP := eqS_refl _ |} map'.

Definition scmupdate {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K) (update: DeciderS (SCMapContains map k) -> option (option (V k))): option (option (SCMap K V))
:= bupdate map (scpath k) (fun entry => option_map (option_map (fun v => {| bekey := k; bevalue := v; bekeyP := eqS_refl (scpath k) |})) (update entry)).

Definition scmpath {K: Type} `{SubCountable K} (k: K) (vpath: BPath): BPath
:= bpath_pair (scpath k) vpath.

Definition SCSet (A: Type) `{SubCountable A}: Type
:= SCMap A (fun _ => unit).

Definition SCSetContains {A: Type} `{SubCountable A}: SCSet A -> A -> SProp
:= SCMapContains.

Definition IMap {K: Type} (index: K -> BPath) (V: Type): Type
:= BTree K (fun _ => V) (fun path key => eqS (index key) path).

Definition IMForallS {K: Type} {index: K -> BPath} (KV: K -> SProp) {V: Type} (R: K -> V -> SProp): IMap index V -> SProp
:= BTreeForallS (fun k v => AndS (KV k) (R k v)).

Definition IMContains {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K): SProp
:= BContainsPath map (index key).

Definition imget_contained {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K) (contains: IMContains map key): V
:= (bget_contained map (index key) contains).(bevalue).

Definition imget {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K): option V
:= option_map (bevalue (V := fun _ => V)) (bget map (index key)).

Definition IMExtends {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K) (value: V) (map': IMap index V): Prop
:= BExtends map (index key) {| bekey := key; bekeyP := eqS_refl _; bevalue := value |} map'.

Definition imempty {K: Type} (index: K -> BPath) (V: Type): IMap index V
:= bempty.

Definition imsingleton {K: Type} (index: K -> BPath) {V: Type} (k: K) (v: V): IMap index V
:= bsingleton (index k) {| bekey := k; bekeyP := eqS_refl (index k); bevalue := v |}.

Definition imupdate {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (k: K) (update: option V -> option V): option (IMap index V)
:= match bupdate map (index k) (fun entry => Some (option_map (fun v => {| bekey := k; bevalue := v; bekeyP := eqS_refl _ |}) (match entry with
                                                                                                                               | sbleftS contains => update (Some (bget_contained map (index k) contains).(bevalue))
                                                                                                                               | sbrightS _ => update None
                                                                                                                               end))) with
   | None => None
   | Some map => map
   end.

Definition imentries {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V): list (prod K V)
:= List.map (fun entry: sigT (fun path => BEntry K (fun _ => V) (fun key => eqS (index key) path)) => pair (projT2 entry).(bekey) (projT2 entry).(bevalue) : prod K V) (bentries map).

Definition ISet {K: Type} (index: K -> BPath): Type
:= IMap index unit.

Definition ISForallS {K: Type} {index: K -> BPath} (KV P: K -> SProp): ISet index -> SProp
:= IMForallS KV (fun k _ => P k).

Definition ISContains {K: Type} {index: K -> BPath}: ISet index -> K -> SProp
:= IMContains.

Definition ISExtends {K: Type} {index: K -> BPath} (set: ISet index) (key: K) (set': ISet index): Prop
:= (ISContains set key -> False) /\ IMExtends set key tt set'.

Definition issingleton {K: Type} (index: K -> BPath) (k: K): ISet index
:= imsingleton index k tt.

Definition isadd {K: Type} {index: K -> BPath} (set: ISet index) (k: K): option (ISet index)
:= imupdate set k (fun entry => match entry with None => Some tt | Some _ => None end).

Definition isvalues {K: Type} {index: K -> BPath} (set: ISet index): list K
:= map fst (imentries set).

Definition IPairSet {K: Type} (kindex: K -> BPath) {V: Type} (vindex: V -> BPath): Type
:= IMap kindex (ISet vindex).

Definition IPSForallS {K: Type} {kindex: K -> BPath} (KV: K -> SProp) {V: Type} {vindex: V -> BPath} (VV: V -> SProp) (P: K -> V -> SProp): IPairSet kindex vindex -> SProp
:= BTreeForallS (fun k vset => ISForallS VV (fun v => AndS (KV k) (P k v)) vset).

Definition IPSContains {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K) (v: V): SProp
:= existsSS contains: IMContains set k, ISContains (imget_contained set k contains) v.

Definition IPSExtends {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K) (v: V) (set': IPairSet kindex vindex): Prop
:= exists2 vset': ISet vindex,
   IMExtends set k vset' set'
 & match imget set k with
   | None => issingleton vindex v = vset'
   | Some vset => ISExtends vset v vset'
   end.

Definition ipsempty {K: Type} (kindex: K -> BPath) {V: Type} (vindex: V -> BPath): IPairSet kindex vindex
:= imempty kindex (ISet vindex).

Definition ipsadd {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K) (v: V): option (IPairSet kindex vindex)
:= imupdate set k (fun vset => match vset with None => Some (issingleton vindex v) | Some vset => isadd vset v end).

Definition ipsget_values {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K): list V
:= match imget set k with
   | None => nil
   | Some vset => isvalues vset
   end.

Definition Sort: Type
:= list Type.

Definition SumSort: Sort -> Type
:= fix SumSort (s: Sort): Type
:= match s with
   | nil => Empty
   | cons T s => sum T (SumSort s)
   end.

Definition sortl {T : Type} {s: Sort}: T -> SumSort (cons T s)
:= inl.

Definition sortr {T : Type} {s: Sort}: SumSort s -> SumSort (cons T s)
:= inr.

Definition sorte {T: Type} {s: Sort} {K: Type}: (T -> K) -> (SumSort s -> K) -> SumSort (cons T s) -> K
:= sume.

Definition SortSelection (T: Type): Sort -> Type
:= fix SortSelection (s: Sort): Type
:= match s with
   | nil => Empty
   | cons T' s => sum (T -> T') (SortSelection s)
   end.

Definition select_head {T T': Type} (f: T -> T') {s: Sort}: SortSelection T (cons T' s)
:= inl f.

Definition extend_selection {T: Type} {s: Sort} (T': Type) (selection: SortSelection T s): SortSelection T (cons T' s)
:= inr selection.

Definition SortMorphism: Sort -> Sort -> Type
:= fix SortMorphism (s: Sort): Sort -> Type
:= match s with
   | nil => fun _ => unit
   | cons T s => fun s' => prod (SortSelection T s') (SortMorphism s s')
   end.

Definition nil_morphism {s: Sort}: SortMorphism nil s
:= tt.

Definition pair_morphism {T: Type} {s s': Sort} (selection: SortSelection T s') (morphism: SortMorphism s s'): SortMorphism (cons T s) s'
:= pair selection morphism.

Definition SortElimination (T: Type): Sort -> Type
:= fix SortElimination (s: Sort): Type
:= match s with
   | nil => unit
   | cons T' s => prod (T' -> T) (SortElimination s)
   end.

Definition nil_elimination {T': Type}: SortElimination T' nil
:= tt.

Definition pair_elimination {T' T: Type} {s: Sort}: (T -> T') -> SortElimination T' s -> SortElimination T' (cons T s)
:= pair.

Definition apply_selection {T: Type}: forall {s: Sort}, SortSelection T s -> T -> SumSort s
:= fix apply_selection {s: Sort}: SortSelection T s -> T -> SumSort s
:= match s with
   | nil => emptye
   | cons T' s => fun selection => match selection with
                                   | inl f => fun t => sortl (f t)
                                   | inr selection => fun t => sortr (apply_selection selection t)
                                   end
   end.

Arguments apply_selection {T !s} !selection.

Definition apply_morphism: forall {s s': Sort}, SortMorphism s s' -> SumSort s -> SumSort s'
:= fix apply_morphism {s: Sort}: forall s': Sort, SortMorphism s s' -> SumSort s -> SumSort s'
:= match s as s return forall s': Sort, SortMorphism s s' -> SumSort s -> SumSort s' with
   | nil => fun _ _ => emptye
   | cons T s => fun s' morphism v => match v with
                                      | inl t => apply_selection (fst morphism) t
                                      | inr v => apply_morphism s' (snd morphism) v
                                      end
   end.

Arguments apply_morphism {!s s'} morphism !v.

Definition apply_elimination {T: Type}: forall {s: Sort}, SortElimination T s -> SumSort s -> T
:= fix apply_elimination {s: Sort}: SortElimination T s -> SumSort s -> T
:= match s with
   | nil => fun _ => emptye
   | cons T' s => fun p v => match v with
                             | inl t' => fst p t'
                             | inr v => apply_elimination (snd p) v
                             end
   end.

Arguments apply_elimination {T !s} elimination !v.

Definition extend_morphism (T: Type) {s': Sort}: forall {s: Sort}, SortMorphism s s' -> SortMorphism s (cons T s')
:= fix extend_morphism {s: Sort}: SortMorphism s s' -> SortMorphism s (cons T s')
:= match s as s return SortMorphism s s' -> SortMorphism s (cons T s')with
   | nil => fun _ => nil_morphism
   | cons T' s => fun morphism => pair_morphism (extend_selection T (fst morphism)) (extend_morphism (snd morphism))
   end.

Definition cons_morphism {T T': Type} (f: T -> T') {s s': Sort} (morphism: SortMorphism s s'): SortMorphism (cons T s) (cons T' s')
:= pair_morphism (select_head f) (extend_morphism T' morphism).

Definition consid_morphism (T: Type): forall {s s': Sort}, SortMorphism s s' -> SortMorphism (cons T s) (cons T s')
:= @cons_morphism T T (fun t => t).

Definition id_morphism: forall {s: Sort}, SortMorphism s s
:= fix id_morphism {s: Sort}: SortMorphism s s
:= match s with
   | nil => nil_morphism
   | cons T s => consid_morphism T id_morphism
   end.

Definition compose_selection {T T': Type} (f: T -> T'): forall {s: Sort}, SortSelection T' s -> SortSelection T s
:= fix compose_selection {s: Sort}: SortSelection T' s -> SortSelection T s
:= match s as s return SortSelection T' s -> SortSelection T s with
   | nil => emptye
   | cons T'' s => fun selection => match selection with
                                    | inl f' => select_head (compose f f')
                                    | inr selection => extend_selection T'' (compose_selection selection)
                                    end
   end.

Definition select_morphism {T: Type}: forall {s: Sort}, SortSelection T s -> forall {s': Sort}, SortMorphism s s' -> SortSelection T s'
:= fix select_morphism {s: Sort}: SortSelection T s -> forall s': Sort, SortMorphism s s' -> SortSelection T s'
:= match s as s return SortSelection T s -> forall {s': Sort}, SortMorphism s s' -> SortSelection T s' with
   | nil => emptye
   | cons T' s => fun selection => match selection with
                                   | inl f => fun s' morphism => compose_selection f (fst morphism)
                                   | inr selection => fun s' morphism => select_morphism selection s' (snd morphism)
                                   end
   end.

Definition compose_morphism: forall {s s' s'': Sort} (morphism: SortMorphism s s') (morphism': SortMorphism s' s''), SortMorphism s s''
:= fix compose_morphism {s: Sort}: forall s' s'': Sort, SortMorphism s s' -> SortMorphism s' s'' -> SortMorphism s s''
:= match s as s return forall s' s'': Sort, SortMorphism s s' -> SortMorphism s' s'' -> SortMorphism s s'' with
   | nil => fun _ _ _ _ => nil_morphism
   | cons T s => fun s' s'' morphism morphism' => pair_morphism (select_morphism (fst morphism) morphism') (compose_morphism s' s'' (snd morphism) morphism')
   end.

Definition compose_elimination {T': Type}: forall {s: Sort}, SortElimination T' s -> forall {T'': Type}, (T' -> T'') -> SortElimination T'' s
:= fix compose_elimination {s: Sort}: SortElimination T' s -> forall T'': Type, (T' -> T'') -> SortElimination T'' s
:= match s with
   | nil => fun _ _ _ => nil_elimination
   | cons T s => fun elimination T'' f' => pair_elimination (compose (fst elimination) f') (compose_elimination (snd elimination) T'' f')
   end.

Definition eliminate_selection {T: Type} {s': Sort} (selection: SortSelection T s') {T'': Type} (elimination: SortElimination T'' s') (t: T): T''
:= apply_elimination elimination (apply_selection selection t).

Definition eliminate_morphism: forall {s s': Sort}, SortMorphism s s' -> forall {T'': Type}, SortElimination T'' s' -> SortElimination T'' s
:= fix eliminate_morphism {s: Sort}: forall s': Sort, SortMorphism s s' -> forall T'': Type, SortElimination T'' s' -> SortElimination T'' s
:= match s as s return forall s': Sort, SortMorphism s s' -> forall T'': Type, SortElimination T'' s' -> SortElimination T'' s with
   | nil => fun s' _ T'' _ => nil_elimination
   | cons T s => fun s' morphism T'' elimination => pair_elimination (eliminate_selection (fst morphism) elimination) (eliminate_morphism s' (snd morphism) T'' elimination)
   end.

Definition eliminate_sum {T: Type}: forall {s: Sort}, (SumSort s -> T) -> SortElimination T s
:= fix eliminate_sum {s: Sort}: (SumSort s -> T) -> SortElimination T s
:= match s with
   | nil => fun _ => nil_elimination
   | cons T s => fun f => pair_elimination (compose sortl f) (eliminate_sum (compose sortr f))
   end.

Definition SubCountableSort: Sort -> Type
:= fix SubCountableSort (sort: Sort): Type
:= match sort with
   | nil => Unit
   | cons T sort => prod (SubCountable T) (SubCountableSort sort)
   end.

Definition SubFiniteSort: Sort -> Type
:= fix SubFiniteSort (sort: Sort): Type
:= match sort with
   | nil => Unit
   | cons T sort => prod (SubFinite T) (SubFiniteSort sort)
   end.

Record Scheme: Type :=
{ Interface: Type;
  IParameter (interface: Interface): Type;
  Method: Type;
  Method_SubCountable :: SubCountable Method;
  MInput (method: Method): Type;
}.

Parameter scheme: Scheme.

Inductive Expression | {Input: Sort}: Type
:= einput (input: SumSort Input)
 | einvoke (receiver: Expression) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> Expression)
 | eobject (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (Input := cons (scheme.(MInput) method) Input)).

Arguments Expression : clear implicits.

Definition AExpression (Input: Sort): Type
:= forall Input': Sort, (SumSort Input -> SumSort Input') -> Expression Input'.

Definition econcretize {Input: Sort} (expression: AExpression Input): Expression Input
:= expression Input (fun input => input).

Definition eabstract: forall {Input: Sort}, Expression Input -> AExpression Input
:= fix eabstract {Input: Sort} (expression: Expression Input): AExpression Input
:= match expression with
   | einput input => fun Input' naming => einput (naming input)
   | einvoke receiver method arguments => fun Input' naming => einvoke (eabstract receiver Input' naming) method (fun input => eabstract (arguments input) Input' naming)
   | eobject interface methods bodies => fun Input' naming => eobject interface methods (fun method contains => eabstract (bodies method contains) (cons (scheme.(MInput) method) Input') (sum_mapr naming))
   end.

Definition aesubstitute: forall {Input: Sort}, Expression Input -> forall {Input': Sort}, (SumSort Input -> AExpression Input') -> Expression Input'
:= fix aesubstitute {Input: Sort} (expression: Expression Input): forall Input': Sort, (SumSort Input -> AExpression Input') -> Expression Input'
:= match expression with
   | einput input => fun Input' substitution => econcretize (substitution input)
   | einvoke receiver method arguments => fun Input' substitution => einvoke (aesubstitute receiver Input' substitution) method (fun input => aesubstitute (arguments input) Input' substitution)
   | eobject interface methods bodies => fun Input' substitution => eobject interface methods (fun method contains => aesubstitute (bodies method contains) (cons (scheme.(MInput) method) Input') (sorte (fun input => eabstract (einput (sortl input))) (fun input => fun Input' naming => substitution input Input' (fun input => naming (sortr input)))))
   end.

Definition esubstitute {Input: Sort} (expression: Expression Input) {Input': Sort} (substitution: SumSort Input -> Expression Input'): Expression Input'
:= aesubstitute expression (fun input => eabstract (substitution input)).

Inductive Value {Input: Sort}: Expression Input -> SProp
:= vobject (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input)): Value (eobject interface methods bodies).

Inductive StepsTo {Input: Sort}: Expression Input -> Expression Input -> SProp
:= step_receiver
     (receiver receiver': Expression Input)
     (method: scheme.(Method))
     (arguments: scheme.(MInput) method -> Expression Input)
      : StepsTo receiver receiver'
     -> StepsTo (einvoke receiver method arguments) (einvoke receiver' method arguments)
 | step_invoke
     (interface: scheme.(Interface))
     (methods: SCSet scheme.(Method))
     (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input))
     (method: scheme.(Method))
     (contains: SCSetContains methods method)
     (arguments: scheme.(MInput) method -> Expression Input)
      : StepsTo (einvoke (eobject interface methods bodies) method arguments)
                (esubstitute (bodies method contains) (sorte arguments einput)).

Arguments StepsTo {_} _ _.

Inductive UserType {Var: Type}: Type
:= utvariable (variable: Var)
 | utany
 | utinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> UserType).

Arguments UserType : clear implicits.

Record UserMethodSignature {Var: Type} {Input: Type}: Type :=
{ umsinput (input: Input): UserType Var;
  umsresult: UserType Var;
}.

Arguments UserMethodSignature : clear implicits.

Record UserBodySignature {Var: Type}: Type :=
{ ubsmethods: SCSet scheme.(Method);
  ubsmethod (method: scheme.(Method)) (contains: SCSetContains ubsmethods method): UserMethodSignature Var (scheme.(MInput) method);
}.

Arguments UserBodySignature : clear implicits.

Record UserInterfaceSignature {Var: Type}: Type :=
{ uisvariance (parameter: Var): Sign;
  uisbody: UserBodySignature Var;
}.

Arguments UserInterfaceSignature : clear implicits.

Record Hierarchy: Type :=
{ hinterface (interface: scheme.(Interface)): UserInterfaceSignature (scheme.(IParameter) interface);
}.

Parameter hierarchy: Hierarchy.

Record Program: Type :=
{ pexpression: Expression nil;
  ptype: UserType Empty;
}.

Inductive UserVariance {Var: Type} {variance: Var -> Sign}: UserType Var -> Sign -> SProp
:= uvvariable (variable: Var): UserVariance (utvariable variable) (variance variable)
 | uvany (sign: Sign): UserVariance utany sign
 | uvinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> UserType Var) (sign: Sign): (forall parameter: scheme.(IParameter) interface, UserVariance (arguments parameter) (multiply sign ((hierarchy.(hinterface) interface).(uisvariance) parameter))) -> UserVariance (utinterface interface arguments) sign.

Arguments UserVariance {_} _ _ _.

Record UserMethodSignatureV {Var Input: Type} {signature: UserMethodSignature Var Input} {variance: Var -> Sign}: SProp :=
{ umsinputv (input: Input): UserVariance variance (signature.(umsinput) input) negative;
  umsresultv: UserVariance variance signature.(umsresult) positive;
}.

Arguments UserMethodSignatureV {_ _} _ _.

Record UserBodySignatureV {Var: Type} {signature: UserBodySignature Var} {variance: Var -> Sign}: SProp :=
{ ubsmethodv (method: scheme.(Method)) (contains: SCSetContains signature.(ubsmethods) method): UserMethodSignatureV (signature.(ubsmethod) method contains) variance;
}.

Arguments UserBodySignatureV {_} _ _.

Record UserInterfaceSignatureV {Var: Type} {signature: UserInterfaceSignature Var}: SProp :=
{ uisbodyv: UserBodySignatureV signature.(uisbody) signature.(uisvariance); }.

Arguments UserInterfaceSignatureV {_} _.

Record HierarchyV: SProp :=
{ hinterfacev (interface: scheme.(Interface)): UserInterfaceSignatureV (hierarchy.(hinterface) interface); }.

Definition utfold {Var: Type} {T: Type} (fany: T) (finterface: forall interface: scheme.(Interface), (scheme.(IParameter) interface -> T) -> T) (fvar: Var -> T): UserType Var -> T
:= fix utfold (type: UserType Var): T
:= match type with
   | utvariable variable => fvar variable
   | utany => fany
   | utinterface interface arguments => finterface interface (fun parameter => utfold (arguments parameter))
   end.

Record TypeSpace: Type :=
{ SpaceType: Type;
  stany: SpaceType;
  stinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> SpaceType): SpaceType;
  SubSpaceType: SpaceType -> SpaceType -> SProp;
  sstrefl (t: SpaceType): SubSpaceType t t;
  ssttrans (t t' t'': SpaceType): SubSpaceType t t' -> SubSpaceType t' t'' -> SubSpaceType t t'';
  sstvariance (interface: scheme.(Interface)) (arguments arguments': scheme.(IParameter) interface -> SpaceType): (forall parameter: scheme.(IParameter) interface, Signed SubSpaceType ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' parameter)) -> SubSpaceType (stinterface interface arguments) (stinterface interface arguments');
  sstinheritance (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> SpaceType): SubSpaceType (stinterface interface arguments) stany;
  UnReachable: SpaceType -> SProp;
  sstur (t t': SpaceType): SubSpaceType t t' -> UnReachable t' -> UnReachable t;
}.

Definition tsubst {Var: Type} {space: TypeSpace}: (Var -> space.(SpaceType)) -> UserType Var -> space.(SpaceType)
:= utfold space.(stany) space.(stinterface).

Record SpaceMethodSignature {space: TypeSpace} {Input: Type}: Type :=
{ smsinput (input: Input): space.(SpaceType);
  smsresult: space.(SpaceType);
}.

Arguments SpaceMethodSignature : clear implicits.

Definition mssubst {Var Input: Type} {space: TypeSpace} (substitution: Var -> space.(SpaceType)) (signature: UserMethodSignature Var Input): SpaceMethodSignature space Input :=
{| smsinput input := tsubst substitution (signature.(umsinput) input);
   smsresult := tsubst substitution signature.(umsresult);
|}.

Record SpaceBodySignature {space: TypeSpace}: Type :=
{ sbsmethods: SCSet scheme.(Method);
  sbsmethod (method: scheme.(Method)) (contains: SCSetContains sbsmethods method): SpaceMethodSignature space (scheme.(MInput) method);
}.

Arguments SpaceBodySignature : clear implicits.

Definition bssubst {Var: Type} {space: TypeSpace} (substitution: Var -> space.(SpaceType)) (signature: UserBodySignature Var): SpaceBodySignature space :=
{| sbsmethods := signature.(ubsmethods);
   sbsmethod method contains := mssubst substitution (signature.(ubsmethod) method contains);
|}.

Record SubSpaceMethodSignature {space: TypeSpace} {Input: Type} {signature signature': SpaceMethodSignature space Input}: SProp :=
{ ssmsinput (input: Input): space.(SubSpaceType) (signature'.(smsinput) input) (signature.(smsinput) input);
  ssmsresult: space.(SubSpaceType) signature.(smsresult) signature'.(smsresult);
}.

Arguments SubSpaceMethodSignature {_ _} _ _.

Record SubSpaceBodySignature {space: TypeSpace} {signature signature': SpaceBodySignature space}: SProp :=
{ ssbsmethods (method: scheme.(Method)): SCSetContains signature'.(sbsmethods) method -> SCSetContains signature.(sbsmethods) method;
  ssbsmethod (method: scheme.(Method)) (contains: SCSetContains signature'.(sbsmethods) method): SubSpaceMethodSignature (signature.(sbsmethod) method (ssbsmethods method contains)) (signature'.(sbsmethod) method contains);
}.

Arguments SubSpaceBodySignature {_} _ _.

Inductive CheckMethod {space: TypeSpace} {method: scheme.(Method)}: space.(SpaceType) -> SpaceMethodSignature space (scheme.(MInput) method) -> SProp
:= cmunreachable (treceiver: space.(SpaceType)) (signature: SpaceMethodSignature space (scheme.(MInput) method)): space.(UnReachable) treceiver -> CheckMethod treceiver signature
 | cminterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (contains: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method): CheckMethod (space.(stinterface) interface arguments) (mssubst arguments ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains)).

Arguments CheckMethod {_} _ _.

Inductive CheckExpression {space: TypeSpace} | {Input: Sort} {context: SortElimination space.(SpaceType) Input}: Expression Input -> space.(SpaceType) -> SProp
:= cesub (expression: Expression Input) (t t': space.(SpaceType)): CheckExpression expression t -> space.(SubSpaceType) t t' -> CheckExpression expression t'
 | ceinput (input: SumSort Input): CheckExpression (einput input) (apply_elimination context input)
 | ceinvoke (ereceiver: Expression Input) (method: scheme.(Method)) (einputs: scheme.(MInput) method -> Expression Input) (treceiver: space.(SpaceType)) (signature: SpaceMethodSignature space (scheme.(MInput) method)): CheckMethod method treceiver signature -> CheckExpression ereceiver treceiver -> (forall input: scheme.(MInput) method, CheckExpression (einputs input) (signature.(smsinput) input)) -> CheckExpression (einvoke ereceiver method einputs) signature.(smsresult)
 | ceobject (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (signatures: forall method: scheme.(Method), SCSetContains methods method -> SpaceMethodSignature space (scheme.(MInput) method)): SubSpaceBodySignature {| sbsmethods := methods; sbsmethod := signatures |} (bssubst arguments (hierarchy.(hinterface) interface).(uisbody)) -> (forall method: scheme.(Method), forall contains: SCSetContains methods method, CheckExpression (context := pair_elimination (signatures method contains).(smsinput) context) (bodies method contains) (signatures method contains).(smsresult)) -> CheckExpression (eobject interface methods bodies) (space.(stinterface) interface arguments).

Arguments CheckExpression _ {_} _ _ _.

Definition CheckAExpression {space: TypeSpace} {Input: Sort} (context: SortElimination space.(SpaceType) Input) (expression: AExpression Input) (type: space.(SpaceType)): SProp
:= forall Input': Sort, forall incl: SumSort Input -> SumSort Input', forall context': SortElimination space.(SpaceType) Input', (forall input: SumSort Input, space.(SubSpaceType) (apply_elimination context' (incl input)) (apply_elimination context input)) -> CheckExpression space context' (expression Input' incl) type.

Record ConsistentTypeSpace `{SSet scheme.(Interface)} {space: TypeSpace}: SProp :=
{ ctsinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> space.(SpaceType)): space.(SubSpaceType) (space.(stinterface) interface arguments) (space.(stinterface) interface' arguments') -> existsSS e: eqS interface interface', forall parameter: scheme.(IParameter) interface, Signed space.(SubSpaceType) ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' (convert e scheme.(IParameter) parameter));
  ctsanyunreachable: space.(UnReachable) space.(stany) -> FalseS;
  ctsanyinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)): space.(SubSpaceType) space.(stany) (space.(stinterface) interface arguments) -> FalseS;
  ctsinterfaceunreachable (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)): space.(UnReachable) (space.(stinterface) interface arguments) -> FalseS;
}.

Arguments ConsistentTypeSpace {_} _.

Inductive SubUserType {Var: Type}: UserType Var -> UserType Var -> SProp
:= sutvariable (variable: Var): SubUserType (utvariable variable) (utvariable variable)
 | sutany: SubUserType utany utany
 | sutvariance (interface: scheme.(Interface)) (arguments arguments': scheme.(IParameter) interface -> UserType Var): (forall parameter: scheme.(IParameter) interface, ISigned SubUserType ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' parameter)) -> SubUserType (utinterface interface arguments) (utinterface interface arguments')
 | sutinheritance (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> UserType Var): SubUserType (utinterface interface arguments) utany.

Inductive UnReachableUserType: UserType Empty -> SProp
:=.

Record ProgramV `{SSet scheme.(Interface)} {program: Program}: SProp :=
{ phierarchyv: HierarchyV;
  pexpressionv: existsTSS space: TypeSpace, ConsistentTypeSpace space & CheckExpression space nil_elimination program.(pexpression) (tsubst emptye program.(ptype));
}.

Arguments ProgramV {_} _.

(* Finite quantification over the supplied encodings. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Logic.Eqdep_dec.

Import ListNotations.
Local Open Scope list_scope.

Lemma pv_btappend_in {A} (tree : BTrunk)
    (f : forall p, BTContains tree p -> list A) p (h : BTContains tree p) x :
    In x (f p h) -> In x (btappend tree f).
Proof.
  revert f p h. induction tree as [|head l IHl r IHr]; intros f p h hx.
  - exact (falseSe h).
  - destruct p as [|p|p]; cbn in h |- *.
    + apply in_or_app; left. destruct head; [exact (falseSe h)|exact hx].
    + apply in_or_app; right. apply in_or_app; left. exact (IHl _ p h hx).
    + apply in_or_app; right. apply in_or_app; right. exact (IHr _ p h hx).
Qed.

Lemma pv_flist_in {A} {F : Finite A} (a : A) :
    In a (flist (fun x : A => x)).
Proof.
  unfold flist, fappend.
  apply (pv_btappend_in _ _ (scpath a) (sfcontains a)).
  left. symmetry. apply scpath_inj. apply eqS_eq, fpath_eqS.
Qed.

Fixpoint pv_list_all {A} (xs : list A) (P : A -> SProp)
    (d : forall a, DeciderS (P a)) : DeciderS (forall a, In a xs -> P a).
Proof.
  destruct xs as [|x xs].
  - left. intros a h. contradiction.
  - destruct (d x) as [hx|nx].
    + destruct (pv_list_all A xs P d) as [hs|ns].
      * left. intros a [<-|ha]; [exact hx|exact (hs a ha)].
      * right. intro h. apply ns. intros a ha. apply h. now right.
    + right. intro h. apply nx, h. now left.
Defined.

Definition pv_finite_all {A} (F : Finite A) (P : A -> SProp)
    (d : forall a, DeciderS (P a)) : DeciderS (forall a, P a).
Proof.
  destruct (pv_list_all (flist (fun x : A => x)) P d) as [h|h].
  - left. intro a. exact (h a (pv_flist_in a)).
  - right. intro e. apply h. intros a _. apply e.
Defined.

Lemma pv_trunk_contains {K V P} (t : BTree K V P) p :
    BContainsPath t p -> BTContains (btree_trunk t) p.
Proof.
  revert p. induction t as [|P h l IHl r IHr]; intros p hp.
  - exact hp.
  - destruct p as [|p|p]; cbn in *.
    + destruct h; exact hp.
    + exact (IHl p hp).
    + exact (IHr p hp).
Qed.

Lemma pv_trunk_path {K V P} (t : BTree K V P) p :
    BTContains (btree_trunk t) p -> BContainsPath t p.
Proof.
  revert p. induction t as [|P h l IHl r IHr]; intros p hp.
  - exact hp.
  - destruct p as [|p|p]; cbn in *.
    + destruct h; exact hp.
    + exact (IHl p hp).
    + exact (IHr p hp).
Qed.

Definition pv_methods (s : SCSet scheme.(Method)) :
    list (sigS (SCSetContains s)) :=
  btappend (btree_trunk s) (fun p h =>
    let e := bget_contained s p (pv_trunk_path s p h) in
    let q := eqS_eq e.(bekeyP) in
    @existS _ _ e.(bekey)
      (match eq_sym q in _ = p' return BContainsPath s p' with
       | eq_refl => pv_trunk_path s p h
       end) :: nil).

Lemma pv_methods_in (s : SCSet scheme.(Method)) m (h : SCSetContains s m) :
    In (@existS _ _ m h) (pv_methods s).
Proof.
  unfold pv_methods.
  apply (pv_btappend_in _ _ (scpath m) (pv_trunk_contains s _ h)).
  cbn beta iota zeta. left.
  set (e := bget_contained _ _ _).
  assert (q : e.(bekey) = m) by (apply scpath_inj, eqS_eq, e.(bekeyP)).
  destruct e as [k kp v]; cbn in *; subst k; reflexivity.
Qed.

Definition pv_methods_all (s : SCSet scheme.(Method))
    (P : forall m, SCSetContains s m -> SProp)
    (d : forall m h, DeciderS (P m h)) :
    DeciderS (forall m h, P m h).
Proof.
  destruct (pv_list_all (pv_methods s)
    (fun e => P e.(proj1_sigS) e.(proj2_sigS))
    (fun e => d e.(proj1_sigS) e.(proj2_sigS))) as [h|h].
  - left. intros m hm. exact (h _ (pv_methods_in s m hm)).
  - right. intro e. apply h. intros [m hm] _. apply e.
Defined.

Fixpoint pv_contains_dec {K V P} (t : BTree K V P) p :
    DeciderS (BContainsPath t p).
Proof.
  destruct t as [|h l r].
  - right. exact (fun f => f).
  - destruct p as [|p|p].
    + destruct h; [left; exact trueS|right; exact (fun f => f)].
    + exact (pv_contains_dec _ _ _ l p).
    + exact (pv_contains_dec _ _ _ r p).
Defined.

Section ValidityDecision.
Context {Interface_Finite : Finite scheme.(Interface)}
        {IParameter_Finite : forall i, Finite (scheme.(IParameter) i)}
        {MInput_Finite : forall m, Finite (scheme.(MInput) m)}.

Lemma pv_eqS_false {A} (x y : A) (h : x <> y) : eqS x y -> FalseS.
Proof.
  intro q. destruct q. exact (false_falseS (h eq_refl)).
Qed.

Lemma pv_variable_sign {A} (v : A -> Sign) :
    forall t s, UserVariance v t s ->
    match t with utvariable a => eqS (v a) s | _ => TrueS end.
Proof. intros t s h. destruct h; constructor. Qed.

Definition pv_sign_eq (s t : Sign) : {s = t} + {s <> t}.
Proof. decide equality. Defined.

Fixpoint pv_variance_test {A} (v : A -> Sign) (t : UserType A) (s : Sign) :
    DeciderS (UserVariance v t s).
Proof.
  destruct t as [a| |i args].
  - destruct (pv_sign_eq (v a) s) as [e|ne].
    + left. rewrite <- e. constructor.
    + right. intro h. exact (pv_eqS_false _ _ ne (pv_variable_sign v _ _ h)).
  - left; constructor.
  - destruct (pv_finite_all (IParameter_Finite i)
      (fun p => UserVariance v (args p) (multiply s ((hierarchy.(hinterface) i).(uisvariance) p)))
      (fun p => pv_variance_test A v (args p) _)) as [h|h].
    + left; now constructor.
    + right. intro bad. apply h.
      assert (test : forall t s, UserVariance v t s ->
        match t with
        | utinterface i args => forall p, UserVariance v (args p)
            (multiply s ((hierarchy.(hinterface) i).(uisvariance) p))
        | _ => TrueS
        end).
      { intros t s' h'. destruct h'; try constructor; assumption. }
      exact (test _ _ bad).
Defined.

Definition pv_hierarchy_test : DeciderS HierarchyV.
Proof.
  assert (d : forall (A B : Type) (F : Finite B) (v : A -> Sign)
      (s : UserMethodSignature A B), DeciderS (UserMethodSignatureV s v)).
  { intros A B F v s.
    destruct (pv_finite_all F _ (fun i => pv_variance_test v (s.(umsinput) i) negative)) as [hi|hi].
    - destruct (pv_variance_test v s.(umsresult) positive) as [ho|ho].
      + left; now constructor.
      + right; intro h; exact (ho h.(umsresultv)).
    - right; intro h; exact (hi h.(umsinputv)). }
  destruct (pv_finite_all Interface_Finite
    (fun i => UserBodySignatureV (hierarchy.(hinterface) i).(uisbody)
      (hierarchy.(hinterface) i).(uisvariance))
    (fun i =>
      match pv_methods_all (hierarchy.(hinterface) i).(uisbody).(ubsmethods) _
        (fun m h => d _ _ (MInput_Finite m) _ ((hierarchy.(hinterface) i).(uisbody).(ubsmethod) m h))
      with
      | sbleftS h => sbleftS {| ubsmethodv := h |}
      | sbrightS h => sbrightS (fun v => h v.(ubsmethodv))
      end)) as [h|h].
  - left. constructor. intro i. constructor. apply h.
  - right. intro v. apply h. intro i. exact (v.(hinterfacev) i).(uisbodyv).
Defined.

(* The finite constraints are interpreted in a space of sequences of
   approximations. Each layer is a bounded lattice, with the order of
   contravariant components reversed. *)


Record pv_lattice := {
  pv_carrier : Type;
  pv_le : pv_carrier -> pv_carrier -> Prop;
  pv_refl : forall x, pv_le x x;
  pv_trans : forall x y z, pv_le x y -> pv_le y z -> pv_le x z;
  pv_bot : pv_carrier;
  pv_top : pv_carrier;
  pv_bot_le : forall x, pv_le pv_bot x;
  pv_le_top : forall x, pv_le x pv_top;
  pv_bot_only : forall x, pv_le x pv_bot -> x = pv_bot;
  pv_join : pv_carrier -> pv_carrier -> pv_carrier;
  pv_join_l : forall x y, pv_le x (pv_join x y);
  pv_join_r : forall x y, pv_le y (pv_join x y);
  pv_join_le : forall x y z, pv_le x z -> pv_le y z -> pv_le (pv_join x y) z;
  pv_meet : pv_carrier -> pv_carrier -> pv_carrier;
  pv_meet_l : forall x y, pv_le (pv_meet x y) x;
  pv_meet_r : forall x y, pv_le (pv_meet x y) y;
  pv_le_meet : forall x y z, pv_le x y -> pv_le x z -> pv_le x (pv_meet y z)
}.

Definition pv_unit_lattice : pv_lattice.
Proof.
  refine {| pv_carrier := unit; pv_le := fun _ _ => True;
    pv_bot := tt; pv_top := tt; pv_join := fun _ _ => tt; pv_meet := fun _ _ => tt |};
    try (intros; exact I).
  now intros [].
Defined.

Inductive pv_layer (A : Type) : Type :=
| pv_bottom : pv_layer
| pv_any : pv_layer
| pv_interface (i : scheme.(Interface)) (a : scheme.(IParameter) i -> A) : pv_layer.

Arguments pv_bottom {_}.
Arguments pv_any {_}.
Arguments pv_interface {_} _ _.

Local Notation param := (scheme.(IParameter)).
Local Notation iface := (scheme.(Interface)).
Local Notation method := (scheme.(Method)).
Local Notation input := (scheme.(MInput)).
Local Notation variance := (fun i p => (hierarchy.(hinterface) i).(uisvariance) p).

Definition pv_cast {i j : iface} (e : i = j) (p : param i) : param j :=
  match e with eq_refl => p end.

Lemma pv_interface_uip (i j : iface) (e f : i = j) : e = f.
Proof. apply UIP_dec. exact dec_eq. Qed.

Definition pv_signed_le (L : pv_lattice) s (a b : L.(pv_carrier)) : Prop :=
  match s with negative => L.(pv_le) b a | positive => L.(pv_le) a b end.

Definition pv_layer_le (L : pv_lattice) (x y : pv_layer L.(pv_carrier)) : Prop :=
  match x, y with
  | pv_bottom, _ | _, pv_any => True
  | pv_interface i a, pv_interface j b =>
      match dec_eq i j with
      | left e => forall p, pv_signed_le L (variance i p) (a p) (b (pv_cast e p))
      | right _ => False
      end
  | _, _ => False
  end.

Lemma pv_layer_same L i a b :
    pv_layer_le L (pv_interface i a) (pv_interface i b) <->
    forall p, pv_signed_le L (variance i p) (a p) (b p).
Proof.
  cbn [pv_layer_le]. destruct (dec_eq i i) as [e|n].
  - rewrite (pv_interface_uip i i e eq_refl). reflexivity.
  - contradiction n; reflexivity.
Qed.

Lemma pv_layer_index L i a j b :
    pv_layer_le L (pv_interface i a) (pv_interface j b) -> i = j.
Proof.
  cbn [pv_layer_le]. destruct (dec_eq i j); tauto.
Qed.

Definition pv_layer_join L (x y : pv_layer L.(pv_carrier)) : pv_layer L.(pv_carrier) :=
  match x, y with
  | pv_bottom, _ => y
  | _, pv_bottom => x
  | pv_interface i a, pv_interface j b =>
      match dec_eq i j with
      | left e => pv_interface i (fun p =>
          match variance i p with
          | positive => L.(pv_join) (a p) (b (pv_cast e p))
          | negative => L.(pv_meet) (a p) (b (pv_cast e p))
          end)
      | right _ => pv_any
      end
  | _, _ => pv_any
  end.

Definition pv_layer_meet L (x y : pv_layer L.(pv_carrier)) : pv_layer L.(pv_carrier) :=
  match x, y with
  | pv_any, _ => y
  | _, pv_any => x
  | pv_interface i a, pv_interface j b =>
      match dec_eq i j with
      | left e => pv_interface i (fun p =>
          match variance i p with
          | positive => L.(pv_meet) (a p) (b (pv_cast e p))
          | negative => L.(pv_join) (a p) (b (pv_cast e p))
          end)
      | right _ => pv_bottom
      end
  | _, _ => pv_bottom
  end.

Lemma pv_layer_refl L x : pv_layer_le L x x.
Proof.
  destruct x; try exact I.
  apply pv_layer_same. intro p. unfold pv_signed_le. destruct (variance i p); apply pv_refl.
Qed.

Lemma pv_layer_trans L x y z :
    pv_layer_le L x y -> pv_layer_le L y z -> pv_layer_le L x z.
Proof.
  destruct x as [| |i a], y as [| |j b], z as [| |k c]; try solve [simpl; tauto].
  intros h1 h2.
  pose proof (pv_layer_index _ _ _ _ _ h1) as e1.
  pose proof (pv_layer_index _ _ _ _ _ h2) as e2. subst j k.
  apply pv_layer_same. intro p.
  pose proof (proj1 (pv_layer_same L i _ _) h1 p) as hp1.
  pose proof (proj1 (pv_layer_same L i _ _) h2 p) as hp2.
  unfold pv_signed_le in *.
  destruct (variance i p); eapply pv_trans; eassumption.
Qed.

Local Ltac pv_layer_pair i j :=
  destruct (dec_eq i j) as [e|ne];
  [subst j; cbn [pv_layer_join pv_layer_meet];
   destruct (dec_eq i i) as [e|ne]; [rewrite (pv_interface_uip i i e eq_refl) | contradiction ne; reflexivity]
  | cbn [pv_layer_join pv_layer_meet]; destruct (dec_eq i j) as [e|]; [contradiction|]].

Lemma pv_layer_join_l L x y : pv_layer_le L x (pv_layer_join L x y).
Proof.
  destruct x as [| |i a], y as [| |j b]; try exact I; try apply pv_layer_refl.
  pv_layer_pair i j; [|exact I].
  apply pv_layer_same. intro p. unfold pv_signed_le. destruct (variance i p);
    [apply pv_meet_l|apply pv_join_l].
Qed.

Lemma pv_layer_join_r L x y : pv_layer_le L y (pv_layer_join L x y).
Proof.
  destruct x as [| |i a], y as [| |j b]; try exact I; try apply pv_layer_refl.
  pv_layer_pair i j; [|exact I].
  apply pv_layer_same. intro p. unfold pv_signed_le. destruct (variance i p);
    [apply pv_meet_r|apply pv_join_r].
Qed.

Lemma pv_layer_meet_l L x y : pv_layer_le L (pv_layer_meet L x y) x.
Proof.
  destruct x as [| |i a], y as [| |j b]; try exact I; try apply pv_layer_refl.
  pv_layer_pair i j; [|exact I].
  apply pv_layer_same. intro p. unfold pv_signed_le. destruct (variance i p);
    [apply pv_join_l|apply pv_meet_l].
Qed.

Lemma pv_layer_meet_r L x y : pv_layer_le L (pv_layer_meet L x y) y.
Proof.
  destruct x as [| |i a], y as [| |j b]; try exact I; try apply pv_layer_refl.
  pv_layer_pair i j; [|exact I].
  apply pv_layer_same. intro p. unfold pv_signed_le. destruct (variance i p);
    [apply pv_join_r|apply pv_meet_r].
Qed.

Lemma pv_layer_join_le L x y z :
    pv_layer_le L x z -> pv_layer_le L y z -> pv_layer_le L (pv_layer_join L x y) z.
Proof.
  destruct x as [| |i a], y as [| |j b], z as [| |k c]; try solve [simpl; tauto].
  all: try solve [cbn [pv_layer_join]; destruct (dec_eq i j); simpl; tauto].
  intros h1 h2.
  pose proof (pv_layer_index _ _ _ _ _ h1) as e1.
  pose proof (pv_layer_index _ _ _ _ _ h2) as e2. subst k j.
  cbn [pv_layer_join]. destruct (dec_eq i i) as [e|n]; [|contradiction n; reflexivity].
  rewrite (pv_interface_uip i i e eq_refl).
  apply pv_layer_same. intro p.
  pose proof (proj1 (pv_layer_same L i _ _) h1 p) as hp1.
  pose proof (proj1 (pv_layer_same L i _ _) h2 p) as hp2.
  unfold pv_signed_le in *.
  destruct (variance i p); [apply pv_le_meet|apply pv_join_le]; assumption.
Qed.

Lemma pv_layer_le_meet L x y z :
    pv_layer_le L x y -> pv_layer_le L x z -> pv_layer_le L x (pv_layer_meet L y z).
Proof.
  destruct x as [| |i a], y as [| |j b], z as [| |k c]; try solve [simpl; tauto].
  all: try solve [cbn [pv_layer_meet]; destruct (dec_eq j k); simpl; tauto].
  intros h1 h2.
  pose proof (pv_layer_index _ _ _ _ _ h1) as e1.
  pose proof (pv_layer_index _ _ _ _ _ h2) as e2. subst j k.
  cbn [pv_layer_meet]. destruct (dec_eq i i) as [e|n]; [|contradiction n; reflexivity].
  rewrite (pv_interface_uip i i e eq_refl).
  apply pv_layer_same. intro p.
  pose proof (proj1 (pv_layer_same L i _ _) h1 p) as hp1.
  pose proof (proj1 (pv_layer_same L i _ _) h2 p) as hp2.
  unfold pv_signed_le in *.
  destruct (variance i p); [apply pv_join_le|apply pv_le_meet]; assumption.
Qed.

Definition pv_layer_lattice (L : pv_lattice) : pv_lattice.
Proof.
  refine {| pv_carrier := pv_layer L.(pv_carrier);
    pv_le := pv_layer_le L; pv_refl := pv_layer_refl L; pv_trans := pv_layer_trans L;
    pv_bot := pv_bottom; pv_top := pv_any;
    pv_join := pv_layer_join L; pv_meet := pv_layer_meet L;
    pv_join_l := pv_layer_join_l L; pv_join_r := pv_layer_join_r L;
    pv_join_le := pv_layer_join_le L;
    pv_meet_l := pv_layer_meet_l L; pv_meet_r := pv_layer_meet_r L;
    pv_le_meet := pv_layer_le_meet L |}.
  - now intros [].
  - now intros [].
  - intros []; simpl; tauto.
Defined.

Fixpoint pv_approx n : pv_lattice :=
  match n with 0 => pv_unit_lattice | S n => pv_layer_lattice (pv_approx n) end.

Definition pv_stream := forall n, (pv_approx n).(pv_carrier).
Definition pv_stream_interface (i : iface) (a : param i -> pv_stream) : pv_stream :=
  fun n => match n as k return (pv_approx k).(pv_carrier) with
           | 0 => tt | S k => pv_interface i (fun p => a p k)
           end.

Definition pv_stream_le (x y : pv_stream) : SProp :=
  Squash (forall n, (pv_approx n).(pv_le) (x n) (y n)).

Definition pv_stream_ur (x : pv_stream) : SProp :=
  Squash (forall n, x n = (pv_approx n).(pv_bot)).

Lemma pv_squash_list {A} (xs : list A) (P : A -> Prop) :
    (forall x, Squash (P x)) -> Squash (forall x, In x xs -> P x).
Proof.
  intro h. induction xs as [|x xs [hs]].
  - constructor. intros a ha. contradiction.
  - destruct (h x) as [hx]. constructor. intros a [<-|ha]; auto.
Qed.

Lemma pv_squash_finite {A} (F : Finite A) (P : A -> Prop) :
    (forall x, Squash (P x)) -> Squash (forall x, P x).
Proof.
  intro h. destruct (pv_squash_list (flist (fun x : A => x)) P h) as [hs].
  constructor. intro x. apply hs, pv_flist_in.
Qed.

Definition pv_space : TypeSpace.
Proof.
  refine {| SpaceType := pv_stream; stany := fun n => (pv_approx n).(pv_top);
    stinterface := pv_stream_interface; SubSpaceType := pv_stream_le;
    UnReachable := pv_stream_ur |}.
  - intro x. constructor. intro n. apply pv_refl.
  - intros x y z [hxy] [hyz]. constructor. intro n. eapply pv_trans; [apply hxy|apply hyz].
  - intros i a b h.
    assert (hs : forall p, Squash (forall n,
      pv_signed_le (pv_approx n) (variance i p) (a p n) (b p n))).
    { intro p. specialize (h p). unfold pv_signed_le.
      destruct (variance i p); exact h. }
    destruct (pv_squash_finite (IParameter_Finite i) _ hs) as [hs'].
    constructor. intros [|n]; [exact I|].
    apply pv_layer_same. intro p. apply hs'.
  - intros i a. constructor. intro n. apply pv_le_top.
  - intros x y [h] [hy]. constructor. intro n. apply pv_bot_only. rewrite <- hy. apply h.
Defined.

Lemma pv_space_consistent : ConsistentTypeSpace pv_space.
Proof.
  constructor.
  - intros i a j b [h].
    assert (e : i = j) by (eapply pv_layer_index; exact (h 1)).
    subst j. refine (@ex_introSS _ _ (eqS_refl i) _).
    intro p. unfold convert. rewrite (pv_interface_uip i i (eqS_eq (eqS_refl i)) eq_refl).
    assert (hp : forall n, pv_signed_le (pv_approx n) (variance i p) (a p n) (b p n)).
    { intro n. apply (proj1 (pv_layer_same _ _ _ _) (h (S n)) p). }
    unfold pv_signed_le in hp. destruct (variance i p); constructor; exact hp.
  - intros [h]. exact (false_falseS (ltac:(pose proof (h 1) as e; discriminate e))).
  - intros i a [h]. exact (false_falseS (h 1)).
  - intros i a [h]. exact (false_falseS (ltac:(pose proof (h 1) as e; discriminate e))).
Qed.


(* Closing a finite set of rules under forward chaining. *)

Definition pv_fact := option (nat * nat).
Definition pv_edge (x y : nat) : pv_fact := Some (x, y).
Definition pv_rule := (list pv_fact * pv_fact)%type.

Definition pv_fact_eq (x y : pv_fact) : {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Definition pv_has (xs : list pv_fact) (x : pv_fact) : bool :=
  if in_dec pv_fact_eq x xs then true else false.

Lemma pv_has_spec xs f : pv_has xs f = true <-> In f xs.
Proof. unfold pv_has. destruct (in_dec pv_fact_eq f xs); intuition discriminate. Qed.

Definition pv_ready (facts : list pv_fact) (r : pv_rule) : bool :=
  forallb (pv_has facts) (fst r) && negb (pv_has facts (snd r)).

Lemma pv_ready_spec facts r :
    pv_ready facts r = true <->
    (forall f, In f (fst r) -> In f facts) /\ ~ In (snd r) facts.
Proof.
  unfold pv_ready. rewrite andb_true_iff, forallb_forall, negb_true_iff.
  destruct (pv_has facts (snd r)) eqn:e.
  - apply pv_has_spec in e. intuition discriminate.
  - assert (n : ~ In (snd r) facts).
    { intro h. apply pv_has_spec in h. congruence. }
    split.
    + intros [h _]; split; [|exact n].
      intros f hf. apply pv_has_spec, h, hf.
    + intros [h _]; split; [|reflexivity].
      intros f hf. apply pv_has_spec, h, hf.
Qed.

Fixpoint pv_close (fuel : nat) (rules : list pv_rule) (facts : list pv_fact) :=
  match fuel with
  | 0 => facts
  | S n => match find (pv_ready facts) rules with
           | Some r => pv_close n rules (snd r :: facts)
           | None => facts
           end
  end.

Lemma pv_close_sound fuel rules facts (P : pv_fact -> SProp) :
    (forall r, In r rules -> (forall f, In f (fst r) -> P f) -> P (snd r)) ->
    (forall f, In f facts -> P f) ->
    forall f, In f (pv_close fuel rules facts) -> P f.
Proof.
  revert facts. induction fuel as [|n IH]; intros facts rule_ok initial f hf.
  - exact (initial f hf).
  - cbn in hf. destruct (find (pv_ready facts) rules) as [r|] eqn:e.
    + apply find_some in e. destruct e as [hr ready]. apply pv_ready_spec in ready.
      refine (IH _ rule_ok _ f hf).
      intros g [<-|hg]; [apply rule_ok; [exact hr|]|now apply initial].
      intros g hg. apply initial, ready, hg.
    + exact (initial f hf).
Qed.

Lemma pv_close_closed fuel rules facts remaining :
    length remaining <= fuel ->
    (forall r, In r rules -> In (snd r) facts \/ In (snd r) remaining) ->
    forall r, In r rules ->
      (forall f, In f (fst r) -> In f (pv_close fuel rules facts)) ->
      In (snd r) (pv_close fuel rules facts).
Proof.
  revert facts remaining. induction fuel as [|n IH]; intros facts remaining bound cover.
  - destruct remaining; [|inversion bound].
    intros r hr _. destruct (cover r hr) as [h|[]]; exact h.
  - cbn. destruct (find (pv_ready facts) rules) as [r|] eqn:e.
    + apply find_some in e. destruct e as [hr ready].
      apply pv_ready_spec in ready. destruct ready as [_ missing].
      assert (pending : In (snd r) remaining) by (destruct (cover r hr); tauto).
      apply (IH (snd r :: facts) (remove pv_fact_eq (snd r) remaining)).
      * apply Nat.lt_succ_r.
        eapply Nat.lt_le_trans; [apply remove_length_lt, pending|exact bound].
      * intros q hq. destruct (pv_fact_eq (snd q) (snd r)) as [same|different].
        -- left; left; congruence.
        -- destruct (cover q hq) as [h|h].
           ++ left; now right.
           ++ right. apply in_in_remove; assumption.
    + intros r hr pre. apply find_none with (x := r) in e; [|exact hr].
      destruct (in_dec pv_fact_eq (snd r) facts) as [h|h]; [exact h|].
      assert (pv_ready facts r = true) by (apply pv_ready_spec; auto).
      congruence.
Qed.

Inductive pv_shape :=
| pv_shape_any
| pv_shape_interface (i : iface) (a : param i -> nat).

Definition pv_decl := (nat * pv_shape)%type.
Record pv_problem := {
  pv_edges : list (nat * nat);
  pv_decls : list pv_decl;
  pv_unreachable : list nat
}.

Definition pv_signed_edge i (p : param i) (x y : nat) : pv_fact :=
  match variance i p with negative => pv_edge y x | positive => pv_edge x y end.

Definition pv_children (d : pv_decl) : list nat :=
  match snd d with
  | pv_shape_interface i a => map a (@flist _ (IParameter_Finite i) _ (fun p => p))
  | _ => nil
  end.

Definition pv_nodes (q : pv_problem) : list nat :=
  flat_map (fun e => [fst e; snd e]) q.(pv_edges) ++
  flat_map (fun d => fst d :: pv_children d) q.(pv_decls) ++ q.(pv_unreachable).

Definition pv_decompose (d e : pv_decl) : list pv_rule :=
  let premise := [pv_edge (fst d) (fst e)] in
  match snd d, snd e with
  | pv_shape_any, pv_shape_interface _ _ => [(premise, None)]
  | pv_shape_interface i a, pv_shape_interface j b =>
      match dec_eq i j with
      | left eqij =>
          map (fun p => (premise, pv_signed_edge i p (a p) (b (pv_cast eqij p))))
            (@flist _ (IParameter_Finite i) _ (fun p => p))
      | right _ => [(premise, None)]
      end
  | _, _ => nil
  end.

Definition pv_rules (q : pv_problem) : list pv_rule :=
  let nodes := nodup Nat.eq_dec (pv_nodes q) in
  map (fun e => (nil, pv_edge (fst e) (snd e))) q.(pv_edges) ++
  map (fun x => (nil, pv_edge x x)) nodes ++
  flat_map (fun x => flat_map (fun y => map (fun z =>
    ([pv_edge x y; pv_edge y z], pv_edge x z)) nodes) nodes) nodes ++
  flat_map (fun d => flat_map (pv_decompose d) q.(pv_decls)) q.(pv_decls) ++
  flat_map (fun d => map (fun u => ([pv_edge (fst d) u], None))
    q.(pv_unreachable)) q.(pv_decls).

Definition pv_facts q :=
  let rules := pv_rules q in pv_close (length (map snd rules)) rules nil.

Lemma pv_fact_closed q r :
    In r (pv_rules q) -> (forall f, In f (fst r) -> In f (pv_facts q)) ->
    In (snd r) (pv_facts q).
Proof.
  unfold pv_facts. apply (pv_close_closed _ _ nil (map snd (pv_rules q))); [reflexivity|].
  intros r' hr. right. now apply in_map.
Qed.

Local Ltac pv_skip_arms n :=
  lazymatch n with
  | O => idtac
  | S ?k => apply in_or_app; right; pv_skip_arms k
  end.

Local Ltac pv_rule_arm n :=
  unfold pv_rules; cbv zeta; pv_skip_arms n;
  first [apply in_or_app; left | idtac].

Lemma pv_fact_edge q x y : In (x,y) q.(pv_edges) -> In (pv_edge x y) (pv_facts q).
Proof.
  intro h. apply (pv_fact_closed q (nil, pv_edge x y)).
  - pv_rule_arm 0. apply in_map with (f := fun e => (@nil pv_fact, pv_edge (fst e) (snd e))) in h. exact h.
  - intros f [].
Qed.

Lemma pv_fact_refl q x : In x (pv_nodes q) -> In (pv_edge x x) (pv_facts q).
Proof.
  intro h. apply (proj2 (nodup_In Nat.eq_dec _ _)) in h.
  apply (pv_fact_closed q (nil, pv_edge x x)).
  - pv_rule_arm 1. apply in_map with (f := fun x => (@nil pv_fact, pv_edge x x)) in h. exact h.
  - intros f [].
Qed.

Lemma pv_fact_trans q x y z :
    In x (pv_nodes q) -> In y (pv_nodes q) -> In z (pv_nodes q) ->
    In (pv_edge x y) (pv_facts q) -> In (pv_edge y z) (pv_facts q) ->
    In (pv_edge x z) (pv_facts q).
Proof.
  intros hx hy hz hxy hyz.
  apply (proj2 (nodup_In Nat.eq_dec _ _)) in hx, hy, hz.
  apply (pv_fact_closed q ([pv_edge x y; pv_edge y z], pv_edge x z)).
  - pv_rule_arm 2. apply in_flat_map. exists x; split; [exact hx|].
    apply in_flat_map. exists y; split; [exact hy|]. apply in_map_iff. now exists z.
  - intros f [<-|[<-|[]]]; assumption.
Qed.

Lemma pv_fact_decompose q d e f :
    In d q.(pv_decls) -> In e q.(pv_decls) ->
    In ([pv_edge (fst d) (fst e)], f) (pv_decompose d e) ->
    In (pv_edge (fst d) (fst e)) (pv_facts q) -> In f (pv_facts q).
Proof.
  intros hd he hf h. apply (pv_fact_closed q ([pv_edge (fst d) (fst e)], f)).
  - pv_rule_arm 3. apply in_flat_map. exists d; split; [exact hd|].
    apply in_flat_map. now exists e.
  - intros f' [<-|[]]. exact h.
Qed.

Lemma pv_fact_unreachable q d u :
    In d q.(pv_decls) -> In u q.(pv_unreachable) ->
    In (pv_edge (fst d) u) (pv_facts q) -> In None (pv_facts q).
Proof.
  intros hd hu h. apply (pv_fact_closed q ([pv_edge (fst d) u], None)).
  - pv_rule_arm 4. apply in_flat_map. exists d; split; [exact hd|]. apply in_map_iff. now exists u.
  - intros f [<-|[]]. exact h.
Qed.

Definition pv_shape_value (s : TypeSpace) (rho : nat -> s.(SpaceType))
    (d : pv_shape) : s.(SpaceType) :=
  match d with
  | pv_shape_any => s.(stany)
  | pv_shape_interface i a => s.(stinterface) i (fun p => rho (a p))
  end.

Record pv_models (s : TypeSpace) (rho : nat -> s.(SpaceType)) (q : pv_problem) : SProp := {
  pv_models_edges : forall x y, In (x,y) q.(pv_edges) ->
    s.(SubSpaceType) (rho x) (rho y);
  pv_models_decls : forall x d, In (x,d) q.(pv_decls) ->
    AndS (s.(SubSpaceType) (rho x) (pv_shape_value s rho d))
         (s.(SubSpaceType) (pv_shape_value s rho d) (rho x));
  pv_models_ur : forall x, In x q.(pv_unreachable) -> s.(UnReachable) (rho x)
}.

Arguments pv_models_edges {_ _ _} _ _ _ _.
Arguments pv_models_decls {_ _ _} _ _ _ _.
Arguments pv_models_ur {_ _ _} _ _ _.

Lemma pv_cts_same (s : TypeSpace) (cs : ConsistentTypeSpace s) i a b :
    s.(SubSpaceType) (s.(stinterface) i a) (s.(stinterface) i b) ->
    forall p, Signed s.(SubSpaceType) (variance i p) (a p) (b p).
Proof.
  intros h p. destruct (cs.(ctsinterface) i a i b h) as [e ht].
  specialize (ht p). unfold convert in ht.
  rewrite (pv_interface_uip i i (eqS_eq e) eq_refl) in ht. exact ht.
Qed.

Definition pv_fact_value (s : TypeSpace) (rho : nat -> s.(SpaceType)) f : SProp :=
  match f with
  | None => FalseS
  | Some (x,y) => s.(SubSpaceType) (rho x) (rho y)
  end.

Scheme pv_eq_indS := Induction for eq Sort SProp.

Lemma pv_rule_decompose_sound (s : TypeSpace) (cs : ConsistentTypeSpace s)
    (rho : nat -> s.(SpaceType)) x y d e r :
    In r (pv_decompose (x,d) (y,e)) ->
    s.(SubSpaceType) (pv_shape_value s rho d) (pv_shape_value s rho e) ->
    pv_fact_value s rho (snd r).
Proof.
  destruct d as [|i a], e as [|j b]; cbn [pv_decompose fst snd pv_shape_value];
    intros hr h; try contradiction.
  - destruct hr as [<-|[]]. exact (cs.(ctsanyinterface) _ _ h).
  - destruct (dec_eq i j) as [ij|ij].
    + revert b hr h. destruct ij using pv_eq_indS. intros b hr h. apply in_map_iff in hr. destruct hr as [p [<- _]].
      pose proof (pv_cts_same s cs i _ _ h p) as hp.
      unfold pv_signed_edge. destruct (variance i p); exact hp.
    + destruct hr as [<-|[]]. destruct (cs.(ctsinterface) _ _ _ _ h) as [ij' _].
      exact (false_falseS (ij (eqS_eq ij'))).
Qed.

Lemma pv_rules_sound (s : TypeSpace) (cs : ConsistentTypeSpace s)
    (rho : nat -> s.(SpaceType)) q (model : pv_models s rho q) r :
    In r (pv_rules q) ->
    (forall f, In f (fst r) -> pv_fact_value s rho f) ->
    pv_fact_value s rho (snd r).
Proof.
  intro hrule. unfold pv_rules in hrule. cbv zeta in hrule. repeat rewrite in_app_iff in hrule.
  intro pre. destruct hrule as [he|[hr|[ht|[hd|hu]]]].
  - apply in_map_iff in he. destruct he as [[x y] [<- h]].
    exact (model.(pv_models_edges) x y h).
  - apply in_map_iff in hr. destruct hr as [x [<- _]]. apply s.(sstrefl).
  - apply in_flat_map in ht. destruct ht as [x [_ ht]].
    apply in_flat_map in ht. destruct ht as [y [_ ht]].
    apply in_map_iff in ht. destruct ht as [z [<- _]].
    exact (s.(ssttrans) _ _ _ (pre _ (or_introl eq_refl)) (pre _ (or_intror (or_introl eq_refl)))).
  - apply in_flat_map in hd. destruct hd as [[x d] [hd he]].
    apply in_flat_map in he. destruct he as [[y e] [he hr]].
    assert (hp : forall f, In f [pv_edge x y] -> pv_fact_value s rho f).
    { unfold pv_decompose in hr. cbn [fst snd] in hr.
      destruct d as [|i a], e as [|j b]; try contradiction;
        try (destruct (dec_eq i j); [apply in_map_iff in hr; destruct hr as [p [<- _]]|]);
        try (destruct hr as [<-|[]]); exact pre. }
    apply (pv_rule_decompose_sound s cs rho x y d e r hr).
    refine (s.(ssttrans) _ _ _ (model.(pv_models_decls) x d hd).(proj2_AndS) _).
    exact (s.(ssttrans) _ _ _ (hp _ (or_introl eq_refl))
      (model.(pv_models_decls) y e he).(proj1_AndS)).
  - apply in_flat_map in hu. destruct hu as [[x d] [hd hu]].
    apply in_map_iff in hu. destruct hu as [y [<- hy]].
    assert (h : s.(UnReachable) (pv_shape_value s rho d)).
    { refine (s.(sstur) _ _ (s.(ssttrans) _ _ _
        (model.(pv_models_decls) x d hd).(proj2_AndS) (pre _ (or_introl eq_refl))) _).
      exact (model.(pv_models_ur) y hy). }
    destruct d; [exact (cs.(ctsanyunreachable) h)|exact (cs.(ctsinterfaceunreachable) _ _ h)].
Qed.

Lemma pv_facts_sound (s : TypeSpace) (cs : ConsistentTypeSpace s)
    (rho : nat -> s.(SpaceType)) q (model : pv_models s rho q) f :
    In f (pv_facts q) -> pv_fact_value s rho f.
Proof.
  apply pv_close_sound; [apply (pv_rules_sound s cs rho q model)|intros ? []].
Qed.

Lemma pv_node_edge q x y :
    In (x,y) q.(pv_edges) -> In x (pv_nodes q) /\ In y (pv_nodes q).
Proof.
  intro h. split; unfold pv_nodes; apply in_or_app; left;
    apply in_flat_map; exists (x,y); split; [exact h|cbn; tauto|exact h|cbn; tauto].
Qed.

Lemma pv_node_decl q x d : In (x,d) q.(pv_decls) -> In x (pv_nodes q).
Proof.
  intro h. unfold pv_nodes. apply in_or_app; right. apply in_or_app; left.
  apply in_flat_map. exists (x,d). split; [exact h|now left].
Qed.

Lemma pv_node_child q x i a (p : param i) :
    In (x,pv_shape_interface i a) q.(pv_decls) -> In (a p) (pv_nodes q).
Proof.
  intro h. unfold pv_nodes. apply in_or_app; right. apply in_or_app; left.
  apply in_flat_map. exists (x,pv_shape_interface i a). split; [exact h|].
  right. apply in_map, pv_flist_in.
Qed.

Lemma pv_close_origin n rules facts f : In f (pv_close n rules facts) ->
    In f facts \/ In f (map snd rules).
Proof.
  revert facts. induction n as [|n IH]; intros facts h; [now left|].
  cbn in h. destruct (find (pv_ready facts) rules) as [r|] eqn:e; [|now left].
  destruct (IH _ h) as [[<-|h']|h']; [right|now left|now right].
  apply in_map. apply find_some in e. exact (proj1 e).
Qed.

Lemma pv_fact_nodes q x y :
    In (pv_edge x y) (pv_facts q) -> In x (pv_nodes q) /\ In y (pv_nodes q).
Proof.
  unfold pv_facts. intro h. apply pv_close_origin in h. destruct h as [[]|h].
  unfold pv_rules in h. cbv zeta in h.
  repeat rewrite map_app, in_app_iff in h.
  destruct h as [he|[hr|[ht|[hd|hu]]]];
    (apply in_map_iff in he || apply in_map_iff in hr ||
     apply in_map_iff in ht || apply in_map_iff in hd || apply in_map_iff in hu).
  - destruct he as [r [er hr]]. apply in_map_iff in hr.
    destruct hr as [[x' y'] [<- hxy]]. inversion er; subst. now apply pv_node_edge.
  - destruct hr as [r [er hr]]. apply in_map_iff in hr.
    destruct hr as [z [<- hz]]. apply nodup_In in hz. inversion er; subst; auto.
  - destruct ht as [r [er hr]]. apply in_flat_map in hr.
    destruct hr as [x' [hx hr]]. apply nodup_In in hx. apply in_flat_map in hr.
    destruct hr as [y' [_ hr]]. apply in_map_iff in hr.
    destruct hr as [z [<- hz]]. apply nodup_In in hz. inversion er; subst; auto.
  - destruct hd as [r [er hr]]. apply in_flat_map in hr.
    destruct hr as [[x' d] [hd hr]]. apply in_flat_map in hr.
    destruct hr as [[y' e] [he hr]].
    unfold pv_decompose in hr; cbn [fst snd] in hr.
    destruct d as [|i a], e as [|j b]; try contradiction.
    + destruct hr as [<-|[]]; discriminate.
    + destruct (dec_eq i j) as [ij|ij].
      * subst j. apply in_map_iff in hr. destruct hr as [p [<- _]].
        unfold pv_signed_edge in er. destruct (variance i p); inversion er; subst;
          split; eapply pv_node_child; eassumption.
      * destruct hr as [<-|[]]; discriminate.
  - destruct hu as [r [er hr]]. apply in_flat_map in hr.
    destruct hr as [d [_ hr]]. apply in_map_iff in hr.
    destruct hr as [u [<- _]]. discriminate.
Qed.

(* At each depth, a node is the join of the declared shapes below it.
   Those shapes are interpreted using the solution at the preceding depth. *)

Definition pv_lower q x : list pv_decl :=
  filter (fun d => pv_has (pv_facts q) (pv_edge (fst d) x)) q.(pv_decls).

Lemma pv_lower_in q x d :
    In d (pv_lower q x) <-> In d q.(pv_decls) /\ In (pv_edge (fst d) x) (pv_facts q).
Proof. unfold pv_lower. now rewrite filter_In, pv_has_spec. Qed.

Definition pv_joins L {A} (f : A -> L.(pv_carrier)) (xs : list A) : L.(pv_carrier) :=
  fold_right (fun x acc => L.(pv_join) (f x) acc) L.(pv_bot) xs.

Lemma pv_joins_member L {A} f (xs : list A) x :
    In x xs -> L.(pv_le) (f x) (pv_joins L f xs).
Proof.
  induction xs as [|a xs IH]; [contradiction|].
  intros [<-|h]; cbn; [apply pv_join_l|].
  eapply pv_trans; [now apply IH|apply pv_join_r].
Qed.

Lemma pv_joins_bound L {A} f (xs : list A) t :
    (forall x, In x xs -> L.(pv_le) (f x) t) -> L.(pv_le) (pv_joins L f xs) t.
Proof.
  induction xs as [|a xs IH]; intro h; cbn; [apply pv_bot_le|].
  apply pv_join_le; [apply h; now left|].
  apply IH. intros x hx. apply h. now right.
Qed.

Definition pv_shape_at n (f : nat -> (pv_approx n).(pv_carrier))
    (d : pv_shape) : (pv_approx (S n)).(pv_carrier) :=
  match d with
  | pv_shape_any => pv_any
  | pv_shape_interface i a => pv_interface i (fun p => f (a p))
  end.

Fixpoint pv_at (q : pv_problem) n : nat -> (pv_approx n).(pv_carrier) :=
  match n as k return nat -> (pv_approx k).(pv_carrier) with
  | 0 => fun _ => tt
  | S k => fun x =>
      pv_joins (pv_approx (S k)) (fun d => pv_shape_at k (pv_at q k) (snd d))
        (pv_lower q x)
  end.

Lemma pv_at_edge q n x y :
    In (pv_edge x y) (pv_facts q) ->
    (pv_approx n).(pv_le) (pv_at q n x) (pv_at q n y).
Proof.
  intro h. destruct n as [|n]; [exact I|].
  change ((pv_approx (S n)).(pv_le)
    (pv_joins _ (fun d => pv_shape_at n (pv_at q n) (snd d)) (pv_lower q x))
    (pv_joins _ (fun d => pv_shape_at n (pv_at q n) (snd d)) (pv_lower q y))).
  apply pv_joins_bound. intros [z d] hz. apply (pv_joins_member (pv_approx (S n)) (fun d => pv_shape_at n (pv_at q n) (snd d)) _ (z,d)).
  apply pv_lower_in in hz. destruct hz as [hd hzx]. apply pv_lower_in. split; [exact hd|].
  destruct (pv_fact_nodes _ _ _ h) as [hx hy].
  eapply pv_fact_trans; [eapply pv_node_decl; exact hd|exact hx|exact hy|exact hzx|exact h].
Qed.

Lemma pv_at_shape q (good : ~ In None (pv_facts q)) n x d :
    In (x,d) q.(pv_decls) ->
    (pv_approx (S n)).(pv_le) (pv_at q (S n) x) (pv_shape_at n (pv_at q n) d) /\
    (pv_approx (S n)).(pv_le) (pv_shape_at n (pv_at q n) d) (pv_at q (S n) x).
Proof.
  intro hd. split.
  - change ((pv_approx (S n)).(pv_le)
      (pv_joins _ (fun d => pv_shape_at n (pv_at q n) (snd d)) (pv_lower q x)) (pv_shape_at n (pv_at q n) d)).
    apply pv_joins_bound. intros [y e] he. apply pv_lower_in in he.
    destruct he as [he hyx].
    assert (rule : forall f, In ([pv_edge y x], f) (pv_decompose (y,e) (x,d)) ->
        In f (pv_facts q)).
    { intros f hf. exact (pv_fact_decompose q (y,e) (x,d) f he hd hf hyx). }
    destruct e as [|i a], d as [|j b]; try exact I.
    + exfalso. apply good, rule. now left.
    + destruct (dec_eq i j) as [ij|ij].
      * subst j. apply pv_layer_same. intro p.
        assert (hp : In (pv_signed_edge i p (a p) (b p)) (pv_facts q)).
        { apply rule. cbn [pv_decompose fst snd]. destruct (dec_eq i i) as [e|ne].
          - rewrite (pv_interface_uip i i e eq_refl). apply in_map_iff.
            exists p. split; [reflexivity|apply pv_flist_in].
          - contradiction ne; reflexivity. }
        unfold pv_signed_edge in hp. unfold pv_signed_le. destruct (variance i p);
          now apply pv_at_edge.
      * exfalso. apply good, rule. cbn [pv_decompose fst snd].
        destruct (dec_eq i j); [contradiction|now left].
  - change ((pv_approx (S n)).(pv_le) (pv_shape_at n (pv_at q n) (snd (x,d)))
      (pv_joins _ (fun d => pv_shape_at n (pv_at q n) (snd d)) (pv_lower q x))).
    apply (pv_joins_member (pv_approx (S n)) (fun d => pv_shape_at n (pv_at q n) (snd d)) _ (x,d)). apply pv_lower_in. split; [exact hd|].
    apply pv_fact_refl. eapply pv_node_decl. exact hd.
Qed.

Lemma pv_at_ur q (good : ~ In None (pv_facts q)) n x :
    In x q.(pv_unreachable) -> pv_at q n x = (pv_approx n).(pv_bot).
Proof.
  intros hx. destruct n as [|n]; [reflexivity|].
  assert (h : pv_lower q x = nil).
  { destruct (pv_lower q x) as [|d ds] eqn:e; [reflexivity|].
    assert (hd : In d (pv_lower q x)) by (rewrite e; now left).
    apply pv_lower_in in hd. destruct hd as [hd hedge].
    exfalso. apply good. exact (pv_fact_unreachable q d x hd hx hedge). }
  cbn [pv_at]. rewrite h. reflexivity.
Qed.

Lemma pv_at_models q (good : ~ In None (pv_facts q)) :
    pv_models pv_space (fun x n => pv_at q n x) q.
Proof.
  constructor.
  - intros x y h. constructor. intro n. apply pv_at_edge, pv_fact_edge, h.
  - intros x d h. constructor; constructor; intros [|n]; try exact I.
    + destruct d; exact (proj1 (pv_at_shape q good n x _ h)).
    + destruct d; exact (proj2 (pv_at_shape q good n x _ h)).
  - intros x h. constructor. intro n. now apply pv_at_ur.
Qed.

Definition pv_problem_test q :
    SplitS (fun rho => pv_models pv_space rho q)
      (forall s (rho : nat -> s.(SpaceType)), ConsistentTypeSpace s -> pv_models s rho q -> FalseS).
Proof.
  destruct (in_dec pv_fact_eq None (pv_facts q)) as [bad|good].
  - apply split_forall. intros s rho cs model. exact (pv_facts_sound s cs rho q model None bad).
  - apply (split_exists (fun x n => pv_at q n x)). exact (pv_at_models q good).
Defined.


(* Formula binders reserve a finite block of node numbers. The formula
   variables are scoped by sums, so separate subformulas can use independent
   bindings even when their free variables are shared. *)

Record pv_slots (A : Type) := {
  pv_width : nat;
  pv_index : A -> nat;
  pv_lookup : nat -> option A;
  pv_index_bound : forall a, pv_index a < pv_width;
  pv_lookup_index : forall a, pv_lookup (pv_index a) = Some a
}.

Arguments pv_width {_} _.
Arguments pv_index {_} _ _.
Arguments pv_lookup {_} _ _.
Arguments pv_index_bound {_} _ _.
Arguments pv_lookup_index {_} _ _.

Fixpoint pv_find_index {A} (d : DecEq A) (a : A) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: xs => if d a x then 0 else S (pv_find_index d a xs)
  end.

Lemma pv_find_index_ok {A} d (a : A) xs :
    In a xs -> nth_error xs (pv_find_index d a xs) = Some a.
Proof.
  induction xs as [|x xs IH]; [contradiction|].
  intro h. cbn [pv_find_index]. destruct (d a x) as [<-|ne]; [reflexivity|].
  cbn. apply IH. destruct h; congruence.
Qed.

Definition pv_list_slots {A} (d : DecEq A) (xs : list A) (all : forall a, In a xs) :
    pv_slots A.
Proof.
  refine {| pv_width := length xs; pv_index a := pv_find_index d a xs;
    pv_lookup := nth_error xs; pv_lookup_index a := pv_find_index_ok d a xs (all a) |}.
  intro a. apply nth_error_Some. rewrite (pv_find_index_ok d a xs (all a)). discriminate.
Defined.

Definition pv_finite_slots {A} (F : Finite A) : pv_slots A :=
  pv_list_slots dec_eq (flist (fun a : A => a)) pv_flist_in.

Definition pv_one_slot : pv_slots unit.
Proof.
  refine {| pv_width := 1; pv_index := fun _ : unit => 0;
    pv_lookup := fun _ => Some tt |}.
  - intros []; apply Nat.lt_0_succ.
  - now intros [].
Defined.

Inductive pv_form | {A : Type} : Type :=
| pv_true : pv_form
| pv_false : pv_form
| pv_sub (x y : A) : pv_form
| pv_is_any (x : A) : pv_form
| pv_is_interface (x : A) (i : iface) (a : param i -> A) : pv_form
| pv_is_ur (x : A) : pv_form
| pv_and (f g : pv_form) : pv_form
| pv_or (f g : pv_form) : pv_form
| pv_bind (B : Type) (slots : pv_slots B) (f : @pv_form (B + A)) : pv_form.

Arguments pv_form : clear implicits.
Arguments pv_true {_}.
Arguments pv_false {_}.
Arguments pv_sub {_} _ _.
Arguments pv_is_any {_} _.
Arguments pv_is_interface {_} _ _ _.
Arguments pv_is_ur {_} _.
Arguments pv_and {_} _ _.
Arguments pv_or {_} _ _.
Arguments pv_bind {_ _} _ _.

Definition pv_extend {A B T} (left : B -> T) (right : A -> T) (x : B + A) : T :=
  match x with inl b => left b | inr a => right a end.

Definition pv_equiv (s : TypeSpace) (x y : s.(SpaceType)) : SProp :=
  AndS (s.(SubSpaceType) x y) (s.(SubSpaceType) y x).

Lemma pv_equiv_refl s x : pv_equiv s x x.
Proof. constructor; apply s.(sstrefl). Qed.

Lemma pv_equiv_sym s x y : pv_equiv s x y -> pv_equiv s y x.
Proof. intros [h k]; now constructor. Qed.

Lemma pv_equiv_trans s x y z : pv_equiv s x y -> pv_equiv s y z -> pv_equiv s x z.
Proof. intros [h1 h2] [h3 h4]; constructor; eapply s.(ssttrans); eassumption. Qed.

Lemma pv_equiv_interface s i a b :
    (forall p, pv_equiv s (a p) (b p)) ->
    pv_equiv s (s.(stinterface) i a) (s.(stinterface) i b).
Proof.
  intro h. constructor; apply s.(sstvariance); intro p;
    specialize (h p); destruct h; unfold Signed; destruct (variance i p); assumption.
Qed.

Lemma pv_sub_equiv s x x' y y' : pv_equiv s x x' -> pv_equiv s y y' ->
    s.(SubSpaceType) x y -> s.(SubSpaceType) x' y'.
Proof. intros [h1 h2] [h3 h4] h. eapply s.(ssttrans); [exact h2|].
  eapply s.(ssttrans); [exact h|exact h3]. Qed.

Fixpoint pv_holds (s : TypeSpace) {A} (f : pv_form A) (rho : A -> s.(SpaceType)) : SProp :=
  match f with
  | pv_true => TrueS
  | pv_false => FalseS
  | pv_sub x y => s.(SubSpaceType) (rho x) (rho y)
  | pv_is_any x => pv_equiv s (rho x) s.(stany)
  | pv_is_interface x i a => pv_equiv s (rho x) (s.(stinterface) i (fun p => rho (a p)))
  | pv_is_ur x => s.(UnReachable) (rho x)
  | pv_and f g => AndS (pv_holds s f rho) (pv_holds s g rho)
  | pv_or f g => OrS (pv_holds s f rho) (pv_holds s g rho)
  | @pv_bind _ B _ f => existsTS values : B -> s.(SpaceType),
      pv_holds s f (pv_extend values rho)
  end.

Lemma pv_holds_equiv s A (f : pv_form A) rho rho' :
    (forall a, pv_equiv s (rho a) (rho' a)) -> pv_holds s f rho -> pv_holds s f rho'.
Proof.
  revert rho rho'. induction f; intros rho rho' hr h; cbn in *; try exact h.
  - eapply pv_sub_equiv; [apply hr|apply hr|exact h].
  - eapply pv_equiv_trans; [apply pv_equiv_sym, hr|exact h].
  - eapply pv_equiv_trans; [apply pv_equiv_sym, hr|].
    eapply pv_equiv_trans; [exact h|]. apply pv_equiv_interface. intro p. apply hr.
  - refine (s.(sstur) _ _ (hr x).(proj2_AndS) h).
  - destruct h; constructor; [eapply IHf1|eapply IHf2]; eassumption.
  - destruct h; [left; eapply IHf1|right; eapply IHf2]; eassumption.
  - destruct h as [v h]. exists v. eapply IHf; [|exact h].
    intros [b|a]; [apply pv_equiv_refl|apply hr].
Qed.

Definition pv_agree {T} n (rho rho' : nat -> T) :=
  forall x, x < n -> rho x = rho' x.

Definition pv_empty_problem : pv_problem :=
  {| pv_edges := []; pv_decls := []; pv_unreachable := [] |}.

Definition pv_append_problem q r : pv_problem :=
  {| pv_edges := q.(pv_edges) ++ r.(pv_edges);
     pv_decls := q.(pv_decls) ++ r.(pv_decls);
     pv_unreachable := q.(pv_unreachable) ++ r.(pv_unreachable) |}.

Definition pv_sub_problem x y : pv_problem :=
  {| pv_edges := [(x,y)]; pv_decls := []; pv_unreachable := [] |}.

Definition pv_decl_problem x d : pv_problem :=
  {| pv_edges := []; pv_decls := [(x,d)]; pv_unreachable := [] |}.

Definition pv_ur_problem x : pv_problem :=
  {| pv_edges := []; pv_decls := []; pv_unreachable := [x] |}.

Definition pv_flat_extend {A B} (slots : pv_slots B) n (env : A -> nat) : B + A -> nat :=
  pv_extend (fun b => n + pv_index slots b) env.

Definition pv_flat_values {B T} (slots : pv_slots B) n
    (rho : nat -> T) (values : B -> T) : nat -> T :=
  fun x => if n <=? x then
    match pv_lookup slots (x - n) with Some b => values b | None => rho x end
  else rho x.

Lemma pv_flat_values_old {B T} (slots : pv_slots B) n (rho : nat -> T) values :
    pv_agree n rho (pv_flat_values slots n rho values).
Proof.
  intros x hx. unfold pv_flat_values. destruct (n <=? x) eqn:e; [|reflexivity].
  apply Nat.leb_le in e. exfalso. exact (Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ hx e)).
Qed.

Lemma pv_flat_values_new {B T} (slots : pv_slots B) n (rho : nat -> T) values b :
    pv_flat_values slots n rho values (n + pv_index slots b) = values b.
Proof.
  unfold pv_flat_values.
  assert (e : (n <=? n + pv_index slots b) = true) by (apply Nat.leb_le, Nat.le_add_r).
  rewrite e, Nat.add_comm, Nat.add_sub, pv_lookup_index. reflexivity.
Qed.

Fixpoint pv_flat {A} (f : pv_form A) (env : A -> nat) n : list (pv_problem * nat) :=
  match f with
  | pv_true => [(pv_empty_problem,n)]
  | pv_false => []
  | pv_sub x y => [(pv_sub_problem (env x) (env y),n)]
  | pv_is_any x => [(pv_decl_problem (env x) pv_shape_any,n)]
  | pv_is_interface x i a =>
      [(pv_decl_problem (env x) (pv_shape_interface i (fun p => env (a p))),n)]
  | pv_is_ur x => [(pv_ur_problem (env x),n)]
  | pv_and f g => flat_map (fun '(q,k) =>
      map (fun '(r,l) => (pv_append_problem q r,l)) (pv_flat g env k)) (pv_flat f env n)
  | pv_or f g => pv_flat f env n ++ pv_flat g env n
  | pv_bind slots f => pv_flat f (pv_flat_extend slots n env) (n + pv_width slots)
  end.

Lemma pv_nodes_append q r x :
    In x (pv_nodes (pv_append_problem q r)) <-> In x (pv_nodes q) \/ In x (pv_nodes r).
Proof.
  unfold pv_nodes, pv_append_problem. cbn [pv_edges pv_decls pv_unreachable].
  repeat rewrite flat_map_app. repeat rewrite in_app_iff. tauto.
Qed.

Lemma pv_flat_extend_bound {A B} (slots : pv_slots B) n (env : A -> nat) :
    (forall a, env a < n) -> forall a, pv_flat_extend slots n env a < n + pv_width slots.
Proof.
  intros h [b|a]; cbn [pv_flat_extend pv_extend].
  - apply Nat.add_lt_mono_l, pv_index_bound.
  - eapply Nat.lt_le_trans; [apply h|apply Nat.le_add_r].
Qed.

Lemma pv_flat_bound A (f : pv_form A) env n q k :
    (forall a, env a < n) -> In (q,k) (pv_flat f env n) ->
    n <= k /\ forall x, In x (pv_nodes q) -> x < k.
Proof.
  revert env n q k. induction f; intros env n q k hen hh; cbn [pv_flat] in hh.
  - destruct hh as [e|[]]. inversion e; subst. split; [reflexivity|intros x []].
  - contradiction.
  - destruct hh as [e|[]]. inversion e; subst. split; [reflexivity|].
    intros z [e'|[e'|[]]]; subst z; apply hen.
  - destruct hh as [e|[]]. inversion e; subst. split; [reflexivity|].
    intros z [<-|[]]; apply hen.
  - destruct hh as [e|[]]. inversion e; subst. split; [reflexivity|].
    intros z [<-|hz]; [apply hen|].
    rewrite in_app_iff in hz. destruct hz as [hz|[]].
    cbn [flat_map pv_children snd] in hz. rewrite app_nil_r in hz.
    apply in_map_iff in hz. destruct hz as [p [<- _]]. apply hen.
  - destruct hh as [e|[]]. inversion e; subst. split; [reflexivity|].
    intros z [<-|[]]; apply hen.
  - apply in_flat_map in hh. destruct hh as [[r j] [hr hh]].
    apply in_map_iff in hh. destruct hh as [[u l] [e hu]]. inversion e; subst.
    destruct (IHf1 _ _ _ _ hen hr) as [hj hbr].
    destruct (IHf2 _ _ _ _ (fun a => Nat.lt_le_trans _ _ _ (hen a) hj) hu) as [hl hbu].
    split; [eapply Nat.le_trans; eassumption|].
    intros x hx. apply pv_nodes_append in hx. destruct hx.
    + eapply Nat.lt_le_trans; [now apply hbr|exact hl].
    + now apply hbu.
  - apply in_app_iff in hh. destruct hh; [eapply IHf1|eapply IHf2]; eassumption.
  - destruct (IHf _ _ _ _ (pv_flat_extend_bound slots n env hen) hh) as [le h].
    split; [eapply Nat.le_trans; [apply Nat.le_add_r|exact le]|exact h].
Qed.

Lemma pv_models_append s rho q r :
    (pv_models s rho (pv_append_problem q r) ->
      AndS (pv_models s rho q) (pv_models s rho r))%type.
Proof.
  intro h. constructor; constructor.
  - intros x y hx. apply h.(pv_models_edges), in_or_app. now left.
  - intros x d hx. apply h.(pv_models_decls), in_or_app. now left.
  - intros x hx. apply h.(pv_models_ur), in_or_app. now left.
  - intros x y hx. apply h.(pv_models_edges), in_or_app. now right.
  - intros x d hx. apply h.(pv_models_decls), in_or_app. now right.
  - intros x hx. apply h.(pv_models_ur), in_or_app. now right.
Qed.

Lemma pv_models_combine s rho q r :
    pv_models s rho q -> pv_models s rho r -> pv_models s rho (pv_append_problem q r).
Proof.
  intros hq hr. constructor.
  - intros x y h. apply in_app_iff in h. destruct h; [apply hq.(pv_models_edges)|apply hr.(pv_models_edges)]; assumption.
  - intros x d h. apply in_app_iff in h. destruct h; [apply hq.(pv_models_decls)|apply hr.(pv_models_decls)]; assumption.
  - intros x h. apply in_app_iff in h. destruct h; [apply hq.(pv_models_ur)|apply hr.(pv_models_ur)]; assumption.
Qed.

Lemma pv_models_agree s rho rho' q k :
    pv_agree k rho rho' -> (forall x, In x (pv_nodes q) -> x < k) ->
    pv_models s rho q -> pv_models s rho' q.
Proof.
  intros agr bound h. constructor.
  - intros x y he. destruct (pv_node_edge _ _ _ he) as [hx hy].
    rewrite <- (agr x (bound x hx)), <- (agr y (bound y hy)).
    now apply h.(pv_models_edges).
  - intros x d hd. rewrite <- (agr x (bound _ (pv_node_decl _ _ _ hd))).
    eapply pv_equiv_trans; [exact (h.(pv_models_decls) x d hd)|].
    destruct d as [|i a]; [apply pv_equiv_refl|].
    apply pv_equiv_interface. intro p.
    rewrite (agr _ (bound _ (pv_node_child _ _ _ _ p hd))). apply pv_equiv_refl.
  - intros x hx. rewrite <- (agr x); [now apply h.(pv_models_ur)|].
    apply bound. unfold pv_nodes. apply in_or_app; right. apply in_or_app; now right.
Qed.

Lemma pv_flat_sound s A (f : pv_form A) env n q k rho :
    In (q,k) (pv_flat f env n) -> pv_models s rho q ->
    pv_holds s f (fun a => rho (env a)).
Proof.
  revert env n q k. induction f; intros env n q k hh hq; cbn [pv_flat] in hh; cbn [pv_holds].
  - constructor.
  - contradiction.
  - destruct hh as [e|[]]. inversion e; subst. apply hq.(pv_models_edges). now left.
  - destruct hh as [e|[]]. inversion e; subst. apply (hq.(pv_models_decls) _ pv_shape_any). now left.
  - destruct hh as [e|[]]. inversion e; subst.
    apply (hq.(pv_models_decls) _ (pv_shape_interface i (fun p => env (a p)))). now left.
  - destruct hh as [e|[]]. inversion e; subst. apply hq.(pv_models_ur). now left.
  - apply in_flat_map in hh. destruct hh as [[r j] [hr hh]].
    apply in_map_iff in hh. destruct hh as [[u l] [e hu]]. inversion e; subst.
    destruct (pv_models_append s rho r u hq) as [h1 h2].
    constructor; [eapply IHf1|eapply IHf2]; eassumption.
  - apply in_app_iff in hh. destruct hh; [left; eapply IHf1|right; eapply IHf2]; eassumption.
  - exists (fun b => rho (n + pv_index slots b)).
    eapply (pv_holds_equiv s _ f (fun a => rho (pv_flat_extend slots n env a))); [intros [b|a]; apply pv_equiv_refl|].
    eapply IHf. exact hh. exact hq.
Qed.

Definition pv_flat_witness s A (f : pv_form A) env n (rho : nat -> s.(SpaceType)) : SProp :=
  existsTSS rk : pv_problem * nat, Squash (In rk (pv_flat f env n)) &
    (existsTSS vals : nat -> s.(SpaceType), Squash (pv_agree n rho vals) & pv_models s vals (fst rk)).

Local Ltac pv_flat_atomic n rho :=
  eapply ex_introSSS with (t := (_,n)); [constructor; now left|];
  eapply ex_introSSS with (t := rho); [constructor; unfold pv_agree; intros; reflexivity|];
  constructor; intros; try contradiction.

Lemma pv_flat_complete s A (f : pv_form A) env n (rho : nat -> s.(SpaceType)) :
    (forall a, env a < n) -> pv_holds s f (fun a => rho (env a)) ->
    pv_flat_witness s A f env n rho.
Proof.
  revert env n rho. induction f; intros env n rho bound h; cbn [pv_holds] in h;
    unfold pv_flat_witness; cbn [pv_flat].
  - pv_flat_atomic n rho.
  - destruct h.
  - pv_flat_atomic n rho. match goal with e : In _ _ |- _ => destruct e as [e|[]]; inversion e; subst end. exact h.
  - pv_flat_atomic n rho. match goal with e : In _ _ |- _ => destruct e as [e|[]]; inversion e; subst end. exact h.
  - pv_flat_atomic n rho. match goal with e : In _ _ |- _ => destruct e as [e|[]]; inversion e; subst end. exact h.
  - pv_flat_atomic n rho. match goal with e : In _ _ |- _ => destruct e as [e|[]]; subst end. exact h.
  - destruct h as [h1 h2].
    destruct (IHf1 env n rho bound h1) as [[q k] [hq] [rho1 [agr1] model1]].
    destruct (pv_flat_bound _ f1 env n q k bound hq) as [nk qb].
    assert (h2' : pv_holds s f2 (fun a => rho1 (env a))).
    { eapply pv_holds_equiv; [intro a; rewrite <- (agr1 _ (bound a)); apply pv_equiv_refl|exact h2]. }
    assert (bound' : forall a, env a < k) by (intro a; eapply Nat.lt_le_trans; [apply bound|exact nk]).
    destruct (IHf2 env k rho1 bound' h2') as [[r l] [hr] [rho2 [agr2] model2]].
    refine (@ex_introSSS _ _ _ (pv_append_problem q r,l) _ _).
    + constructor. apply in_flat_map. exists (q,k); split; [exact hq|].
      apply in_map_iff. now exists (r,l).
    + refine (@ex_introSSS _ _ _ rho2 _ _).
      * constructor. intros x hx. rewrite (agr1 x hx). apply agr2. eapply Nat.lt_le_trans; eassumption.
      * apply pv_models_combine; [eapply pv_models_agree; eassumption|exact model2].
  - destruct h as [h|h].
    + destruct (IHf1 env n rho bound h) as [rk [hr] hm].
      exists rk; [constructor; apply in_or_app; now left|exact hm].
    + destruct (IHf2 env n rho bound h) as [rk [hr] hm].
      exists rk; [constructor; apply in_or_app; now right|exact hm].
  - destruct h as [values h].
    set (rho1 := pv_flat_values slots n rho values).
    assert (h' : pv_holds s f (fun a => rho1 (pv_flat_extend slots n env a))).
    { eapply pv_holds_equiv; [|exact h].
      intros [b|a]; cbn [pv_flat_extend pv_extend].
      - unfold rho1. rewrite pv_flat_values_new. apply pv_equiv_refl.
      - unfold rho1. rewrite <- (pv_flat_values_old slots n rho values _ (bound a)).
        apply pv_equiv_refl. }
    destruct (IHf (pv_flat_extend slots n env) (n + pv_width slots) rho1
      (pv_flat_extend_bound slots n env bound) h') as [rk hr [rho2 [agr2] model]].
    exists rk; [exact hr|]. exists rho2; [|exact model].
    constructor. intros x hx. rewrite (pv_flat_values_old slots n rho values x hx).
    apply agr2. eapply Nat.lt_le_trans; [exact hx|apply Nat.le_add_r].
Qed.

Fixpoint pv_flat_test (xs : list (pv_problem * nat)) :
    SplitS (fun rho => existsTS rk : pv_problem * nat,
        AndS (Squash (In rk xs)) (pv_models pv_space rho (fst rk)))
      (forall s (rho : nat -> s.(SpaceType)) rk,
        In rk xs -> ConsistentTypeSpace s -> pv_models s rho (fst rk) -> FalseS).
Proof.
  destruct xs as [|[q k] xs].
  - apply split_forall. intros s rho rk [].
  - destruct (pv_problem_test q) as [rho model|no].
    + apply (split_exists rho). exists (q,k). constructor; [constructor; now left|exact model].
    + destruct (pv_flat_test xs) as [rho some|none].
      * apply (split_exists rho). destruct some as [rk [[hr] hm]]. exists rk. constructor; [constructor; now right|exact hm].
      * apply split_forall. intros s rho rk [<-|hr] cs hm.
        -- exact (no s rho cs hm).
        -- exact (none s rho rk hr cs hm).
Defined.

Definition pv_closed_test (f : pv_form Empty) :
    DeciderS (existsTSS s : TypeSpace, ConsistentTypeSpace s & pv_holds s f emptye).
Proof.
  destruct (pv_flat_test (pv_flat f (fun x => emptye x) 0)) as [rho some|no].
  - left. destruct some as [rk [[h] m]]. exists pv_space; [apply pv_space_consistent|].
    eapply pv_holds_equiv; [intros a; destruct a|].
    destruct rk as [q k]. exact (pv_flat_sound pv_space _ f _ _ q k rho h m).
  - right. intros [s cs h].
    assert (h' : pv_holds s f (fun a => s.(stany))).
    { eapply pv_holds_equiv; [intros a; destruct a|exact h]. }
    destruct (pv_flat_complete s _ f (fun x => emptye x) 0 (fun _ => s.(stany))
      (fun a => emptye a) h') as [rk [hr] [rho _ hm]].
    exact (no s rho rk hr cs hm).
Defined.


(* Building formulas for signatures and expressions. *)

Fixpoint pv_every {X A} (xs : list X) (f : X -> pv_form A) : pv_form A :=
  match xs with [] => pv_true | x :: xs => pv_and (f x) (pv_every xs f) end.

Fixpoint pv_some {X A} (xs : list X) (f : X -> pv_form A) : pv_form A :=
  match xs with [] => pv_false | x :: xs => pv_or (f x) (pv_some xs f) end.

Lemma pv_every_elim s X A (xs : list X) (f : X -> pv_form A) rho :
    pv_holds s (pv_every xs f) rho -> forall x, In x xs -> pv_holds s (f x) rho.
Proof.
  induction xs as [|a xs IH]; [intros _ x []|].
  intros [ha hs] x [<-|hx]; [exact ha|exact (IH hs x hx)].
Qed.

Lemma pv_every_intro s X A (xs : list X) (f : X -> pv_form A) rho :
    (forall x, In x xs -> pv_holds s (f x) rho) -> pv_holds s (pv_every xs f) rho.
Proof.
  induction xs as [|x xs IH]; intro h; constructor.
  - apply h; now left.
  - apply IH. intros a ha. apply h; now right.
Qed.

Lemma pv_some_elim s X A (xs : list X) (f : X -> pv_form A) rho :
    pv_holds s (pv_some xs f) rho ->
    existsTS x : X, AndS (Squash (In x xs)) (pv_holds s (f x) rho).
Proof.
  induction xs as [|a xs IH]; [intros []|].
  intros [ha|hs].
  - exists a. constructor; [constructor; now left|exact ha].
  - destruct (IH hs) as [x [[hx] h]]. exists x. constructor; [constructor; now right|exact h].
Qed.

Lemma pv_some_intro s X A (xs : list X) (f : X -> pv_form A) rho x :
    In x xs -> pv_holds s (f x) rho -> pv_holds s (pv_some xs f) rho.
Proof.
  induction xs as [|a xs IH]; [contradiction|].
  intros [<-|hx] h; [left; exact h|right; exact (IH hx h)].
Qed.

Definition pv_all_values {X A} (F : Finite X) (f : X -> pv_form A) : pv_form A :=
  pv_every (flist (fun x : X => x)) f.

Lemma pv_all_values_elim s X A (F : Finite X) f rho :
    pv_holds s (@pv_all_values X A F f) rho -> forall x, pv_holds s (f x) rho.
Proof. intros h x. eapply pv_every_elim; [exact h|apply pv_flist_in]. Qed.

Lemma pv_all_values_intro s X A (F : Finite X) f rho :
    (forall x, pv_holds s (f x) rho) -> pv_holds s (@pv_all_values X A F f) rho.
Proof. intros h. apply pv_every_intro. intros x _. apply h. Qed.

Definition pv_one {A} (k : (A -> unit + A) -> unit + A -> pv_form (unit + A)) : pv_form A :=
  pv_bind pv_one_slot (k inr (inl tt)).

Definition pv_signature {A} m
    (k : (A -> unit + (input m + A)) -> (input m -> unit + (input m + A)) ->
      unit + (input m + A) -> pv_form (unit + (input m + A))) : pv_form A :=
  pv_bind (pv_finite_slots (MInput_Finite m))
    (pv_one (fun lift out => k (fun a => lift (inr a)) (fun x => lift (inl x)) out)).

Definition pv_var_signature (s : TypeSpace) {A} m (rho : A -> s.(SpaceType))
    (ins : input m -> A) (out : A) : SpaceMethodSignature s (input m) :=
  {| smsinput := fun x => rho (ins x); smsresult := rho out |}.

Fixpoint pv_type_equal {V A} (t : UserType V) (subst : V -> A) (x : A) : pv_form A :=
  match t with
  | utany => pv_is_any x
  | utvariable v => pv_and (pv_sub x (subst v)) (pv_sub (subst v) x)
  | utinterface i a =>
      pv_bind (pv_finite_slots (IParameter_Finite i))
        (pv_and (pv_is_interface (inr x) i inl)
          (pv_all_values (IParameter_Finite i)
            (fun p => pv_type_equal (a p) (fun v => inr (subst v)) (inl p))))
  end.

Lemma pv_type_equal_sound s V (t : UserType V) :
    forall A (rho : A -> s.(SpaceType)) (subst : V -> A) x,
      pv_holds s (pv_type_equal t subst x) rho ->
      pv_equiv s (rho x) (tsubst (fun v => rho (subst v)) t).
Proof.
  induction t as [v| |i a IH]; intros A rho sub x h; cbn [pv_type_equal pv_holds] in h.
  - exact h.
  - exact h.
  - destruct h as [values [h1 h2]]. eapply pv_equiv_trans; [exact h1|].
    apply pv_equiv_interface. intro p.
    exact (IH p _ (pv_extend values rho) (fun v => inr (sub v)) (inl p)
      (pv_all_values_elim s _ _ (IParameter_Finite i) _ _ h2 p)).
Qed.

Lemma pv_type_equal_complete s V (t : UserType V) :
    forall A (rho : A -> s.(SpaceType)) (subst : V -> A) x,
      pv_equiv s (rho x) (tsubst (fun v => rho (subst v)) t) ->
      pv_holds s (pv_type_equal t subst x) rho.
Proof.
  induction t as [v| |i a IH]; intros A rho sub x h; cbn [pv_type_equal pv_holds].
  - exact h.
  - exact h.
  - exists (fun p => tsubst (fun v => rho (sub v)) (a p)).
    constructor; [exact h|]. apply pv_all_values_intro. intro p.
    apply IH, pv_equiv_refl.
Qed.

Definition pv_signature_equal {A V} m (sig : UserMethodSignature V (input m))
    (sub : V -> A) (ins : input m -> A) (out : A) : pv_form A :=
  pv_and (pv_all_values (MInput_Finite m) (fun x => pv_type_equal (sig.(umsinput) x) sub (ins x)))
    (pv_type_equal sig.(umsresult) sub out).

Record pv_sig_equiv (s : TypeSpace) m
    (a b : SpaceMethodSignature s (input m)) : SProp := {
  pv_sig_in : forall x, pv_equiv s (a.(smsinput) x) (b.(smsinput) x);
  pv_sig_out : pv_equiv s a.(smsresult) b.(smsresult)
}.

Arguments pv_sig_in {_ _ _ _} _ _.
Arguments pv_sig_out {_ _ _ _} _.

Lemma pv_signature_equal_sound s A V m (sig : UserMethodSignature V (input m))
    (sub : V -> A) ins out rho :
    pv_holds s (pv_signature_equal m sig sub ins out) rho ->
    pv_sig_equiv s m (pv_var_signature s m rho ins out) (mssubst (fun v => rho (sub v)) sig).
Proof.
  intros [hi ho]. constructor.
  - intro x. exact (pv_type_equal_sound s V (sig.(umsinput) x) A rho sub (ins x)
      (pv_all_values_elim s _ _ (MInput_Finite m) _ _ hi x)).
  - exact (pv_type_equal_sound s V sig.(umsresult) A rho sub out ho).
Qed.

Lemma pv_signature_equal_complete s A V m (sig : UserMethodSignature V (input m))
    (sub : V -> A) ins out rho :
    pv_sig_equiv s m (pv_var_signature s m rho ins out) (mssubst (fun v => rho (sub v)) sig) ->
    pv_holds s (pv_signature_equal m sig sub ins out) rho.
Proof.
  intro h. constructor.
  - apply pv_all_values_intro. intro x. apply pv_type_equal_complete. exact (h.(pv_sig_in) x).
  - apply pv_type_equal_complete. exact h.(pv_sig_out).
Qed.

Local Notation body_sig i := ((hierarchy.(hinterface) i).(uisbody)).
Local Notation methods i := ((body_sig i).(ubsmethods)).
Local Notation user_sig i m h := ((body_sig i).(ubsmethod) m h).

Definition pv_method_formula {A} m (r : A) (ins : input m -> A) (out : A) : pv_form A :=
  pv_or (pv_is_ur r)
    (pv_some (flist (fun i : iface => i)) (fun i =>
      match pv_contains_dec (methods i) (scpath m) with
      | sbleftS h => pv_bind (pv_finite_slots (IParameter_Finite i))
          (pv_and (pv_is_interface (inr r) i inl)
            (pv_signature_equal m (user_sig i m h) inl (fun x => inr (ins x)) (inr out)))
      | sbrightS _ => pv_false
      end)).

Definition pv_method_shape (s : TypeSpace) m r (sig : SpaceMethodSignature s (input m)) : SProp :=
  OrS (s.(UnReachable) r)
    (existsTS i : iface, existsTS a : param i -> s.(SpaceType),
      existsSS h : SCSetContains (methods i) m,
        AndS (pv_equiv s r (s.(stinterface) i a))
          (pv_sig_equiv s m sig (mssubst a (user_sig i m h)))).

Lemma pv_method_formula_sound s A m (r : A) ins out rho :
    pv_holds s (pv_method_formula m r ins out) rho ->
    pv_method_shape s m (rho r) (pv_var_signature s m rho ins out).
Proof.
  intros [ur|hs]; [now left|right].
  destruct (pv_some_elim _ _ _ _ _ _ hs) as [i [_ h]].
  destruct (pv_contains_dec (methods i) (scpath m)) as [hm|hm]; [|destruct h].
  destruct h as [values [hi ht]]. exists i. exists values. exists hm. constructor; [exact hi|].
  exact (pv_signature_equal_sound s _ _ m (user_sig i m hm) inl _ _ (pv_extend values rho) ht).
Qed.

Lemma pv_method_formula_complete s A m (r : A) ins out rho :
    pv_method_shape s m (rho r) (pv_var_signature s m rho ins out) ->
    pv_holds s (pv_method_formula m r ins out) rho.
Proof.
  intros [ur|hs]; [now left|right].
  destruct hs as [i [a [hm [hi ht]]]].
  eapply pv_some_intro with (x := i); [apply pv_flist_in|].
  destruct (pv_contains_dec (methods i) (scpath m)) as [h|h]; [|exact (h hm)].
  exists a. constructor; [exact hi|].
  apply pv_signature_equal_complete. exact ht.
Qed.

Lemma pv_method_shape_intro s m r sig :
    @CheckMethod s m r sig -> pv_method_shape s m r sig.
Proof.
  intros h. destruct h as [r sig ur|i a hm].
  - now left.
  - right. exists i. exists a. exists hm. constructor; [apply pv_equiv_refl|].
    constructor; intros; apply pv_equiv_refl.
Qed.

Definition pv_method_bound {A} i m (a : param i -> A) (ins : input m -> A) (out : A) :
    pv_form A :=
  match pv_contains_dec (methods i) (scpath m) with
  | sbrightS _ => pv_true
  | sbleftS hm =>
      pv_signature m (fun lift required result =>
        pv_and (pv_signature_equal m (user_sig i m hm) (fun p => lift (a p)) required result)
          (pv_and (pv_all_values (MInput_Finite m) (fun x => pv_sub (required x) (lift (ins x))))
            (pv_sub (lift out) result)))
  end.

Definition pv_matches_body s i m (a : param i -> s.(SpaceType))
    (sig : SpaceMethodSignature s (input m)) : SProp :=
  forall h : SCSetContains (methods i) m,
    SubSpaceMethodSignature sig (mssubst a (user_sig i m h)).

Lemma pv_method_bound_sound s A i m (a : param i -> A) ins out rho :
    pv_holds s (pv_method_bound i m a ins out) rho ->
    pv_matches_body s i m (fun p => rho (a p)) (pv_var_signature s m rho ins out).
Proof.
  unfold pv_method_bound. destruct (pv_contains_dec (methods i) (scpath m)) as [hm|hm].
  - intros [req [res [eqs [hi ho]]]] h.
    pose proof (pv_signature_equal_sound s _ _ m (user_sig i m hm)
      (fun p => inr (inr (a p))) (fun x => inr (inl x)) (inl tt)
      (pv_extend res (pv_extend req rho)) eqs) as he.
    constructor.
    + intro x. eapply s.(ssttrans); [exact (he.(pv_sig_in) x).(proj2_AndS)|].
      exact (pv_all_values_elim s _ _ (MInput_Finite m) _ _ hi x).
    + eapply s.(ssttrans); [exact ho|exact he.(pv_sig_out).(proj1_AndS)].
  - intros _ h. destruct (hm h).
Qed.

Lemma pv_method_bound_complete s A i m (a : param i -> A) ins out rho :
    pv_matches_body s i m (fun p => rho (a p)) (pv_var_signature s m rho ins out) ->
    pv_holds s (pv_method_bound i m a ins out) rho.
Proof.
  unfold pv_method_bound. destruct (pv_contains_dec (methods i) (scpath m)) as [hm|hm].
  - intro h. specialize (h hm).
    exists (fun x => tsubst (fun p => rho (a p)) ((user_sig i m hm).(umsinput) x)).
    exists (fun _ => tsubst (fun p => rho (a p)) (user_sig i m hm).(umsresult)).
    constructor.
    + apply pv_signature_equal_complete. constructor; intros; apply pv_equiv_refl.
    + constructor; [apply pv_all_values_intro; exact h.(ssmsinput)|exact h.(ssmsresult)].
  - intros _. constructor.
Qed.

Definition pv_covers {A} (required actual : SCSet method) : pv_form A :=
  match pv_methods_all required (fun m _ => SCSetContains actual m)
    (fun m _ => pv_contains_dec actual (scpath m)) with
  | sbleftS _ => pv_true
  | sbrightS _ => pv_false
  end.

Lemma pv_covers_sound s A required actual (rho : A -> s.(SpaceType)) :
    pv_holds s (pv_covers required actual) rho ->
    forall m, SCSetContains required m -> SCSetContains actual m.
Proof.
  unfold pv_covers. destruct pv_methods_all as [h|h]; [intros _; exact h|intros []].
Qed.

Lemma pv_covers_complete s A required actual (rho : A -> s.(SpaceType)) :
    (forall m, SCSetContains required m -> SCSetContains actual m) ->
    pv_holds s (pv_covers required actual) rho.
Proof.
  unfold pv_covers. destruct pv_methods_all as [h|h]; [intros _; constructor|exact h].
Qed.

Lemma pv_method_key_inj (ms : SCSet method) (x y : sigS (SCSetContains ms)) :
    x.(proj1_sigS) = y.(proj1_sigS) -> x = y.
Proof. destruct x, y. cbn. intros ->. reflexivity. Qed.

Lemma pv_list_choice A (d : DecEq A) (xs : list A) (D : A -> Type)
    (P : forall a, D a -> SProp) (default : forall a, D a) :
    (forall a, In a xs -> existsTS b : D a, P a b) ->
    existsTS f : forall a, D a, forall a, In a xs -> P a (f a).
Proof.
  induction xs as [|x xs IH]; intro h.
  - exists default. intros a [].
  - destruct (h x (or_introl eq_refl)) as [b hb].
    destruct (IH (fun a ha => h a (or_intror ha))) as [f hf].
    exists (fun a =>
      match d x a with
      | left e => match e with eq_refl => b end
      | right _ => f a
      end).
    intros a ha. destruct (d x a) as [e|ne].
    + destruct e using pv_eq_indS. exact hb.
    + apply hf. destruct ha; congruence.
Qed.

Lemma pv_methods_choice s (ms : SCSet method)
    (P : forall m, SCSetContains ms m -> SpaceMethodSignature s (input m) -> SProp) :
    (forall m h, existsTS sg : SpaceMethodSignature s (input m), P m h sg) ->
    existsTS sigs : (forall m, SCSetContains ms m -> SpaceMethodSignature s (input m)),
      forall m h, P m h (sigs m h).
Proof.
  intro h.
  destruct (pv_list_choice _ (inj_DecEq (@proj1_sigS _ _) (pv_method_key_inj ms))
    (pv_methods ms)
    (fun e => SpaceMethodSignature s (input e.(proj1_sigS)))
    (fun e => P e.(proj1_sigS) e.(proj2_sigS))
    (fun _ => {| smsinput := fun _ => s.(stany); smsresult := s.(stany) |})
    (fun e _ => h e.(proj1_sigS) e.(proj2_sigS))) as [f hf].
  exists (fun m hm => f (@existS _ _ m hm)).
  intros m hm. exact (hf _ (pv_methods_in ms m hm)).
Qed.

Definition pv_expr_code :
    forall I, Expression I -> forall A, (SumSort I -> A) -> A -> pv_form A :=
  fix code I (e : Expression I) :=
    match e return forall A, (SumSort I -> A) -> A -> pv_form A with
    | einput x => fun A ctx out => pv_sub (ctx x) out
    | einvoke r m args => fun A ctx out =>
        pv_signature m (fun lift ins res =>
          pv_and (pv_sub res (lift out))
            (pv_and (pv_all_values (MInput_Finite m) (fun x =>
                code _ (args x) _ (fun v => lift (ctx v)) (ins x)))
              (pv_one (fun lift' recv =>
                pv_and (code _ r _ (fun v => lift' (lift (ctx v))) recv)
                  (pv_method_formula m recv (fun x => lift' (ins x)) (lift' res))))))
    | eobject i ms bodies => fun A ctx out =>
        pv_and (pv_covers (methods i) ms)
          (pv_bind (pv_finite_slots (IParameter_Finite i))
            (pv_and (pv_one (fun lift obj =>
                pv_and (pv_is_interface obj i (fun p => lift (inl p)))
                  (pv_sub obj (lift (inr out)))))
              (pv_every (pv_methods ms) (fun e =>
                let m := e.(proj1_sigS) in
                let h := e.(proj2_sigS) in
                pv_signature m (fun lift ins res =>
                  pv_and (pv_method_bound i m (fun p => lift (inl p)) ins res)
                    (code _ (bodies m h) _
                      (sorte ins (fun v => lift (inr (ctx v)))) res))))))
    end.

Definition pv_expr_check (s : TypeSpace) :
    forall I, Expression I -> (SumSort I -> s.(SpaceType)) -> s.(SpaceType) -> SProp :=
  fix check I (e : Expression I) :=
    match e return (SumSort I -> s.(SpaceType)) -> s.(SpaceType) -> SProp with
    | einput x => fun ctx out => s.(SubSpaceType) (ctx x) out
    | einvoke r m args => fun ctx out =>
        existsTS recv : s.(SpaceType), existsTS sig : SpaceMethodSignature s (input m),
          AndS (@CheckMethod s m recv sig)
            (AndS (check _ r ctx recv)
              (AndS (forall x, check _ (args x) ctx (sig.(smsinput) x))
                (s.(SubSpaceType) sig.(smsresult) out)))
    | eobject i ms bodies => fun ctx out =>
        existsTS a : param i -> s.(SpaceType),
          existsTS sigs : (forall m, SCSetContains ms m -> SpaceMethodSignature s (input m)),
            AndS (SubSpaceBodySignature {| sbsmethods := ms; sbsmethod := sigs |} (bssubst a (body_sig i)))
              (AndS (forall m h, check _ (bodies m h) (sorte (sigs m h).(smsinput) ctx) (sigs m h).(smsresult))
                (s.(SubSpaceType) (s.(stinterface) i a) out))
    end.

Lemma pv_expr_sub s I (e : Expression I) ctx x y :
    pv_expr_check s I e ctx x -> s.(SubSpaceType) x y -> pv_expr_check s I e ctx y.
Proof.
  destruct e; cbn [pv_expr_check].
  - intros h h'. eapply s.(ssttrans); eassumption.
  - intros [recv [sig [hm [hr [ha ho]]]]] h.
    exists recv. exists sig. constructor; [exact hm|].
    constructor; [exact hr|]. constructor; [exact ha|eapply s.(ssttrans); eassumption].
  - intros [a [sigs [hs [hb ho]]]] h.
    exists a. exists sigs. constructor; [exact hs|].
    constructor; [exact hb|eapply s.(ssttrans); eassumption].
Qed.

Lemma pv_expr_ctx s I (e : Expression I) :
    forall ctx ctx' x, (forall v, ctx v = ctx' v) ->
    pv_expr_check s I e ctx x -> pv_expr_check s I e ctx' x.
Proof.
  revert I e. fix IH 2. intros I e ctx ctx' x agr.
  destruct e as [v|r m args|i ms bodies]; cbn [pv_expr_check].
  - rewrite (agr v). exact (fun h => h).
  - intros [recv [sg [hm [hr [ha ho]]]]].
    exists recv. exists sg. constructor; [exact hm|].
    constructor; [eapply IH; eassumption|].
    constructor; [intro a; eapply IH; [exact agr|apply ha]|exact ho].
  - intros [a [sigs [hs [hb ho]]]].
    exists a. exists sigs. constructor; [exact hs|].
    constructor; [|exact ho]. intros m hm. eapply IH; [|apply hb].
    intros [b|v]; [reflexivity|apply agr].
Qed.

Lemma pv_finish_invoke s I (r : Expression I) m args ctx out recv sig :
    pv_method_shape s m recv sig ->
    pv_expr_check s I r ctx recv ->
    (forall x, pv_expr_check s I (args x) ctx (sig.(smsinput) x)) ->
    s.(SubSpaceType) sig.(smsresult) out ->
    pv_expr_check s I (einvoke r m args) ctx out.
Proof.
  intros [ur|hs] hr ha ho.
  - exists recv. exists sig. constructor; [now constructor|].
    exact (@conjS _ _ hr (@conjS _ _ ha ho)).
  - destruct hs as [i [a [hm [he hsg]]]].
    exists (s.(stinterface) i a). exists (mssubst a (user_sig i m hm)).
    constructor; [apply cminterface|]. constructor.
    + eapply pv_expr_sub; [exact hr|exact he.(proj1_AndS)].
    + constructor.
      * intro x. eapply pv_expr_sub; [apply ha|exact (hsg.(pv_sig_in) x).(proj1_AndS)].
      * eapply s.(ssttrans); [exact hsg.(pv_sig_out).(proj2_AndS)|exact ho].
Qed.

Lemma pv_expr_code_sound s I (e : Expression I) :
    forall A (ctx : SumSort I -> A) out (rho : A -> s.(SpaceType)),
      pv_holds s (pv_expr_code I e A ctx out) rho ->
      pv_expr_check s I e (fun v => rho (ctx v)) (rho out).
Proof.
  revert I e. fix IH 2. intros I e A ctx out rho h.
  destruct e as [v|r m args|i ms bodies].
  - exact h.
  - cbn [pv_expr_code pv_signature pv_one pv_holds] in h.
    destruct h as [ins [res [ho [ha [recvs [hr hm]]]]]].
    set (rho' := pv_extend res (pv_extend ins rho)).
    set (rho'' := pv_extend recvs rho').
    refine (pv_finish_invoke s I r m args _ _ (recvs tt)
      (pv_var_signature s m rho' (fun x => inr (inl x)) (inl tt)) _ _ _ ho).
    + exact (pv_method_formula_sound s _ m (inl tt) (fun x => inr (inr (inl x)))
        (inr (inl tt)) rho'' hm).
    + exact (IH I r _ (fun v => inr (inr (inr (ctx v)))) (inl tt) rho'' hr).
    + intro x. apply (IH I (args x) _ (fun v => inr (inr (ctx v))) (inr (inl x)) rho').
      exact (pv_all_values_elim s _ _ (MInput_Finite m) _ _ ha x).
  - cbn [pv_expr_code pv_holds pv_one] in h.
    destruct h as [hc [vals [[obj [hi ho]] hb]]].
    set (env := pv_extend vals rho).
    pose proof (pv_covers_sound s A (methods i) ms rho hc) as cover.
    assert (local_sigs : forall m hm,
        existsTS sg : SpaceMethodSignature s (input m),
          AndS (pv_matches_body s i m vals sg)
            (pv_expr_check s (input m :: I) (bodies m hm)
              (sorte sg.(smsinput) (fun v => rho (ctx v))) sg.(smsresult))).
    { intros m hm.
      pose proof (pv_every_elim s _ _ (pv_methods ms) _ env hb
        (@existS _ _ m hm) (pv_methods_in ms m hm)) as h.
      cbn [pv_signature pv_one pv_holds] in h. destruct h as [ins [res [hs ht]]].
      set (env' := pv_extend res (pv_extend ins env)).
      exists (pv_var_signature s m env' (fun x => inr (inl x)) (inl tt)).
      constructor.
      - exact (pv_method_bound_sound s _ i m (fun p => inr (inr (inl p)))
          (fun x => inr (inl x)) (inl tt) env' hs).
      - eapply pv_expr_ctx; [|exact (IH _ (bodies m hm) _
          (sorte (fun x => inr (inl x)) (fun v => inr (inr (inr (ctx v)))))
          (inl tt) env' ht)].
        intros [x|v]; reflexivity. }
    destruct (pv_methods_choice s ms _ local_sigs) as [sigs hsg].
    exists vals. exists sigs. constructor.
    + refine (@Build_SubSpaceBodySignature s {| sbsmethods := ms; sbsmethod := sigs |}
        (bssubst vals (body_sig i)) cover _).
      intros m hm. exact ((hsg m (cover m hm)).(proj1_AndS) hm).
    + constructor.
      * intros m hm. exact (hsg m hm).(proj2_AndS).
      * eapply s.(ssttrans); [exact hi.(proj2_AndS)|exact ho].
Qed.

Lemma pv_expr_code_complete s I (e : Expression I) :
    forall A (ctx : SumSort I -> A) out (rho : A -> s.(SpaceType)),
      pv_expr_check s I e (fun v => rho (ctx v)) (rho out) ->
      pv_holds s (pv_expr_code I e A ctx out) rho.
Proof.
  revert I e. fix IH 2. intros I e A ctx out rho h.
  destruct e as [v|r m args|i ms bodies].
  - exact h.
  - cbn [pv_expr_check] in h.
    destruct h as [recv [sg [hm [hr [ha ho]]]]].
    cbn [pv_expr_code pv_signature pv_one pv_holds].
    exists sg.(smsinput). exists (fun _ => sg.(smsresult)).
    constructor; [exact ho|]. constructor.
    + apply pv_all_values_intro. intro x.
      exact (IH I (args x) _ (fun v => inr (inr (ctx v))) (inr (inl x))
        (pv_extend (fun _ : unit => sg.(smsresult)) (pv_extend sg.(smsinput) rho)) (ha x)).
    + exists (fun _ => recv). constructor.
      * exact (IH I r _ (fun v => inr (inr (inr (ctx v)))) (inl tt)
          (pv_extend (fun _ : unit => recv)
            (pv_extend (fun _ : unit => sg.(smsresult)) (pv_extend sg.(smsinput) rho))) hr).
      * apply pv_method_formula_complete. apply pv_method_shape_intro.
        destruct sg. exact hm.
  - cbn [pv_expr_check] in h.
    destruct h as [vals [sigs [hs [hb ho]]]].
    cbn [pv_expr_code pv_holds pv_one]. constructor.
    + apply pv_covers_complete. exact hs.(ssbsmethods).
    + exists vals. constructor.
      * exists (fun _ => s.(stinterface) i vals). constructor; [apply pv_equiv_refl|exact ho].
      * apply pv_every_intro. intros [m hm] _.
        cbn [proj1_sigS proj2_sigS pv_signature pv_one pv_holds].
        set (sg := sigs m hm).
        exists sg.(smsinput). exists (fun _ => sg.(smsresult)).
        set (env := pv_extend (fun _ : unit => sg.(smsresult))
          (pv_extend sg.(smsinput) (pv_extend vals rho))).
        constructor.
        -- apply pv_method_bound_complete. intro h. exact (hs.(ssbsmethod) m h).
        -- apply (IH _ (bodies m hm) _
             (sorte (fun x => inr (inl x)) (fun v => inr (inr (inr (ctx v))))) (inl tt) env).
           eapply pv_expr_ctx; [|exact (hb m hm)]. intros [x|v]; reflexivity.
Qed.

Lemma pv_expr_to_check s I (e : Expression I) :
    forall (ctx : SortElimination s.(SpaceType) I) out,
      pv_expr_check s I e (apply_elimination ctx) out -> CheckExpression s ctx e out.
Proof.
  revert I e. fix IH 2. intros I e ctx out h.
  destruct e as [v|r m args|i ms bodies].
  - eapply cesub; [apply ceinput|exact h].
  - destruct h as [recv [sg [hm [hr [ha ho]]]]].
    eapply cesub; [|exact ho]. eapply ceinvoke; [exact hm|apply IH, hr|].
    intro x. apply IH, ha.
  - destruct h as [vals [sigs [hs [hb ho]]]].
    eapply cesub; [|exact ho]. eapply ceobject; [exact hs|].
    intros m hm. apply IH. eapply pv_expr_ctx; [|exact (hb m hm)].
    intros [x|v]; reflexivity.
Qed.

Lemma pv_check_to_expr s :
    forall I (ctx : SortElimination s.(SpaceType) I) e out,
      CheckExpression s ctx e out -> pv_expr_check s I e (apply_elimination ctx) out.
Proof.
  fix IH 5. intros I ctx e out h.
  destruct h as [e t t' h hsub|v|r m args recv sg hm hr ha|i ms bodies vals sigs hs hb].
  - eapply pv_expr_sub; [apply IH, h|exact hsub].
  - apply s.(sstrefl).
  - exists recv. exists sg. constructor; [exact hm|]. constructor; [apply IH, hr|].
    constructor; [intro x; apply IH, ha|apply s.(sstrefl)].
  - exists vals. exists sigs. constructor; [exact hs|]. constructor; [|apply s.(sstrefl)].
    intros m hm. eapply pv_expr_ctx; [|apply IH; apply hb].
    intros [x|v]; reflexivity.
Qed.

Definition pv_program_code (program : Program) : pv_form Empty :=
  pv_one (fun lift result =>
    pv_and (pv_type_equal program.(ptype) (fun v => lift v) result)
      (pv_expr_code nil program.(pexpression) _ (fun v => lift v) result)).

Lemma pv_program_code_sound s program :
    pv_holds s (pv_program_code program) emptye ->
    CheckExpression s nil_elimination program.(pexpression) (tsubst emptye program.(ptype)).
Proof.
  intros [r [ht he]].
  pose proof (pv_type_equal_sound s _ program.(ptype) _ (pv_extend r emptye) inr
    (inl tt) ht) as h.
  apply pv_expr_to_check. eapply pv_expr_sub; [|exact h.(proj1_AndS)].
  exact (pv_expr_code_sound s nil program.(pexpression) _ inr (inl tt)
    (pv_extend r emptye) he).
Qed.

Lemma pv_program_code_complete s program :
    CheckExpression s nil_elimination program.(pexpression) (tsubst emptye program.(ptype)) ->
    pv_holds s (pv_program_code program) emptye.
Proof.
  intro h. exists (fun _ => tsubst emptye program.(ptype)). constructor.
  - apply pv_type_equal_complete, pv_equiv_refl.
  - apply pv_expr_code_complete. exact (pv_check_to_expr s _ _ _ _ h).
Qed.

End ValidityDecision.
Theorem programv_decider
      {Interface_Finite: Finite scheme.(Interface)}
      {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)}
      {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)}
      (program: Program)
    : DeciderS (ProgramV program).
Proof.
  destruct (@pv_hierarchy_test Interface_Finite IParameter_Finite MInput_Finite) as [hv|no].
  - destruct (@pv_closed_test Interface_Finite IParameter_Finite
      (@pv_program_code Interface_Finite IParameter_Finite MInput_Finite program)) as [ok|no].
    + left. constructor; [exact hv|].
      destruct ok as [s cs h]. exists s; [exact cs|].
      exact (@pv_program_code_sound Interface_Finite IParameter_Finite MInput_Finite s program h).
    + right. intro h. apply no. destruct h.(pexpressionv) as [s cs check].
      exists s; [exact cs|].
      exact (@pv_program_code_complete Interface_Finite IParameter_Finite MInput_Finite s program check).
  - right. intro h. exact (no h.(phierarchyv)).
Defined.
