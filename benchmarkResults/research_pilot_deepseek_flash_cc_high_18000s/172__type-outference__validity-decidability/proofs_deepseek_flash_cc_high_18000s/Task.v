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

Import ListNotations.

(* ==== Verified helper infrastructure (enumeration, SProp list/B-tree lemmas,
   UserVariance and HierarchyV deciders) ==== *)

Lemma btappend_In : forall (T : Type) (trunk : BTrunk)
  (f : forall path : BPath, BTContains trunk path -> list T)
  (path : BPath) (c : BTContains trunk path) (x : T),
  In x (f path c) -> In x (btappend trunk f).
Proof.
  intros T trunk.
  induction trunk as [| head first IHfirst second IHsecond]; intros f path c x Hx.
  - exact (falseSe c).
  - destruct path as [| path | path].
    + simpl. destruct head as [|].
      * exact (falseSe c).
      * apply in_or_app. left. exact Hx.
    + simpl. apply in_or_app. right. apply in_or_app. left.
      exact (IHfirst (fun path' => f (bfirst path')) path c x Hx).
    + simpl. apply in_or_app. right. apply in_or_app. right.
      exact (IHsecond (fun path' => f (bsecond path')) path c x Hx).
Qed.

Lemma flist_In : forall {A : Type} `{Finite A} (a : A), In a (flist (fun x : A => x)).
Proof.
  intros A H a.
  unfold flist, fappend.
  set (c := sfcontains a).
  assert (Hin : In (fpath A (scpath a) c) (btappend (sftrunk A) (fun path contains => fpath A path contains :: nil))).
  { apply btappend_In with (path := scpath a) (c := c) (x := fpath A (scpath a) c). apply in_eq. }
  assert (Heq : fpath A (scpath a) c = a).
  { apply scpath_inj. symmetry. apply (eqS_eq (T := BPath)). apply fpath_eqS. }
  rewrite <- Heq. exact Hin.
Qed.


Definition falseSeS {P : SProp} (f : FalseS) : P := match f with end.

Section ListS.
  Context {T : Type}.

  Lemma ListContains_app_l : forall (x : T) (l l' : list T),
    ListContains x l -> ListContains x (app l l').
  Proof.
    intros x l l' H. induction H as [tail | head tail Ht IHt].
    - exact (lchead (app tail l')).
    - exact (lctail head (app tail l') IHt).
  Qed.

  Lemma ListContains_app_r : forall (x : T) (l l' : list T),
    ListContains x l' -> ListContains x (app l l').
  Proof.
    intros x l. induction l as [| a l IH]; intros l' H.
    - simpl. exact H.
    - simpl. apply lctail. apply IH. exact H.
  Qed.

  Lemma ListContains_app_or : forall (x : T) (l l' : list T),
    ListContains x (app l l') -> OrS (ListContains x l) (ListContains x l').
  Proof.
    intros x l l' H.
    remember (app l l') as L eqn:EL.
    revert l l' EL.
    induction H as [tail | head tail Ht IHt]; intros l l' EL.
    - destruct l as [| a l].
      + simpl in EL. subst l'. exact (orightS (lchead tail)).
      + simpl in EL. injection EL as Ha Ht. subst a. exact (oleftS (lchead l)).
    - destruct l as [| a l].
      + simpl in EL. subst l'.
        exact (orightS (lctail head tail Ht)).
      + simpl in EL. injection EL as Ha Hrest. subst a.
        destruct (IHt l l' Hrest) as [Hl | Hr].
        * exact (oleftS (lctail head l Hl)).
        * exact (orightS Hr).
  Qed.
End ListS.

Definition eqS_trans {T : Type} {a b c : T} (e1 : eqS a b) (e2 : eqS b c) : eqS a c.
Proof. destruct e1. destruct e2. exact (eqS_refl a). Defined.

Definition eqS_sym {T : Type} {a b : T} (e : eqS a b) : eqS b a.
Proof. destruct e. exact (eqS_refl a). Defined.

Definition ListContains_nil_absurd {T : Type} {x : T} (H : ListContains x nil) : FalseS
:= match H in ListContains _ l0 return (match l0 with nil => FalseS | cons _ _ => TrueS end) with
   | lchead tail => trueS
   | lctail head tail _ => trueS
   end.


Inductive InB {T : Type} : list T -> T -> SProp :=
| inb_head (x : T) (xs : list T) : InB (x :: xs) x
| inb_tail (x y : T) (xs : list T) : InB xs y -> InB (x :: xs) y.
Arguments InB {_} _ _.

Definition InB_nil_absurd {T : Type} {x : T} (H : InB nil x) : FalseS
:= match H in InB l0 e0 return (match l0 with nil => FalseS | cons _ _ => TrueS end) with
   | inb_head x0 xs => trueS
   | inb_tail x0 y xs _ => trueS
   end.

Definition eqS_subst {T : Type} (P : T -> SProp) {a b : T} (e : eqS a b) : P a -> P b.
Proof. destruct e. exact (fun p => p). Defined.

Definition eqS_subst' {T : Type} (P : T -> SProp) {a b : T} (e : eqS a b) : P b -> P a.
Proof. destruct e. exact (fun p => p). Defined.

Section ListB.
  Context {T : Type}.

  Lemma InB_or : forall (E elem : T) (xs : list T),
    InB (E :: xs) elem -> OrS (eqS elem E) (InB xs elem).
  Proof.
    intros E elem xs H.
    remember (E :: xs) as L eqn:EL.
    revert E xs EL.
    destruct H as [x xs0 | x y xs0 H']; intros E xs EL.
    - injection EL as HE Hxs. subst E. exact (oleftS (eqS_refl x)).
    - injection EL as HE Hxs. subst E. subst xs0. exact (orightS H').
  Qed.

  Lemma InB_app_l : forall (x : T) (l l' : list T), InB l x -> InB (app l l') x.
  Proof.
    intros x l l' H. induction H as [x0 xs | x0 y xs H' IH].
    - exact (inb_head x0 (app xs l')).
    - exact (inb_tail x0 y (app xs l') IH).
  Qed.

  Lemma InB_app_r : forall (x : T) (l l' : list T), InB l' x -> InB (app l l') x.
  Proof.
    intros x l. induction l as [| a l IH]; intros l' H.
    - simpl. exact H.
    - simpl. exact (inb_tail a x (app l l') (IH l' H)).
  Qed.

  Lemma InB_app_or : forall (x : T) (l l' : list T),
    InB (app l l') x -> OrS (InB l x) (InB l' x).
  Proof.
    intros x l. induction l as [| a l IH]; intros l' H.
    - simpl in H. exact (orightS H).
    - simpl in H. apply InB_or in H. destruct H as [Heq | Htail].
      + exact (oleftS (eqS_subst' (fun z => InB (a :: l) z) Heq (inb_head a l))).
      + destruct (IH l' Htail) as [Hl | Hr].
        * left. exact (inb_tail a x l Hl).
        * right. exact Hr.
  Qed.
End ListB.


Lemma ListForallS_In : forall (T : Type) (P : T -> SProp) (l : list T) (a : T),
  ListForallS P l -> In a l -> P a.
Proof.
  intros T P l. induction l as [| x xs IH]; intros a H Hin.
  - destruct Hin.
  - destruct H as [px pxs].
    destruct Hin as [Heq | Hin'].
    + subst a. exact px.
    + exact (IH a pxs Hin').
Qed.

Fixpoint ListForallS_of_forall (T : Type) (P : T -> SProp) (l : list T)
  : (forall a, P a) -> ListForallS P l :=
  match l as l0 return (forall a, P a) -> ListForallS P l0 with
  | nil => fun _ => trueS
  | cons x xs => fun H => conjS (P x) (ListForallS P xs) (H x) (ListForallS_of_forall T P xs H)
  end.

Section FiniteDec.
  Context {A : Type} `{Finite A}.

  Fixpoint dec_forall_list (P : A -> SProp) (d : forall a, DeciderS (P a)) (l : list A)
    : DeciderS (ListForallS P l) :=
    match l as l0 return DeciderS (ListForallS P l0) with
    | nil => sbleftS trueS
    | cons a l' =>
        match d a with
        | sbleftS pa =>
            match dec_forall_list P d l' with
            | sbleftS Hl => sbleftS (conjS (P a) (ListForallS P l') pa Hl)
            | sbrightS n => sbrightS (fun H => n (proj2_AndS H))
            end
        | sbrightS na => sbrightS (fun H => na (proj1_AndS H))
        end
    end.

  Definition dec_forall (P : A -> SProp) (d : forall a, DeciderS (P a)) : DeciderS (forall a, P a)
  := match dec_forall_list P d (flist (fun a : A => a)) with
     | sbleftS H => sbleftS (fun a => ListForallS_In A P (flist (fun x : A => x)) a H (flist_In a))
     | sbrightS n => sbrightS (fun H => n (ListForallS_of_forall A P (flist (fun x : A => x)) H))
     end.
End FiniteDec.



Definition uv_interface_inv {Var : Type} {variance : Var -> Sign}
  : forall (interface : Interface scheme) (args : IParameter scheme interface -> UserType Var) (s : Sign)
      (h : UserVariance variance (utinterface interface args) s),
    forall p, UserVariance variance (args p) (multiply s ((hierarchy.(hinterface) interface).(uisvariance) p))
:= fun interface args s h =>
   match h in UserVariance _ u s0
     return (match u with
             | utinterface interface' args' =>
                 forall p, UserVariance variance (args' p) (multiply s0 ((hierarchy.(hinterface) interface').(uisvariance) p))
             | _ => TrueS
             end)
   with
   | uvvariable v => trueS
   | uvany s' => trueS
   | uvinterface interface' args' s' H => H
   end.

Section VarianceDec2.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).

  Definition dec_uv2 : forall {Var : Type} (variance : Var -> Sign) (t : UserType Var),
      forall s : Sign, DeciderS (UserVariance variance t s).
  Proof.
    intros Var variance. fix IH 1. intros t. destruct t as [v | | i args].
    - intros s. destruct (variance v) eqn:Ev; destruct s.
      + rewrite <- Ev. exact (sbleftS (uvvariable v)).
      + apply sbrightS. intro h. inversion h. subst. rewrite Ev in *. discriminate.
      + apply sbrightS. intro h. inversion h. subst. rewrite Ev in *. discriminate.
      + rewrite <- Ev. exact (sbleftS (uvvariable v)).
    - intros s. destruct s.
      + exact (sbleftS (uvany negative)).
      + exact (sbleftS (uvany positive)).
    - intros s.
      pose (d := @dec_forall (IParameter scheme i) (IPFin i)
        (fun p => UserVariance variance (args p) (multiply s ((hierarchy.(hinterface) i).(uisvariance) p)))
        (fun p => IH (args p) (multiply s ((hierarchy.(hinterface) i).(uisvariance) p)))).
      destruct d as [H | n].
      + exact (sbleftS (uvinterface i args s H)).
      + exact (sbrightS (fun h => n (uv_interface_inv i args s h))).
  Qed.
End VarianceDec2.


Section BEntriesS.
  Context {K : Type} {V : K -> Type} {P : BPath -> K -> SProp}.

  Fixpoint bentries'_contains_S (f : BPath -> BPath) (tree : BTree K V (compose f P)) {struct tree}
    : forall elem : sigT (fun path => BEntry K V (P path)),
      InB (bentries' f tree) elem ->
      existsTS q : BPath, AndS (BContainsPath tree q) (eqS (projT1 elem) (f q)).
  Proof.
    intros elem Hin.
    destruct tree as [| head t1 t2].
    - simpl in Hin. exact (falseSeS (InB_nil_absurd Hin)).
    - simpl in Hin.
      destruct head as [entry0 |].
      + apply InB_or in Hin. destruct Hin as [Heq | Hin'].
        * assert (Hc : BContainsPath (bnode (Some entry0) t1 t2) bend)
            by (simpl; exact trueS).
          assert (He : eqS (projT1 elem) (f bend))
            by (exact (eqS_subst' (fun e => eqS (projT1 e) (f bend)) Heq (eqS_refl (f bend)))).
          exact (ex_introTS bend (conjS _ _ Hc He)).
        * apply InB_app_or in Hin'. destruct Hin' as [Hl | Hr].
          -- destruct (bentries'_contains_S (compose bfirst f) t1 elem Hl) as [q Hq].
             destruct Hq as [Hc Hq].
             exact (ex_introTS (bfirst q) (conjS _ _ Hc Hq)).
          -- destruct (bentries'_contains_S (compose bsecond f) t2 elem Hr) as [q Hq].
             destruct Hq as [Hc Hq].
             exact (ex_introTS (bsecond q) (conjS _ _ Hc Hq)).
      + apply InB_app_or in Hin. destruct Hin as [Hl | Hr].
        * destruct (bentries'_contains_S (compose bfirst f) t1 elem Hl) as [q Hq].
          destruct Hq as [Hc Hq].
          exact (ex_introTS (bfirst q) (conjS _ _ Hc Hq)).
        * destruct (bentries'_contains_S (compose bsecond f) t2 elem Hr) as [q Hq].
          destruct Hq as [Hc Hq].
          exact (ex_introTS (bsecond q) (conjS _ _ Hc Hq)).
  Qed.
End BEntriesS.

Section BEntriesSComplete.
  Context {K : Type} {V : K -> Type} {P : BPath -> K -> SProp}.

  Fixpoint bentries'_complete_S (f : BPath -> BPath) (tree : BTree K V (compose f P)) {struct tree}
    : forall (q : BPath), BContainsPath tree q ->
      existsTS elem : sigT (fun path => BEntry K V (P path)),
        AndS (InB (bentries' f tree) elem) (eqS (projT1 elem) (f q)).
  Proof.
    intros q Hc.
    destruct tree as [| head t1 t2].
    - exact (falseSeS Hc).
    - simpl in Hc. destruct q as [| q1 | q2].
      + simpl in Hc. destruct head as [entry0 |].
        * exact (ex_introTS (existT (fun path => BEntry K V (P path)) (f bend) entry0)
                  (conjS _ _
                    (inb_head (existT (fun path => BEntry K V (P path)) (f bend) entry0)
                       (app (bentries' (compose bfirst f) t1) (bentries' (compose bsecond f) t2)))
                    (eqS_refl (f bend)))).
        * exact (falseSeS Hc).
      + simpl in Hc.
        destruct (bentries'_complete_S (compose bfirst f) t1 q1 Hc) as [elem Hp].
        destruct Hp as [Hin He].
        destruct head as [entry0 |].
        * exact (ex_introTS elem (conjS _ _
            (inb_tail (existT (fun path => BEntry K V (P path)) (f bend) entry0) elem
               (app (bentries' (compose bfirst f) t1) (bentries' (compose bsecond f) t2))
               (InB_app_l elem (bentries' (compose bfirst f) t1) (bentries' (compose bsecond f) t2) Hin))
            He)).
        * exact (ex_introTS elem (conjS _ _
            (InB_app_l elem (bentries' (compose bfirst f) t1) (bentries' (compose bsecond f) t2) Hin)
            He)).
      + simpl in Hc.
        destruct (bentries'_complete_S (compose bsecond f) t2 q2 Hc) as [elem Hp].
        destruct Hp as [Hin He].
        destruct head as [entry0 |].
        * exact (ex_introTS elem (conjS _ _
            (inb_tail (existT (fun path => BEntry K V (P path)) (f bend) entry0) elem
               (app (bentries' (compose bfirst f) t1) (bentries' (compose bsecond f) t2))
               (InB_app_r elem (bentries' (compose bfirst f) t1) (bentries' (compose bsecond f) t2) Hin))
            He)).
        * exact (ex_introTS elem (conjS _ _
            (InB_app_r elem (bentries' (compose bfirst f) t1) (bentries' (compose bsecond f) t2) Hin)
            He)).
  Qed.
End BEntriesSComplete.



Section SCM.
  Context {K : Type} `{SubCountable K} {V : K -> Type}.

  Definition SCMEntry := sigT (fun path => BEntry K V (fun k => eqS (scpath k) path)).

  Lemma scmap_entry_contained (map : SCMap K V) (elem : SCMEntry)
    (Hin : InB (bentries map) elem) : SCMapContains map (projT2 elem).(bekey).
  Proof.
    unfold SCMapContains.
    destruct (@bentries'_contains_S K V (fun path k => eqS (scpath k) path)
                (fun p => p) map elem Hin) as [q Hp].
    destruct Hp as [Hc He].
    assert (Hcomp : eqS (scpath (projT2 elem).(bekey)) q)
      by (exact (eqS_trans (projT2 elem).(bekeyP) He)).
    exact (eqS_subst' (fun p => BContainsPath map p) Hcomp Hc).
  Qed.

  Fixpoint dec_entries (P : K -> SProp) (d : forall k, DeciderS (P k))
    (l : list SCMEntry) {struct l}
    : DeciderS (forall elem, InB l elem -> P (projT2 elem).(bekey)).
  Proof.
    destruct l as [| x xs].
    - exact (sbleftS (fun elem Hin => falseSeS (InB_nil_absurd Hin))).
    - destruct (d (projT2 x).(bekey)) as [px | nx].
      + destruct (dec_entries P d xs) as [Hxs | nxs].
        * exact (sbleftS (fun elem Hin =>
            match InB_or x elem xs Hin with
            | oleftS Heq => eqS_subst' (fun e => P (projT2 e).(bekey)) Heq px
            | orightS Hin' => Hxs elem Hin'
            end)).
        * exact (sbrightS (fun H => nxs (fun elem Hin => H elem (inb_tail x elem xs Hin)))).
      + exact (sbrightS (fun H => nx (H x (inb_head x xs)))).
  Qed.

  Definition dec_scm_forall (P : K -> SProp) (d : forall k, DeciderS (P k)) (map : SCMap K V)
    : DeciderS (forall k, SCMapContains map k -> P k).
  Proof.
    destruct (dec_entries P d (bentries map)) as [Hall | n].
    - apply sbleftS. intros k c.
      destruct (@bentries'_complete_S K V (fun path k => eqS (scpath k) path)
                  (fun p => p) map (scpath k) c) as [elem Hp].
      destruct Hp as [Hin He].
      pose (pk := Hall elem Hin).
      assert (Hk : (projT2 elem).(bekey) = k).
      { apply (scpath_inj).
        apply (eqS_eq (T := BPath)).
        exact (eqS_trans (projT2 elem).(bekeyP) He). }
      destruct Hk. exact pk.
    - apply sbrightS. intros Hf.
      apply n. intros elem Hin. exact (Hf (projT2 elem).(bekey) (scmap_entry_contained map elem Hin)).
  Qed.
End SCM.


Section Contains.
  Context {K : Type} {V : K -> Type}.

  Fixpoint dec_bcontains (P : BPath -> K -> SProp) (tree : BTree K V P) (path : BPath) {struct tree}
    : DeciderS (BContainsPath tree path).
  Proof.
    destruct tree as [| head t1 t2].
    - exact (sbrightS (fun h => h)).
    - destruct path as [| p | p].
      + destruct head as [entry0 |].
        * exact (sbleftS trueS).
        * exact (sbrightS (fun h => h)).
      + simpl. exact (dec_bcontains (fun path => P (bfirst path)) t1 p).
      + simpl. exact (dec_bcontains (fun path => P (bsecond path)) t2 p).
  Qed.
End Contains.

Section Hierarchy.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (MFin : forall method : Method scheme, Finite (MInput scheme method)).

  Definition dec_umsv {Var Input : Type} (Input_Fin : Finite Input)
    (signature : UserMethodSignature Var Input) (variance : Var -> Sign)
    : DeciderS (UserMethodSignatureV signature variance).
  Proof.
    destruct (@dec_forall Input Input_Fin
                (fun input => UserVariance variance (signature.(umsinput) input) negative)
                (fun input => @dec_uv2 IPFin Var variance (signature.(umsinput) input) negative))
      as [Hin | nin].
    - destruct (@dec_uv2 IPFin Var variance signature.(umsresult) positive) as [Hres | nres].
      + exact (sbleftS (@Build_UserMethodSignatureV Var Input signature variance Hin Hres)).
      + exact (sbrightS (fun H => nres (umsresultv H))).
    - exact (sbrightS (fun H => nin (umsinputv H))).
  Qed.

  Definition dec_ubsv {Var : Type} (signature : UserBodySignature Var) (variance : Var -> Sign)
    : DeciderS (UserBodySignatureV signature variance).
  Proof.
    pose (P := fun method => forall contains : SCSetContains signature.(ubsmethods) method,
                UserMethodSignatureV (signature.(ubsmethod) method contains) variance).
    pose (d := fun method =>
      match @dec_bcontains (Method scheme) (fun _ => unit) (fun path k => eqS (scpath k) path)
              signature.(ubsmethods) (scpath method)
      with
      | sbleftS c0 =>
          match @dec_umsv Var (MInput scheme method) (MFin method) (signature.(ubsmethod) method c0) variance with
          | sbleftS p => sbleftS (fun contains => (p : UserMethodSignatureV (signature.(ubsmethod) method contains) variance))
          | sbrightS np => sbrightS (fun H => np (H c0))
          end
      | sbrightS n => sbleftS (fun contains => falseSeS (n contains))
      end).
    destruct (@dec_scm_forall (Method scheme) (Method_SubCountable scheme) (fun _ => unit) P d signature.(ubsmethods))
      as [Hall | n].
    - exact (sbleftS (@Build_UserBodySignatureV Var signature variance (fun method contains => Hall method contains contains))).
    - exact (sbrightS (fun H => n (fun k c c' => ubsmethodv H k c'))).
  Qed.

  Definition dec_uisv {Var : Type} (signature : UserInterfaceSignature Var)
    : DeciderS (UserInterfaceSignatureV signature).
  Proof.
    destruct (@dec_ubsv Var signature.(uisbody) signature.(uisvariance)) as [H | n].
    - exact (sbleftS (@Build_UserInterfaceSignatureV Var signature H)).
    - exact (sbrightS (fun H => n (uisbodyv H))).
  Qed.

  Definition dec_hierarchyv (IFin : Finite (Interface scheme))
    : DeciderS HierarchyV.
  Proof.
    destruct (@dec_forall (Interface scheme) IFin
                (fun interface => UserInterfaceSignatureV (hierarchy.(hinterface) interface))
                (fun interface => @dec_uisv (IParameter scheme interface) (hierarchy.(hinterface) interface)))
      as [Hall | n].
    - exact (sbleftS (Build_HierarchyV Hall)).
    - exact (sbrightS (fun H => n (hinterfacev H))).
  Qed.
End Hierarchy.



(* ==== Canonical type space: UT, its preorder, and consistency ==== *)
From Stdlib Require Import Lia.
From Stdlib Require Import Eqdep_dec.

Inductive UT : Type :=
| utanyT : UT
| utbotT : UT
| utifaceT (i : Interface scheme) (args : IParameter scheme i -> UT).

Definition ut_size (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)) (t : UT) : nat
:= (fix go (t : UT) {struct t} : nat :=
      match t with
      | utanyT => 0
      | utbotT => 0
      | utifaceT i args =>
          S (fold_right Nat.add 0 (map (fun p : IParameter scheme i => go (args p))
                                       (flist (fun p : IParameter scheme i => p))))
      end) t.

Lemma In_le_sum : forall (l : list nat) (x : nat), In x l -> x <= fold_right Nat.add 0 l.
Proof.
  intros l. induction l as [| a l IH]; intros x Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst x. lia.
    + specialize (IH x Hin). lia.
Qed.

Lemma ut_size_sub : forall (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (i : Interface scheme) (args : IParameter scheme i -> UT) (p : IParameter scheme i),
  ut_size IPFin (args p) < ut_size IPFin (utifaceT i args).
Proof.
  intros.
  assert (H : ut_size IPFin (args p) <=
              fold_right Nat.add 0 (map (fun q : IParameter scheme i => ut_size IPFin (args q))
                                        (flist (fun q : IParameter scheme i => q)))).
  { apply In_le_sum. apply (@List.in_map (IParameter scheme i) nat (fun q => ut_size IPFin (args q)) (flist (fun q : IParameter scheme i => q)) p). apply flist_In. }
  simpl. lia.
Qed.


Inductive SubT : UT -> UT -> SProp :=
| subT_bot (b : UT) : SubT utbotT b
| subT_top (a : UT) : SubT a utanyT
| subT_variance (i : Interface scheme) (args args' : IParameter scheme i -> UT) :
    (forall p, ISigned SubT ((hierarchy.(hinterface) i).(uisvariance) p) (args p) (args' p)) ->
    SubT (utifaceT i args) (utifaceT i args').

Lemma isigned_neg_inv {A : Type} {R : A -> A -> SProp} {a b : A}
  (h : ISigned R negative a b) : R b a.
Proof. inversion h. assumption. Qed.

Lemma isigned_pos_inv {A : Type} {R : A -> A -> SProp} {a b : A}
  (h : ISigned R positive a b) : R a b.
Proof. inversion h. assumption. Qed.

Definition isigned_refl {A : Type} {R : A -> A -> SProp} (Rrefl : forall a, R a a)
  (s : Sign) (a : A) : ISigned R s a a
:= match s with
   | negative => isnegative a a (Rrefl a)
   | positive => ispositive a a (Rrefl a)
   end.

Fixpoint subT_refl (t : UT) {struct t} : SubT t t.
Proof.
  destruct t as [| | i args].
  - exact (subT_top utanyT).
  - exact (subT_bot utbotT).
  - apply (subT_variance i args args). intro p.
    apply isigned_refl. intro q. apply subT_refl.
Qed.


Definition interface_K (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (i : Interface scheme) : K i
:= fun e => @UIP_dec (Interface scheme) deq i i eq_refl e.

Section Trans.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Fixpoint subT_trans_n (n : nat)
    : forall a c : UT, ut_size IPFin a + ut_size IPFin c <= n ->
      forall b, SubT a b -> SubT b c -> SubT a c.
  Proof.
    destruct n as [| n'].
    - intros a c Hle b h1 h2.
      destruct h1 as [b0 | a0 | i args args' Hargs].
      + exact (subT_bot c).
      + inversion h2. subst. exact (subT_top a0).
      + exfalso. simpl in Hle. lia.
    - intros a c Hle b h1 h2.
      destruct h1 as [b0 | a0 | i args args' Hargs].
      + exact (subT_bot c).
      + inversion h2. subst. exact (subT_top a0).
      + inversion h2.
        * subst. exact (subT_top (utifaceT i args)).
        * subst.
          assert (Hargseq : args1 = args').
          { apply (@k_inj_projT2 (Interface scheme) (fun i => IParameter scheme i -> UT) i
                     (interface_K deq i) args1 args'). exact H1. }
          subst args1.
          apply (subT_variance i args args'0).
          intro p.
          pose proof (H2 p) as H2p.
          pose proof (Hargs p) as Hargsp.
          destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
          -- apply (isnegative (args p) (args'0 p)).
             refine (subT_trans_n n' (args'0 p) (args p) _ (args' p) _ _).
             ++ assert (HA := ut_size_sub IPFin i args p).
                assert (HC := ut_size_sub IPFin i args'0 p).
                lia.
             ++ exact (isigned_neg_inv H2p).
             ++ exact (isigned_neg_inv Hargsp).
          -- apply (ispositive (args p) (args'0 p)).
             refine (subT_trans_n n' (args p) (args'0 p) _ (args' p) _ _).
             ++ assert (HA := ut_size_sub IPFin i args p).
                assert (HC := ut_size_sub IPFin i args'0 p).
                lia.
             ++ exact (isigned_pos_inv Hargsp).
             ++ exact (isigned_pos_inv H2p).
  Qed.
End Trans.


Section Canon.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition subT_trans (a b c : UT) (h1 : SubT a b) (h2 : SubT b c) : SubT a c
  := subT_trans_n IPFin deq (ut_size IPFin a + ut_size IPFin c) a c (le_n _) b h1 h2.

  Definition signed_isigned {A : Type} {R : A -> A -> SProp} : forall (s : Sign) (a b : A),
      Signed R s a b -> ISigned R s a b
  := fun s a b h =>
     match s return Signed R s a b -> ISigned R s a b with
     | negative => fun h' => isnegative a b h'
     | positive => fun h' => ispositive a b h'
     end h.

  Definition isigned_signed {A : Type} {R : A -> A -> SProp} : forall (s : Sign) (a b : A),
      ISigned R s a b -> Signed R s a b
  := fun s a b h =>
     match s return ISigned R s a b -> Signed R s a b with
     | negative => fun h' => isigned_neg_inv h'
     | positive => fun h' => isigned_pos_inv h'
     end h.

  Definition unReachableT (t : UT) : SProp
  := match t with utbotT => TrueS | _ => FalseS end.

  Lemma subT_ur : forall (a b : UT), SubT a b -> unReachableT b -> unReachableT a.
  Proof.
    intros a b h. induction h as [b0 | a0 | i args args' Hargs].
    - intro H; exact trueS.
    - intro Hc. exact (falseSeS Hc).
    - intro Hc. exact (falseSeS Hc).
  Qed.

  Definition canonSpace : TypeSpace :=
  {| SpaceType := UT;
     stany := utanyT;
     stinterface := utifaceT;
     SubSpaceType := SubT;
     sstrefl := subT_refl;
     ssttrans := fun t t' t'' h1 h2 => subT_trans t t' t'' h1 h2;
     sstvariance := fun i args args' H => subT_variance i args args' (fun p => signed_isigned _ _ _ (H p));
     sstinheritance := fun i args => subT_top (utifaceT i args);
     UnReachable := unReachableT;
     sstur := fun t t' h hu => subT_ur t t' h hu |}.
End Canon.


Definition convert_eqS_refl {A : Type} `{DecEq A} `{SSet A}
  (a : A) (B : A -> Type) (b : B a) : convert (eqS_refl a) B b = b.
Proof.
  unfold convert.
  exact (eq_sym (@eq_rect_eq_dec A (fun x y => dec_eq x y) a (B) b
                  (eqS_eq (eqS_refl a)))).
Qed.

Section Cons.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.

  Lemma cts_iface : forall (i : Interface scheme) (args : IParameter scheme i -> UT)
      (i' : Interface scheme) (args' : IParameter scheme i' -> UT),
      SubT (utifaceT i args) (utifaceT i' args') ->
      existsSS e : eqS i i',
        forall p, Signed SubT ((hierarchy.(hinterface) i).(uisvariance) p)
                          (args p) (args' (convert e (IParameter scheme) p)).
  Proof.
    intros i args i' args' h. inversion h.
    subst i'.
    assert (Ha : args1 = args).
    { apply (@k_inj_projT2 (Interface scheme) (fun i => IParameter scheme i -> UT) i
               (interface_K deq i) args1 args). exact H3. }
    assert (Hb : args'1 = args').
    { apply (@k_inj_projT2 (Interface scheme) (fun i => IParameter scheme i -> UT) i
               (interface_K deq i) args'1 args'). exact H5. }
    subst args1. subst args'1.
    apply (ex_introSS (eqS i i)
             (fun e => forall p, Signed SubT ((hierarchy.(hinterface) i).(uisvariance) p)
                                   (args p) (args' (convert e (IParameter scheme) p)))
             (eqS_refl i)).
    intro p.
    rewrite convert_eqS_refl.
    exact (isigned_signed _ _ _ (H2 p)).
  Qed.

  Lemma cts_any_interface : forall (i : Interface scheme) (args : IParameter scheme i -> UT),
      SubT utanyT (utifaceT i args) -> FalseS.
  Proof.
    intros i args h. inversion h.
  Qed.

  Definition canonConsistent : ConsistentTypeSpace (canonSpace IPFin deq) :=
  @Build_ConsistentTypeSpace H (canonSpace IPFin deq) cts_iface
    (fun h => h) cts_any_interface (fun i args h => h).
End Cons.


(* Soundness: a check in the canonical space yields ProgramV. *)
Lemma programv_of_canon
  {Interface_Finite: Finite scheme.(Interface)}
  {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)}
  {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)}
  (program : Program)
  (hh : HierarchyV)
  (hc : CheckExpression (canonSpace IParameter_Finite (fun x y => dec_eq x y))
          nil_elimination program.(pexpression) (tsubst emptye program.(ptype)))
  : ProgramV program.
Proof.
  refine {| phierarchyv := hh;
            pexpressionv := ex_introSSS (canonSpace IParameter_Finite (fun x y => dec_eq x y))
                              (canonConsistent IParameter_Finite (fun x y => dec_eq x y)) hc |}.
Qed.

(* ==== Decidability of SubT ==== *)
Section SubDec.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context `{DecEq (Interface scheme)}.

  Definition deqI : forall x y : Interface scheme, {x = y} + {x = y -> False}
  := fun x y => dec_eq x y.

  Lemma subT_iface_inv : forall (i : Interface scheme) (args args' : IParameter scheme i -> UT),
      SubT (utifaceT i args) (utifaceT i args') ->
      forall p, ISigned SubT ((hierarchy.(hinterface) i).(uisvariance) p) (args p) (args' p).
  Proof.
    intros i args args' h p. inversion h.
    assert (Ha : args1 = args).
    { apply (@k_inj_projT2 (Interface scheme) (fun i => IParameter scheme i -> UT) i
               (interface_K deqI i) args1 args). exact H2. }
    assert (Hb : args'0 = args').
    { apply (@k_inj_projT2 (Interface scheme) (fun i => IParameter scheme i -> UT) i
               (interface_K deqI i) args'0 args'). exact H3. }
    subst args1. subst args'0. exact (H1 p).
  Qed.

  Lemma subT_iface_neq : forall (i : Interface scheme) (args : IParameter scheme i -> UT)
      (i' : Interface scheme) (args' : IParameter scheme i' -> UT),
      (i = i' -> False) -> SubT (utifaceT i args) (utifaceT i' args') -> FalseS.
  Proof.
    intros i args i' args' ne h. inversion h.
    exact (false_falseS (ne H3)).
  Qed.

  Lemma subT_any_bot_absurd : SubT utanyT utbotT -> FalseS.
  Proof. intro h. inversion h. Qed.

  Lemma subT_iface_bot_absurd : forall (i : Interface scheme) (args : IParameter scheme i -> UT),
      SubT (utifaceT i args) utbotT -> FalseS.
  Proof. intros i args h. inversion h. Qed.

  Fixpoint dec_subT_n (n : nat) (a b : UT)
    (Hle : ut_size IPFin a + ut_size IPFin b <= n) {struct n}
    : DeciderS (SubT a b).
  Proof.
    destruct n as [| n'].
    - destruct a as [| | i args]; destruct b as [| | i' args']; simpl in Hle; try lia.
      + exact (sbleftS (subT_top utanyT)).
      + exact (sbrightS (fun h => subT_any_bot_absurd h)).
      + exact (sbleftS (subT_bot utanyT)).
      + exact (sbleftS (subT_bot utbotT)).
    - destruct a as [| | i args]; destruct b as [| | i' args'].
      + exact (sbleftS (subT_top utanyT)).
      + exact (sbrightS (fun h => subT_any_bot_absurd h)).
      + exact (sbrightS (fun h => cts_any_interface i' args' h)).
      + exact (sbleftS (subT_bot utanyT)).
      + exact (sbleftS (subT_bot utbotT)).
      + exact (sbleftS (subT_bot (utifaceT i' args'))).
      + exact (sbleftS (subT_top (utifaceT i args))).
      + exact (sbrightS (fun h => subT_iface_bot_absurd i args h)).
      + destruct (dec_eq i i') as [e | ne].
        * subst i'.
          assert (Hb1 : forall p, ut_size IPFin (args p) + ut_size IPFin (args' p) <= n')
            by (intro p; assert (h1 := ut_size_sub IPFin i args p);
                assert (h2 := ut_size_sub IPFin i args' p); lia).
          assert (Hb2 : forall p, ut_size IPFin (args' p) + ut_size IPFin (args p) <= n')
            by (intro p; assert (h1 := ut_size_sub IPFin i args p);
                assert (h2 := ut_size_sub IPFin i args' p); lia).
          pose (d := fun p =>
            match ((hierarchy.(hinterface) i).(uisvariance) p) as sg
              return DeciderS (Signed SubT sg (args p) (args' p)) with
            | negative => dec_subT_n n' (args' p) (args p) (Hb2 p)
            | positive => dec_subT_n n' (args p) (args' p) (Hb1 p)
            end).
          destruct (@dec_forall (IParameter scheme i) (IPFin i)
                      (fun p => Signed SubT ((hierarchy.(hinterface) i).(uisvariance) p) (args p) (args' p)) d)
            as [Hv | nv].
          -- exact (sbleftS (subT_variance i args args' (fun p => signed_isigned _ _ _ (Hv p)))).
          -- exact (sbrightS (fun h => nv (fun p => isigned_signed _ _ _ (subT_iface_inv i args args' h p)))).
        * exact (sbrightS (fun h => subT_iface_neq i args i' args' ne h)).
  Qed.

  Definition dec_subT (a b : UT) : DeciderS (SubT a b)
  := dec_subT_n (ut_size IPFin a + ut_size IPFin b) a b (le_n _).
End SubDec.


(* Space-independent necessary condition extracted from any derivation. *)
Lemma check_eobject_conformance {S : TypeSpace} :
  forall {Input : Sort} (ctx : SortElimination S.(SpaceType) Input)
    (e : Expression Input) (t : S.(SpaceType)),
  CheckExpression S ctx e t ->
  match e with
  | eobject interface methods bodies =>
      forall method : Method scheme,
        SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method ->
        SCSetContains methods method
  | _ => TrueS
  end.
Proof.
  intros Input ctx e t h.
  induction h.
  - assumption.
  - exact trueS.
  - exact trueS.
  - simpl. intros method hc.
    match goal with
    | H : SubSpaceBodySignature _ _ |- _ => exact (ssbsmethods H method hc)
    end.
Qed.


Lemma check_eobject_type {S : TypeSpace} :
  forall {Input : Sort} (ctx : SortElimination S.(SpaceType) Input)
    (e : Expression Input) (t : S.(SpaceType)),
  CheckExpression S ctx e t ->
  match e with
  | eobject interface methods bodies =>
      existsTS args0 : (IParameter scheme interface -> SpaceType S),
        SubSpaceType S (stinterface S interface args0) t
  | _ => TrueS
  end.
Proof.
  intros Input ctx e t h.
  induction h.
  - destruct expression as [input | er m en | i ms bs].
    + exact trueS.
    + exact trueS.
    + destruct IHh as [args0 hsub].
      refine (ex_introTS args0 (ssttrans S (stinterface S i args0) t t' hsub s)).
  - exact trueS.
  - exact trueS.
  - simpl.
    refine (ex_introTS arguments (sstrefl S (stinterface S interface arguments))).
Qed.


Lemma check_invoke_recv_method {S : TypeSpace} `{SSet (Interface scheme)}
  (ct : ConsistentTypeSpace S) :
  forall {Input : Sort} (ctx : SortElimination S.(SpaceType) Input)
    (e : Expression Input) (t : S.(SpaceType)),
  CheckExpression S ctx e t ->
  match e with
  | einvoke r method args =>
      match r with
      | eobject interface methods bodies =>
          SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method
      | _ => TrueS
      end
  | _ => TrueS
  end.
Proof.
  intros Input ctx e t h.
  induction h.
  - destruct expression as [input | er m en | i ms bs].
    + exact trueS.
    + destruct er as [input' | er' m' en' | i' ms' bs'].
      * exact trueS.
      * exact trueS.
      * exact IHh.
    + exact trueS.
  - exact trueS.
  - (* ceinvoke *) simpl.
    destruct ereceiver as [input' | er' m' en' | i' ms' bs'].
    + exact trueS.
    + exact trueS.
    + (* receiver is eobject i' ms' bs' *)
      destruct (check_eobject_type context (eobject i' ms' bs') treceiver h) as [args0 hsub].
      destruct c as [tre0 sig0 ur | intf argsc contains].
      * (* cmunreachable *)
        exact (falseSeS (ctsinterfaceunreachable ct i' args0
                           (sstur S (stinterface S i' args0) tre0 hsub ur))).
      * (* cminterface *)
        destruct (ctsinterface ct i' args0 intf argsc hsub) as [ee hv].
        exact (eqS_subst' (fun j => SCSetContains (hierarchy.(hinterface) j).(uisbody).(ubsmethods) method)
                ee contains).
  - exact trueS.
Qed.


Lemma top_eobject_head {S : TypeSpace} `{SSet (Interface scheme)}
  (ct : ConsistentTypeSpace S) (program : Program)
  (i : Interface scheme) (ms : SCSet (Method scheme))
  (bs : forall method : Method scheme, SCSetContains ms method ->
          Expression (MInput scheme method :: nil)%list) :
  CheckExpression S nil_elimination (eobject i ms bs) (tsubst emptye program.(ptype)) ->
  forall (j : Interface scheme) (args : IParameter scheme j -> UserType Empty),
    program.(ptype) = utinterface j args -> eqS i j.
Proof.
  intros h j args hp.
  destruct (check_eobject_type nil_elimination (eobject i ms bs)
              (tsubst emptye program.(ptype)) h) as [args0 hsub].
  rewrite hp in hsub. cbn in hsub.
  exact (proj1_exSS (ctsinterface ct i args0 j (fun p => tsubst emptye (args p)) hsub)).
Qed.


Lemma check_einput_le {S : TypeSpace} :
  forall {Input : Sort} (ctx : SortElimination S.(SpaceType) Input)
    (e : Expression Input) (t : S.(SpaceType)),
  CheckExpression S ctx e t ->
  match e with
  | einput input => SubSpaceType S (apply_elimination ctx input) t
  | _ => TrueS
  end.
Proof.
  intros Input ctx e t h.
  induction h.
  - destruct expression as [input' | er m en | i ms bs].
    + exact (ssttrans S (apply_elimination context input') t t' IHh s).
    + exact trueS.
    + exact trueS.
  - exact (sstrefl S (apply_elimination context input)).
  - exact trueS.
  - exact trueS.
Qed.

Section Transfer.
Context {S : TypeSpace} {T : TypeSpace}.
Variable phi : S.(SpaceType) -> T.(SpaceType).
Variable Hiface : forall (i : Interface scheme) (args : IParameter scheme i -> S.(SpaceType)),
  phi (S.(stinterface) i args) = T.(stinterface) i (fun p => phi (args p)).
Variable Htsubst : forall (Var : Type) (sigma : Var -> S.(SpaceType)) (u : UserType Var),
  phi (tsubst (space:=S) sigma u) = tsubst (space:=T) (fun v => phi (sigma v)) u.
Variable Hsub : forall a b, S.(SubSpaceType) a b -> T.(SubSpaceType) (phi a) (phi b).
Variable Hur : forall a, S.(UnReachable) a -> T.(UnReachable) (phi a).

Definition mapSig {Input : Type} (sig : SpaceMethodSignature S Input) : SpaceMethodSignature T Input :=
  {| smsinput input := phi (smsinput sig input); smsresult := phi (smsresult sig) |}.

Lemma check_transfer :
  forall (Input : Sort) (ctx : SortElimination S.(SpaceType) Input)
         (e : Expression Input) (t : S.(SpaceType)),
    CheckExpression S ctx e t ->
    forall (ctx' : SortElimination T.(SpaceType) Input),
      (forall input : SumSort Input, T.(SubSpaceType) (apply_elimination ctx' input) (phi (apply_elimination ctx input))) ->
      CheckExpression T ctx' e (phi t).
Proof.
  intros Input ctx e t h.
  induction h; intros ctx' Hctx.
  - (* cesub *)
    exact (@cesub T Input ctx' expression (phi t) (phi t')
             (IHh ctx' Hctx) (Hsub t t' s)).
  - (* ceinput *)
    exact (@cesub T Input ctx' (einput input) (apply_elimination ctx' input)
             _
             (@ceinput T Input ctx' input) (Hctx input)).
  - (* ceinvoke *)
    destruct c as [tr0 sg0 ur | i a contains].
    + (* cmunreachable *)
      exact (@ceinvoke T Input ctx' ereceiver method einputs (phi tr0) (mapSig sg0)
               (@cmunreachable T method (phi tr0) (mapSig sg0) (Hur tr0 ur))
               (IHh ctx' Hctx)
               (fun input => H input ctx' Hctx)).
    + (* cminterface *)
      refine (match eq_sym (Htsubst (IParameter scheme i) a
                (umsresult (ubsmethod (uisbody (hinterface hierarchy i)) method contains)))
              in _ = y return CheckExpression T ctx' (einvoke ereceiver method einputs) y with
              | eq_refl =>
                @ceinvoke T Input ctx' ereceiver method einputs
                  (T.(stinterface) i (fun p => phi (a p)))
                  (mssubst (space:=T) (fun p => phi (a p))
                     (ubsmethod (uisbody (hinterface hierarchy i)) method contains))
                  (@cminterface T method i (fun p => phi (a p)) contains)
                  _ _
              end).
      * (* receiver *)
        refine (match Hiface i a in _ = y return
                  CheckExpression T ctx' ereceiver y with
                | eq_refl => IHh ctx' Hctx end).
      * (* arguments *)
        intro input.
        refine (match Htsubst (IParameter scheme i) a
                  (umsinput (ubsmethod (uisbody (hinterface hierarchy i)) method contains) input)
                in _ = y return CheckExpression T ctx' (einputs input) y with
                | eq_refl => H input ctx' Hctx end).
  - (* ceobject *)
    rewrite Hiface.
    refine (@ceobject T Input ctx' interface methods bodies
              (fun p => phi (arguments p))
              (fun m contains => mapSig (signatures m contains)) _ _).
    + (* body signature subspace *)
      refine (@Build_SubSpaceBodySignature T
        {| sbsmethods := methods; sbsmethod := fun m contains => mapSig (signatures m contains) |}
        (bssubst (fun p => phi (arguments p)) (uisbody (hinterface hierarchy interface)))
        (fun m contains => ssbsmethods (space:=S) s m contains) _).
      intros m contains.
      refine {| ssmsinput := fun input => _ ; ssmsresult := _ |}.
      * simpl.
        refine (match Htsubst (IParameter scheme interface) arguments
                  (umsinput (ubsmethod (uisbody (hinterface hierarchy interface)) m contains) input)
                in _ = y return
                  T.(SubSpaceType) y (phi (smsinput (signatures m (ssbsmethods (space:=S) s m contains)) input)) with
                | eq_refl => Hsub _ _ (ssmsinput (ssbsmethod (space:=S) s m contains) input) end).
      * simpl.
        refine (match Htsubst (IParameter scheme interface) arguments
                  (umsresult (ubsmethod (uisbody (hinterface hierarchy interface)) m contains))
                in _ = y return
                  T.(SubSpaceType) (phi (smsresult (signatures m (ssbsmethods (space:=S) s m contains)))) y with
                | eq_refl => Hsub _ _ (ssmsresult (ssbsmethod (space:=S) s m contains)) end).
    + (* bodies *)
      intros m contains.
      refine (H m contains (pair_elimination (smsinput (mapSig (signatures m contains))) ctx') _).
      intros input.
      destruct input as [x | y].
      * simpl. exact (T.(sstrefl) (phi (smsinput (signatures m contains) x))).
      * simpl. exact (Hctx y).
Qed.
End Transfer.

Definition uusize (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  {Var : Type} (t : UserType Var) : nat
:= (fix go (t : UserType Var) {struct t} : nat :=
      match t with
      | utvariable _ => 0
      | utany => 0
      | utinterface i args =>
          S (fold_right Nat.add 0 (map (fun p : IParameter scheme i => go (args p))
                                       (flist (fun p : IParameter scheme i => p))))
      end) t.

Lemma uusize_sub : forall (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  {Var : Type} (i : Interface scheme) (args : IParameter scheme i -> UserType Var)
  (p : IParameter scheme i),
  uusize IPFin (args p) < uusize IPFin (utinterface i args).
Proof.
  intros.
  assert (H : uusize IPFin (args p) <=
              fold_right Nat.add 0 (map (fun q : IParameter scheme i => uusize IPFin (args q))
                                        (flist (fun q : IParameter scheme i => q)))).
  { apply In_le_sum. apply (@List.in_map (IParameter scheme i) nat
      (fun q => uusize IPFin (args q)) (flist (fun q : IParameter scheme i => q)) p).
    apply flist_In. }
  simpl. lia.
Qed.

Section SubUserDecSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (ideq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma subuser_iface_inv : forall {Var : Type} (i : Interface scheme)
      (args args' : IParameter scheme i -> UserType Var),
    SubUserType (utinterface i args) (utinterface i args') ->
    forall p, ISigned SubUserType ((hierarchy.(hinterface) i).(uisvariance) p) (args p) (args' p).
  Proof.
    intros Var i args args' h p. inversion h.
    assert (Ha : arguments0 = args).
    { apply (@k_inj_projT2 (Interface scheme)
               (fun i => IParameter scheme i -> UserType Var) i
               (interface_K ideq i) arguments0 args). exact H1. }
    assert (Hb : arguments' = args').
    { apply (@k_inj_projT2 (Interface scheme)
               (fun i => IParameter scheme i -> UserType Var) i
               (interface_K ideq i) arguments' args'). exact H2. }
    subst arguments0. subst arguments'. exact (H0 p).
  Qed.

  Lemma subuser_iface_neq : forall {Var : Type} (i : Interface scheme)
      (args : IParameter scheme i -> UserType Var)
      (i' : Interface scheme) (args' : IParameter scheme i' -> UserType Var),
    (i = i' -> False) -> SubUserType (utinterface i args) (utinterface i' args') -> FalseS.
  Proof.
    intros Var i args i' args' ne h. inversion h.
    exact (false_falseS (ne H2)).
  Qed.

  Lemma subuser_var_var_neq : forall {Var : Type} (x y : Var),
    (x = y -> False) -> SubUserType (utvariable x) (utvariable y) -> FalseS.
  Proof. intros Var x y ne h. inversion h. exact (false_falseS (ne H)). Qed.

  Lemma subuser_var_any_absurd : forall {Var : Type} (x : Var),
    SubUserType (utvariable x) utany -> FalseS.
  Proof. intros Var x h. inversion h. Qed.

  Lemma subuser_any_var_absurd : forall {Var : Type} (x : Var),
    SubUserType utany (utvariable x) -> FalseS.
  Proof. intros Var x h. inversion h. Qed.

  Lemma subuser_var_iface_absurd : forall {Var : Type} (x : Var) (i : Interface scheme)
      (args : IParameter scheme i -> UserType Var),
    SubUserType (utvariable x) (utinterface i args) -> FalseS.
  Proof. intros Var x i args h. inversion h. Qed.

  Lemma subuser_iface_var_absurd : forall {Var : Type} (i : Interface scheme)
      (args : IParameter scheme i -> UserType Var) (x : Var),
    SubUserType (utinterface i args) (utvariable x) -> FalseS.
  Proof. intros Var i args x h. inversion h. Qed.

  Lemma subuser_any_iface_absurd : forall {Var : Type} (i : Interface scheme)
      (args : IParameter scheme i -> UserType Var),
    SubUserType utany (utinterface i args) -> FalseS.
  Proof. intros Var i args h. inversion h. Qed.

  Fixpoint dec_subuser_n (n : nat) (Var : Type)
    (vdeq : forall x y : Var, {x = y} + {x = y -> False})
    (u v : UserType Var)
    (Hle : uusize IPFin u + uusize IPFin v <= n) {struct n}
    : DeciderS (SubUserType u v).
  Proof.
    destruct n as [| n'].
    - destruct u as [x | | i args]; destruct v as [y | | i' args'];
        try (exfalso; simpl in Hle; lia).
      + destruct (vdeq x y) as [e | ne].
        * subst y. exact (sbleftS (sutvariable x)).
        * exact (sbrightS (fun h => subuser_var_var_neq x y ne h)).
      + exact (sbrightS (fun h => subuser_var_any_absurd x h)).
      + exact (sbrightS (fun h => subuser_any_var_absurd y h)).
      + exact (sbleftS sutany).
    - destruct u as [x | | i args]; destruct v as [y | | i' args'];
        try (exfalso; simpl in Hle; lia).
      + destruct (vdeq x y) as [e | ne].
        * subst y. exact (sbleftS (sutvariable x)).
        * exact (sbrightS (fun h => subuser_var_var_neq x y ne h)).
      + exact (sbrightS (fun h => subuser_var_any_absurd x h)).
      + exact (sbrightS (fun h => subuser_var_iface_absurd x i' args' h)).
      + exact (sbrightS (fun h => subuser_any_var_absurd y h)).
      + exact (sbleftS sutany).
      + exact (sbrightS (fun h => subuser_any_iface_absurd i' args' h)).
      + exact (sbrightS (fun h => subuser_iface_var_absurd i args y h)).
      + exact (sbleftS (sutinheritance i args)).
      + destruct (ideq i i') as [e | ne].
        * subst i'.
          assert (Hb1 : forall p, uusize IPFin (args p) + uusize IPFin (args' p) <= n')
            by (intro p; assert (h1 := uusize_sub IPFin i args p);
                assert (h2 := uusize_sub IPFin i args' p); lia).
          assert (Hb2 : forall p, uusize IPFin (args' p) + uusize IPFin (args p) <= n')
            by (intro p; assert (h1 := uusize_sub IPFin i args p);
                assert (h2 := uusize_sub IPFin i args' p); lia).
          pose (d := fun p =>
            match ((hierarchy.(hinterface) i).(uisvariance) p) as sg
              return DeciderS (Signed SubUserType sg (args p) (args' p)) with
            | negative => dec_subuser_n n' Var vdeq (args' p) (args p) (Hb2 p)
            | positive => dec_subuser_n n' Var vdeq (args p) (args' p) (Hb1 p)
            end).
          destruct (@dec_forall (IParameter scheme i) (IPFin i)
                      (fun p => Signed SubUserType ((hierarchy.(hinterface) i).(uisvariance) p) (args p) (args' p)) d)
            as [Hv | nv].
          -- exact (sbleftS (sutvariance i args args' (fun p => signed_isigned _ _ _ (Hv p)))).
          -- exact (sbrightS (fun h => nv (fun p => isigned_signed _ _ _ (subuser_iface_inv i args args' h p)))).
        * exact (sbrightS (fun h => subuser_iface_neq i args i' args' ne h)).
  Qed.

  Definition dec_subuser (Var : Type)
    (vdeq : forall x y : Var, {x = y} + {x = y -> False})
    (u v : UserType Var) : DeciderS (SubUserType u v)
  := dec_subuser_n (uusize IPFin u + uusize IPFin v) Var vdeq u v (le_n _).
End SubUserDecSection.

Section PolSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).

  Definition pol_low (i : Interface scheme) (_ : IParameter scheme i -> UT) : IParameter scheme i -> UT
  := fun p => match ((hierarchy.(hinterface) i).(uisvariance) p) with
              | negative => utanyT
              | positive => utbotT
              end.

  Definition pol_high (i : Interface scheme) (_ : IParameter scheme i -> UT) : IParameter scheme i -> UT
  := fun p => match ((hierarchy.(hinterface) i).(uisvariance) p) with
              | negative => utbotT
              | positive => utanyT
              end.

  Lemma subT_iface_low : forall (i : Interface scheme) (b : IParameter scheme i -> UT),
    SubT (utifaceT i (pol_low i b)) (utifaceT i b).
  Proof.
    intros i b. apply (subT_variance i (pol_low i b) b). intro p.
    unfold pol_low.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
    - exact (isnegative utanyT (b p) (subT_top (b p))).
    - exact (ispositive utbotT (b p) (subT_bot (b p))).
  Qed.

  Lemma subT_iface_high : forall (i : Interface scheme) (a : IParameter scheme i -> UT),
    SubT (utifaceT i a) (utifaceT i (pol_high i a)).
  Proof.
    intros i a. apply (subT_variance i a (pol_high i a)). intro p.
    unfold pol_high.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
    - exact (isnegative (a p) utbotT (subT_bot (a p))).
    - exact (ispositive (a p) utanyT (subT_top (a p))).
  Qed.
End PolSection.

Definition LowIface (i : Interface scheme) : UT
:= utifaceT i (pol_low i (fun _ => utanyT)).

Definition HighIface (i : Interface scheme) : UT
:= utifaceT i (pol_high i (fun _ => utanyT)).

Lemma LowIface_sub_low : forall (i : Interface scheme) (b : IParameter scheme i -> UT),
  SubT (LowIface i) (utifaceT i b).
Proof.
  intros i b. unfold LowIface.
  exact (subT_iface_low i b).
Qed.

Lemma any_iface_high : forall (i : Interface scheme) (a : IParameter scheme i -> UT),
  SubT (utifaceT i a) (HighIface i).
Proof.
  intros i a. unfold HighIface.
  exact (subT_iface_high i a).
Qed.

Lemma LowIface_high : forall (i : Interface scheme),
  SubT (LowIface i) (HighIface i).
Proof.
  intros i.
  apply (subT_variance i (pol_low i (fun _ => utanyT)) (pol_high i (fun _ => utanyT))).
  intro p.
  unfold pol_low, pol_high.
  destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
  - exact (isnegative utanyT utbotT (subT_bot utanyT)).
  - exact (ispositive utbotT utanyT (subT_top utbotT)).
Qed.

Lemma ur_absurd : forall (u : UserType Empty), UnReachableUserType u -> FalseS.
Proof. intros u h. destruct h. Qed.

Section SubUserMore.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (ideq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition dec_signed_subuser (Var : Type)
    (vdeq : forall x y : Var, {x = y} + {x = y -> False})
    (s : Sign) (u v : UserType Var) : DeciderS (Signed SubUserType s u v)
  := match s as sg return DeciderS (Signed SubUserType sg u v) with
     | negative => dec_subuser IPFin ideq Var vdeq v u
     | positive => dec_subuser IPFin ideq Var vdeq u v
     end.

  Definition dec_unreachable_usertype (u : UserType Empty) : DeciderS (UnReachableUserType u)
  := sbrightS (ur_absurd u).
End SubUserMore.

Lemma convert_eqS_self {A : Type} `{DecEq A} `{SSet A}
  (a : A) (e : eqS a a) (B : A -> Type) (b : B a) : convert e B b = b.
Proof.
  unfold convert.
  exact (eq_sym (@eq_rect_eq_dec A (fun x y => dec_eq x y) a B b (eqS_eq e))).
Qed.

Definition utsubst {Var : Type} (tau : Var -> UT) (u : UserType Var) : UT
:= utfold utanyT utifaceT tau u.

Section SubstSimSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).
  Context (Var : Type).

  Fixpoint AssignRel (u : UserType Var) (s : Sign)
    (sigma sigma' : Var -> S.(SpaceType)) (tau tau' : Var -> UT) : SProp
  := match u with
     | utvariable q => Signed S.(SubSpaceType) s (sigma q) (sigma' q) -> Signed SubT s (tau q) (tau' q)
     | utany => TrueS
     | utinterface i f =>
         forall p : IParameter scheme i,
           match s with
           | positive => AssignRel (f p) ((hierarchy.(hinterface) i).(uisvariance) p) sigma sigma' tau tau'
           | negative => AssignRel (f p) ((hierarchy.(hinterface) i).(uisvariance) p) sigma' sigma tau' tau
           end
     end.

  Lemma tsubst_sim : forall (u : UserType Var) (s : Sign)
    (sigma sigma' : Var -> S.(SpaceType)) (tau tau' : Var -> UT),
    AssignRel u s sigma sigma' tau tau' ->
    Signed S.(SubSpaceType) s (tsubst (space:=S) sigma u) (tsubst (space:=S) sigma' u) ->
    Signed SubT s (utsubst tau u) (utsubst tau' u).
  Proof.
    induction u as [q | | i f IH]; intros s sigma sigma' tau tau' Hass Hrel.
    - simpl in *. exact (Hass Hrel).
    - destruct s; simpl; exact (subT_top utanyT).
    - destruct s.
      + (* negative *)
        simpl in Hass. simpl in Hrel.
        destruct (ctsinterface CS i (fun p => tsubst (space:=S) sigma' (f p)) i
                    (fun p => tsubst (space:=S) sigma (f p)) Hrel) as [e Hpt].
        apply (subT_variance i (fun p => utsubst tau' (f p)) (fun p => utsubst tau (f p))).
        intro p.
        specialize (Hpt p).
        rewrite (convert_eqS_self i e (IParameter scheme) p) in Hpt.
        specialize (Hass p).
        apply signed_isigned.
        exact (IH p ((hierarchy.(hinterface) i).(uisvariance) p) sigma' sigma tau' tau Hass Hpt).
      + (* positive *)
        simpl in Hass. simpl in Hrel.
        destruct (ctsinterface CS i (fun p => tsubst (space:=S) sigma (f p)) i
                    (fun p => tsubst (space:=S) sigma' (f p)) Hrel) as [e Hpt].
        apply (subT_variance i (fun p => utsubst tau (f p)) (fun p => utsubst tau' (f p))).
        intro p.
        specialize (Hpt p).
        rewrite (convert_eqS_self i e (IParameter scheme) p) in Hpt.
        specialize (Hass p).
        apply signed_isigned.
        exact (IH p ((hierarchy.(hinterface) i).(uisvariance) p) sigma sigma' tau tau' Hass Hpt).
  Qed.
End SubstSimSection.

Section ContextTools.
  Context {S : TypeSpace}.

  Lemma AssignRel_refl : forall (Var : Type) (u : UserType Var) (s : Sign)
    (sigma : Var -> S.(SpaceType)) (tau : Var -> UT),
    AssignRel Var u s sigma sigma tau tau.
  Proof.
    intros Var u. induction u as [q | | i f IH]; intros s sigma tau.
    - simpl. intro. destruct s; exact (subT_refl (tau q)).
    - simpl. exact trueS.
    - simpl. destruct s; intro p; apply IH.
  Qed.

  Lemma check_context_lower :
    forall (Input : Sort) (ctx ctx' : SortElimination S.(SpaceType) Input),
      (forall input : SumSort Input, S.(SubSpaceType) (apply_elimination ctx' input) (apply_elimination ctx input)) ->
      forall (e : Expression Input) (t : S.(SpaceType)),
        CheckExpression S ctx e t -> CheckExpression S ctx' e t.
  Proof.
    intros Input ctx ctx' Hctx e t h.
    induction h.
    - exact (@cesub S Input ctx' expression t t' (IHh ctx' Hctx) s).
    - exact (@cesub S Input ctx' (einput input) (apply_elimination ctx' input)
               (apply_elimination context input)
               (@ceinput S Input ctx' input) (Hctx input)).
    - exact (@ceinvoke S Input ctx' ereceiver method einputs treceiver signature c (IHh ctx' Hctx) (fun input => H input ctx' Hctx)).
    - refine (@ceobject S Input ctx' interface methods bodies arguments signatures s _).
      intros method contains.
      refine (H method contains (pair_elimination (smsinput (signatures method contains)) ctx') _).
      intros input.
      destruct input as [x | y].
      + simpl. exact (S.(sstrefl) (smsinput (signatures method contains) x)).
      + simpl. exact (Hctx y).
  Qed.
End ContextTools.

Section RepSetupSection.
  Context {S : TypeSpace}.
  Variable RepArgs : forall (i : Interface scheme)
    (a : IParameter scheme i -> S.(SpaceType)) (b : IParameter scheme i -> UT), SProp.

  Inductive SRep (t : S.(SpaceType)) : UT -> SProp :=
  | srep_any : SRep utanyT
  | srep_bot : S.(UnReachable) t -> SRep utbotT
  | srep_iface (i : Interface scheme)
      (a : IParameter scheme i -> S.(SpaceType)) (b : IParameter scheme i -> UT) :
      S.(SubSpaceType) t (S.(stinterface) i a) ->
      RepArgs i a b ->
      SRep (utifaceT i b).

  Lemma SRep_lower : forall (t t' : S.(SpaceType)) (u : UT),
    SRep t' u -> S.(SubSpaceType) t t' -> SRep t u.
  Proof.
    intros t t' u h sub. destruct h as [| ur | i a b hle hra].
    - exact (srep_any t).
    - apply (srep_bot t). exact (S.(sstur) t t' sub ur).
    - apply (srep_iface t i a b).
      + exact (S.(ssttrans) t t' (S.(stinterface) i a) sub hle).
      + exact hra.
  Qed.
End RepSetupSection.


Section MutRepSection.
  Context {S : TypeSpace}.

  Inductive RArgs : forall (i : Interface scheme),
      (IParameter scheme i -> S.(SpaceType)) ->
      (IParameter scheme i -> UT) -> SProp :=
  | mkRArgs (i : Interface scheme)
      (a : IParameter scheme i -> S.(SpaceType))
      (b : IParameter scheme i -> UT) :
      (forall p, RRep (a p) (b p)) -> RArgs i a b
  with RRep : S.(SpaceType) -> UT -> SProp :=
  | rrep_any (t : S.(SpaceType)) : RRep t utanyT
  | rrep_bot (t : S.(SpaceType)) : S.(UnReachable) t -> RRep t utbotT
  | rrep_iface (t : S.(SpaceType)) (i : Interface scheme)
      (a : IParameter scheme i -> S.(SpaceType))
      (b : IParameter scheme i -> UT) :
      S.(SubSpaceType) t (S.(stinterface) i a) ->
      RArgs i a b ->
      RRep t (utifaceT i b).

  Lemma RRep_lower : forall (t t' : S.(SpaceType)) (u : UT),
    RRep t' u -> S.(SubSpaceType) t t' -> RRep t u.
  Proof.
    intros t t' u h sub. destruct h as [t0 | t0 ur | t0 i a b hle hra].
    - exact (rrep_any t).
    - apply (rrep_bot t). exact (S.(sstur) t t0 sub ur).
    - apply (rrep_iface t i a b).
      + exact (S.(ssttrans) t t0 (S.(stinterface) i a) sub hle).
      + exact hra.
  Qed.

  Lemma RRep_subst : forall (Var : Type) (R : UserType Var)
    (sigma : Var -> S.(SpaceType)) (tau : Var -> UT),
    (forall q, RRep (sigma q) (tau q)) ->
    RRep (tsubst (space:=S) sigma R) (utsubst tau R).
  Proof.
    intros Var R. induction R as [q | | i f IH]; intros sigma tau Hass.
    - exact (Hass q).
    - exact (rrep_any (S.(stany))).
    - simpl.
      apply (rrep_iface (S.(stinterface) i (fun p => tsubst (space:=S) sigma (f p)))
                        i (fun p => tsubst (space:=S) sigma (f p))
                        (fun p => utsubst tau (f p))).
      + exact (S.(sstrefl) (S.(stinterface) i (fun p => tsubst (space:=S) sigma (f p)))).
      + apply mkRArgs. intro p. exact (IH p sigma tau Hass).
  Qed.
End MutRepSection.

Section RObjSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Lemma RRep_obj : forall (i j : Interface scheme)
    (args : IParameter scheme j -> S.(SpaceType))
    (a : IParameter scheme i -> S.(SpaceType))
    (b : IParameter scheme i -> UT),
    S.(SubSpaceType) (S.(stinterface) j args) (S.(stinterface) i a) ->
    RArgs i a b ->
    existsTSS c : IParameter scheme j -> UT,
      RArgs j args c & SubT (utifaceT j c) (utifaceT i b).
  Proof.
    intros i j args a b h hra.
    destruct (ctsinterface CS j args i a h) as [e hpt].
    destruct (eqS_eq e).
    assert (hc : forall p : IParameter scheme j,
      Signed S.(SubSpaceType) ((hierarchy.(hinterface) j).(uisvariance) p) (args p) (a p)).
    { intro p. specialize (hpt p).
      rewrite (convert_eqS_self j e (IParameter scheme) p) in hpt. exact hpt. }
    pose (c := fun p : IParameter scheme j =>
      match ((hierarchy.(hinterface) j).(uisvariance) p) with
      | negative => utanyT
      | positive => b p
      end).
    refine (ex_introSSS c _ _).
    - destruct hra as [hrp aa bb hfun].
      apply (mkRArgs hrp args c). intro p.
      pose proof (hc p) as hp.
      pose proof (hfun p) as hrpp.
      unfold c.
      destruct ((hierarchy.(hinterface) hrp).(uisvariance) p) as [|].
      + exact (rrep_any (args p)).
      + apply (RRep_lower (args p) (aa p) (bb p) hrpp).
        exact hp.
    - unfold c.
      apply (subT_variance j (fun p => match ((hierarchy.(hinterface) j).(uisvariance) p) with
                                      | negative => utanyT
                                      | positive => b p
                                      end) b).
      intro p.
      destruct ((hierarchy.(hinterface) j).(uisvariance) p) as [|].
      + exact (isnegative utanyT (b p) (subT_top (b p))).
      + exact (ispositive (b p) (b p) (subT_refl (b p))).
  Qed.
End RObjSection.

Section RClassSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Lemma RRep_above_any : forall (t : S.(SpaceType)) (u : UT),
    S.(SubSpaceType) S.(stany) t -> RRep t u -> eqS u utanyT.
  Proof.
    intros t u hab hr.
    destruct hr as [t0 | t0 ur | t0 i a b hle hra].
    - exact (eqS_refl utanyT).
    - exact (falseSeS (ctsanyunreachable CS (S.(sstur) S.(stany) t0 hab ur))).
    - exact (falseSeS (ctsanyinterface CS i a
               (S.(ssttrans) S.(stany) t0 (S.(stinterface) i a) hab hle))).
  Qed.

  Lemma RRep_bot_inv : forall (t : S.(SpaceType)),
    RRep t utbotT -> S.(UnReachable) t.
  Proof.
    intros t h. inversion h.
    - (* rrep_bot *) assumption.
  Qed.

  Lemma RRep_iface_inv : forall (t : S.(SpaceType)) (i : Interface scheme)
    (b : IParameter scheme i -> UT),
    RRep t (utifaceT i b) ->
    existsTSS a : IParameter scheme i -> S.(SpaceType),
      S.(SubSpaceType) t (S.(stinterface) i a) & RArgs i a b.
  Proof.
    intros t i b h. inversion h.
    assert (Hb : b1 = b).
    { apply (@k_inj_projT2 (Interface scheme)
               (fun i => IParameter scheme i -> UT) i
               (interface_K (fun x y => dec_eq x y) i) b1 b).
      exact H2. }
    subst b1.
    exact (ex_introSSS a H4 H5).
  Qed.
End RClassSection.

Lemma eqS_utany_top : forall (u u' : UT), eqS u' utanyT -> SubT u u'.
Proof.
  intros u u' e. destruct u'.
  - exact (subT_top u).
  - inversion e.
  - inversion e.
Qed.

Section RMonoSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Lemma RRep_top : forall (t : S.(SpaceType)) (u : UT), RRep t u -> SubT u utanyT.
  Proof. intros t u h. exact (subT_top u). Qed.

  Lemma RRep_mono_stany : forall (t t' : S.(SpaceType)) (u u' : UT),
    S.(SubSpaceType) t t' ->
    S.(SubSpaceType) S.(stany) t' ->
    RRep t u -> RRep t' u' -> SubT u u'.
  Proof.
    intros t t' u u' hsub hab hr hr'.
    pose proof (RRep_above_any CS t' u' hab hr') as e.
    exact (eqS_utany_top u u' e).
  Qed.
End RMonoSection.

Section TRepSection.
  Context {S : TypeSpace}.

  Inductive TArgs : forall (i : Interface scheme),
      (IParameter scheme i -> S.(SpaceType)) ->
      (IParameter scheme i -> UT) -> SProp :=
  | mkTArgs (i : Interface scheme)
      (a : IParameter scheme i -> S.(SpaceType))
      (b : IParameter scheme i -> UT) :
      (forall p, TRep (a p) (b p)) -> TArgs i a b
  with TRep : S.(SpaceType) -> UT -> SProp :=
  | trep_any (t : S.(SpaceType)) :
      S.(SubSpaceType) S.(stany) t -> TRep t utanyT
  | trep_bot (t : S.(SpaceType)) :
      S.(UnReachable) t -> TRep t utbotT
  | trep_iface (t : S.(SpaceType)) (i : Interface scheme)
      (a : IParameter scheme i -> S.(SpaceType))
      (b : IParameter scheme i -> UT) :
      S.(SubSpaceType) t (S.(stinterface) i a) ->
      TArgs i a b ->
      TRep t (utifaceT i b).

  Lemma TRep_subst : forall (Var : Type) (R : UserType Var)
    (sigma : Var -> S.(SpaceType)) (tau : Var -> UT),
    (forall q, TRep (sigma q) (tau q)) ->
    TRep (tsubst (space:=S) sigma R) (utsubst tau R).
  Proof.
    intros Var R. induction R as [q | | i f IH]; intros sigma tau Hass.
    - exact (Hass q).
    - apply trep_any. exact (S.(sstrefl) S.(stany)).
    - simpl.
      apply (trep_iface (S.(stinterface) i (fun p => tsubst (space:=S) sigma (f p)))
                        i (fun p => tsubst (space:=S) sigma (f p))
                        (fun p => utsubst tau (f p))).
      + exact (S.(sstrefl) (S.(stinterface) i (fun p => tsubst (space:=S) sigma (f p)))).
      + apply mkTArgs. intro p. exact (IH p sigma tau Hass).
  Qed.
End TRepSection.

Section TClassSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Lemma TRep_above_any : forall (t : S.(SpaceType)) (u : UT),
    S.(SubSpaceType) S.(stany) t -> TRep t u -> eqS u utanyT.
  Proof.
    intros t u hab hr.
    destruct hr as [t0 hany | t0 ur | t0 i a b hle hta].
    - exact (eqS_refl utanyT).
    - exact (falseSeS (ctsanyunreachable CS (S.(sstur) S.(stany) t0 hab ur))).
    - exact (falseSeS (ctsanyinterface CS i a
               (S.(ssttrans) S.(stany) t0 (S.(stinterface) i a) hab hle))).
  Qed.

  Lemma TRep_bot_inv : forall (t : S.(SpaceType)),
    TRep t utbotT -> S.(UnReachable) t.
  Proof.
    intros t h. inversion h.
    - assumption.
  Qed.

  Lemma TRep_iface_inv : forall (t : S.(SpaceType)) (i : Interface scheme)
    (b : IParameter scheme i -> UT),
    TRep t (utifaceT i b) ->
    existsTSS a : IParameter scheme i -> S.(SpaceType),
      S.(SubSpaceType) t (S.(stinterface) i a) & TArgs i a b.
  Proof.
    intros t i b h. inversion h.
    assert (Hb : b1 = b).
    { apply (@k_inj_projT2 (Interface scheme)
               (fun i => IParameter scheme i -> UT) i
               (interface_K (fun x y => dec_eq x y) i) b1 b).
      exact H2. }
    subst b1.
    exact (ex_introSSS a H4 H5).
  Qed.
End TClassSection.

Section TToRSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context {S : TypeSpace}.

  Fixpoint TRep_to_RRep_n (n : nat) (t : S.(SpaceType)) (u : UT)
    (h : TRep t u) (Hle : ut_size IPFin u <= n) {struct n} : RRep t u.
  Proof.
    destruct n as [| n'].
    - destruct h as [t0 hany | t0 ur | t0 i a b hle hta].
      + exact (rrep_any t0).
      + exact (rrep_bot t0 ur).
      + assert (Hf : False) by (cbn in Hle; lia).
        exact (falseSeS (false_falseS Hf)).
    - destruct h as [t0 hany | t0 ur | t0 i a b hle hta].
      + exact (rrep_any t0).
      + exact (rrep_bot t0 ur).
      + destruct hta as [ht].
        refine (rrep_iface t0 ht a b hle _).
        apply mkRArgs. intro p.
        assert (Hp : ut_size IPFin (b p) <= n').
        { assert (hsub := ut_size_sub IPFin ht b p). lia. }
        exact (TRep_to_RRep_n n' (a p) (b p) (t p) Hp).
  Qed.

  Definition TRep_to_RRep (t : S.(SpaceType)) (u : UT) (h : TRep t u) : RRep t u
  := TRep_to_RRep_n (ut_size IPFin u) t u h (le_n _).
End TToRSection.

Section TInvSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.

  Lemma TRep_any_inv : forall (t : S.(SpaceType)),
    TRep t utanyT -> S.(SubSpaceType) S.(stany) t.
  Proof.
    intros t h. inversion h.
    - assumption.
  Qed.
End TInvSection.

Section RAbsurdSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Lemma RRep_iface_above_absurd : forall (t : S.(SpaceType))
    (i : Interface scheme) (b : IParameter scheme i -> UT),
    S.(SubSpaceType) S.(stany) t -> RRep t (utifaceT i b) -> FalseS.
  Proof.
    intros t i b hab hr.
    pose proof (RRep_above_any CS t (utifaceT i b) hab hr) as e.
    inversion e.
  Qed.

  Lemma RRep_bot_above_absurd : forall (t : S.(SpaceType)),
    S.(SubSpaceType) S.(stany) t -> RRep t utbotT -> FalseS.
  Proof.
    intros t hab hr.
    pose proof (RRep_above_any CS t utbotT hab hr) as e.
    inversion e.
  Qed.

  Lemma TRep_iface_above_absurd : forall (t : S.(SpaceType))
    (i : Interface scheme) (b : IParameter scheme i -> UT),
    S.(SubSpaceType) S.(stany) t -> TRep t (utifaceT i b) -> FalseS.
  Proof.
    intros t i b hab hr.
    pose proof (TRep_above_any CS t (utifaceT i b) hab hr) as e.
    inversion e.
  Qed.

  Lemma TRep_bot_above_absurd : forall (t : S.(SpaceType)),
    S.(SubSpaceType) S.(stany) t -> TRep t utbotT -> FalseS.
  Proof.
    intros t hab hr.
    pose proof (TRep_above_any CS t utbotT hab hr) as e.
    inversion e.
  Qed.
End RAbsurdSection.

Section SubTInvSection.
  Context `{DecEq (Interface scheme)}.

  Lemma subT_bot_target_inv : forall (u : UT), SubT u utbotT -> eqS u utbotT.
  Proof.
    intros u h. inversion h.
    - exact (eqS_refl utbotT).
  Qed.

  Lemma subT_any_source_inv : forall (u : UT), SubT utanyT u -> eqS u utanyT.
  Proof.
    intros u h. inversion h.
    - exact (eqS_refl utanyT).
  Qed.

  Lemma subT_iface_source_inv : forall (i : Interface scheme)
    (a : IParameter scheme i -> UT) (u : UT),
    SubT (utifaceT i a) u ->
    OrS (eqS u utanyT)
        (existsTSS b : IParameter scheme i -> UT,
           eqS u (utifaceT i b) &
           (forall p, ISigned SubT ((hierarchy.(hinterface) i).(uisvariance) p) (a p) (b p))).
  Proof.
    intros i a u h. inversion h.
    - exact (oleftS (eqS_refl utanyT)).
    - right.
      assert (Ha : args0 = a).
      { apply (@k_inj_projT2 (Interface scheme)
                 (fun i => IParameter scheme i -> UT) i
                 (interface_K (fun x y => dec_eq x y) i) args0 a). exact H2. }
      subst args0.
      exact (ex_introSSS args' (eqS_refl (utifaceT i args')) H3).
  Qed.
End SubTInvSection.

Section TRepLowerSection.
  Context {S : TypeSpace}.
  Context `{DecEq (Interface scheme)}.

  Lemma TRep_lower_bot : forall (t t' : S.(SpaceType)),
    TRep t' utbotT -> S.(SubSpaceType) t t' -> TRep t utbotT.
  Proof.
    intros t t' h sub.
    apply (trep_bot t).
    exact (S.(sstur) t t' sub (TRep_bot_inv t' h)).
  Qed.

  Lemma TRep_lower_iface : forall (t t' : S.(SpaceType)) (i : Interface scheme)
    (b : IParameter scheme i -> UT),
    TRep t' (utifaceT i b) -> S.(SubSpaceType) t t' -> TRep t (utifaceT i b).
  Proof.
    intros t t' i b h sub.
    destruct (TRep_iface_inv t' i b h) as [a hle hta].
    apply (trep_iface t i a b).
    - exact (S.(ssttrans) t t' (S.(stinterface) i a) sub hle).
    - exact hta.
  Qed.
End TRepLowerSection.

Lemma subT_LowIface_refl : forall (i : Interface scheme), SubT (LowIface i) (LowIface i).
Proof. intro i. exact (subT_refl (LowIface i)). Qed.

Lemma subT_LowIface_any : forall (i : Interface scheme), SubT (LowIface i) utanyT.
Proof. intro i. exact (subT_top (LowIface i)). Qed.

Lemma subT_bot_LowIface : forall (i : Interface scheme), SubT utbotT (LowIface i).
Proof. intro i. exact (subT_bot (LowIface i)). Qed.

Lemma subT_bot_high : forall (i : Interface scheme), SubT utbotT (HighIface i).
Proof. intro i. exact (subT_bot (HighIface i)). Qed.

Inductive Sh : Type :=
| shbot : Sh
| shany : Sh
| shiface (i : Interface scheme) : Sh.

Definition realize (s : Sh) : UT
:= match s with
   | shbot => utbotT
   | shany => utanyT
   | shiface i => LowIface i
   end.

Inductive ShSub : Sh -> Sh -> SProp :=
| shsub_bot (b : Sh) : ShSub shbot b
| shsub_any (a : Sh) : ShSub a shany
| shsub_iface (i : Interface scheme) : ShSub (shiface i) (shiface i).

Arguments ShSub : clear implicits.

Lemma ShSub_realize : forall (s t : Sh), ShSub s t -> SubT (realize s) (realize t).
Proof.
  intros s t h. destruct h as [b | a | i].
  - simpl. exact (subT_bot (realize b)).
  - simpl. exact (subT_top (realize a)).
  - simpl. exact (subT_refl (LowIface i)).
Qed.

Lemma ShSub_refl : forall (s : Sh), ShSub s s.
Proof.
  intro s. destruct s as [| | i].
  - exact (shsub_bot shbot).
  - exact (shsub_any shany).
  - exact (shsub_iface i).
Qed.

Lemma ShSub_any_bot_absurd : ShSub shany shbot -> FalseS.
Proof. intro h. inversion h. Qed.

Lemma ShSub_any_iface_absurd : forall (j : Interface scheme),
  ShSub shany (shiface j) -> FalseS.
Proof. intros j h. inversion h. Qed.

Lemma ShSub_iface_bot_absurd : forall (i : Interface scheme),
  ShSub (shiface i) shbot -> FalseS.
Proof. intros i h. inversion h. Qed.

Lemma ShSub_iface_neq_absurd : forall (i j : Interface scheme),
  (i = j -> False) -> ShSub (shiface i) (shiface j) -> FalseS.
Proof.
  intros i j ne h. inversion h.
  exact (false_falseS (ne H)).
Qed.

Definition dec_shsub (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (s t : Sh) : DeciderS (ShSub s t).
Proof.
  destruct s as [| | i]; destruct t as [| | j].
  - exact (sbleftS (shsub_bot shbot)).
  - exact (sbleftS (shsub_bot shany)).
  - exact (sbleftS (shsub_bot (shiface j))).
  - exact (sbrightS (fun h => ShSub_any_bot_absurd h)).
  - exact (sbleftS (shsub_any shany)).
  - exact (sbrightS (fun h => ShSub_any_iface_absurd j h)).
  - exact (sbrightS (fun h => ShSub_iface_bot_absurd i h)).
  - exact (sbleftS (shsub_any (shiface i))).
  - destruct (deq i j) as [e | ne].
    + subst j. exact (sbleftS (shsub_iface i)).
    + exact (sbrightS (fun h => ShSub_iface_neq_absurd i j ne h)).
Qed.

Definition shlist (l : list (Interface scheme)) : list Sh
:= shbot :: shany :: map shiface l.

Lemma shlist_In : forall (l : list (Interface scheme)) (s : Sh),
  (forall i : Interface scheme, In i l) -> In s (shlist l).
Proof.
  intros l s Hall. destruct s as [| | i].
  - simpl. left. reflexivity.
  - simpl. right. left. reflexivity.
  - simpl. right. right. apply in_map. apply Hall.
Qed.

Definition shshape {Var : Type} (ps : Var -> Sh) (u : UserType Var) : Sh
:= match u with
   | utvariable p => ps p
   | utany => shany
   | utinterface i _ => shiface i
   end.

Definition shrealize {Var : Type} (ps : Var -> Sh) (u : UserType Var) : UT
:= utsubst (fun p => realize (ps p)) u.

Definition realize_high (s : Sh) : UT
:= match s with
   | shbot => utbotT
   | shany => utanyT
   | shiface i => HighIface i
   end.

Definition shrealize_high {Var : Type} (ps : Var -> Sh) (u : UserType Var) : UT
:= utsubst (fun p => realize_high (ps p)) u.

Lemma realize_shshape_le : forall (Var : Type) (ps : Var -> Sh) (u : UserType Var),
  SubT (realize (shshape ps u)) (shrealize ps u).
Proof.
  intros Var ps u. induction u as [p | | i f IH].
  - simpl. exact (subT_refl (realize (ps p))).
  - simpl. exact (subT_refl utanyT).
  - simpl. exact (subT_iface_low i (fun q => shrealize ps (f q))).
Qed.

Lemma shshape_high_le : forall (Var : Type) (ps : Var -> Sh) (u : UserType Var),
  SubT (shrealize_high ps u) (realize_high (shshape ps u)).
Proof.
  intros Var ps u. induction u as [p | | i f IH].
  - simpl. exact (subT_refl (realize_high (ps p))).
  - simpl. exact (subT_refl utanyT).
  - simpl. exact (subT_iface_high i (fun q => shrealize_high ps (f q))).
Qed.

Definition sh_of_ut (u : UT) : Sh
:= match u with
   | utanyT => shany
   | utbotT => shbot
   | utifaceT i _ => shiface i
   end.

Lemma realize_sh_of_ut_le : forall (u : UT),
  SubT (realize (sh_of_ut u)) u.
Proof.
  intro u. destruct u as [| | i args].
  - simpl. exact (subT_refl utanyT).
  - simpl. exact (subT_refl utbotT).
  - simpl. exact (subT_iface_low i args).
Qed.

Lemma realize_high_sh_of_ut_ge : forall (u : UT),
  SubT u (realize_high (sh_of_ut u)).
Proof.
  intro u. destruct u as [| | i args].
  - simpl. exact (subT_refl utanyT).
  - simpl. exact (subT_refl utbotT).
  - simpl. exact (subT_iface_high i args).
Qed.

Lemma ShSub_realize_mixed : forall (s t : Sh),
  ShSub s t -> SubT (realize s) (realize_high t).
Proof.
  intros s t h. destruct h as [b | a | i].
  - simpl. exact (subT_bot (realize_high b)).
  - simpl. exact (subT_top (realize a)).
  - simpl. exact (LowIface_high i).
Qed.

Lemma realize_le_high : forall (s : Sh), SubT (realize s) (realize_high s).
Proof.
  intro s. apply (ShSub_realize_mixed s s (ShSub_refl s)).
Qed.

Lemma shrealize_le_high_shape : forall (Var : Type) (ps : Var -> Sh)
  (u : UserType Var),
  SubT (shrealize ps u) (realize_high (shshape ps u)).
Proof.
  intros Var ps u. induction u as [p | | i f IH].
  - simpl. exact (realize_le_high (ps p)).
  - simpl. exact (subT_refl utanyT).
  - simpl. exact (subT_iface_high i (fun q => shrealize ps (f q))).
Qed.

Section ArgsFitSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition args_of_shapes (i : Interface scheme)
    (ps : IParameter scheme i -> Sh) : IParameter scheme i -> UT
  := fun p => match ((hierarchy.(hinterface) i).(uisvariance) p) with
              | positive => realize (ps p)
              | negative => realize_high (ps p)
              end.

  Lemma ShSub_realize_high : forall (s t : Sh),
    ShSub s t -> SubT (realize_high s) (realize_high t).
  Proof.
    intros s t h. destruct h as [b | a | i].
    - simpl. exact (subT_bot (realize_high b)).
    - simpl. exact (subT_top (realize_high a)).
    - simpl. exact (subT_refl (HighIface i)).
  Qed.

  Lemma args_of_shapes_le : forall (i : Interface scheme)
    (ps : IParameter scheme i -> Sh) (b : IParameter scheme i -> UT),
    (forall p : IParameter scheme i,
       match ((hierarchy.(hinterface) i).(uisvariance) p) with
       | positive => ShSub (ps p) (sh_of_ut (b p))
       | negative => ShSub (sh_of_ut (b p)) (ps p)
       end) ->
    SubT (utifaceT i (args_of_shapes i ps)) (utifaceT i b).
  Proof.
    intros i ps b Hfit.
    apply (subT_variance i (args_of_shapes i ps) b).
    intro p.
    specialize (Hfit p).
    unfold args_of_shapes.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
    - (* negative *)
      simpl in Hfit.
      apply (isnegative (realize_high (ps p)) (b p)).
      refine (subT_trans IPFin deq (b p)
                (realize_high (sh_of_ut (b p)))
                (realize_high (ps p)) _ _).
      + exact (realize_high_sh_of_ut_ge (b p)).
      + exact (ShSub_realize_high (sh_of_ut (b p)) (ps p) Hfit).
    - (* positive *)
      simpl in Hfit.
      apply (ispositive (realize (ps p)) (b p)).
      refine (subT_trans IPFin deq (realize (ps p))
                (realize (sh_of_ut (b p))) (b p) _ _).
      + exact (ShSub_realize (ps p) (sh_of_ut (b p)) Hfit).
      + exact (realize_sh_of_ut_le (b p)).
  Qed.
End ArgsFitSection.

Lemma sh_of_ut_shrealize : forall (Var : Type) (ps : Var -> Sh) (u : UserType Var),
  sh_of_ut (shrealize ps u) = shshape ps u.
Proof.
  intros Var ps u. induction u as [p | | i f IH].
  - simpl. destruct (ps p) as [| | j]; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma sh_of_ut_shrealize_high : forall (Var : Type) (ps : Var -> Sh) (u : UserType Var),
  sh_of_ut (shrealize_high ps u) = shshape ps u.
Proof.
  intros Var ps u. induction u as [p | | i f IH].
  - simpl. destruct (ps p) as [| | j]; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Section ArgsSelfSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma ShSub_refl_any : forall (s : Sh), ShSub s s.
  Proof. exact ShSub_refl. Qed.

  Lemma args_of_shapes_self_le : forall (i : Interface scheme)
    (b : IParameter scheme i -> UT),
    SubT (utifaceT i (args_of_shapes i (fun p => sh_of_ut (b p))))
         (utifaceT i b).
  Proof.
    intros i b.
    apply (args_of_shapes_le IPFin deq i (fun p => sh_of_ut (b p)) b).
    intro p.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
    - exact (ShSub_refl (sh_of_ut (b p))).
    - exact (ShSub_refl (sh_of_ut (b p))).
  Qed.
End ArgsSelfSection.

Definition shapes_all (l : list (Interface scheme)) : list Sh
:= shbot :: shany :: map shiface l.

Lemma shapes_all_complete : forall (l : list (Interface scheme)),
  (forall i : Interface scheme, In i l) ->
  forall s : Sh, In s (shapes_all l).
Proof.
  intros l Hall s. destruct s as [| | i].
  - simpl. left. reflexivity.
  - simpl. right. left. reflexivity.
  - simpl. right. right. apply in_map. apply Hall.
Qed.

Section AllAssnsSection.
  Context (i : Interface scheme).
  Context (pdeq : forall x y : IParameter scheme i, {x = y} + {x = y -> False}).
  Context (sl : list Sh).
  Context (Hsl : forall s : Sh, In s sl).

  Fixpoint all_assns (l : list (IParameter scheme i)) : list (IParameter scheme i -> Sh)
  := match l with
     | nil => (fun _ => shany) :: nil
     | a :: l' =>
         flat_map
           (fun f => map (fun s => fun p => if pdeq p a then s else f p) sl)
           (all_assns l')
     end.

  Lemma all_assns_complete : forall (l : list (IParameter scheme i))
    (ps : IParameter scheme i -> Sh),
    exists f : IParameter scheme i -> Sh,
      In f (all_assns l) /\ forall p : IParameter scheme i, In p l -> ps p = f p.
  Proof.
    induction l as [| a l' IH]; intros ps.
    - exists (fun _ => shany). split.
      + simpl. left. reflexivity.
      + intros p Hin. destruct Hin.
    - destruct (IH ps) as [f [Hf Hagree]].
      exists (fun p => if pdeq p a then ps a else f p). split.
      + simpl. apply in_flat_map. exists f. split; [exact Hf |].
        apply in_map_iff. exists (ps a). split; [reflexivity | exact (Hsl (ps a))].
      + intros p Hin. destruct Hin as [e | Hin].
        * subst p. simpl. destruct (pdeq a a) as [e | ne].
          -- reflexivity.
          -- exfalso. apply ne. reflexivity.
        * simpl. destruct (pdeq p a) as [e | ne].
          -- subst p. reflexivity.
          -- apply Hagree. exact Hin.
  Qed.
End AllAssnsSection.

Lemma ShSub_trans : forall (s t u : Sh), ShSub s t -> ShSub t u -> ShSub s u.
Proof.
  intros s t u h1 h2.
  destruct h1 as [b | a | i].
  - exact (shsub_bot u).
  - inversion h2; subst; auto using shsub_bot, shsub_any, shsub_iface.
  - inversion h2; subst; auto using shsub_bot, shsub_any, shsub_iface.
Qed.

Section ObjShapesSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition formalBody (i : Interface scheme) : UserBodySignature (IParameter scheme i)
  := (hierarchy.(hinterface) i).(uisbody).

  Definition obj_signature (i : Interface scheme) (ps : IParameter scheme i -> Sh)
    (m : Method scheme) : SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
  := match dec_bcontains (fun path k => eqS (scpath k) path)
                         (formalBody i).(ubsmethods) (scpath m) with
     | sbleftS cf =>
         @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
           (fun input => utsubst (args_of_shapes i ps)
                (((formalBody i).(ubsmethod) m cf).(umsinput) input))
           (utsubst (args_of_shapes i ps)
                (((formalBody i).(ubsmethod) m cf).(umsresult)))
     | sbrightS _ =>
         @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
           (fun _ => utanyT) utanyT
     end.

  Lemma canon_object_shapes :
    forall (Input : Sort) (ctxc : SortElimination UT Input)
      (i : Interface scheme) (methods : SCSet (Method scheme))
      (bodies : forall method : Method scheme,
                  SCSetContains methods method ->
                  Expression (MInput scheme method :: Input)%list)
      (ps : IParameter scheme i -> Sh)
      (Hcontains : forall m : Method scheme,
          SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m)
      (Hbodies : forall (m : Method scheme) (c : SCSetContains methods m),
          CheckExpression (canonSpace IPFin deq)
            (pair_elimination ((fun m _ => obj_signature i ps m) m c).(smsinput) ctxc)
            (bodies m c)
            ((fun m _ => obj_signature i ps m) m c).(smsresult)),
    CheckExpression (canonSpace IPFin deq) ctxc (eobject i methods bodies)
      (utifaceT i (args_of_shapes i ps)).
  Proof.
    intros Input ctxc i methods bodies ps Hcontains Hbodies.
    pose (argsC := (fun p => (args_of_shapes i ps p : SpaceType (canonSpace IPFin deq)))).
    refine (@ceobject (canonSpace IPFin deq) Input ctxc i methods bodies
              argsC (fun m _ => obj_signature i ps m) _ _).
    - refine (@Build_SubSpaceBodySignature (canonSpace IPFin deq)
                (@Build_SpaceBodySignature (canonSpace IPFin deq) methods
                   (fun m _ => obj_signature i ps m))
                (@bssubst (IParameter scheme i) (canonSpace IPFin deq) argsC (formalBody i))
                (fun m c => Hcontains m c) _).
      intros m cf.
      unfold obj_signature.
      destruct (dec_bcontains (fun path k => eqS (scpath k) path)
                  (formalBody i).(ubsmethods) (scpath m)) as [cf' | ncf] eqn:Edec.
      + change (SubSpaceMethodSignature
          (match dec_bcontains (fun path k => eqS (scpath k) path)
                   (formalBody i).(ubsmethods) (scpath m) with
           | sbleftS cf0 =>
               @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                 (fun input => utsubst (args_of_shapes i ps)
                    (((formalBody i).(ubsmethod) m cf0).(umsinput) input))
                 (utsubst (args_of_shapes i ps)
                    (((formalBody i).(ubsmethod) m cf0).(umsresult)))
           | sbrightS _ =>
               @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                 (fun _ => utanyT) utanyT
           end)
          (@Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
             (fun input => utsubst (fun p => args_of_shapes i ps p)
                (((formalBody i).(ubsmethod) m cf).(umsinput) input))
             (utsubst (fun p => args_of_shapes i ps p)
                (((formalBody i).(ubsmethod) m cf).(umsresult))))).
        rewrite Edec.
        refine (@Build_SubSpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m) _ _ _ _).
        * intro input. exact (subT_refl _).
        * exact (subT_refl _).
      + exact (falseSeS (ncf cf)).
    - exact Hbodies.
  Qed.
End ObjShapesSection.

Section InvShapesSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma canon_invoke_unreachable :
    forall (Input : Sort) (ctxc : SortElimination UT Input)
      (er : Expression Input) (m : Method scheme)
      (eargs : MInput scheme m -> Expression Input) (u : UT),
      CheckExpression (canonSpace IPFin deq) ctxc er utbotT ->
      (forall input : MInput scheme m,
         CheckExpression (canonSpace IPFin deq) ctxc (eargs input) utanyT) ->
      CheckExpression (canonSpace IPFin deq) ctxc (einvoke er m eargs) u.
  Proof.
    intros Input ctxc er m eargs u Hr Ha.
    refine (@ceinvoke (canonSpace IPFin deq) Input ctxc er m eargs utbotT
              (@Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                 (fun _ => utanyT) u) _ Hr Ha).
    refine (@cmunreachable (canonSpace IPFin deq) m utbotT
              (@Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                 (fun _ => utanyT) u) _).
    exact trueS.
  Qed.

  Lemma canon_invoke_iface :
    forall (Input : Sort) (ctxc : SortElimination UT Input)
      (i : Interface scheme) (m : Method scheme)
      (contains : SCSetContains (formalBody i).(ubsmethods) m)
      (ps : IParameter scheme i -> Sh)
      (er : Expression Input)
      (eargs : MInput scheme m -> Expression Input),
      CheckExpression (canonSpace IPFin deq) ctxc er
        (utifaceT i (args_of_shapes i ps)) ->
      (forall input : MInput scheme m,
         CheckExpression (canonSpace IPFin deq) ctxc (eargs input)
           (utsubst (args_of_shapes i ps)
              (((formalBody i).(ubsmethod) m contains).(umsinput) input))) ->
      CheckExpression (canonSpace IPFin deq) ctxc (einvoke er m eargs)
        (utsubst (args_of_shapes i ps)
           (((formalBody i).(ubsmethod) m contains).(umsresult))).
  Proof.
    intros Input ctxc i m contains ps er eargs Hr Ha.
    refine (@ceinvoke (canonSpace IPFin deq) Input ctxc er m eargs
              (utifaceT i (args_of_shapes i ps))
              (@mssubst (IParameter scheme i) (MInput scheme m) (canonSpace IPFin deq)
                 (args_of_shapes i ps) ((formalBody i).(ubsmethod) m contains)) _ Hr _).
    - refine (@cminterface (canonSpace IPFin deq) m i (args_of_shapes i ps) contains).
    - intro input. exact (Ha input).
  Qed.
End InvShapesSection.

Lemma sh_of_ut_utsubst_args : forall (i : Interface scheme)
  (ps : IParameter scheme i -> Sh) (u : UserType (IParameter scheme i)),
  sh_of_ut (utsubst (args_of_shapes i ps) u) = shshape ps u.
Proof.
  intros i ps u. induction u as [p | | j f IH].
  - simpl. unfold args_of_shapes.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|];
      destruct (ps p) as [| | k]; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Section ObjGenSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition obj_signature_gen (i : Interface scheme) (c : IParameter scheme i -> UT)
    (m : Method scheme) : SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
  := match dec_bcontains (fun path k => eqS (scpath k) path)
                         (formalBody i).(ubsmethods) (scpath m) with
     | sbleftS cf =>
         @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
           (fun input => utsubst (c)
                (((formalBody i).(ubsmethod) m cf).(umsinput) input))
           (utsubst (c)
                (((formalBody i).(ubsmethod) m cf).(umsresult)))
     | sbrightS _ =>
         @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
           (fun _ => utanyT) utanyT
     end.

  Lemma canon_object_gen :
    forall (Input : Sort) (ctxc : SortElimination UT Input)
      (i : Interface scheme) (methods : SCSet (Method scheme))
      (bodies : forall method : Method scheme,
                  SCSetContains methods method ->
                  Expression (MInput scheme method :: Input)%list)
      (c : IParameter scheme i -> UT)
      (Hcontains : forall m : Method scheme,
          SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m)
      (Hbodies : forall (m : Method scheme) (hc : SCSetContains methods m),
          CheckExpression (canonSpace IPFin deq)
            (pair_elimination ((fun m _ => obj_signature_gen i c m) m c).(smsinput) ctxc)
            (bodies m hc)
            ((fun m _ => obj_signature_gen i c m) m c).(smsresult)),
    CheckExpression (canonSpace IPFin deq) ctxc (eobject i methods bodies)
      (utifaceT i (c)).
  Proof.
    intros Input ctxc i methods bodies c Hcontains Hbodies.
    pose (argsC := (fun p => (c p : SpaceType (canonSpace IPFin deq)))).
    refine (@ceobject (canonSpace IPFin deq) Input ctxc i methods bodies
              argsC (fun m _ => obj_signature_gen i c m) _ _).
    - refine (@Build_SubSpaceBodySignature (canonSpace IPFin deq)
                (@Build_SpaceBodySignature (canonSpace IPFin deq) methods
                   (fun m _ => obj_signature_gen i c m))
                (@bssubst (IParameter scheme i) (canonSpace IPFin deq) argsC (formalBody i))
                (fun m c => Hcontains m c) _).
      intros m cf.
      unfold obj_signature_gen.
      destruct (dec_bcontains (fun path k => eqS (scpath k) path)
                  (formalBody i).(ubsmethods) (scpath m)) as [cf' | ncf] eqn:Edec.
      + change (SubSpaceMethodSignature
          (match dec_bcontains (fun path k => eqS (scpath k) path)
                   (formalBody i).(ubsmethods) (scpath m) with
           | sbleftS cf0 =>
               @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                 (fun input => utsubst (c)
                    (((formalBody i).(ubsmethod) m cf0).(umsinput) input))
                 (utsubst (c)
                    (((formalBody i).(ubsmethod) m cf0).(umsresult)))
           | sbrightS _ =>
               @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                 (fun _ => utanyT) utanyT
           end)
          (@Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
             (fun input => utsubst (fun p => c p)
                (((formalBody i).(ubsmethod) m cf).(umsinput) input))
             (utsubst (fun p => c p)
                (((formalBody i).(ubsmethod) m cf).(umsresult))))).
        rewrite Edec.
        refine (@Build_SubSpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m) _ _ _ _).
        * intro input. exact (subT_refl _).
        * exact (subT_refl _).
      + exact (falseSeS (ncf cf)).
    - exact Hbodies.
  Qed.
End ObjGenSection.

Section InvGenSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma canon_invoke_iface_gen :
    forall (Input : Sort) (ctxc : SortElimination UT Input)
      (i : Interface scheme) (m : Method scheme)
      (contains : SCSetContains (formalBody i).(ubsmethods) m)
      (c : IParameter scheme i -> UT)
      (er : Expression Input)
      (eargs : MInput scheme m -> Expression Input),
      CheckExpression (canonSpace IPFin deq) ctxc er (utifaceT i c) ->
      (forall input : MInput scheme m,
         CheckExpression (canonSpace IPFin deq) ctxc (eargs input)
           (utsubst c (((formalBody i).(ubsmethod) m contains).(umsinput) input))) ->
      CheckExpression (canonSpace IPFin deq) ctxc (einvoke er m eargs)
        (utsubst c (((formalBody i).(ubsmethod) m contains).(umsresult))).
  Proof.
    intros Input ctxc i m contains c er eargs Hr Ha.
    refine (@ceinvoke (canonSpace IPFin deq) Input ctxc er m eargs
              (utifaceT i c)
              (@mssubst (IParameter scheme i) (MInput scheme m) (canonSpace IPFin deq)
                 c ((formalBody i).(ubsmethod) m contains)) _ Hr _).
    - refine (@cminterface (canonSpace IPFin deq) m i c contains).
    - intro input. exact (Ha input).
  Qed.
End InvGenSection.

Section SubShapeSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma canon_sub_shape : forall (Input : Sort) (ctxc : SortElimination UT Input)
    (e : Expression Input) (s t : Sh),
    CheckExpression (canonSpace IPFin deq) ctxc e (realize s) ->
    ShSub s t ->
    CheckExpression (canonSpace IPFin deq) ctxc e (realize_high t).
  Proof.
    intros Input ctxc e s t Hcheck Hsub.
    exact (@cesub (canonSpace IPFin deq) Input ctxc e (realize s) (realize_high t)
             Hcheck (ShSub_realize_mixed s t Hsub)).
  Qed.

  Lemma canon_to_target : forall (Input : Sort) (ctxc : SortElimination UT Input)
    (e : Expression Input) (s : Sh) (tgt : UT),
    CheckExpression (canonSpace IPFin deq) ctxc e (realize s) ->
    ShSub s (sh_of_ut tgt) ->
    CheckExpression (canonSpace IPFin deq) ctxc e tgt.
  Proof.
    intros Input ctxc e s tgt Hcheck Hsub.
    refine (@cesub (canonSpace IPFin deq) Input ctxc e (realize s) tgt Hcheck _).
    refine (subT_trans IPFin deq (realize s) (realize (sh_of_ut tgt)) tgt _ _).
    - exact (ShSub_realize s (sh_of_ut tgt) Hsub).
    - exact (realize_sh_of_ut_le tgt).
  Qed.
End SubShapeSection.

Section ObjSigFormalSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma obj_signature_gen_formal : forall (i : Interface scheme)
    (c : IParameter scheme i -> UT) (m : Method scheme)
    (cf : SCSetContains (formalBody i).(ubsmethods) m),
    obj_signature_gen IPFin deq i c m
    = mssubst (space := canonSpace IPFin deq) c (((formalBody i).(ubsmethod) m cf)).
  Proof.
    intros i c m cf.
    unfold obj_signature_gen.
    destruct (dec_bcontains (fun path k => eqS (scpath k) path)
                (formalBody i).(ubsmethods) (scpath m)) as [cf' | ncf] eqn:E.
    - simpl.
      unfold mssubst. simpl.
      reflexivity.
    - exfalso. apply falseS_false. exact (ncf cf).
  Qed.
End ObjSigFormalSection.

Lemma utiface_le_realize_high : forall (i : Interface scheme)
  (c : IParameter scheme i -> UT) (s : Sh),
  ShSub (shiface i) s -> SubT (utifaceT i c) (realize_high s).
Proof.
  intros i c s h. inversion h.
  - simpl. exact (subT_top (utifaceT i c)).
  - simpl. exact (subT_iface_high i c).
Qed.

Section ObjTargetSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma canon_object_gen_to_shape :
    forall (Input : Sort) (ctxc : SortElimination UT Input)
      (i : Interface scheme) (methods : SCSet (Method scheme))
      (bodies : forall method : Method scheme,
                  SCSetContains methods method ->
                  Expression (MInput scheme method :: Input)%list)
      (c : IParameter scheme i -> UT) (s : Sh)
      (Hcontains : forall m : Method scheme,
          SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m)
      (Hbodies : forall (m : Method scheme) (hc : SCSetContains methods m),
          CheckExpression (canonSpace IPFin deq)
            (pair_elimination ((fun m _ => obj_signature_gen IPFin deq i c m) m hc).(smsinput) ctxc)
            (bodies m hc)
            ((fun m _ => obj_signature_gen IPFin deq i c m) m hc).(smsresult)),
      ShSub (shiface i) s ->
      CheckExpression (canonSpace IPFin deq) ctxc (eobject i methods bodies)
        (realize_high s).
  Proof.
    intros Input ctxc i methods bodies c s Hcontains Hbodies Hsub.
    refine (@cesub (canonSpace IPFin deq) Input ctxc (eobject i methods bodies)
              (utifaceT i c) (realize_high s) _ _).
    - exact (canon_object_gen IPFin deq Input ctxc i methods bodies c Hcontains Hbodies).
    - exact (utiface_le_realize_high i c s Hsub).
  Qed.
End ObjTargetSection.

Section EInputIffSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma check_einput_forward_gen : forall (Input : Sort)
    (ctxc : SortElimination UT Input) (e : Expression Input) (tgt : UT),
    CheckExpression (canonSpace IPFin deq) ctxc e tgt ->
    forall x : SumSort Input, e = einput x -> SubT (apply_elimination ctxc x) tgt.
  Proof.
    intros Input ctxc e tgt h. induction h; intros x Heq.
    - exact (subT_trans IPFin deq _ _ _ (IHh x Heq) s).
    - injection Heq as Hx. subst. exact (subT_refl (apply_elimination context x)).
    - discriminate Heq.
    - discriminate Heq.
  Qed.

  Lemma check_einput_forward : forall (Input : Sort)
    (ctxc : SortElimination UT Input) (x : SumSort Input) (tgt : UT),
    CheckExpression (canonSpace IPFin deq) ctxc (einput x) tgt ->
    SubT (apply_elimination ctxc x) tgt.
  Proof.
    intros Input ctxc x tgt h.
    exact (check_einput_forward_gen Input ctxc (einput x) tgt h x eq_refl).
  Qed.

  Lemma check_einput_backward : forall (Input : Sort)
    (ctxc : SortElimination UT Input) (x : SumSort Input) (tgt : UT),
    SubT (apply_elimination ctxc x) tgt ->
    CheckExpression (canonSpace IPFin deq) ctxc (einput x) tgt.
  Proof.
    intros Input ctxc x tgt h.
    exact (@cesub (canonSpace IPFin deq) Input ctxc (einput x)
             (apply_elimination ctxc x) tgt
             (@ceinput (canonSpace IPFin deq) Input ctxc x) h).
  Qed.
End EInputIffSection.

Lemma shrealize_empty_le : forall (u : UserType Empty),
  SubT (realize (shshape (emptye (T := Sh)) u)) (utsubst (emptye (T := UT)) u).
Proof.
  intros u. induction u as [e | | i f IH].
  - destruct e.
  - simpl. exact (subT_refl utanyT).
  - simpl. exact (subT_iface_low i (fun p => utsubst (emptye (T := UT)) (f p))).
Qed.

Section ProgramShapeSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma program_canon_target_le : forall (ptype : UserType Empty),
    SubT (realize (shshape (emptye (T := Sh)) ptype))
         (tsubst (space := canonSpace IPFin deq) emptye ptype).
  Proof.
    intro ptype.
    change (SubT (realize (shshape (emptye (T := Sh)) ptype))
              (utsubst (emptye (T := UT)) ptype)).
    exact (shrealize_empty_le ptype).
  Qed.
End ProgramShapeSection.

Section DecFitSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition args_fit (i : Interface scheme) (ps : IParameter scheme i -> Sh)
    (b : IParameter scheme i -> UT) : SProp
  := forall p : IParameter scheme i,
       match ((hierarchy.(hinterface) i).(uisvariance) p) with
       | positive => ShSub (ps p) (sh_of_ut (b p))
       | negative => ShSub (sh_of_ut (b p)) (ps p)
       end.

  Definition dec_args_fit (i : Interface scheme) (ps : IParameter scheme i -> Sh)
    (b : IParameter scheme i -> UT) : DeciderS (args_fit i ps b)
  := @dec_forall (IParameter scheme i) (IPFin i)
       (fun p => match ((hierarchy.(hinterface) i).(uisvariance) p) with
                 | positive => ShSub (ps p) (sh_of_ut (b p))
                 | negative => ShSub (sh_of_ut (b p)) (ps p)
                 end)
       (fun p => match ((hierarchy.(hinterface) i).(uisvariance) p) as sg
                   return DeciderS (match sg with
                                    | positive => ShSub (ps p) (sh_of_ut (b p))
                                    | negative => ShSub (sh_of_ut (b p)) (ps p)
                                    end) with
                 | positive => dec_shsub deq (ps p) (sh_of_ut (b p))
                 | negative => dec_shsub deq (sh_of_ut (b p)) (ps p)
                 end).

  Lemma args_fit_to_le : forall (i : Interface scheme)
    (ps : IParameter scheme i -> Sh) (b : IParameter scheme i -> UT),
    args_fit i ps b ->
    SubT (utifaceT i (args_of_shapes i ps)) (utifaceT i b).
  Proof.
    intros i ps b Hfit.
    exact (args_of_shapes_le IPFin deq i ps b Hfit).
  Qed.
End DecFitSection.


(* ==== Sound canonical-shape check relation ==== *)
Section SChkSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Inductive SChk : forall {Input : Sort},
      SortElimination UT Input -> Expression Input -> UT -> SProp :=
  | schk_input : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (x : SumSort Input),
      SChk ctxc (einput x) (apply_elimination ctxc x)
  | schk_sub : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (e : Expression Input) (u v : UT),
      SChk ctxc e u -> SubT u v -> SChk ctxc e v
  | schk_invoke_unr : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (er : Expression Input) (m : Method scheme)
      (eargs : MInput scheme m -> Expression Input) (u : UT),
      SChk ctxc er utbotT ->
      (forall input : MInput scheme m, SChk ctxc (eargs input) utanyT) ->
      SChk ctxc (einvoke er m eargs) u
  | schk_invoke_iface : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (m : Method scheme)
      (contains : SCSetContains (formalBody i).(ubsmethods) m)
      (c : IParameter scheme i -> UT) (er : Expression Input)
      (eargs : MInput scheme m -> Expression Input),
      SChk ctxc er (utifaceT i c) ->
      (forall input : MInput scheme m,
         SChk ctxc (eargs input)
           (utsubst c (((formalBody i).(ubsmethod) m contains).(umsinput) input))) ->
      SChk ctxc (einvoke er m eargs)
        (utsubst c (((formalBody i).(ubsmethod) m contains).(umsresult)))
  | schk_object : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (methods : SCSet (Method scheme))
      (bodies : forall method : Method scheme,
                  SCSetContains methods method ->
                  Expression (MInput scheme method :: Input)%list)
      (c : IParameter scheme i -> UT)
      (Hcontains : forall m : Method scheme,
          SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m),
      (forall (m : Method scheme) (hc : SCSetContains methods m),
         SChk
           (pair_elimination ((fun m _ => obj_signature_gen IPFin deq i c m) m hc).(smsinput) ctxc)
           (bodies m hc)
           ((fun m _ => obj_signature_gen IPFin deq i c m) m hc).(smsresult)) ->
      SChk ctxc (eobject i methods bodies) (utifaceT i c).

  Lemma SChk_sound : forall (Input : Sort)
    (ctxc : SortElimination UT Input) (e : Expression Input) (u : UT),
    SChk ctxc e u -> CheckExpression (canonSpace IPFin deq) ctxc e u.
  Proof.
    intros Input ctxc e u h. induction h.
    - exact (@ceinput (canonSpace IPFin deq) Input ctxc x).
    - exact (@cesub (canonSpace IPFin deq) Input ctxc e u v IHh s).
    - exact (canon_invoke_unreachable IPFin deq Input ctxc er m eargs u IHh H).
    - exact (canon_invoke_iface_gen IPFin deq Input ctxc i m contains c er eargs IHh H).
    - exact (canon_object_gen IPFin deq Input ctxc i methods bodies c Hcontains H).
  Qed.
End SChkSection.


(* ==== Shape monotonicity and user-type shape composition ==== *)
Lemma shsub_of_subT : forall (u v : UT), SubT u v -> ShSub (sh_of_ut u) (sh_of_ut v).
Proof.
  intros u v h. induction h as [b | a | i args args' Hargs].
  - simpl. exact (shsub_bot (sh_of_ut b)).
  - simpl. destruct a as [| | j ar].
    + simpl. exact (shsub_any shany).
    + simpl. exact (shsub_bot shany).
    + simpl. exact (shsub_any (shiface j)).
  - simpl. exact (shsub_iface i).
Qed.

Lemma sh_of_ut_utsubst_shape : forall (Var : Type) (Q : UserType Var)
  (c : Var -> UT), sh_of_ut (utsubst c Q) = shshape (fun p => sh_of_ut (c p)) Q.
Proof.
  intros Var Q. induction Q as [p | | i f IH]; intro c.
  - simpl. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


(* ==== Interface-head uniqueness along subtype chains ==== *)
Section HeadUniqueSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Definition HeadUnique (t : S.(SpaceType)) : SProp
  := forall (i : Interface scheme) (a : IParameter scheme i -> S.(SpaceType))
            (j : Interface scheme) (b : IParameter scheme j -> S.(SpaceType)),
       S.(SubSpaceType) t (S.(stinterface) i a) ->
       S.(SubSpaceType) t (S.(stinterface) j b) ->
       eqS i j.

  Lemma HeadUnique_up : forall (t t' : S.(SpaceType)),
    S.(SubSpaceType) t t' -> HeadUnique t -> HeadUnique t'.
  Proof.
    intros t t' hsub hu i a j b h1 h2.
    apply (hu i a j b).
    - exact (S.(ssttrans) t t' (S.(stinterface) i a) hsub h1).
    - exact (S.(ssttrans) t t' (S.(stinterface) j b) hsub h2).
  Qed.

  Lemma HeadUnique_stinterface : forall (i : Interface scheme)
    (args : IParameter scheme i -> S.(SpaceType)),
    HeadUnique (S.(stinterface) i args).
  Proof.
    intros i args j a k b h1 h2.
    destruct (ctsinterface CS i args j a h1) as [e1 _].
    destruct (ctsinterface CS i args k b h2) as [e2 _].
    exact (eqS_trans (eqS_sym e1) e2).
  Qed.

  Lemma HeadUnique_subst : forall (Var : Type) (Q : UserType Var)
    (sigma : Var -> S.(SpaceType)),
    (forall q : Var, HeadUnique (sigma q)) ->
    HeadUnique (tsubst (space:=S) sigma Q).
  Proof.
    intros Var Q. induction Q as [q | | i f IH]; intros sigma Hsig.
    - exact (Hsig q).
    - simpl. intros j a k b h1 h2.
      exact (falseSeS (ctsanyinterface CS j a h1)).
    - simpl. intros j a k b h1 h2.
      destruct (ctsinterface CS i (fun p => tsubst (space:=S) sigma (f p)) j a h1) as [e1 _].
      destruct (ctsinterface CS i (fun p => tsubst (space:=S) sigma (f p)) k b h2) as [e2 _].
      exact (eqS_trans (eqS_sym e1) e2).
  Qed.

  Lemma HeadUnique_closed : forall (Q : UserType Empty),
    HeadUnique (tsubst (space:=S) (emptye (T := S.(SpaceType))) Q).
  Proof.
    intro Q. induction Q as [e | | i f IH].
    - destruct e.
    - simpl. intros j a k b h1 h2.
      exact (falseSeS (ctsanyinterface CS j a h1)).
    - simpl. intros j a k b h1 h2.
      destruct (ctsinterface CS i (fun p => tsubst (space:=S) (emptye (T := S.(SpaceType))) (f p)) j a h1) as [e1 _].
      destruct (ctsinterface CS i (fun p => tsubst (space:=S) (emptye (T := S.(SpaceType))) (f p)) k b h2) as [e2 _].
      exact (eqS_trans (eqS_sym e1) e2).
  Qed.
End HeadUniqueSection.


(* ==== Finite-shape canonical check relation (sound) ==== *)
Section SChkShSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Inductive SChkSh : forall {Input : Sort},
      SortElimination UT Input -> Expression Input -> UT -> SProp :=
  | schksh_input : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (x : SumSort Input),
      SChkSh ctxc (einput x) (apply_elimination ctxc x)
  | schksh_sub : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (e : Expression Input) (u v : UT),
      SChkSh ctxc e u -> SubT u v -> SChkSh ctxc e v
  | schksh_invoke_unr : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (er : Expression Input) (m : Method scheme)
      (eargs : MInput scheme m -> Expression Input) (u : UT),
      SChkSh ctxc er utbotT ->
      (forall input : MInput scheme m, SChkSh ctxc (eargs input) utanyT) ->
      SChkSh ctxc (einvoke er m eargs) u
  | schksh_invoke_iface : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (m : Method scheme)
      (contains : SCSetContains (formalBody i).(ubsmethods) m)
      (ps : IParameter scheme i -> Sh) (er : Expression Input)
      (eargs : MInput scheme m -> Expression Input),
      SChkSh ctxc er (utifaceT i (args_of_shapes i ps)) ->
      (forall input : MInput scheme m,
         SChkSh ctxc (eargs input)
           (utsubst (args_of_shapes i ps)
              (((formalBody i).(ubsmethod) m contains).(umsinput) input))) ->
      SChkSh ctxc (einvoke er m eargs)
        (utsubst (args_of_shapes i ps)
           (((formalBody i).(ubsmethod) m contains).(umsresult)))
  | schksh_object : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (methods : SCSet (Method scheme))
      (bodies : forall method : Method scheme,
                  SCSetContains methods method ->
                  Expression (MInput scheme method :: Input)%list)
      (ps : IParameter scheme i -> Sh)
      (Hcontains : forall m : Method scheme,
          SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m),
      (forall (m : Method scheme) (hc : SCSetContains methods m),
         SChkSh
           (pair_elimination (smsinput (obj_signature IPFin deq i ps m)) ctxc)
           (bodies m hc)
           (smsresult (obj_signature IPFin deq i ps m))) ->
      SChkSh ctxc (eobject i methods bodies) (utifaceT i (args_of_shapes i ps)).

  Lemma SChkSh_sound : forall (Input : Sort)
    (ctxc : SortElimination UT Input) (e : Expression Input) (u : UT),
    SChkSh ctxc e u -> CheckExpression (canonSpace IPFin deq) ctxc e u.
  Proof.
    intros Input ctxc e u h. induction h.
    - exact (@ceinput (canonSpace IPFin deq) Input ctxc x).
    - exact (@cesub (canonSpace IPFin deq) Input ctxc e u v IHh s).
    - exact (canon_invoke_unreachable IPFin deq Input ctxc er m eargs u IHh H).
    - exact (canon_invoke_iface IPFin deq Input ctxc i m contains ps er eargs IHh H).
    - exact (canon_object_shapes IPFin deq Input ctxc i methods bodies ps Hcontains H).
  Qed.
End SChkShSection.


(* ==== Interfacial lower bound for RRep images ==== *)
Section RRepLowerBoundSection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context `{DecEq (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Lemma RRep_iface_lower_bound : forall (i : Interface scheme)
    (a : IParameter scheme i -> S.(SpaceType)) (sig : S.(SpaceType)) (v : UT),
    S.(SubSpaceType) (S.(stinterface) i a) sig ->
    RRep sig v ->
    SubT (LowIface i) v.
  Proof.
    intros i a sig v hle hrep.
    destruct v as [| | j b].
    - exact (subT_top (LowIface i)).
    - exfalso.
      apply falseS_false.
      exact (ctsinterfaceunreachable CS i a
               (S.(sstur) (S.(stinterface) i a) sig hle (RRep_bot_inv sig hrep))).
    - pose proof (RRep_iface_inv sig j b hrep) as [a' hs hra].
      destruct (ctsinterface CS i a j a'
                  (S.(ssttrans) (S.(stinterface) i a) sig (S.(stinterface) j a') hle hs)) as [e _].
      destruct (eqS_eq e).
      exact (LowIface_sub_low i b).
  Qed.
End RRepLowerBoundSection.


(* ==== Shape solution for an all-quantified source ==== *)
Section ShapeAnySection.
  Context {S : TypeSpace}.
  Context `{SSet (Interface scheme)}.
  Context (CS : ConsistentTypeSpace S).

  Lemma utsubst_allany_any_le : forall (Var : Type) (R : UserType Var)
    (a : Var -> S.(SpaceType)),
    S.(SubSpaceType) S.(stany) (tsubst (space:=S) a R) ->
    SubT utanyT (utsubst (fun _ : Var => utanyT) R).
  Proof.
    intros Var R. induction R as [p | | i f IH]; intros a h.
    - simpl. exact (subT_refl utanyT).
    - simpl. exact (subT_refl utanyT).
    - simpl. exact (falseSeS (ctsanyinterface CS i
                 (fun p => tsubst (space:=S) a (f p)) h)).
  Qed.
End ShapeAnySection.


(* ==== Shape approximations of an arbitrary interface target ==== *)
Section TargetShapesSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma shapes_fit_any_iface : forall (i : Interface scheme)
    (b : IParameter scheme i -> UT),
    args_fit i (fun p => sh_of_ut (b p)) b.
  Proof.
    intros i b p.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
    - exact (ShSub_refl (sh_of_ut (b p))).
    - exact (ShSub_refl (sh_of_ut (b p))).
  Qed.

  Lemma args_of_shapes_target_le : forall (i : Interface scheme)
    (b : IParameter scheme i -> UT),
    SubT (utifaceT i (args_of_shapes i (fun p => sh_of_ut (b p))))
         (utifaceT i b).
  Proof.
    intros i b.
    exact (args_of_shapes_le IPFin deq i (fun p => sh_of_ut (b p)) b
             (shapes_fit_any_iface i b)).
  Qed.
End TargetShapesSection.

Section SubUserSubstSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Fixpoint usize {Var : Type} (u : UserType Var) : nat :=
    match u with
    | utvariable _ => 1
    | utany => 1
    | utinterface i f =>
        S (fold_right Nat.add 0
             (map (fun p : IParameter scheme i => usize (f p))
                  (@flist (IParameter scheme i) (IPFin i) (IParameter scheme i) (fun p => p))))
    end.

  Lemma usize_pos : forall (Var : Type) (u : UserType Var), 0 < usize u.
  Proof. intros Var u. destruct u; simpl; lia. Qed.

  Lemma usize_arg : forall (Var : Type) (i : Interface scheme)
    (f : IParameter scheme i -> UserType Var) (p : IParameter scheme i),
    usize (f p) < usize (utinterface i f).
  Proof.
    intros Var i f p. simpl.
    assert (Hin : In (usize (f p))
      (map (fun q : IParameter scheme i => usize (f q))
           (@flist (IParameter scheme i) (IPFin i) (IParameter scheme i) (fun q => q)))).
    { apply (@List.in_map (IParameter scheme i) nat (fun q => usize (f q))
               (@flist (IParameter scheme i) (IPFin i) (IParameter scheme i) (fun q => q)) p).
      apply (@flist_In (IParameter scheme i) (IPFin i) p). }
    pose proof (In_le_sum _ _ Hin). lia.
  Qed.

  Lemma subuser_tsubst_subT_gen : forall (fuel : nat) (Var : Type)
    (Q R : UserType Var),
    usize Q + usize R <= fuel ->
    SubUserType Q R ->
    forall (c : Var -> UT), SubT (utsubst c Q) (utsubst c R).
  Proof.
    induction fuel as [| fuel IH]; intros Var Q R Hsz h c.
    - exfalso. pose proof (usize_pos Var Q). pose proof (usize_pos Var R). lia.
    - destruct Q as [p | | i f].
      + inversion h; subst. simpl. exact (subT_refl (c p)).
      + inversion h; subst. simpl. exact (subT_refl utanyT).
      + destruct R as [q | | j g].
        * inversion h.
        * inversion h; subst.
          assert (Hf : arguments0 = f) by
            (apply (@k_inj_projT2 (Interface scheme)
                      (fun interface => IParameter scheme interface -> UserType Var)
                      i (interface_K deq i) arguments0 f H1)).
          subst arguments0.
          simpl. exact (subT_top (utifaceT i (fun p => utsubst c (f p)))).
        * inversion h; subst.
          assert (Hf : arguments0 = f) by
            (apply (@k_inj_projT2 (Interface scheme)
                      (fun interface => IParameter scheme interface -> UserType Var)
                      j (interface_K deq j) arguments0 f H1)).
          assert (Hg : arguments'0 = g) by
            (apply (@k_inj_projT2 (Interface scheme)
                      (fun interface => IParameter scheme interface -> UserType Var)
                      j (interface_K deq j) arguments'0 g H3)).
          subst arguments0; subst arguments'0.
          simpl. apply (subT_variance j (fun p => utsubst c (f p))
                                         (fun p => utsubst c (g p))).
          intro p.
          pose proof (H0 p) as Hp.
          destruct ((hierarchy.(hinterface) j).(uisvariance) p) as [|].
          -- apply isnegative.
             exact (IH Var (g p) (f p)
                      ltac:(pose proof (usize_arg Var j f p); pose proof (usize_arg Var j g p); lia)
                      (isigned_neg_inv Hp) c).
          -- apply ispositive.
             exact (IH Var (f p) (g p)
                      ltac:(pose proof (usize_arg Var j f p); pose proof (usize_arg Var j g p); lia)
                      (isigned_pos_inv Hp) c).
  Qed.

  Lemma subuser_tsubst_subT : forall (Var : Type) (Q R : UserType Var),
    SubUserType Q R ->
    forall (c : Var -> UT), SubT (utsubst c Q) (utsubst c R).
  Proof.
    intros Var Q R h c.
    exact (subuser_tsubst_subT_gen (usize Q + usize R) Var Q R (le_n _) h c).
  Qed.

  Lemma subuser_tsubst_subT_signed : forall (Var : Type) (s : Sign)
    (Q R : UserType Var), ISigned SubUserType s Q R ->
    forall (c : Var -> UT), ISigned SubT s (utsubst c Q) (utsubst c R).
  Proof.
    intros Var s Q R h c. destruct s as [|].
    - apply isnegative.
      exact (subuser_tsubst_subT Var R Q (isigned_neg_inv h) c).
    - apply ispositive.
      exact (subuser_tsubst_subT Var Q R (isigned_pos_inv h) c).
  Qed.

  Lemma subuser_tsubst_subT_signed_any : forall (Var : Type) (s : Sign)
    (Q R : UserType Var), ISigned SubUserType s Q R ->
    forall (c : Var -> UT), Signed SubT s (utsubst c Q) (utsubst c R).
  Proof.
    intros Var s Q R h c.
    exact (isigned_signed s _ _ (subuser_tsubst_subT_signed Var s Q R h c)).
  Qed.

End SubUserSubstSection.


(* ==== Reflexivity of syntactic user-type subtyping ==== *)
Lemma subuser_refl : forall (Var : Type) (u : UserType Var), SubUserType u u.
Proof.
  intros Var u. induction u as [p | | i f IH].
  - exact (sutvariable p).
  - exact sutany.
  - apply (sutvariance i f f). intro p.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
    + apply isnegative. exact (IH p).
    + apply ispositive. exact (IH p).
Qed.


(* ==== Context weakening for expressions over the empty sort ==== *)
Lemma check_nil_any_ctx : forall (S : TypeSpace)
  (ctx' : SortElimination S.(SpaceType) nil)
  (e : Expression nil) (t : S.(SpaceType)),
  CheckExpression S nil_elimination e t -> CheckExpression S ctx' e t.
Proof.
  intros S ctx' e t h.
  refine (@check_context_lower S nil nil_elimination ctx' _ e t h).
  intros input. destruct input.
Qed.

(* ==== Conditional canonical realization transport (verified) ==== *)
Set Uniform Inductive Parameters.

(* ============================================================
   Conditional completeness: a "canonical realization" map
   phi : S.SpaceType -> UT that is a TypeSpace homomorphism and
   sends unreachable types to utbotT transports any check in S
   to a check in the canonical space.

   The remaining (open) ingredient for unconditioned completeness
   is the construction of such a phi from the finite derivation.
   ============================================================ *)

Record CanonRealize (S : TypeSpace) : Type :=
{ crphi : S.(SpaceType) -> UT;
  cr_any : crphi S.(stany) = utanyT;
  cr_iface : forall (i : Interface scheme) (a : IParameter scheme i -> S.(SpaceType)),
      crphi (S.(stinterface) i a) = utifaceT i (fun p => crphi (a p));
  cr_sub : forall (t t' : S.(SpaceType)),
      S.(SubSpaceType) t t' -> SubT (crphi t) (crphi t');
  cr_ur : forall (t : S.(SpaceType)),
      S.(UnReachable) t -> unReachableT (crphi t);
}.


Section MapElim.
  Context {A B : Type}.
  Variable f : A -> B.

  Definition mapElimination :
    forall {s : Sort}, SortElimination A s -> SortElimination B s
  := fix go {s : Sort} : SortElimination A s -> SortElimination B s
     := match s as s0 return SortElimination A s0 -> SortElimination B s0 with
        | nil => fun _ => tt
        | cons T s' => fun ctx =>
            pair (fun t => f (fst ctx t)) (go (snd ctx))
        end.

  Lemma mapElimination_apply : forall {s : Sort}
    (ctx : SortElimination A s) (x : SumSort s),
    apply_elimination (mapElimination ctx) x = f (apply_elimination ctx x).
  Proof.
    intros s. induction s as [| T s' IH]; intros ctx x.
    - destruct x.
    - destruct ctx as [h ctx']. destruct x as [t | y]; simpl.
      + reflexivity.
      + apply IH.
  Qed.

  Lemma mapElimination_pair : forall {T : Type} {s : Sort}
    (h : T -> A) (ctx : SortElimination A s),
    mapElimination (pair_elimination h ctx)
    = pair_elimination (fun t => f (h t)) (mapElimination ctx).
  Proof.
    intros. simpl. reflexivity.
  Qed.
End MapElim.

Arguments mapElimination {A B} f {s} ctx.

Section RealizeCheck.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context {S : TypeSpace}.
  Context (R : CanonRealize S).

  Let phi : S.(SpaceType) -> UT := @crphi S R.
  Let phi_any : phi S.(stany) = utanyT := @cr_any S R.
  Let phi_iface : forall (i : Interface scheme) (a : IParameter scheme i -> S.(SpaceType)),
      phi (S.(stinterface) i a) = utifaceT i (fun p => phi (a p)) := @cr_iface S R.
  Let phi_sub : forall (t t' : S.(SpaceType)),
      S.(SubSpaceType) t t' -> SubT (phi t) (phi t') := @cr_sub S R.
  Let phi_ur : forall (t : S.(SpaceType)),
      S.(UnReachable) t -> unReachableT (phi t) := @cr_ur S R.

  Inductive SubTBoth (a b : UT) : SProp :=
  | subtboth : SubT a b -> SubT b a -> SubTBoth.


  Lemma cr_both : forall (Var : Type) (Q : UserType Var)
    (sigma : Var -> S.(SpaceType)),
    SubTBoth (utsubst (fun p => phi (sigma p)) Q)
             (phi (tsubst (space := S) sigma Q)).
  Proof.
    intros Var Q. induction Q as [q | | i f IH]; intro sigma.
    - simpl. apply subtboth; apply subT_refl.
    - simpl. rewrite phi_any. apply subtboth; apply subT_refl.
    - simpl. rewrite phi_iface. apply subtboth.
      + apply (subT_variance i
                 (fun p => utsubst (fun p => phi (sigma p)) (f p))
                 (fun p => phi (tsubst (space := S) sigma (f p)))).
        intro p. destruct (IH p sigma) as [hle hge].
        destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
        * exact (isnegative _ _ hge).
        * exact (ispositive _ _ hle).
      + apply (subT_variance i
                 (fun p => phi (tsubst (space := S) sigma (f p)))
                 (fun p => utsubst (fun p => phi (sigma p)) (f p))).
        intro p. destruct (IH p sigma) as [hle hge].
        destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
        * exact (isnegative _ _ hle).
        * exact (ispositive _ _ hge).
  Qed.

  Lemma cr_tsubst_le : forall (Var : Type) (Q : UserType Var)
    (sigma : Var -> S.(SpaceType)),
    SubT (utsubst (fun p => phi (sigma p)) Q)
         (phi (tsubst (space := S) sigma Q)).
  Proof. intros Var Q sigma. destruct (cr_both Var Q sigma) as [hle hge]. exact hle. Qed.

  Lemma cr_tsubst_ge : forall (Var : Type) (Q : UserType Var)
    (sigma : Var -> S.(SpaceType)),
    SubT (phi (tsubst (space := S) sigma Q))
         (utsubst (fun p => phi (sigma p)) Q).
  Proof. intros Var Q sigma. destruct (cr_both Var Q sigma) as [hle hge]. exact hge. Qed.

  Lemma realize_check : forall (Input : Sort)
    (ctx : SortElimination S.(SpaceType) Input)
    (e : Expression Input) (t : S.(SpaceType)),
    CheckExpression S ctx e t ->
    CheckExpression (canonSpace IPFin deq) (mapElimination phi ctx) e (phi t).
  Proof.
    intros Input context e t h. induction h.
    - (* cesub *)
      exact (@cesub (canonSpace IPFin deq) Input (mapElimination phi context)
               expression (phi t) (phi t') IHh (phi_sub t t' s)).
    - (* ceinput *)
      rewrite <- (mapElimination_apply phi context input).
      exact (@ceinput (canonSpace IPFin deq) Input (mapElimination phi context) input).
    - (* ceinvoke *)
      destruct c as [treceiver0 signature0 ur | i arguments contains].
      + (* cmunreachable *)
        pose (sigC := @Build_SpaceMethodSignature (canonSpace IPFin deq)
                       (MInput scheme method)
                       (fun input => phi (signature0.(smsinput) input))
                       (phi signature0.(smsresult))).
        refine (@ceinvoke (canonSpace IPFin deq) Input (mapElimination phi context)
                  ereceiver method einputs (phi treceiver0) sigC _ IHh _).
        * refine (@cmunreachable (canonSpace IPFin deq) method (phi treceiver0) sigC _).
          exact (phi_ur treceiver0 ur).
        * intro input. unfold sigC. simpl. exact (H input).
      + (* cminterface *)
        pose (Qin := fun input : MInput scheme method =>
                       (((hierarchy.(hinterface) i).(uisbody).(ubsmethod) method contains).(umsinput) input)).
        pose (Qres := (((hierarchy.(hinterface) i).(uisbody).(ubsmethod) method contains).(umsresult))).
        pose (cC := fun p : IParameter scheme i => phi (arguments p)).
        pose (sigC := @Build_SpaceMethodSignature (canonSpace IPFin deq)
                       (MInput scheme method)
                       (fun input => utsubst cC (Qin input))
                       (utsubst cC Qres)).
        refine (@cesub (canonSpace IPFin deq) Input (mapElimination phi context)
                  (einvoke ereceiver method einputs)
                  (utsubst cC Qres)
                  (phi (tsubst (space := S) arguments Qres))
                  _ (cr_tsubst_le (IParameter scheme i) Qres arguments)).
        refine (@ceinvoke (canonSpace IPFin deq) Input (mapElimination phi context)
                  ereceiver method einputs (utifaceT i cC) sigC _ _ _).
        * refine (@cminterface (canonSpace IPFin deq) method i cC contains).
        * rewrite (phi_iface i arguments) in IHh.
          unfold cC. exact IHh.
        * intro input. unfold sigC. simpl.
          pose proof (cr_both (IParameter scheme i) (Qin input) arguments) as [hle hge].
          refine (@cesub (canonSpace IPFin deq) Input (mapElimination phi context)
                    (einputs input)
                    (phi (tsubst (space := S) arguments (Qin input)))
                    (utsubst cC (Qin input))
                    (H input) hge).
    - (* ceobject *)
      rewrite (phi_iface interface arguments).
      pose (cC := fun p : IParameter scheme interface => phi (arguments p)).
      pose (sigC := fun (method : Method scheme) (contains : SCSetContains methods method) =>
                      @Build_SpaceMethodSignature (canonSpace IPFin deq)
                        (MInput scheme method)
                        (fun input => phi ((signatures method contains).(smsinput) input))
                        (phi (signatures method contains).(smsresult))).
      refine (@ceobject (canonSpace IPFin deq) Input (mapElimination phi context)
                interface methods bodies cC sigC _ _).
      + (* conformance *)
        refine (@Build_SubSpaceBodySignature (canonSpace IPFin deq)
                  (@Build_SpaceBodySignature (canonSpace IPFin deq) methods sigC)
                  (@bssubst (IParameter scheme interface) (canonSpace IPFin deq) cC (hierarchy.(hinterface) interface).(uisbody))
                  (fun method contains => s.(ssbsmethods) method contains) _).
        intros method contains.
        pose (QinC := ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains).(umsinput)).
        pose (QresC := ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains).(umsresult)).
        refine (@Build_SubSpaceMethodSignature (canonSpace IPFin deq)
                  (MInput scheme method)
                  (sigC method (s.(ssbsmethods) method contains))
                  (@mssubst (IParameter scheme interface) (MInput scheme method)
                     (canonSpace IPFin deq) cC
                     ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains))
                  _ _).
        * (* ssmsinput *)
          intro input. unfold sigC. simpl.
          refine (subT_trans IPFin deq _ _ _
                    (cr_tsubst_le (IParameter scheme interface) (QinC input) arguments)
                    (phi_sub _ _
                       ((s.(ssbsmethod) method contains).(ssmsinput) input))).
        * (* ssmsresult *)
          unfold sigC. simpl.
          refine (subT_trans IPFin deq _ _ _
                    (phi_sub _ _
                       ((s.(ssbsmethod) method contains).(ssmsresult)))
                    (cr_tsubst_ge (IParameter scheme interface) QresC arguments)).
      + (* bodies *)
        intro method. intro contains. unfold sigC. simpl.
        rewrite <- (@mapElimination_pair S.(SpaceType) UT phi
                      (MInput scheme method) Input
                      (smsinput (signatures method contains)) context).
        exact (H method contains).
  Qed.

End RealizeCheck.

(* ============================================================
   Consequences: closed targets and the program-level corollary
   ============================================================ *)
Section ClosedRealize.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context {S : TypeSpace}.
  Context (R : CanonRealize S).

  Let phi : S.(SpaceType) -> UT := @crphi S R.

  Inductive UTBoth (a b : UT) : SProp :=
  | utboth : SubT a b -> SubT b a -> UTBoth.

  Lemma utsubst_empty_both : forall (f g : Empty -> UT) (Q : UserType Empty),
    UTBoth (utsubst f Q) (utsubst g Q).
  Proof.
    intros f g Q. induction Q as [e | | i h IH].
    - destruct e.
    - simpl. apply utboth; apply subT_refl.
    - simpl. apply utboth.
      + apply (subT_variance i (fun p => utsubst f (h p)) (fun p => utsubst g (h p))).
        intro p. destruct (IH p) as [hle hge].
        destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
        * exact (isnegative _ _ hge).
        * exact (ispositive _ _ hle).
      + apply (subT_variance i (fun p => utsubst g (h p)) (fun p => utsubst f (h p))).
        intro p. destruct (IH p) as [hle hge].
        destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
        * exact (isnegative _ _ hle).
        * exact (ispositive _ _ hge).
  Qed.

  Lemma realize_closed_le : forall (Q : UserType Empty),
    SubT (phi (tsubst (space := S) (emptye (T := S.(SpaceType))) Q))
         (utsubst (emptye (T := UT)) Q).
  Proof.
    intro Q.
    refine (subT_trans IPFin deq _ _ _
              (cr_tsubst_ge R Empty Q (emptye (T := S.(SpaceType))))
              _).
    destruct (utsubst_empty_both
                (fun e : Empty => phi (emptye (T := S.(SpaceType)) e))
                (emptye (T := UT)) Q) as [hle hge].
    exact hle.
  Qed.

  Theorem realize_program :
    forall (program : Program),
    CheckExpression S nil_elimination program.(pexpression)
      (tsubst (space := S) (emptye (T := S.(SpaceType))) program.(ptype)) ->
    CheckExpression (canonSpace IPFin deq) nil_elimination program.(pexpression)
      (utsubst (emptye (T := UT)) program.(ptype)).
  Proof.
    intros program h.
    refine (@cesub (canonSpace IPFin deq) nil (nil_elimination)
              program.(pexpression)
              (phi (tsubst (space := S) (emptye (T := S.(SpaceType))) program.(ptype)))
              (utsubst (emptye (T := UT)) program.(ptype))
              _ (realize_closed_le program.(ptype))).
    change (CheckExpression (canonSpace IPFin deq)
              (mapElimination phi nil_elimination) program.(pexpression)
              (phi (tsubst (space := S) (emptye (T := S.(SpaceType))) program.(ptype)))).
    exact (realize_check IPFin deq R nil nil_elimination program.(pexpression)
             (tsubst (space := S) (emptye (T := S.(SpaceType))) program.(ptype)) h).
  Qed.
End ClosedRealize.

(* The canonical space realizes itself. *)
Section CanonSelfRealize.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition canonRealizeSelf : CanonRealize (canonSpace IPFin deq).
  Proof.
    refine (@Build_CanonRealize (canonSpace IPFin deq)
              (fun (t : UT) => t) eq_refl _ _ _).
    - intros i a. reflexivity.
    - intros t t' h. exact h.
    - intros t h. exact h.
  Defined.
End CanonSelfRealize.

(* Conditional completeness at the program level: if every consistent
   space admits a canonical realization, then the canonical check is
   complete for ProgramV. *)
Section ProgramCompleteness.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context `{SSet (Interface scheme)}.

  Theorem programv_canon_check_of_realization :
    (forall (S : TypeSpace), ConsistentTypeSpace S -> CanonRealize S) ->
    forall (program : Program),
      ProgramV program ->
      CheckExpression (canonSpace IPFin deq) nil_elimination program.(pexpression)
        (utsubst (emptye (T := UT)) program.(ptype)).
  Proof.
    intros Hreal program pv.
    destruct pv as [hv hex].
    destruct hex as [S CS hcheck].
    exact (realize_program IPFin deq (Hreal S CS) program hcheck).
  Qed.
End ProgramCompleteness.

(* ==== Every check gives a check of the abstracted expression ==== *)
Section EAbsCheckSection.
  Context {space : TypeSpace}.

  Lemma check_eabstract : forall (Input : Sort)
    (ctx : SortElimination space.(SpaceType) Input)
    (e : Expression Input) (t : space.(SpaceType)),
    CheckExpression space ctx e t ->
    CheckAExpression (space := space) (Input := Input) ctx (eabstract e) t.
  Proof.
    intros Input ctx e t h.
    unfold CheckAExpression.
    induction h; intros Input' incl ctx' Hle.
    - (* cesub *)
      simpl. exact (@cesub space Input' ctx' (eabstract expression Input' incl)
                     t t' (IHh Input' incl ctx' Hle) s).
    - (* ceinput *)
      simpl. refine (@cesub space Input' ctx' (einput (incl input))
                     (apply_elimination ctx' (incl input))
                     (apply_elimination context input)
                     (@ceinput space Input' ctx' (incl input)) (Hle input)).
    - (* ceinvoke *)
      simpl. refine (@ceinvoke space Input' ctx'
                       (eabstract ereceiver Input' incl) method
                       (fun input => eabstract (einputs input) Input' incl)
                       treceiver signature c
                       (IHh Input' incl ctx' Hle) _).
      intro input. exact (H input Input' incl ctx' Hle).
    - (* ceobject *)
      simpl. refine (@ceobject space Input' ctx' interface methods
                       (fun method contains =>
                          eabstract (bodies method contains)
                            (cons (scheme.(MInput) method) Input')
                            (sum_mapr incl))
                       arguments signatures s _).
      intros method contains.
      refine (H method contains (cons (scheme.(MInput) method) Input')
                (sum_mapr incl)
                (pair_elimination (smsinput (signatures method contains)) ctx') _).
      intro input. destruct input as [x | y].
      + simpl. exact (space.(sstrefl) (smsinput (signatures method contains) x)).
      + simpl. exact (Hle y).
  Qed.
End EAbsCheckSection.

(* ==== Finite shape lattice: meet and join projections ==== *)
Section ShLatticeSection.
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Definition shmeet (s t : Sh) : Sh :=
    match s, t with
    | shbot, _ => shbot
    | _, shbot => shbot
    | shany, t => t
    | s, shany => s
    | shiface i, shiface j => match deq i j with
                              | left _ => shiface i
                              | right _ => shbot
                              end
    end.

  Definition shjoin (s t : Sh) : Sh :=
    match s, t with
    | shany, _ => shany
    | _, shany => shany
    | shbot, t => t
    | s, shbot => s
    | shiface i, shiface j => match deq i j with
                              | left _ => shiface i
                              | right _ => shany
                              end
    end.

  Lemma ShSub_shmeet_l : forall s t, ShSub (shmeet s t) s.
  Proof.
    intros s t. destruct s as [| | i]; destruct t as [| | j]; simpl;
      try constructor;
      try (destruct (deq i j) as [e | ne]; [subst; constructor | constructor]).
  Qed.

  Lemma ShSub_shmeet_r : forall s t, ShSub (shmeet s t) t.
  Proof.
    intros s t. destruct s as [| | i]; destruct t as [| | j]; simpl;
      try constructor;
      try (destruct (deq i j) as [e | ne]; [subst; constructor | constructor]).
  Qed.

  Lemma ShSub_shjoin_l : forall s t, ShSub s (shjoin s t).
  Proof.
    intros s t. destruct s as [| | i]; destruct t as [| | j]; simpl;
      try constructor;
      try (destruct (deq i j) as [e | ne]; [subst; constructor | constructor]).
  Qed.

  Lemma ShSub_shjoin_r : forall s t, ShSub t (shjoin s t).
  Proof.
    intros s t. destruct s as [| | i]; destruct t as [| | j]; simpl;
      try constructor;
      try (destruct (deq i j) as [e | ne]; [subst; constructor | constructor]).
  Qed.

  Lemma ShSub_shmeet_intro : forall u s t, ShSub u s -> ShSub u t -> ShSub u (shmeet s t).
  Proof.
    intros u s t hs ht.
    destruct u as [| | k]; destruct s as [| | i]; destruct t as [| | j]; simpl in *;
      try (inversion hs; subst); try (inversion ht; subst);
      try (destruct (deq i j) as [e | ne]; [subst | exfalso; apply ne; reflexivity]);
      try (destruct (deq j j) as [e | ne]; [simpl; constructor | exfalso; apply ne; reflexivity]);
      try constructor; try assumption.
  Qed.

  Lemma ShSub_shmeet_elim : forall u s t, ShSub u (shmeet s t) -> AndS (ShSub u s) (ShSub u t).
  Proof.
    intros u s t h.
    destruct u as [| | k]; destruct s as [| | i]; destruct t as [| | j]; simpl in *;
      try (destruct (deq i j) as [e | ne]; [subst | try (exfalso; apply ne; reflexivity)]);
      try (inversion h; subst);
      try (apply conjS); try constructor; try assumption.
  Qed.

  Lemma ShSub_shjoin_intro : forall u s t, ShSub s u -> ShSub t u -> ShSub (shjoin s t) u.
  Proof.
    intros u s t hs ht.
    destruct u as [| | k]; destruct s as [| | i]; destruct t as [| | j]; simpl in *;
      try (inversion hs; subst); try (inversion ht; subst);
      try (destruct (deq i j) as [e | ne]; [subst | exfalso; apply ne; reflexivity]);
      try (destruct (deq k k) as [e | ne]; [simpl; constructor | exfalso; apply ne; reflexivity]);
      try constructor; try assumption.
  Qed.

  Lemma ShSub_shjoin_elim : forall u s t, ShSub (shjoin s t) u -> AndS (ShSub s u) (ShSub t u).
  Proof.
    intros u s t h.
    destruct u as [| | k]; destruct s as [| | i]; destruct t as [| | j]; simpl in *;
      try (destruct (deq i j) as [e | ne]; [subst | idtac]);
      try (inversion h; subst);
      try (apply conjS); try constructor; try assumption.
  Qed.

End ShLatticeSection.

(* ==== Finite Solver for Flat Shape Constraint Systems ==== *)
Section ShapeSystemSection.
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

Record ShapeSystem (Var : Type) : Type :=
  { sys_lower : Var -> list Sh;
    sys_upper : Var -> list Sh; }.

Definition sys_lower_bound {Var : Type} (sys : ShapeSystem Var) (p : Var) : Sh
:= fold_right (shjoin deq) shbot (sys_lower _ sys p).

Definition sys_upper_bound {Var : Type} (sys : ShapeSystem Var) (p : Var) : Sh
:= fold_right (shmeet deq) shany (sys_upper _ sys p).

Definition sys_consistent {Var : Type} (sys : ShapeSystem Var) : SProp
:= forall p, ShSub (sys_lower_bound sys p) (sys_upper_bound sys p).

Definition sys_solution {Var : Type} (sys : ShapeSystem Var) (p : Var) : Sh
:= sys_lower_bound sys p.

Lemma fold_shjoin_member : forall (l : list Sh) (s : Sh),
    In s l -> ShSub s (fold_right (shjoin deq) shbot l).
Proof.
  induction l as [| a l IH]; intros s Hin; simpl in Hin.
  - destruct Hin.
  - destruct Hin as [e | Hin].
    + subst. apply (ShSub_shjoin_l deq s (fold_right (shjoin deq) shbot l)).
    + apply (ShSub_trans s (fold_right (shjoin deq) shbot l)
                  (shjoin deq a (fold_right (shjoin deq) shbot l))).
      * apply IH; exact Hin.
      * apply (ShSub_shjoin_r deq a (fold_right (shjoin deq) shbot l)).
Qed.

Lemma fold_shmeet_member : forall (l : list Sh) (s : Sh),
    In s l -> ShSub (fold_right (shmeet deq) shany l) s.
Proof.
  induction l as [| a l IH]; intros s Hin; simpl in Hin.
  - destruct Hin.
  - destruct Hin as [e | Hin].
    + subst. apply (ShSub_shmeet_l deq s (fold_right (shmeet deq) shany l)).
    + apply (ShSub_trans (shmeet deq a (fold_right (shmeet deq) shany l))
                  (fold_right (shmeet deq) shany l) s).
      * apply (ShSub_shmeet_r deq a (fold_right (shmeet deq) shany l)).
      * apply IH; exact Hin.
Qed.


Lemma fold_shjoin_least : forall (l : list Sh) (u : Sh),
    (forall s : Sh, In s l -> ShSub s u) ->
    ShSub (fold_right (shjoin deq) shbot l) u.
Proof.
  induction l as [| a l IH]; intros u Hall; simpl.
  - exact (shsub_bot u).
  - apply (ShSub_shjoin_intro deq u a (fold_right (shjoin deq) shbot l)).
    + apply Hall. simpl. left. reflexivity.
    + apply IH. intros s Hin. apply Hall. simpl. right. exact Hin.
Qed.

Lemma fold_shmeet_greatest : forall (l : list Sh) (u : Sh),
    (forall s : Sh, In s l -> ShSub u s) ->
    ShSub u (fold_right (shmeet deq) shany l).
Proof.
  induction l as [| a l IH]; intros u Hall; simpl.
  - exact (shsub_any u).
  - apply (ShSub_shmeet_intro deq u a (fold_right (shmeet deq) shany l)).
    + apply Hall. simpl. left. reflexivity.
    + apply IH. intros s Hin. apply Hall. simpl. right. exact Hin.
Qed.

Lemma sys_solution_lower : forall {Var : Type} (sys : ShapeSystem Var)
    (p : Var) (s : Sh),
    In s (sys_lower _ sys p) -> ShSub s (sys_solution sys p).
Proof.
  intros Var sys p s Hin. unfold sys_solution, sys_lower_bound.
  apply fold_shjoin_member. exact Hin.
Qed.

Lemma sys_solution_upper : forall {Var : Type} (sys : ShapeSystem Var),
    sys_consistent sys ->
    forall (p : Var) (s : Sh),
      In s (sys_upper _ sys p) -> ShSub (sys_solution sys p) s.
Proof.
  intros Var sys Hc p s Hin.
  unfold sys_solution.
  apply (ShSub_trans (sys_lower_bound sys p) (sys_upper_bound sys p) s).
  - apply Hc.
  - unfold sys_upper_bound. apply fold_shmeet_member. exact Hin.
Qed.

Theorem shape_system_solvable : forall {Var : Type} (sys : ShapeSystem Var),
    sys_consistent sys ->
    existsTS ps : Var -> Sh,
      AndS (forall (p : Var) (s : Sh),
              In s (sys_lower _ sys p) -> ShSub s (ps p))
           (forall (p : Var) (s : Sh),
              In s (sys_upper _ sys p) -> ShSub (ps p) s).
Proof.
  intros Var sys Hc.
  refine (ex_introTS (sys_solution sys) _).
  apply conjS.
  - intros p s Hin. apply sys_solution_lower. exact Hin.
  - intros p s Hin. apply sys_solution_upper. exact Hc. exact Hin.
Qed.

(* A model of the constraint system (any ps satisfying all listed bounds)
   makes the system consistent.  This is the abstract bridge used to turn
   an S witness into solvability. *)
Lemma sys_consistent_of_model : forall {Var : Type} (sys : ShapeSystem Var)
    (ps : Var -> Sh),
    (forall (p : Var) (s : Sh),
        In s (sys_lower _ sys p) -> ShSub s (ps p)) ->
    (forall (p : Var) (s : Sh),
        In s (sys_upper _ sys p) -> ShSub (ps p) s) ->
    sys_consistent sys.
Proof.
  intros Var sys ps Hlow Hup p.
  assert (HL : ShSub (sys_lower_bound sys p) (ps p)).
  { unfold sys_lower_bound.
    apply fold_shjoin_least. intros s Hin. apply Hlow. exact Hin. }
  assert (HU : ShSub (ps p) (sys_upper_bound sys p)).
  { unfold sys_upper_bound.
    apply fold_shmeet_greatest. intros s Hin. apply Hup. exact Hin. }
  apply (ShSub_trans (sys_lower_bound sys p) (ps p) (sys_upper_bound sys p) HL HU).
Qed.

Theorem shape_system_solvable_of_model : forall {Var : Type}
    (sys : ShapeSystem Var) (ps : Var -> Sh),
    (forall (p : Var) (s : Sh),
        In s (sys_lower _ sys p) -> ShSub s (ps p)) ->
    (forall (p : Var) (s : Sh),
        In s (sys_upper _ sys p) -> ShSub (ps p) s) ->
    existsTS ps' : Var -> Sh,
      AndS (forall (p : Var) (s : Sh),
              In s (sys_lower _ sys p) -> ShSub s (ps' p))
           (forall (p : Var) (s : Sh),
              In s (sys_upper _ sys p) -> ShSub (ps' p) s).
Proof.
  intros Var sys ps Hlow Hup.
  apply shape_system_solvable.
  apply (sys_consistent_of_model sys ps Hlow Hup).
Qed.

(* ------------------------------------------------------------------ *)
(* A finite family of canonical targets at one interface: the          *)
(* per-parameter lower and upper shape requirements are combined with  *)
(* shjoin/shmeet, and the resulting system is consistent without any   *)
(* external model.  This is the target-directed half of the bridge.    *)
(* ------------------------------------------------------------------ *)

End ShapeSystemSection.

(* ==== Finite-candidate full-UT canonical checker ==== *)
Section SChkCSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Variable C : forall i : Interface scheme, list (IParameter scheme i -> UT).

  Inductive SChkC : forall {Input : Sort},
      SortElimination UT Input -> Expression Input -> UT -> SProp :=
  | schkc_input : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (x : SumSort Input),
      SChkC ctxc (einput x) (apply_elimination ctxc x)
  | schkc_sub : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (e : Expression Input) (u v : UT),
      SChkC ctxc e u -> SubT u v -> SChkC ctxc e v
  | schkc_invoke_unr : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (er : Expression Input) (m : Method scheme)
      (eargs : MInput scheme m -> Expression Input) (u : UT),
      SChkC ctxc er utbotT ->
      (forall input : MInput scheme m, SChkC ctxc (eargs input) utanyT) ->
      SChkC ctxc (einvoke er m eargs) u
  | schkc_invoke_iface : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (m : Method scheme)
      (contains : SCSetContains (formalBody i).(ubsmethods) m)
      (c : IParameter scheme i -> UT)
      (er : Expression Input) (eargs : MInput scheme m -> Expression Input),
      In c (C i) ->
      SChkC ctxc er (utifaceT i c) ->
      (forall input : MInput scheme m,
         SChkC ctxc (eargs input)
           (utsubst c (((formalBody i).(ubsmethod) m contains).(umsinput) input))) ->
      SChkC ctxc (einvoke er m eargs)
        (utsubst c (((formalBody i).(ubsmethod) m contains).(umsresult)))
  | schkc_object : forall {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (methods : SCSet (Method scheme))
      (bodies : forall method : Method scheme,
                  SCSetContains methods method ->
                  Expression (MInput scheme method :: Input)%list)
      (c : IParameter scheme i -> UT)
      (Hcontains : forall m : Method scheme,
          SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m),
      In c (C i) ->
      (forall (m : Method scheme) (hc : SCSetContains methods m),
         SChkC
           (pair_elimination ((fun m _ => obj_signature_gen IPFin deq i c m) m hc).(smsinput) ctxc)
           (bodies m hc)
           ((fun m _ => obj_signature_gen IPFin deq i c m) m hc).(smsresult)) ->
      SChkC ctxc (eobject i methods bodies) (utifaceT i c).

  Lemma SChkC_to_SChk : forall {Input : Sort} (ctxc : SortElimination UT Input)
    (e : Expression Input) (u : UT), SChkC ctxc e u -> SChk IPFin deq ctxc e u.
  Proof.
    intros Input ctxc e u h. induction h.
    - exact (@schk_input IPFin deq Input ctxc x).
    - exact (@schk_sub IPFin deq Input ctxc e u v IHh s).
    - exact (@schk_invoke_unr IPFin deq Input ctxc er m eargs u IHh H).
    - exact (@schk_invoke_iface IPFin deq Input ctxc i m contains c er eargs IHh H).
    - exact (@schk_object IPFin deq Input ctxc i methods bodies c Hcontains H).
  Qed.

  Lemma SChkC_sound : forall (Input : Sort)
    (ctxc : SortElimination UT Input) (e : Expression Input) (u : UT),
    SChkC ctxc e u -> CheckExpression (canonSpace IPFin deq) ctxc e u.
  Proof.
    intros Input ctxc e u h.
    exact (SChk_sound IPFin deq Input ctxc e u (SChkC_to_SChk ctxc e u h)).
  Qed.
End SChkCSection.

(* ==== Finite candidate function enumeration ==== *)
Section AllFunsSection.
  Context (i : Interface scheme).
  Context (pdeq : forall x y : IParameter scheme i, {x = y} + {x = y -> False}).
  Context (D : list UT).

  Fixpoint all_funs (l : list (IParameter scheme i)) : list (IParameter scheme i -> UT) :=
    match l with
    | nil => (fun _ => utanyT) :: nil
    | a :: l' =>
        flat_map
          (fun f => map (fun u => fun p => if pdeq p a then u else f p) D)
          (all_funs l')
    end.

  Lemma all_funs_complete : forall (l : list (IParameter scheme i))
    (f : IParameter scheme i -> UT),
    (forall p : IParameter scheme i, In p l -> In (f p) D) ->
    exists f' : IParameter scheme i -> UT,
      In f' (all_funs l) /\ forall p : IParameter scheme i, In p l -> f p = f' p.
  Proof.
    induction l as [| a l' IH]; intros f Hf.
    - exists (fun _ => utanyT). split.
      + simpl. left. reflexivity.
      + intros p Hin. destruct Hin.
    - destruct (IH f) as [f0 [Hmem Hagree]].
      { intros p Hin. apply Hf. simpl. right. exact Hin. }
      exists (fun p => if pdeq p a then f a else f0 p). split.
      + simpl. apply in_flat_map. exists f0. split; [exact Hmem |].
        apply in_map_iff. exists (f a). split; [reflexivity | exact (Hf a (or_introl eq_refl))].
      + intros p Hin. destruct Hin as [e | Hin].
        * subst p. simpl. destruct (pdeq a a) as [e | ne].
          -- reflexivity.
          -- exfalso. apply ne. reflexivity.
        * simpl. destruct (pdeq p a) as [e | ne].
          -- subst p. reflexivity.
          -- apply Hagree. exact Hin.
  Qed.
End AllFunsSection.


(* ==== Finite candidate argument functions over a finite UT value set ==== *)
Definition deqIP (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (i : Interface scheme) : forall x y : IParameter scheme i, {x = y} + {x = y -> False}
  := fun x y => @dec_eq (IParameter scheme i)
       (@SubCountable_DecEq (IParameter scheme i)
          (@SubFinite_SubCountable (IParameter scheme i)
             (@Finite_SubFinite (IParameter scheme i) (IPFin i)))) x y.

Definition CFinite (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (D : list UT) (i : Interface scheme) : list (IParameter scheme i -> UT)
  := all_funs i (deqIP IPFin i) D (flist (fun p : IParameter scheme i => p)).

Definition SChkFinite (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (D : list UT) : forall {Input : Sort},
    SortElimination UT Input -> Expression Input -> UT -> SProp
  := fun Input ctx e u => SChkC IPFin deq (CFinite IPFin D) ctx e u.

Lemma SChkFinite_sound (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (D : list UT) : forall (Input : Sort)
    (ctx : SortElimination UT Input) (e : Expression Input) (u : UT),
    SChkFinite IPFin deq D ctx e u -> CheckExpression (canonSpace IPFin deq) ctx e u.
Proof.
  intros Input ctx e u h.
  exact (SChkC_sound IPFin deq (CFinite IPFin D) Input ctx e u h).
Qed.

(* ==== Finite-range canonical checker with inferred method signatures ==== *)
Section SChkD2Section.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Inductive SChkD2 : list UT -> forall {Input : Sort},
      SortElimination UT Input -> Expression Input -> UT -> SProp :=
  | d2_input : forall (D : list UT) {Input : Sort} (ctxc : SortElimination UT Input)
      (x : SumSort Input),
      SChkD2 D ctxc (einput x) (apply_elimination ctxc x)
  | d2_sub : forall (D : list UT) {Input : Sort} (ctxc : SortElimination UT Input)
      (e : Expression Input) (u v : UT),
      SChkD2 D ctxc e u -> SubT u v -> SChkD2 D ctxc e v
  | d2_invoke_unr : forall (D : list UT) {Input : Sort} (ctxc : SortElimination UT Input)
      (er : Expression Input) (m : Method scheme)
      (eargs : MInput scheme m -> Expression Input) (u : UT),
      SChkD2 D ctxc er utbotT ->
      (forall input : MInput scheme m, SChkD2 D ctxc (eargs input) utanyT) ->
      SChkD2 D ctxc (einvoke er m eargs) u
  | d2_invoke_iface : forall (D : list UT) {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (m : Method scheme)
      (contains : SCSetContains (formalBody i).(ubsmethods) m)
      (c : IParameter scheme i -> UT)
      (Hc : forall p : IParameter scheme i, InB D (c p))
      (er : Expression Input) (eargs : MInput scheme m -> Expression Input),
      SChkD2 D ctxc er (utifaceT i c) ->
      (forall input : MInput scheme m,
         SChkD2 D ctxc (eargs input)
           (utsubst c (((formalBody i).(ubsmethod) m contains).(umsinput) input))) ->
      SChkD2 D ctxc (einvoke er m eargs)
        (utsubst c (((formalBody i).(ubsmethod) m contains).(umsresult)))
  | d2_object : forall (D : list UT) {Input : Sort} (ctxc : SortElimination UT Input)
      (i : Interface scheme) (methods : SCSet (Method scheme))
      (bodies : forall method : Method scheme,
                  SCSetContains methods method ->
                  Expression (MInput scheme method :: Input)%list)
      (c : IParameter scheme i -> UT)
      (Hc : forall p : IParameter scheme i, InB D (c p))
      (sigs : forall (m : Method scheme) (hc : SCSetContains methods m),
          SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m))
      (Hsin : forall (m : Method scheme) (hc : SCSetContains methods m)
                     (input : MInput scheme m), InB D (smsinput (sigs m hc) input))
      (Hsres : forall (m : Method scheme) (hc : SCSetContains methods m),
          InB D (smsresult (sigs m hc)))
      (Hconf : SubSpaceBodySignature
                 (@Build_SpaceBodySignature (canonSpace IPFin deq) methods sigs)
                 (@bssubst (IParameter scheme i) (canonSpace IPFin deq) c (formalBody i))),
      (forall (m : Method scheme) (hc : SCSetContains methods m),
         SChkD2 D (pair_elimination (smsinput (sigs m hc)) ctxc)
           (bodies m hc) (smsresult (sigs m hc))) ->
      SChkD2 D ctxc (eobject i methods bodies) (utifaceT i c).

  Lemma SChkD2_sound : forall (D : list UT) (Input : Sort)
    (ctxc : SortElimination UT Input) (e : Expression Input) (u : UT),
    SChkD2 D ctxc e u -> CheckExpression (canonSpace IPFin deq) ctxc e u.
  Proof.
    intros D Input ctxc e u h. induction h.
    - exact (@ceinput (canonSpace IPFin deq) Input ctxc x).
    - exact (@cesub (canonSpace IPFin deq) Input ctxc e u v IHh s).
    - exact (canon_invoke_unreachable IPFin deq Input ctxc er m eargs u IHh H).
    - exact (canon_invoke_iface_gen IPFin deq Input ctxc i m contains c er eargs IHh H).
    - refine (@ceobject (canonSpace IPFin deq) Input ctxc i methods bodies c sigs Hconf _).
      intros m hc. exact (H m hc).
  Qed.
End SChkD2Section.

(* ==== Finite-model property for canonical checks ==== *)
(* ============================================================
   Monotonicity of SChkD2 in the finite value list.
   ============================================================ *)

Section SChkD2MonoSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma SChkD2_mono : forall (D D' : list UT),
    (forall u : UT, InB D u -> InB D' u) ->
    forall {Input : Sort} (ctxc : SortElimination UT Input)
      (e : Expression Input) (u : UT),
    SChkD2 IPFin deq D ctxc e u -> SChkD2 IPFin deq D' ctxc e u.
  Proof.
    intros D D' Hsub Input ctxc e u h.
    induction h.
    - exact (@d2_input IPFin deq D' Input ctxc x).
    - exact (@d2_sub IPFin deq D' Input ctxc e u v (IHh Hsub) s).
    - exact (@d2_invoke_unr IPFin deq D' Input ctxc er m eargs u (IHh Hsub)
               (fun input => H input Hsub)).
    - refine (@d2_invoke_iface IPFin deq D' Input ctxc i m contains c
                (fun p => Hsub (c p) (Hc p)) er eargs _ _).
      + exact (IHh Hsub).
      + intro input. exact (H input Hsub).
    - refine (@d2_object IPFin deq D' Input ctxc i methods bodies c
                (fun p => Hsub (c p) (Hc p))
                sigs
                (fun m hc input => Hsub _ (Hsin m hc input))
                (fun m hc => Hsub _ (Hsres m hc))
                Hconf
                (fun m hc => H m hc Hsub)).
  Qed.

End SChkD2MonoSection.

(* ============================================================
   Generic finite collection lemmas.
   ============================================================ *)

Section CollectSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma SChkD2_list_forall : forall (A : Type) (l : list A)
    (P : A -> list UT -> SProp),
    (forall (a : A) (D D' : list UT),
        (forall u : UT, InB D u -> InB D' u) -> P a D -> P a D') ->
    (forall a : A, In a l -> existsTS D : list UT, P a D) ->
    existsTS D : list UT, forall a : A, In a l -> P a D.
  Proof.
    intros A l. induction l as [| a l' IH]; intros P Pmono H.
    - exists (nil : list UT). intros a Hin. destruct Hin.
    - destruct (H a (or_introl eq_refl)) as [Da Ha].
      destruct (IH P Pmono) as [Dl Hl].
      { intros b Hb. apply H. right. exact Hb. }
      exists (app Da Dl). intros b Hb.
      destruct Hb as [e | Hb].
      + subst b. apply (Pmono a Da (app Da Dl)).
        * intros u Hu. apply InB_app_l. exact Hu.
        * exact Ha.
      + apply (Pmono b Dl (app Da Dl)).
        * intros u Hu. apply InB_app_r. exact Hu.
        * apply Hl. exact Hb.
  Qed.

  Lemma SChkD2_finite_forall : forall (A : Type) `{Finite A}
    (P : A -> list UT -> SProp),
    (forall (a : A) (D D' : list UT),
        (forall u : UT, InB D u -> InB D' u) -> P a D -> P a D') ->
    (forall a : A, existsTS D : list UT, P a D) ->
    existsTS D : list UT, forall a : A, P a D.
  Proof.
    intros A HA P Pmono H.
    destruct (@SChkD2_list_forall A (flist (fun a : A => a)) P Pmono) as [D HD].
    - intros a _. apply H.
    - exists D. intro a. apply HD. apply flist_In.
  Qed.

  Definition vals {A : Type} (HA : Finite A) (f : A -> UT) : list UT
  := map f (flist (fun a : A => a)).

  Lemma vals_complete : forall {A : Type} (HA : Finite A) (f : A -> UT) (a : A),
    In (f a) (vals HA f).
  Proof.
    intros A HA f a. unfold vals.
    apply (@List.in_map A UT f (flist (fun x : A => x)) a). apply flist_In.
  Qed.

End CollectSection.

(* ============================================================
   Finite enumeration of an SCSet, with SProp membership.
   ============================================================ *)

Section SCSetEnumSection.

  Lemma InB_map : forall {A B : Type} (f : A -> B) (l : list A) (a : A),
    InB l a -> InB (List.map f l) (f a).
  Proof.
    intros A B f l. induction l as [| x xs IH]; intros a h.
    - exact (falseSeS (InB_nil_absurd h)).
    - simpl. apply InB_or in h. destruct h as [Heq | Htail].
      + exact (@eqS_subst' A (fun y => InB (f x :: List.map f xs) (f y))
                 a x Heq (inb_head (f x) (List.map f xs))).
      + exact (inb_tail (f x) (f a) (List.map f xs) (IH a Htail)).
  Qed.

  Lemma InB_map_inv : forall {A B : Type} (f : A -> B) (l : list A) (b : B),
    InB (List.map f l) b ->
    existsTSS a : A, InB l a & eqS (f a) b.
  Proof.
    intros A B f l. induction l as [| x xs IH]; intros b h.
    - exact (falseSeS (InB_nil_absurd h)).
    - simpl in h. apply InB_or in h. destruct h as [Heq | Htail].
      + refine (ex_introSSS x (inb_head x xs) _).
        exact (eqS_sym Heq).
      + destruct (IH b Htail) as [a Hin Ha].
        exact (ex_introSSS a (inb_tail x a xs Hin) Ha).
  Qed.

  Lemma isvalues_eq_bentries : forall {A : Type} `{SubCountable A}
    (set : SCSet A),
    isvalues set
    = List.map (fun entry : sigT (fun path => BEntry A (fun _ => unit)
                                    (fun k => eqS (scpath k) path))
                  => (projT2 entry).(bekey)) (bentries set).
  Proof.
    intros A HSub set.
    unfold isvalues, imentries.
    rewrite List.map_map.
    reflexivity.
  Qed.

  Lemma isvalues_complete : forall {A : Type} `{SubCountable A}
    (set : SCSet A) (a : A),
    SCSetContains set a -> InB (isvalues set) a.
  Proof.
    intros A HSub set a Hc.
    rewrite isvalues_eq_bentries.
    destruct (@bentries'_complete_S A (fun _ => unit)
                (fun path k => eqS (scpath k) path) (fun p => p) set
                (scpath a) Hc) as [elem Hp].
    destruct Hp as [Hin He].
    pose proof (InB_map (fun entry : sigT (fun path => BEntry A (fun _ => unit)
                                           (fun k => eqS (scpath k) path))
                          => (projT2 entry).(bekey)) (bentries set) elem Hin)
      as Hmap.
    assert (Hmap' : InB (List.map (fun entry : sigT (fun path => BEntry A
                        (fun _ => unit) (fun k => eqS (scpath k) path))
                      => (projT2 entry).(bekey)) (bentries set))
                        ((projT2 elem).(bekey))) by exact Hmap.
    assert (Hkey : (projT2 elem).(bekey) = a).
    { apply (scpath_inj). apply (eqS_eq (T := BPath)).
      exact (eqS_trans (projT2 elem).(bekeyP) He). }
    rewrite Hkey in Hmap'. exact Hmap'.
  Qed.

  Lemma isvalues_contains : forall {A : Type} `{SubCountable A}
    (set : SCSet A) (a : A),
    InB (isvalues set) a -> SCSetContains set a.
  Proof.
    intros A HSub set a Hin.
    rewrite isvalues_eq_bentries in Hin.
    destruct (InB_map_inv (fun entry : sigT (fun path => BEntry A (fun _ => unit)
                                    (fun k => eqS (scpath k) path))
                            => (projT2 entry).(bekey)) (bentries set) a Hin)
      as [elem Hinl Hkey].
    pose proof (scmap_entry_contained set elem Hinl) as Hc.
    exact (eqS_subst (fun y => SCSetContains set y) Hkey Hc).
  Qed.

  (* Collection over the values of an SCSet, in SProp. *)
  Lemma SChkD2_set_forall : forall {A : Type} `{SubCountable A}
    (set : SCSet A) (P : A -> list UT -> SProp),
    (forall (a : A) (D D' : list UT),
        (forall u : UT, InB D u -> InB D' u) -> P a D -> P a D') ->
    (forall (a : A) (ha : InB (isvalues set) a), existsTS D : list UT, P a D) ->
    existsTS D : list UT, forall a : A, InB (isvalues set) a -> P a D.
  Proof.
    intros A HSub set P Pmono H.
    induction (isvalues set) as [| x xs IH].
    - exists (nil : list UT). intros a Hin.
      exact (falseSeS (InB_nil_absurd Hin)).
    - destruct (H x (inb_head x xs)) as [Dx Hx].
      destruct IH as [Dxs Hxs].
      { intros a ha. apply H. exact (inb_tail x a xs ha). }
      exists (app Dx Dxs). intros a Ha.
      apply InB_or in Ha. destruct Ha as [Heq | Htail].
      + apply (Pmono a Dx (app Dx Dxs)).
        * intros u Hu. apply InB_app_l. exact Hu.
        * exact (@eqS_subst' A (fun y => P y Dx) a x Heq Hx).
      + apply (Pmono a Dxs (app Dx Dxs)).
        * intros u Hu. apply InB_app_r. exact Hu.
        * apply Hxs. exact Htail.
  Qed.

End SCSetEnumSection.

(* ============================================================
   Canonical completeness: every canonical CheckExpression has a
   finite SChkD2 witness.
   ============================================================ *)

(* Membership in a list as an SProp, obtained from ordinary membership. *)
Lemma In_to_InB : forall {A : Type} (l : list A) (a : A),
  In a l -> InB l a.
Proof.
  intros A l. induction l as [| x xs IH]; intros a H.
  - destruct H.
  - simpl. destruct H as [Heq | Htail].
    + subst a. exact (inb_head x xs).
    + exact (inb_tail x a xs (IH a Htail)).
Qed.

(* ============================================================
   A Type-level enumeration of all signature values of a finite
   method set, needed because the [In] facts required by
   [d2_object] live in Prop and cannot be extracted from SProp.
   ============================================================ *)



Section CanonSChkD2Section.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context (MFin : forall m : Method scheme, Finite (MInput scheme m)).

  Lemma canon_check_SChkD2 : forall {Input : Sort}
    (ctx : SortElimination UT Input) (e : Expression Input) (u : UT),
    CheckExpression (canonSpace IPFin deq) ctx e u ->
    existsTS D : list UT, SChkD2 IPFin deq D ctx e u.
  Proof.
    intros Input ctx e u h.
    induction h.
    - (* cesub *)
      destruct IHh as [D HD].
      exists D.
      exact (@d2_sub IPFin deq D Input context expression t t' HD s).
    - (* ceinput *)
      exists (nil : list UT).
      exact (@d2_input IPFin deq nil Input context input).
    - (* ceinvoke *)
      destruct c as [treceiver0 signature0 hu | i0 args0 contains0].
      + (* cmunreachable *)
        destruct IHh as [Drecv Hrecv].
        assert (Hargs : existsTS D : list UT,
          forall input : MInput scheme method,
            SChkD2 IPFin deq D context (einputs input) utanyT).
        { apply (@SChkD2_finite_forall (MInput scheme method) (MFin method)
                   (fun input D => SChkD2 IPFin deq D context (einputs input) utanyT)).
          - intros input D D' Hsub HD.
            exact (SChkD2_mono IPFin deq D D' Hsub context (einputs input) utanyT HD).
          - intro input.
            destruct (H input) as [Di HDi].
            exists Di.
            exact (@d2_sub IPFin deq Di Input context (einputs input)
                     (signature0.(smsinput) input) utanyT HDi (subT_top _)). }
        destruct Hargs as [Dargs Hargs].
        exists (app Drecv Dargs).
        unfold unReachableT in hu.
        destruct treceiver0; simpl in hu.
        * exact (falseSeS hu).
        * apply (@d2_invoke_unr IPFin deq (app Drecv Dargs) Input context
                   ereceiver method einputs signature0.(smsresult)).
          -- apply (SChkD2_mono IPFin deq Drecv (app Drecv Dargs)).
             ++ intros u0 Hu0. apply InB_app_l. exact Hu0.
             ++ exact Hrecv.
          -- intro input.
             apply (SChkD2_mono IPFin deq Dargs (app Drecv Dargs)).
             ++ intros u0 Hu0. apply InB_app_r. exact Hu0.
             ++ exact (Hargs input).
        * exact (falseSeS hu).
      + (* cminterface *)
        destruct IHh as [Drecv Hrecv].
        assert (Hargs : existsTS D : list UT,
          forall input : MInput scheme method,
            SChkD2 IPFin deq D context (einputs input)
              (utsubst args0 ((((formalBody i0).(ubsmethod) method contains0).(umsinput) input)))).
        { apply (@SChkD2_finite_forall (MInput scheme method) (MFin method)
                   (fun input D => SChkD2 IPFin deq D context (einputs input)
                      (utsubst args0 ((((formalBody i0).(ubsmethod) method contains0).(umsinput) input))))).
          - intros input D D' Hsub HD.
            exact (SChkD2_mono IPFin deq D D' Hsub context (einputs input)
                     (utsubst args0 ((((formalBody i0).(ubsmethod) method contains0).(umsinput) input))) HD).
          - intro input.
            exact (H input). }
        destruct Hargs as [Dargs Hargs].
        exists (app (vals (IPFin i0) args0) (app Drecv Dargs)).
        refine (@d2_invoke_iface IPFin deq
                  (app (vals (IPFin i0) args0) (app Drecv Dargs)) Input context
                  i0 method contains0 args0 _ ereceiver einputs _ _).
        * intros p. apply InB_app_l. apply In_to_InB. apply vals_complete.
        * apply (SChkD2_mono IPFin deq Drecv (app (vals (IPFin i0) args0) (app Drecv Dargs))).
          -- intros u0 Hu0. apply InB_app_r. apply InB_app_l. exact Hu0.
          -- exact Hrecv.
        * intro input.
          apply (SChkD2_mono IPFin deq Dargs (app (vals (IPFin i0) args0) (app Drecv Dargs))).
          -- intros u0 Hu0. apply InB_app_r. apply InB_app_r. exact Hu0.
          -- exact (Hargs input).
    - (* ceobject *)
      pose (Pmeth := fun (m : Method scheme) (D : list UT) =>
        AndS
          (forall ha : InB (isvalues methods) m,
             SChkD2 IPFin deq D
               (pair_elimination (smsinput (signatures m (isvalues_contains methods m ha))) context)
               (bodies m (isvalues_contains methods m ha))
               (smsresult (signatures m (isvalues_contains methods m ha))))
          (AndS
             (forall (ha : InB (isvalues methods) m) (input : MInput scheme m),
                InB D (smsinput (signatures m (isvalues_contains methods m ha)) input))
             (forall ha : InB (isvalues methods) m,
                InB D (smsresult (signatures m (isvalues_contains methods m ha)))))).
      assert (Pmono : forall (m : Method scheme) (D D' : list UT),
        (forall u : UT, InB D u -> InB D' u) -> Pmeth m D -> Pmeth m D').
      { intros m D D' Hsub [Hb [Hin Hres]].
        split.
        - intros ha. exact (SChkD2_mono IPFin deq D D' Hsub
            (pair_elimination (smsinput (signatures m (isvalues_contains methods m ha))) context)
            (bodies m (isvalues_contains methods m ha))
            (smsresult (signatures m (isvalues_contains methods m ha)))
            (Hb ha)).
        - split.
          + intros ha input. apply Hsub. exact (Hin ha input).
          + intros ha. apply Hsub. exact (Hres ha). }
      assert (Hper : forall (m : Method scheme) (ha : InB (isvalues methods) m),
        existsTS D : list UT, Pmeth m D).
      { intros m ha.
        pose (hc0 := isvalues_contains methods m ha).
        pose (sig0 := signatures m hc0).
        destruct (H m hc0) as [Dbody HbodyD].
        exists (app Dbody (app (vals (MFin m) (sig0.(smsinput))) [sig0.(smsresult)])).
        split.
        - intros ha'. exact (SChkD2_mono IPFin deq Dbody
            (app Dbody (app (vals (MFin m) (sig0.(smsinput))) [sig0.(smsresult)]))
            (fun u Hu => InB_app_l _ _ _ Hu)
            (pair_elimination (smsinput (signatures m (isvalues_contains methods m ha'))) context)
            (bodies m (isvalues_contains methods m ha'))
            (smsresult (signatures m (isvalues_contains methods m ha')))
            HbodyD).
        - split.
          + intros ha' input.
            apply InB_app_r. apply InB_app_l. apply In_to_InB.
            apply (vals_complete (MFin m) (smsinput sig0) input).
          + intros ha'.
            apply InB_app_r. apply InB_app_r. apply inb_head. }
      destruct (@SChkD2_set_forall (Method scheme) (Method_SubCountable scheme)
                  methods Pmeth Pmono Hper) as [Dmeth Hall].
      exists (app Dmeth (vals (IPFin interface) arguments)).
      refine (@d2_object IPFin deq (app Dmeth (vals (IPFin interface) arguments)) Input context
                interface methods bodies arguments _ signatures _ _ s _).
      + intros p. apply InB_app_r. apply In_to_InB. apply vals_complete.
      + intros m hc input.
        pose (HinB := isvalues_complete methods m hc).
        destruct (Hall m HinB) as [Hb [Hin Hres]].
        apply InB_app_l.
        exact (Hin (isvalues_complete methods m hc) input).
      + intros m hc.
        pose (HinB := isvalues_complete methods m hc).
        destruct (Hall m HinB) as [Hb [Hin Hres]].
        apply InB_app_l.
        exact (Hres (isvalues_complete methods m hc)).
      + intros m hc.
        pose (HinB := isvalues_complete methods m hc).
        destruct (Hall m HinB) as [Hb [Hin Hres]].
        apply (SChkD2_mono IPFin deq Dmeth (app Dmeth (vals (IPFin interface) arguments))).
        * intros u Hu. apply InB_app_l. exact Hu.
        * exact (Hb (isvalues_complete methods m hc)).
  Qed.

End CanonSChkD2Section.



(* ==== Pointwise substitution and inferred-signature monotonicity ==== *)
Section PointwiseSubstSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma utsubst_pointwise_sub : forall {Var : Type} (f g : Var -> UT)
    (Q : UserType Var),
    (forall p : Var, f p = g p) ->
    AndS (SubT (utsubst f Q) (utsubst g Q))
         (SubT (utsubst g Q) (utsubst f Q)).
  Proof.
    intros Var f g Q.
    induction Q as [p | | i args IH]; intros Heq.
    - simpl. rewrite (Heq p).
      exact (conjS (SubT (g p) (g p)) (SubT (g p) (g p))
                (subT_refl (g p)) (subT_refl (g p))).
    - simpl.
      exact (conjS (SubT utanyT utanyT) (SubT utanyT utanyT)
                (subT_top utanyT) (subT_top utanyT)).
    - simpl.
      refine (conjS _ _
        (@subT_variance i
           (fun p => utsubst f (args p)) (fun p => utsubst g (args p))
           (fun p => _))
        (@subT_variance i
           (fun p => utsubst g (args p)) (fun p => utsubst f (args p))
           (fun p => _))).
      + destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
        * apply isnegative. exact (proj2_AndS (IH p Heq)).
        * apply ispositive. exact (proj1_AndS (IH p Heq)).
      + destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
        * apply isnegative. exact (proj1_AndS (IH p Heq)).
        * apply ispositive. exact (proj2_AndS (IH p Heq)).
  Qed.

  Lemma utifaceT_pointwise_sub : forall (i : Interface scheme)
    (f g : IParameter scheme i -> UT),
    (forall p : IParameter scheme i, f p = g p) ->
    SubT (utifaceT i f) (utifaceT i g).
  Proof.
    intros i f g Heq.
    apply (subT_variance i f g).
    intro p.
    destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
    - apply isnegative. rewrite (Heq p). apply subT_refl.
    - apply ispositive. rewrite (Heq p). apply subT_refl.
  Qed.

End PointwiseSubstSection.

Section ObjSignaturePointwiseSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma obj_signature_gen_input_le : forall (i : Interface scheme)
    (c f' : IParameter scheme i -> UT) (m : Method scheme),
    (forall p : IParameter scheme i, c p = f' p) ->
    forall input : MInput scheme m,
    SubT ((obj_signature_gen IPFin deq i f' m).(smsinput) input)
         ((obj_signature_gen IPFin deq i c m).(smsinput) input).
  Proof.
    intros i c f' m Hagree input.
    unfold obj_signature_gen.
    destruct (dec_bcontains (fun path k => eqS (scpath k) path)
                (formalBody i).(ubsmethods) (scpath m)) as [cf | ncf].
    - simpl.
      exact (proj2_AndS
        (utsubst_pointwise_sub c f'
           (((formalBody i).(ubsmethod) m cf).(umsinput) input) Hagree)).
    - simpl. apply subT_refl.
  Qed.

  Lemma obj_signature_gen_result_le : forall (i : Interface scheme)
    (c f' : IParameter scheme i -> UT) (m : Method scheme),
    (forall p : IParameter scheme i, c p = f' p) ->
    SubT ((obj_signature_gen IPFin deq i c m).(smsresult))
         ((obj_signature_gen IPFin deq i f' m).(smsresult)).
  Proof.
    intros i c f' m Hagree.
    unfold obj_signature_gen.
    destruct (dec_bcontains (fun path k => eqS (scpath k) path)
                (formalBody i).(ubsmethods) (scpath m)) as [cf | ncf].
    - simpl.
      exact (proj1_AndS
        (utsubst_pointwise_sub c f'
           (((formalBody i).(ubsmethod) m cf).(umsresult)) Hagree)).
    - simpl. apply subT_refl.
  Qed.

End ObjSignaturePointwiseSection.

(* ==== Context monotonicity for SChkD2 ==== *)
Section SChkD2CtxSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma pair_elimination_le : forall {T : Type} {Input : Sort}
    (f : T -> UT) (ctx ctx' : SortElimination UT Input),
    (forall x : SumSort Input,
        SubT (apply_elimination ctx' x) (apply_elimination ctx x)) ->
    forall x : SumSort (T :: Input)%list,
      SubT (apply_elimination (pair_elimination f ctx') x)
           (apply_elimination (pair_elimination f ctx) x).
  Proof.
    intros T Input f ctx ctx' H x.
    destruct x as [t | x'].
    - simpl. apply subT_refl.
    - simpl. apply H.
  Qed.

  Lemma SChkD2_context_le : forall (D : list UT) {Input : Sort}
    (ctx ctx' : SortElimination UT Input),
    (forall x : SumSort Input,
        SubT (apply_elimination ctx' x) (apply_elimination ctx x)) ->
    forall (e : Expression Input) (u : UT),
    SChkD2 IPFin deq D ctx e u -> SChkD2 IPFin deq D ctx' e u.
  Proof.
    intros D Input ctx ctx' Hle e u h.
    revert ctx' Hle.
    induction h; intros ctx' Hle.
    - eapply (@d2_sub IPFin deq D Input ctx' (einput x)
               (apply_elimination ctx' x) (apply_elimination ctxc x)).
      + exact (@d2_input IPFin deq D Input ctx' x).
      + apply Hle.
    - eapply (@d2_sub IPFin deq D Input ctx' e u v).
      + exact (IHh ctx' Hle).
      + exact s.
    - eapply (@d2_invoke_unr IPFin deq D Input ctx' er m eargs u).
      + exact (IHh ctx' Hle).
      + intro input. exact (H input ctx' Hle).
    - eapply (@d2_invoke_iface IPFin deq D Input ctx' i m contains c Hc er eargs).
      + exact (IHh ctx' Hle).
      + intro input. exact (H input ctx' Hle).
    - eapply (@d2_object IPFin deq D Input ctx' i methods bodies c Hc sigs Hsin Hsres Hconf).
      + intros m hc.
        eapply (H m hc (pair_elimination (smsinput (sigs m hc)) ctx')).
        apply pair_elimination_le. exact Hle.
  Qed.
End SChkD2CtxSection.


(* ==== ProgramV from a finite canonical witness ==== *)
Lemma programv_of_SChkD2
  (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (ISS : SSet (Interface scheme))
  (D : list UT) (program : Program) (hh : HierarchyV)
  (h : SChkD2 IPFin deq D nil_elimination program.(pexpression)
         (utsubst (emptye (T := UT)) program.(ptype)))
  : @ProgramV ISS program.
Proof.
  refine (@Build_ProgramV ISS program hh _).
  refine (ex_introSSS (canonSpace IPFin deq) (@canonConsistent IPFin deq ISS deq) _).
  exact (SChkD2_sound IPFin deq D nil nil_elimination program.(pexpression)
           (utsubst (emptye (T := UT)) program.(ptype)) h).
Qed.


(* ==== SChkD2 target weakening to top ==== *)
Lemma SChkD2_top
  (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (D : list UT) {Input : Sort} (ctx : SortElimination UT Input)
  (e : Expression Input) (u : UT)
  (h : SChkD2 IPFin deq D ctx e u)
  : SChkD2 IPFin deq D ctx e utanyT.
Proof.
  eapply (@d2_sub IPFin deq D Input ctx e u utanyT h).
  exact (subT_top u).
Qed.

(* ==== Trivial any/bot signature conformance ==== *)
Section AnyBotConfSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma any_bot_bssubst_conformance : forall (i : Interface scheme)
    (methods : SCSet (Method scheme))
    (c : IParameter scheme i -> UT)
    (Hcontains : forall m : Method scheme,
        SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m),
    SubSpaceBodySignature
      (@Build_SpaceBodySignature (canonSpace IPFin deq) methods
         (fun (m : Method scheme) (_ : SCSetContains methods m) =>
            @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
              (fun _ => utanyT) utbotT))
      (@bssubst (IParameter scheme i) (canonSpace IPFin deq) c (formalBody i)).
  Proof.
    intros i methods c Hcontains.
    refine (@Build_SubSpaceBodySignature (canonSpace IPFin deq)
              (@Build_SpaceBodySignature (canonSpace IPFin deq) methods
                 (fun (m : Method scheme) (_ : SCSetContains methods m) =>
                    @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                      (fun _ => utanyT) utbotT))
              (@bssubst (IParameter scheme i) (canonSpace IPFin deq) c (formalBody i))
              (fun m cf => Hcontains m cf) _).
    intros m cf.
    refine (@Build_SubSpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m) _ _ _ _).
    - intro input. exact (subT_top _).
    - exact (subT_bot _).
  Qed.
End AnyBotConfSection.

(* ==== SChkD2 object constructor with utany/bot signatures ==== *)
Section D2AnyBotSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma d2_object_any_bot : forall (D : list UT) {Input : Sort}
    (ctx : SortElimination UT Input) (i : Interface scheme)
    (methods : SCSet (Method scheme))
    (bodies : forall method : Method scheme,
                SCSetContains methods method ->
                Expression (MInput scheme method :: Input)%list)
    (c : IParameter scheme i -> UT)
    (Hc : forall p : IParameter scheme i, InB D (c p))
    (Hany : InB D utanyT) (Hbot : InB D utbotT)
    (Hcontains : forall m : Method scheme,
        SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m)
    (Hbodies : forall (m : Method scheme) (hc : SCSetContains methods m),
        SChkD2 IPFin deq D (pair_elimination (fun _ => utanyT) ctx)
          (bodies m hc) utbotT),
    SChkD2 IPFin deq D ctx (eobject i methods bodies) (utifaceT i c).
  Proof.
    intros D Input ctx i methods bodies c Hc Hany Hbot Hcontains Hbodies.
    refine (@d2_object IPFin deq D Input ctx i methods bodies c Hc
              (fun (m : Method scheme) (_ : SCSetContains methods m) =>
                 @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                   (fun _ => utanyT) utbotT)
              (fun m hc input => Hany) (fun m hc => Hbot)
              (any_bot_bssubst_conformance IPFin deq i methods c Hcontains)
              Hbodies).
  Qed.
End D2AnyBotSection.

(* ==== Global realization yields a finite SChkD2 witness ==== *)
Section RealToFiniteSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context (MFin : forall m : Method scheme, Finite (MInput scheme m)).
  Context (ISS : SSet (Interface scheme)).

  Lemma programv_SChkD2_of_realization :
    (forall S : TypeSpace, ConsistentTypeSpace S -> CanonRealize S) ->
    forall (program : Program),
      @ProgramV ISS program ->
      existsTS D : list UT,
        SChkD2 IPFin deq D nil_elimination program.(pexpression)
          (utsubst (emptye (T := UT)) program.(ptype)).
  Proof.
    intros Hreal program pv.
    pose proof (@programv_canon_check_of_realization IPFin deq ISS Hreal program pv) as hcan.
    exact (@canon_check_SChkD2 IPFin deq MFin nil nil_elimination
             program.(pexpression) (utsubst (emptye (T := UT)) program.(ptype)) hcan).
  Qed.
End RealToFiniteSection.

(* ==== Canonical object constructor with utany/bot signatures ==== *)
Section CanonObjAnyBotSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).

  Lemma canon_object_any_bot : forall {Input : Sort}
    (ctx : SortElimination UT Input) (i : Interface scheme)
    (methods : SCSet (Method scheme))
    (bodies : forall method : Method scheme,
                SCSetContains methods method ->
                Expression (MInput scheme method :: Input)%list)
    (c : IParameter scheme i -> UT)
    (Hcontains : forall m : Method scheme,
        SCSetContains (formalBody i).(ubsmethods) m -> SCSetContains methods m)
    (Hbodies : forall (m : Method scheme) (hc : SCSetContains methods m),
        CheckExpression (canonSpace IPFin deq)
          (pair_elimination (fun _ => utanyT) ctx) (bodies m hc) utbotT),
    CheckExpression (canonSpace IPFin deq) ctx (eobject i methods bodies)
      (utifaceT i c).
  Proof.
    intros Input ctx i methods bodies c Hcontains Hbodies.
    refine (@ceobject (canonSpace IPFin deq) Input ctx i methods bodies c
              (fun (m : Method scheme) (_ : SCSetContains methods m) =>
                 @Build_SpaceMethodSignature (canonSpace IPFin deq) (MInput scheme m)
                   (fun _ => utanyT) utbotT) _ _).
    - exact (any_bot_bssubst_conformance IPFin deq i methods c Hcontains).
    - intros m hc. exact (Hbodies m hc).
  Qed.
End CanonObjAnyBotSection.


(* ==== Canonical checks weaken to the top type ==== *)
Lemma check_canon_top
  (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  {Input : Sort} (ctx : SortElimination UT Input)
  (e : Expression Input) (u : UT)
  (h : CheckExpression (canonSpace IPFin deq) ctx e u)
  : CheckExpression (canonSpace IPFin deq) ctx e utanyT.
Proof.
  eapply (@cesub (canonSpace IPFin deq) Input ctx e u utanyT h).
  exact (subT_top u).
Qed.

(* ==== ProgramV vs finite canonical witness (conditional forward) ==== *)
Section ProgFiniteSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context (MFin : forall m : Method scheme, Finite (MInput scheme m)).
  Context (ISS : SSet (Interface scheme)).

  Lemma programv_finite_forward :
    (forall S : TypeSpace, ConsistentTypeSpace S -> CanonRealize S) ->
    forall (program : Program),
      @ProgramV ISS program ->
      AndS HierarchyV
        (existsTS D : list UT,
           SChkD2 IPFin deq D nil_elimination program.(pexpression)
             (utsubst (emptye (T := UT)) program.(ptype))).
  Proof.
    intros Hreal program pv. apply conjS.
    - exact (phierarchyv pv).
    - exact (programv_SChkD2_of_realization IPFin deq MFin ISS Hreal program pv).
  Qed.

  Lemma programv_finite_backward :
    forall (program : Program),
      AndS HierarchyV
        (existsTS D : list UT,
           SChkD2 IPFin deq D nil_elimination program.(pexpression)
             (utsubst (emptye (T := UT)) program.(ptype))) ->
      @ProgramV ISS program.
  Proof.
    intros program [hh [D hD]].
    exact (programv_of_SChkD2 IPFin deq ISS D program hh hD).
  Qed.
End ProgFiniteSection.


(* ==== Program-level canonical finite-model specialization ==== *)
Lemma program_canon_finite
  (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (MFin : forall m : Method scheme, Finite (MInput scheme m))
  (program : Program)
  (h : CheckExpression (canonSpace IPFin deq) nil_elimination
         program.(pexpression) (utsubst (emptye (T := UT)) program.(ptype)))
  : existsTS D : list UT,
      SChkD2 IPFin deq D nil_elimination program.(pexpression)
        (utsubst (emptye (T := UT)) program.(ptype)).
Proof.
  exact (@canon_check_SChkD2 IPFin deq MFin nil nil_elimination
           program.(pexpression) (utsubst (emptye (T := UT)) program.(ptype)) h).
Qed.

(* ==== Decidable SProp list existential ==== *)
Section ListExistsSSection.
  Context {A : Type}.

  Inductive ListExistsS : (A -> SProp) -> list A -> SProp :=
  | les_head (P : A -> SProp) (a : A) (l : list A) : P a -> ListExistsS P (a :: l)
  | les_tail (P : A -> SProp) (a : A) (l : list A) : ListExistsS P l -> ListExistsS P (a :: l).

  Definition ListExistsS_nil_absurd (P : A -> SProp) (h : ListExistsS P nil) : FalseS
  := match h in ListExistsS _ l0
           return match l0 with nil => FalseS | cons _ _ => TrueS end with
     | les_head _ _ _ _ => trueS
     | les_tail _ _ _ _ => trueS
     end.

  Lemma ListExistsS_cons_inv : forall (P : A -> SProp) (a : A) (l : list A),
    ListExistsS P (a :: l) -> OrS (P a) (ListExistsS P l).
  Proof.
    intros P a l h. remember (a :: l) as L eqn:E. revert a l E.
    induction h as [P0 b l' pb | P0 b l' h' IH]; intros a0 l0 E.
    - injection E as Ha Hl. subst. exact (oleftS pb).
    - injection E as Ha Hl. subst. exact (orightS h').
  Qed.

  Lemma ListExistsS_mono : forall (P Q : A -> SProp) (l : list A),
    (forall a : A, P a -> Q a) -> ListExistsS P l -> ListExistsS Q l.
  Proof.
    intros P Q l H h. induction h as [P0 a l0 pa | P0 a l0 h' IH].
    - exact (les_head Q a l0 (H a pa)).
    - exact (les_tail Q a l0 (IH H)).
  Qed.

  Lemma ListExistsS_app_l : forall (P : A -> SProp) (l l' : list A),
    ListExistsS P l -> ListExistsS P (app l l').
  Proof.
    intros P l. induction l as [| a l IH]; intros l' h.
    - inversion h.
    - inversion h as [P0 b l0 pa | P0 b l0 h'];
        subst; simpl.
      + exact (les_head P a (app l l') pa).
      + exact (les_tail P a (app l l') (IH l' h')).
  Qed.

  Fixpoint dec_list_existsS (P : A -> SProp)
    (d : forall a : A, DeciderS (P a)) (l : list A)
    : DeciderS (ListExistsS P l).
  Proof.
    destruct l as [| a l'].
    - exact (sbrightS (fun h => ListExistsS_nil_absurd P h)).
    - destruct (d a) as [pa | na].
      + exact (sbleftS (les_head P a l' pa)).
      + destruct (dec_list_existsS P d l') as [hl | nl].
        * exact (sbleftS (les_tail P a l' hl)).
        * exact (sbrightS (fun h =>
            match ListExistsS_cons_inv P a l' h with
            | oleftS pa => na pa
            | orightS hl => nl hl
            end)).
  Qed.
End ListExistsSSection.


(* ==== Finite program-witness search interface ==== *)
Lemma dec_program_finite_witness
  (IPFin : forall i : Interface scheme, Finite (IParameter scheme i))
  (deq : forall x y : Interface scheme, {x = y} + {x = y -> False})
  (program : Program) (Ds : list (list UT))
  (d : forall D : list UT,
      DeciderS (SChkD2 IPFin deq D nil_elimination program.(pexpression)
                  (utsubst (emptye (T := UT)) program.(ptype))))
  : DeciderS
      (ListExistsS
         (fun D : list UT =>
            SChkD2 IPFin deq D nil_elimination program.(pexpression)
              (utsubst (emptye (T := UT)) program.(ptype)))
         Ds).
Proof.
  exact (dec_list_existsS
           (fun D : list UT =>
              SChkD2 IPFin deq D nil_elimination program.(pexpression)
                (utsubst (emptye (T := UT)) program.(ptype)))
           d Ds).
Qed.


(* ==== Finite choice for finitely enumerable domains ==== *)
Section ProjFiniteSection.
  Context (T : Type) (T' : Type) (d : T') (Rel : T -> T' -> SProp).
  Context `{FinT : Finite T}.

  Let full : BTrunk := sftrunk T.

  Fixpoint trunk_choice (f : BPath -> BPath) (trunk : BTrunk)
    (feq : forall path : BPath, BTContains trunk path -> BTContains full (f path))
    (H : forall (path : BPath) (c : BTContains trunk path),
        existsTS u : T', Rel (fpath T (f path) (feq path c)) u) {struct trunk}
    : existsTS g : BPath -> T',
        forall (path : BPath) (c : BTContains trunk path),
          Rel (fpath T (f path) (feq path c)) (g path).
  Proof.
    destruct trunk as [| head first second].
    - refine (ex_introTS (fun _ => d) _).
      intros path c. exact (falseSeS c).
    - destruct head as [|].
      + destruct (trunk_choice (fun p => f (bfirst p)) first
                    (fun p c => feq (bfirst p) c)
                    (fun p c => H (bfirst p) c)) as [g1 hg1].
        destruct (trunk_choice (fun p => f (bsecond p)) second
                    (fun p c => feq (bsecond p) c)
                    (fun p c => H (bsecond p) c)) as [g2 hg2].
        refine (ex_introTS
                  (fun path => match path with
                               | bend => d
                               | bfirst p => g1 p
                               | bsecond p => g2 p
                               end) _).
        intros path c. destruct path as [| p | p]; simpl.
        * exact (falseSeS c).
        * exact (hg1 p c).
        * exact (hg2 p c).
      + destruct (H bend trueS) as [u hu].
        destruct (trunk_choice (fun p => f (bfirst p)) first
                    (fun p c => feq (bfirst p) c)
                    (fun p c => H (bfirst p) c)) as [g1 hg1].
        destruct (trunk_choice (fun p => f (bsecond p)) second
                    (fun p c => feq (bsecond p) c)
                    (fun p c => H (bsecond p) c)) as [g2 hg2].
        refine (ex_introTS
                  (fun path => match path with
                               | bend => u
                               | bfirst p => g1 p
                               | bsecond p => g2 p
                               end) _).
        intros path c. destruct path as [| p | p]; simpl.
        * exact hu.
        * exact (hg1 p c).
        * exact (hg2 p c).
  Qed.

  Lemma finite_choice :
    (forall t : T, existsTS u : T', Rel t u) ->
    existsTS g : T -> T', forall t : T, Rel t (g t).
  Proof.
    intro H.
    pose proof (trunk_choice (fun path => path) (sftrunk T)
                  (fun path c => c)
                  (fun path c => H (fpath T path c))) as Htr.
    destruct Htr as [g hg].
    refine (ex_introTS (fun t => g (scpath t)) _).
    intro t.
    pose proof (hg (scpath t) (sfcontains t)) as hc.
    assert (E : fpath T (scpath t) (sfcontains t) = t).
    { apply scpath_inj. symmetry.
      apply (eqS_eq (T := BPath)). apply fpath_eqS. }
    rewrite E in hc. exact hc.
  Qed.
End ProjFiniteSection.

(* ==== Extract a canonical check from a finite SChkD2 witness ==== *)
Section FinalReductionSection.
  Context (IPFin : forall i : Interface scheme, Finite (IParameter scheme i)).
  Context (deq : forall x y : Interface scheme, {x = y} + {x = y -> False}).
  Context (ISS : SSet (Interface scheme)).

  Lemma exists_SChkD2_sound : forall {Input : Sort}
    (ctx : SortElimination UT Input) (e : Expression Input) (u : UT),
    (existsTS D : list UT, SChkD2 IPFin deq D ctx e u) ->
    CheckExpression (canonSpace IPFin deq) ctx e u.
  Proof.
    intros Input ctx e u h.
    destruct h as [D hD].
    exact (@SChkD2_sound IPFin deq D Input ctx e u hD).
  Qed.

  Lemma programv_of_SChkD2_exists
    (program : Program) (hh : HierarchyV)
    (hD : existsTS D : list UT,
            SChkD2 IPFin deq D nil_elimination program.(pexpression)
              (utsubst (emptye (T := UT)) program.(ptype)))
    : @ProgramV ISS program.
  Proof.
    refine (@Build_ProgramV ISS program hh _).
    refine (ex_introSSS (canonSpace IPFin deq)
              (@canonConsistent IPFin deq ISS deq) _).
    exact (exists_SChkD2_sound nil_elimination program.(pexpression)
             (utsubst (emptye (T := UT)) program.(ptype)) hD).
  Qed.

  Theorem programv_decider_of_parts
    (Hh : DeciderS HierarchyV)
    (Hdec : forall program : Program,
        DeciderS (existsTS D : list UT,
          SChkD2 IPFin deq D nil_elimination program.(pexpression)
            (utsubst (emptye (T := UT)) program.(ptype))))
    (Hcomp : forall program : Program,
        @ProgramV ISS program ->
        existsTS D : list UT,
          SChkD2 IPFin deq D nil_elimination program.(pexpression)
            (utsubst (emptye (T := UT)) program.(ptype)))
    : forall program : Program, DeciderS (@ProgramV ISS program).
  Proof.
    intros program.
    destruct Hh as [hh | nh].
    - destruct (Hdec program) as [hD | nD].
      + exact (sbleftS (programv_of_SChkD2_exists program hh hD)).
      + exact (sbrightS (fun pv => nD (Hcomp program pv))).
    - exact (sbrightS (fun pv => nh (phierarchyv pv))).
  Qed.
End FinalReductionSection.


(* ==== Flat canonical targets and their approximation relation ==== *)
Section FlatTargetSection.
  Context (S : TypeSpace).

  Definition RFlat (t : S.(SpaceType)) (u : UT) : SProp
  := match u with
     | utanyT => TrueS
     | utbotT => S.(UnReachable) t
     | utifaceT i b => existsTS a : IParameter scheme i -> S.(SpaceType),
                          S.(SubSpaceType) t (S.(stinterface) i a)
     end.

  Lemma RFlat_any : forall t : S.(SpaceType), RFlat t utanyT.
  Proof. intro t. exact trueS. Qed.

  Lemma RFlat_lower : forall (t t' : S.(SpaceType)) (u : UT),
    S.(SubSpaceType) t t' -> RFlat t' u -> RFlat t u.
  Proof.
    intros t t' u hsub hr.
    destruct u as [| | i b].
    - exact trueS.
    - exact (S.(sstur) t t' hsub hr).
    - destruct hr as [a hle].
      exact (ex_introTS a (S.(ssttrans) t t' (S.(stinterface) i a) hsub hle)).
  Qed.

  Lemma RFlat_iface_char : forall (t : S.(SpaceType)) (i : Interface scheme),
    RFlat t (utifaceT i (fun _ : IParameter scheme i => utanyT)) ->
    existsTS a : IParameter scheme i -> S.(SpaceType),
      S.(SubSpaceType) t (S.(stinterface) i a).
  Proof.
    intros t i h. exact h.
  Qed.
End FlatTargetSection.


(* ==== The all-bottom interface and its order facts ==== *)
Definition BotIface (i : Interface scheme) : UT
:= utifaceT i (fun _ : IParameter scheme i => utbotT).

Lemma subT_bot_iface : forall (i : Interface scheme),
  SubT utbotT (BotIface i).
Proof. intro i. exact (subT_bot (BotIface i)). Qed.

Lemma bot_iface_any : forall (i : Interface scheme),
  SubT (BotIface i) utanyT.
Proof. intro i. exact (subT_top (BotIface i)). Qed.

Lemma bot_iface_high : forall (i : Interface scheme),
  SubT (BotIface i) (HighIface i).
Proof.
  intro i. unfold BotIface, HighIface.
  apply (subT_variance i (fun _ => utbotT) (pol_high i (fun _ => utanyT))).
  intro p. unfold pol_high.
  destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
  - exact (isnegative utbotT utbotT (subT_refl utbotT)).
  - exact (ispositive utbotT utanyT (subT_bot utanyT)).
Qed.

Lemma low_iface_bot : forall (i : Interface scheme),
  SubT (LowIface i) (BotIface i).
Proof.
  intro i. unfold LowIface, BotIface.
  apply (subT_variance i (pol_low i (fun _ => utanyT)) (fun _ => utbotT)).
  intro p. unfold pol_low.
  destruct ((hierarchy.(hinterface) i).(uisvariance) p) as [|].
  - exact (isnegative utanyT utbotT (subT_bot utanyT)).
  - exact (ispositive utbotT utbotT (subT_refl utbotT)).
Qed.


(* ==== RFlat at the extremal same-head targets ==== *)
Section RFlatExtremalSection.
  Context (S : TypeSpace).

  Lemma RFlat_high_iff : forall (t : S.(SpaceType)) (i : Interface scheme),
    RFlat S t (HighIface i) ->
    existsTS a : IParameter scheme i -> S.(SpaceType),
      S.(SubSpaceType) t (S.(stinterface) i a).
  Proof. intros t i h. exact h. Qed.

  Lemma RFlat_low_iff : forall (t : S.(SpaceType)) (i : Interface scheme),
    RFlat S t (LowIface i) ->
    existsTS a : IParameter scheme i -> S.(SpaceType),
      S.(SubSpaceType) t (S.(stinterface) i a).
  Proof. intros t i h. exact h. Qed.

  Lemma RFlat_bot_iface_iff : forall (t : S.(SpaceType)) (i : Interface scheme),
    RFlat S t (BotIface i) ->
    existsTS a : IParameter scheme i -> S.(SpaceType),
      S.(SubSpaceType) t (S.(stinterface) i a).
  Proof. intros t i h. exact h. Qed.

  Lemma RFlat_of_iface_bound : forall (t : S.(SpaceType))
    (i : Interface scheme) (a : IParameter scheme i -> S.(SpaceType)) (u : UT),
    S.(SubSpaceType) t (S.(stinterface) i a) -> RFlat S t (utifaceT i
      (fun p => match u with utanyT => utanyT | _ => utbotT end)).
  Proof.
    intros t i a u h. destruct u; simpl; exact (ex_introTS a h).
  Qed.
End RFlatExtremalSection.

Theorem programv_decider
      {Interface_Finite: Finite scheme.(Interface)}
      {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)}
      {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)}
      (program: Program)
    : DeciderS (ProgramV program).
