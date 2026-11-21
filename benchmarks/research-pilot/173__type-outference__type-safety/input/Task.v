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

Theorem safety {Interface_SSet: SSet scheme.(Interface)}
               (space: TypeSpace)
               (expression: Expression nil)
               (type: space.(SpaceType))
             : HierarchyV
            -> ConsistentTypeSpace space
            -> CheckExpression space nil_elimination expression type
            -> AndS (OrS (Value expression) (existsTS expression': Expression nil, StepsTo expression expression'))
                    (forall expression': Expression nil, StepsTo expression expression' -> CheckExpression space nil_elimination expression' type).
