Set Implicit Arguments.

Require Import Coq.Init.Datatypes.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax Envs.

Notation simlist := (list var) (only parsing).

Definition simlist_relates (xs1 xs2: simlist) x1 x2 :=
  exists n, LibList.Nth n xs1 x1 /\ LibList.Nth n xs2 x2.

Class Similar (A: Type) := similar: simlist -> simlist -> A -> A -> Prop.

Class SimilarWith (A: Type) := similar_with: simlist -> simlist -> simlist -> simlist -> A -> A -> Prop.

Class SimilarCommon {A: Type} (AS: Similar A) := {

  similar_symm xs ys a b:
    similar xs ys a b ->
    similar ys xs b a ;

  similar_trans xs ys zs a b c:
    fresh \{} (length ys) ys ->
    similar xs ys a b ->
    similar ys zs b c ->
    similar xs zs a c ;

  similar_length xs ys a b:
    similar xs ys a b ->
    length xs = length ys ;

  similar_reorder xs1 ys1 xs2 ys2 ns a b:
    similar xs1 ys1 a b ->
    list_reorder xs1 ns xs2 ->
    list_reorder ys1 ns ys2 ->
    LibList.noduplicates ns ->
    length ns = length xs1 ->
    similar xs2 ys2 a b ;
}.

Class SimilarOut {A: Set} (AS: Similar A) {AF: FreeVar A} := {

  similar_by_same_eq xs a b:
    similar xs xs a b ->
    a = b ;

  similar_refl_by_fv xs a:
    (fv a) \c (from_list xs) ->
    similar xs xs a a ;

  similar_extend x xs y ys a b:
    similar xs ys a b ->
    similar (x::xs) (y::ys) a b ;

  similar_out_fvl xs ys a b:
    similar xs ys a b ->
    fv a \c (from_list xs) ;
  similar_out_fvr xs ys a b:
    similar xs ys a b ->
    fv b \c (from_list ys) ;

  similar_out_shorten_l x xs y ys a b:
    x \notin fv a ->
    similar (x::xs) (y::ys) a b ->
    similar xs ys a b
}.

Class Envy (E: Type) := {
  envy_ok (e: E): Prop;
  envy_dom (e: E): vars;
  envy_fv (e: E): vars;
  envy_concat(e1 e2: E): E
}.

Class SimilarWithIn (E: Type) (En: Envy E) (AS: SimilarWith E):= {
  similar_with_o_push y1 ys1 y2 ys2 (S1 S2: E) xs1 xs2:
    similar_with ys1 ys2 xs1 xs2 S1 S2 ->
    similar_with (y1::ys1) (y2::ys2) xs1 xs2 S1 S2 ;
  similar_with_i_append_invl ys1 ys2 (S1 S2: E) xs11 xs12 xs21 xs22:
    length xs11 = length xs21 ->
    similar_with ys1 ys2 (xs11 ++ xs12) (xs21 ++ xs22) S1 S2 ->
    similar_with ys1 ys2 (xs11) (xs21) S1 S2 ;
  similar_with_i_reorder (a1 a2: E) ns (xs1 xs2 ys1 ys2 zs1 zs2: list var):
    list_reorder xs1 ns zs1 ->
    list_reorder xs2 ns zs2 ->
    LibList.noduplicates ns ->
    length xs1 = length ns ->
    length xs2 = length ns ->
    similar_with ys1 ys2 xs1 xs2 a1 a2 ->
    similar_with ys1 ys2 zs1 zs2 a1 a2 ;
  similar_with_o_reorder (a1 a2: E) ns (ys1 ys2 zs1 zs2: list var):
    list_reorder ys1 ns zs1 ->
    list_reorder ys2 ns zs2 ->
    LibList.noduplicates ns ->
    length ys1 = length ns ->
    length ys2 = length ns ->
    forall (xs1 xs2: list var),
    similar_with ys1 ys2 xs1 xs2 a1 a2 ->
    similar_with zs1 zs2 xs1 xs2 a1 a2 ;
  similar_with_i_push_notin ys1 ys2 xs1 xs2 x1 x2 S1 S2 :
    similar_with ys1 ys2 xs1 xs2 S1 S2 ->
    (x1 \notin envy_dom S1) ->
    (x2 \notin envy_dom S2) ->
    similar_with ys1 ys2 (x1::xs1) (x2::xs2) S1 S2
}.

Class SimilarIn (E: Type) (En: Envy E) (AS: Similar E) := {
  similar_weaken xs ys a1 a2 b1 b2:
    envy_ok (envy_concat a1 a2) ->
    envy_ok (envy_concat b1 b2) ->
    (forall x y, simlist_relates xs ys x y -> (x \in envy_dom a2 <-> y \in envy_dom b2)) ->
    similar xs ys (envy_concat a1 a2) (envy_concat b1 b2) ->
    similar xs ys (a1) (b1) ;
  similar_in_refl_by_fv a xs:
    envy_ok a ->
    (envy_fv a) \c (from_list xs) ->
    similar xs xs a a;
  similar_append_fresh xs1 xs2 (S1 S2: E) zs1 zs2:
    similar xs1 xs2 S1 S2 ->
    fresh (envy_dom S1) (length zs1) zs1 ->
    fresh (envy_dom S2) (length zs2) zs2 ->
    length zs1 = length zs2 ->
    similar (zs1 ++ xs1) (zs2 ++ xs2) (S1) (S2)
}.

Class SimilarEnvIn (A: Set) (AS: Similar (env A)) := {

  similar_by_nil a b:
    similar nil nil a b ;
  similar_extend_notin x xs y ys a b:
    similar xs ys a b ->
    x # a ->
    y # b ->
    similar (x::xs) (y::ys) a b ;
  similar_extend_dom x xs y ys a b c d:
    similar xs ys a b ->
    similar (x::xs) (y::ys) (x ~ c) (y ~ d) ->
    binds x c a ->
    binds y d b ->
    similar (x::xs) (y::ys) a b ;
  similar_swap_after xs ys a1 a2 a3 b1 b2 b3:
    ok (a1 & a2 & a3) ->
    ok (b1 & b2 & b3) ->
    similar xs ys (a1 & a2 & a3) (b1 & b2 & b3) ->
    similar xs ys (a1 & a3 & a2) (b1 & b3 & b2) ;
  similar_concat xs ys a1 b1 a2 b2:
    similar xs ys (a1) (b1) ->
    similar xs ys (a2) (b2) ->
    similar xs ys (a1 & a2) (b1 & b2)
}.

Definition similar_by_subst{A: Set}{AS: SubstVar A}{AF: FreeVar A} (xs1 xs2: simlist) (a1 a2: A) :=
  exists a3 xs3,
    (length xs1) = (length xs3) /\
    (length xs2) = (length xs3) /\
    (fresh ((fv a1) \u (fv a2) \u (from_list xs1) \u (from_list xs2)) (length xs3) xs3) /\
    (fv a3) \c (from_list xs3) /\
    a3 /[xs3 --> xs1] = a1 /\
    a3 /[xs3 --> xs2] = a2.

Section SimilarBySubst.

Context  {A: Set}{AS: SubstVar A}{AF: FreeVar A}{AO: Openable A}{AAS: AbstractSyntax AO AF AS}{ASC: SubstCommut AAS}{AFC: FvSubstCases AAS}{ASF: SubstFresh AAS}.

Let SA: Similar A := similar_by_subst.

End SimilarBySubst.

Section SimilarBySubst.

Context  {A: Set}{AS: SubstVar A}{AF: FreeVar A}{AO: Openable A}{AAS: AbstractSyntax AO AF AS}{ASC: SubstCommut AAS}{AFC: FvSubstCases AAS}{ASF: SubstFresh AAS}.

Let SA: Similar A := similar_by_subst.

End SimilarBySubst.

Section SimilarBySubst.

Context  {A: Set}{AS: SubstVar A}{AF: FreeVar A}{AO: Openable A}{AAS: AbstractSyntax AO AF AS}{ASC: SubstCommut AAS}{AFC: FvSubstCases AAS}{ASF: SubstFresh AAS}{ASI: SubstId AAS}.

End SimilarBySubst.

Section SimilarCommon.

Context {A: Set} {AS: Similar A} {AF: FreeVar A} {ASC: SimilarCommon AS}.

End SimilarCommon.

Section SimilarOut.

Context {A: Set} {AS: Similar A} {AF: FreeVar A} {ASC: SimilarCommon AS} {ASO: SimilarOut AS}.

End SimilarOut.

Section SimilarWithIn.

Context {A: Type}{E: Envy A}{SW: SimilarWith A}{SWI: SimilarWithIn E SW}.

End SimilarWithIn.

Inductive similar_env_with{A: Set}(AS: Similar A): SimilarWith (env A)  :=
| similar_env_empty ys1 ys2 S1 S2:
    length ys1 = length ys2 ->
    similar_with ys1 ys2 nil nil S1 S2
| similar_env_dom ys1 ys2 S1 S2 xs1 xs2 x1 x2 it1 it2:
    @similar_with (env A) (@similar_env_with A AS) ys1 ys2 xs1 xs2 S1 S2 ->
    (binds x1 it1 S1) ->
    (binds x2 it2 S2) ->
    similar ys1 ys2 it1 it2 ->
    similar_with ys1 ys2 (x1::xs1) (x2::xs2) S1 S2
| similar_env_notin ys1 ys2 S1 S2 xs1 xs2 x1 x2:
    @similar_with (env A) (@similar_env_with A AS) ys1 ys2 xs1 xs2 S1 S2 ->
    (x1 # S1) ->
    (x2 # S2) ->
    similar_with ys1 ys2 (x1::xs1) (x2::xs2) S1 S2.

Section SimilarEnvWith.

Context {A: Set}{AS: Similar A}{AF: FreeVar A}{ASC: SimilarCommon AS}{ASO: SimilarOut AS}.

Let SW: SimilarWith (env A) := similar_env_with AS.

#[local] Existing Instance SW.

Definition similar_env x1 x2 a1 a2 := similar_with x1 x2 x1 x2 a1 a2.

End SimilarEnvWith.

Section SimilarEnv.

Context {A: Set}{AS: Similar A}{AF: FreeVar A}{ASC: SimilarCommon AS}{ASO: SimilarOut AS}.

Section SimilarEnvWith.

Let SW: SimilarWith (env A) := similar_env_with AS.

End SimilarEnvWith.

Let SE: Similar (env A) := similar_env.

End SimilarEnv.
