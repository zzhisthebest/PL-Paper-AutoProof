Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Require Import Context Equivalence Indep GeneralTyping.

Require Import Transformation Weakening EWeakening Substitution TransformationTerm.

Require Import Narrowing Substitution Subenvironments.

Require Import Sealing.

Require Import Visibility.

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive trf_local_trm (Cond: LiftCond) (TL: TermTransform): TermTransform :=

| trf_local_trm_local Ga Gb ea eb Ta Tb ta tb Sa Sb:
    〈Ga⁏ea ⊢ ta ∶ Ta〉 ∼TL∼> 〈Gb⁏eb ⊢ tb ∶ Tb〉 ->
    Ga ⁏ ea ⊢ Ta <: Sa ->
    Gb ⁏ eb ⊢ Tb <: Sb ->
    〈Ga⁏ea ⊢ ta ∶ Sa〉 ∼(Cond TrfContextTy typ trm)∼∼(trf_local_trm Cond TL)∼> 〈Gb⁏eb ⊢ tb ∶ Sb〉

| trf_local_trm_letl Ga Gb ea eb tla tlb Ta Tb Tla Tlb tr L Sa Sb:
    〈Ga⁏ea ⊢ tla ∶ Tla〉 ∼(trf_local_trm Cond TL)∼> 〈Gb⁏eb ⊢ tlb ∶ Tlb〉 ->
    (forall x, x \notin L -> (Ga § x / v_let ~ Tla) ⁏ ea ⊢ (open x tr) ∶ Ta) ->
    (forall x, x \notin L -> (Gb § x / v_let ~ Tlb) ⁏ eb ⊢ (open x tr) ∶ Tb) ->
    Ga ⁏ ea ⊢ Ta <: Sa ->
    Gb ⁏ eb ⊢ Tb <: Sb ->
    〈Ga⁏ea ⊢ (trm_let tla tr) ∶ Sa〉 ∼(Cond TrfContextTy typ trm)∼∼(trf_local_trm Cond TL)∼> 〈Gb⁏eb ⊢ (trm_let tlb tr) ∶ Sb〉

| trf_local_trm_letr Ga Gb ea eb tl Ta Tb Tla Tlb tra trb L Sa Sb:
    (forall x, x \notin L ->
      〈Ga § x / v_let ~ Tla⁏ea ⊢ (open x tra) ∶ Ta〉 ∼(trf_local_trm Cond TL)∼> 〈Gb § x / v_let ~ Tlb⁏eb ⊢ (open x trb) ∶ Tb〉
    ) ->
    Ga ⁏ ea ⊢ tl ∶ Tla ->
    Gb ⁏ eb ⊢ tl ∶ Tlb ->
    Ga ⁏ ea ⊢ Ta <: Sa ->
    Gb ⁏ eb ⊢ Tb <: Sb ->
    〈Ga⁏ea ⊢ (trm_let tl tra) ∶ Sa〉 ∼(Cond TrfContextTy typ trm)∼∼(trf_local_trm Cond TL)∼> 〈Gb⁏eb ⊢ (trm_let tl trb) ∶ Sb〉

| trf_local_trm_litl Ga Gb ea eb tla tlb Ta Tb Tla Tlb tr L Sa Sb:
    〈Ga⁏ea ⊢ tla ∶ Tla〉 ∼(trf_local_lit Cond TL)∼> 〈Gb⁏eb ⊢ tlb ∶ Tlb〉 ->
    (forall x, x \notin L ->
      (Ga § x / v_let ~ Tla) ⁏ ea ⊢ (open x tr) ∶ Ta
    ) ->
    (forall x, x \notin L ->
      (Gb § x / v_let ~ Tlb) ⁏ eb ⊢ (open x tr) ∶ Tb
    ) ->
    Ga ⁏ ea ⊢ Ta <: Sa ->
    Gb ⁏ eb ⊢ Tb <: Sb ->
    〈Ga⁏ea ⊢ (trm_lit tla tr) ∶ Sa〉 ∼(Cond TrfContextTy typ trm)∼∼(trf_local_trm Cond TL)∼> 〈Gb⁏eb ⊢ (trm_lit tlb tr) ∶ Sb〉

| trf_local_trm_litr Ga Gb ea eb tl Ta Tb Tla Tlb tra trb L Sa Sb:
    (forall x, x \notin L ->
      〈Ga § x / v_let ~ Tla⁏ea ⊢ (open x tra) ∶ Ta〉 ∼(trf_local_trm Cond TL)∼> 〈Gb § x / v_let ~ Tlb⁏eb ⊢ (open x trb) ∶ Tb〉
    ) ->
    Ga ⁏ ea ⊢ tl ∶ Tla ->
    Gb ⁏ eb ⊢ tl ∶ Tlb ->
    Ga ⁏ ea ⊢ Ta <: Sa ->
    Gb ⁏ eb ⊢ Tb <: Sb ->
    〈Ga⁏ea ⊢ (trm_lit tl tra) ∶ Sa〉 ∼(Cond TrfContextTy typ trm)∼∼(trf_local_trm Cond TL)∼> 〈Gb⁏eb ⊢ (trm_lit tl trb) ∶ Sb〉
with trf_local_lit (Cond: LiftCond) (TL: TermTransform): LitTransform :=

| trf_local_lit_fun Ga Gb ea eb Ta Tb Ua Ub ta tb L:
    mode_has_fun typing_mode ->
    (forall x, x \notin L ->
      〈Ga § x / v_par ~ Ta⁏ea ⊢ (open x ta) ∶ (open x Ua)〉 ∼(trf_local_trm Cond TL)∼> 〈Gb § x / v_par ~ Tb⁏eb ⊢ (open x tb) ∶ (open x Ub)〉
    ) ->
    〈Ga⁏ea ⊢ (lit_fun Ta ta) ∶ (typ_fun Ta Ua)〉 ∼(Cond TrfContextTy typ lit)∼∼(trf_local_lit Cond TL)∼> 〈Gb⁏eb ⊢ (lit_fun Tb tb) ∶ (typ_fun Tb Ub)〉

| trf_local_lit_obj Ga Gb ea eb Ta Tb dsa dsb L:
    (forall x, x \notin L ->
      〈Ga§§(objctx_lit x Ta)⁏ea ⊢ (open x dsa) ∶ (open x Ta)〉 ∼(trf_local_defs Cond TL)∼> 〈Gb§§(objctx_lit x Tb)⁏eb ⊢ (open x dsb) ∶ (open x Tb)〉
    ) ->
    typ_indep_b 0 Ta ->
    typ_indep_b 0 Tb ->
    〈Ga⁏ea ⊢ (lit_obj Ta dsa) ∶ (typ_objlit typing_mode Ta)〉 ∼(Cond TrfContextTy typ lit)∼∼(trf_local_lit Cond TL)∼> 〈Gb⁏eb ⊢ (lit_obj Tb dsb) ∶ (typ_objlit typing_mode Tb)〉
with trf_local_def (Cond: LiftCond) (TL: TermTransform): DefTransform :=

| trf_local_def_met Ga Gb Goa Gob ea eb Ta Tb TCa TCb TZa TZb m ta tb L:
    ( forall xz, xz \notin L ->
      forall xc, xc <> xz -> xc \notin L ->
      〈(ctx_obj_met typing_mode Ga Goa xz TZa xc TCa)⁏ea ⊢ (open_met xz xc ta) ∶ (open_met xz xc Ta)〉 ∼(trf_local_trm Cond TL)∼> 〈(ctx_obj_met typing_mode Gb Gob xz TZb xc TCb)⁏eb ⊢ (open_met xz xc tb) ∶ (open_met xz xc Tb)〉
    ) ->
    〈Ga §§ Goa⁏ea ⊢ (def_met m ta) ∶ (dec_met m TCa TZa Ta)〉 ∼(Cond TrfContextObjTy dec def)∼∼(trf_local_def Cond TL)∼> 〈Gb §§ Gob⁏eb ⊢ (def_met m tb) ∶ (dec_met m TCb TZb Tb)〉
with trf_local_defs (Cond: LiftCond) (TL: TermTransform): DefsTransform :=

| trf_local_defs_one Ga Gb Goa Gob ea eb Da Db dsla dslb:
    〈Ga §§ Goa⁏ea ⊢ dsla ∶ Da〉 ∼(trf_local_def Cond TL)∼> 〈Gb §§ Gob⁏eb ⊢ dslb ∶ Db〉 ->
    〈Ga §§ Goa⁏ea ⊢ (defs_cons defs_nil dsla) ∶ typ_rcd Da〉 ∼(Cond TrfContextObjTy typ defs)∼∼(trf_local_defs Cond TL)∼> 〈Gb §§ Gob⁏eb ⊢ (defs_cons defs_nil dslb) ∶ typ_rcd Db〉

| trf_local_defs_consl Ga Gb Goa Gob ea eb Ta Tb Da Db dsla dslb dsr:
    〈Ga §§ Goa⁏ea ⊢ dsla ∶ Ta〉 ∼(trf_local_defs Cond TL)∼> 〈Gb §§ Gob⁏eb ⊢ dslb ∶ Tb〉 ->
    Ga §§ Goa⁏ea ⊢ dsr ∶d Da ->
    Gb §§ Gob⁏eb ⊢ dsr ∶d Db ->
    defs_hasnt dsla (label_of dsr) ->
    defs_hasnt dslb (label_of dsr) ->
    〈Ga §§ Goa⁏ea ⊢ (defs_cons dsla dsr) ∶ (typ_and Ta (typ_rcd Da))〉 ∼(Cond TrfContextObjTy typ defs)∼∼(trf_local_defs Cond TL)∼> 〈Gb §§ Gob⁏eb ⊢ (defs_cons dslb dsr) ∶ (typ_and Tb (typ_rcd Db))〉

| trf_local_defs_consr Ga Gb Goa Gob ea eb Ta Tb Da Db dsl dsra dsrb:
    〈Ga§§Goa⁏ea ⊢ dsra ∶ Da〉 ∼(trf_local_def Cond TL)∼> 〈Gb§§Gob⁏eb ⊢ dsrb ∶ Db〉 ->
    Ga §§ Goa⁏ea ⊢ dsl ∶ Ta ->
    Gb §§ Gob⁏eb ⊢ dsl ∶ Tb ->
    defs_hasnt dsl (label_of dsra) ->
    defs_hasnt dsl (label_of dsrb) ->
    〈Ga §§ Goa⁏ea ⊢ (defs_cons dsl dsra) ∶ (typ_and Ta (typ_rcd Da))〉 ∼(Cond TrfContextObjTy typ defs)∼∼(trf_local_defs Cond TL)∼> 〈Gb §§ Gob⁏eb ⊢ (defs_cons dsl dsrb) ∶ (typ_and Tb (typ_rcd Db))〉
.

Scheme trf_local_trm_mut    := Induction for trf_local_trm Sort Prop
with   trf_local_lit_mut    := Induction for trf_local_lit Sort Prop
with   trf_local_def_mut    := Induction for trf_local_def Sort Prop
with   trf_local_defs_mut   := Induction for trf_local_defs Sort Prop.

Combined Scheme trf_local_mutind from trf_local_trm_mut, trf_local_lit_mut,
trf_local_def_mut, trf_local_defs_mut.

Inductive trf_local_idtyp_trm (TL: TermTransform): TermTransform :=

| trf_local_idtyp_trm_local G e T ta tb S:
    〈G⁏e ⊢ ta ∶ T〉 ∼TL∼> 〈G⁏e ⊢ tb ∶ T〉 ->
    G ⁏ e ⊢ T <: S ->
    〈G⁏e ⊢ ta ∶ S〉 ∼(trf_local_idtyp_trm TL)∼> 〈G⁏e ⊢ tb ∶ S〉

| trf_local_idtyp_trm_letl G e tla tlb T Tl tr L S:
    〈G⁏e ⊢ tla ∶ Tl〉 ∼(trf_local_idtyp_trm TL)∼> 〈G⁏e ⊢ tlb ∶ Tl〉 ->
    (forall x, x \notin L -> (G § x / v_let ~ Tl) ⁏ e ⊢ (open x tr) ∶ T) ->
    G ⁏ e ⊢ T <: S ->
    〈G⁏e ⊢ (trm_let tla tr) ∶ S〉 ∼(trf_local_idtyp_trm TL)∼> 〈G⁏e ⊢ (trm_let tlb tr) ∶ S〉

| trf_local_idtyp_trm_letr G e tl T Tl tra trb L S:
    (forall x, x \notin L ->
      〈G § x / v_let ~ Tl⁏e ⊢ (open x tra) ∶ T〉 ∼(trf_local_idtyp_trm TL)∼> 〈G § x / v_let ~ Tl⁏e ⊢ (open x trb) ∶ T〉
    ) ->
    G ⁏ e ⊢ tl ∶ Tl ->
    G ⁏ e ⊢ T <: S ->
    〈G⁏e ⊢ (trm_let tl tra) ∶ S〉 ∼(trf_local_idtyp_trm TL)∼> 〈G⁏e ⊢ (trm_let tl trb) ∶ S〉

| trf_local_idtyp_trm_litl G e tla tlb T Tl tr L S:
    〈G⁏e ⊢ tla ∶ Tl〉 ∼(trf_local_idtyp_lit TL)∼> 〈G⁏e ⊢ tlb ∶ Tl〉 ->
    (forall x, x \notin L ->
      (G § x / v_let ~ Tl) ⁏ e ⊢ (open x tr) ∶ T
    ) ->
    G ⁏ e ⊢ T <: S ->
    〈G⁏e ⊢ (trm_lit tla tr) ∶ S〉 ∼(trf_local_idtyp_trm TL)∼> 〈G⁏e ⊢ (trm_lit tlb tr) ∶ S〉

| trf_local_idtyp_trm_litr G e tl T Tl tra trb L S:
    (forall x, x \notin L ->
      〈G § x / v_let ~ Tl⁏e ⊢ (open x tra) ∶ T〉 ∼(trf_local_idtyp_trm TL)∼> 〈G § x / v_let ~ Tl⁏e ⊢ (open x trb) ∶ T〉
    ) ->
    G ⁏ e ⊢ tl ∶ Tl ->
    G ⁏ e ⊢ T <: S ->
    〈G⁏e ⊢ (trm_lit tl tra) ∶ S〉 ∼(trf_local_idtyp_trm TL)∼> 〈G⁏e ⊢ (trm_lit tl trb) ∶ S〉

with trf_local_idtyp_lit (TL: TermTransform): LitTransform :=

| trf_local_idtyp_lit_fun G e T U ta tb L:
    mode_has_fun typing_mode ->
    (forall x, x \notin L ->
      〈G § x / v_par ~ T⁏e ⊢ (open x ta) ∶ (open x U)〉 ∼(trf_local_idtyp_trm TL)∼> 〈G § x / v_par ~ T⁏e ⊢ (open x tb) ∶ (open x U)〉
    ) ->
    〈G⁏e ⊢ (lit_fun T ta) ∶ (typ_fun T U)〉 ∼(trf_local_idtyp_lit TL)∼> 〈G⁏e ⊢ (lit_fun T tb) ∶ (typ_fun T U)〉

| trf_local_idtyp_lit_obj G e T dsa dsb L:
    (forall x, x \notin L ->
      〈G§§(objctx_lit x T)⁏e ⊢ (open x dsa) ∶ (open x T)〉 ∼(trf_local_idtyp_defs TL)∼> 〈G§§(objctx_lit x T)⁏e ⊢ (open x dsb) ∶ (open x T)〉
    ) ->
    typ_indep_b 0 T ->
    〈G⁏e ⊢ (lit_obj T dsa) ∶ (typ_objlit typing_mode T)〉 ∼(trf_local_idtyp_lit TL)∼> 〈G⁏e ⊢ (lit_obj T dsb) ∶ (typ_objlit typing_mode T)〉

with trf_local_idtyp_def (TL: TermTransform): DefTransform :=

| trf_local_idtyp_def_met G Go e T TC TZ m ta tb L:
    ( forall xz, xz \notin L ->
      forall xc, xc <> xz -> xc \notin L ->
      〈(ctx_obj_met typing_mode G Go xz TZ xc TC)⁏e ⊢ (open_met xz xc ta) ∶ (open_met xz xc T)〉 ∼(trf_local_idtyp_trm TL)∼> 〈(ctx_obj_met typing_mode G Go xz TZ xc TC)⁏e ⊢ (open_met xz xc tb) ∶ (open_met xz xc T)〉
    ) ->
    〈G §§ Go⁏e ⊢ (def_met m ta) ∶ (dec_met m TC TZ T)〉 ∼(trf_local_idtyp_def TL)∼> 〈G §§ Go⁏e ⊢ (def_met m tb) ∶ (dec_met m TC TZ T)〉

with trf_local_idtyp_defs (TL: TermTransform): DefsTransform :=

| trf_local_idtyp_defs_one G Go e D dsla dslb:
    〈G §§ Go⁏e ⊢ dsla ∶ D〉 ∼(trf_local_idtyp_def TL)∼> 〈G §§ Go⁏e ⊢ dslb ∶ D〉 ->
    〈G §§ Go⁏e ⊢ (defs_cons defs_nil dsla) ∶ typ_rcd D〉 ∼(trf_local_idtyp_defs TL)∼> 〈G §§ Go⁏e ⊢ (defs_cons defs_nil dslb) ∶ typ_rcd D〉

| trf_local_idtyp_defs_consl G Go e T D dsla dslb dsr:
    〈G §§ Go⁏e ⊢ dsla ∶ T〉 ∼(trf_local_idtyp_defs TL)∼> 〈G §§ Go⁏e ⊢ dslb ∶ T〉 ->
    G §§ Go⁏e ⊢ dsr ∶d D ->
    defs_hasnt dsla (label_of dsr) ->
    defs_hasnt dslb (label_of dsr) ->
    〈G §§ Go⁏e ⊢ (defs_cons dsla dsr) ∶ (typ_and T (typ_rcd D))〉 ∼(trf_local_idtyp_defs TL)∼> 〈G §§ Go⁏e ⊢ (defs_cons dslb dsr) ∶ (typ_and T (typ_rcd D))〉

| trf_local_idtyp_defs_consr G Go e T D dsl dsra dsrb:
    〈G§§Go⁏e ⊢ dsra ∶ D〉 ∼(trf_local_idtyp_def TL)∼> 〈G§§Go⁏e ⊢ dsrb ∶ D〉 ->
    G §§ Go⁏e ⊢ dsl ∶ T ->
    defs_hasnt dsl (label_of dsra) ->
    defs_hasnt dsl (label_of dsrb) ->
    〈G §§ Go⁏e ⊢ (defs_cons dsl dsra) ∶ (typ_and T (typ_rcd D))〉 ∼(trf_local_idtyp_defs TL)∼> 〈G §§ Go⁏e ⊢ (defs_cons dsl dsrb) ∶ (typ_and T (typ_rcd D))〉
.

Scheme trf_local_idtyp_trm_mut    := Induction for trf_local_idtyp_trm Sort Prop
with   trf_local_idtyp_lit_mut    := Induction for trf_local_idtyp_lit Sort Prop
with   trf_local_idtyp_def_mut    := Induction for trf_local_idtyp_def Sort Prop
with   trf_local_idtyp_defs_mut   := Induction for trf_local_idtyp_defs Sort Prop.

Combined Scheme trf_local_idtyp_mutind from trf_local_idtyp_trm_mut, trf_local_idtyp_lit_mut,
trf_local_idtyp_def_mut, trf_local_idtyp_defs_mut.

End WithTypingMode.
