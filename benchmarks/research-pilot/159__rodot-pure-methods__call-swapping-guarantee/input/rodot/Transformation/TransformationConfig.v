Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Require Import Context Equivalence Indep GeneralTyping.

Require Import Transformation TransformationTerm TransformationLifting Weakening EWeakening Substitution.

Require Import ConfigTyping TFree TFreeTyping HeapCorrespondence InertContext ConfigTypingAccessories.

Require Import TypedOperationalSemantics OperationalSemantics ConfigVarkinds EnvCorrespondence SealClosed.

Require Import Sealing.

Definition TransformHeap := Transform renv ctx heap.

Definition TransformItem := Transform TrfContextTy var item.

Definition TransformStack := Transform TrfContextTy (typ*typ) stack.

Definition TransformConfig := Transform ctx typ config.

Section WithTypingMode.

Context (typing_mode: Mode).

Definition TransformCondConfTyped (TEa: TypedElement ctx typ config) :=
  match TEa with
    〈G ⊢ C ∶ T〉 => ty_config G C T
  end.

Definition TransformCondHeapCorr (TEa: TypedElement renv ctx heap) :=
  match TEa with
    〈e ⊢ Si ∶ G〉 =>
      heap_correspond_accessories G e Si ->
      heap_correspond G e Si
  end.

Definition TransformCondStackTyped (TEa: TypedElement TrfContextTy (typ*typ) stack) :=
  match TEa with
    〈G⁏e ⊢ fs ∶ (Tt, T)〉 => ty_stack G e Tt fs T
  end.

Inductive trf_focus_conf (Cond: LiftCond) (TL: TermTransform): TransformConfig:=
  trf_focus_conf_focus Ga Gb ea eb fs S ta tb Tta Ttb Tsa Tsb Ta Tb Lva Lvb:
    ty_config_accessories Ga ea fs S ta Ta Lva ->
    ty_config_accessories Gb eb fs S tb Tb Lvb ->
    heap_correspond Ga ea S ->
    heap_correspond Gb eb S ->
    ty_stack Ga ea Tsa fs Ta ->
    ty_stack Gb eb Tsb fs Tb ->
    〈Ga⁏ea ⊢ ta ∶ Tta〉 ∼TL∼> 〈Gb⁏eb ⊢ tb ∶ Ttb〉 ->
    Ga ⁏ ea ⊢ Tta <: Tsa ->
    Gb ⁏ eb ⊢ Ttb <: Tsb ->
    〈Ga ⊢ ta; fs; S; ea; Lva ∶ Ta〉 ∼(Cond _ _ _)∼∼(trf_focus_conf Cond TL)∼> 〈Gb ⊢ tb; fs; S; eb; Lvb ∶ Tb〉.

Inductive trf_focus_idtyp_conf (TL: TermTransform): TransformConfig:=

  trf_focus_idtyp_conf_focus G e fs S ta tb Tt Ts T Lva Lvb:
    ty_config_accessories G e fs S ta T Lva ->
    ty_config_accessories G e fs S tb T Lvb ->
    heap_correspond G e S ->
    ty_stack G e Ts fs T ->
    〈G⁏e ⊢ ta ∶ Tt〉 ∼TL∼> 〈G⁏e ⊢ tb ∶ Tt〉 ->
    G ⁏ e ⊢ Tt <: Ts ->
    〈G ⊢ ta; fs; S; e; Lva ∶ T〉 ∼(trf_focus_idtyp_conf TL)∼> 〈G ⊢ tb; fs; S; e; Lvb ∶ T〉.

Inductive trf_lift_stack (Cond: LiftCond) (TL: TermTransform): TransformStack :=
| trf_lift_stack_e Ga ea Gb eb fs ta tb T1a T1b T2a T2b T3a T3b L:
    (forall x, x \notin L ->
      〈Ga § x / v_let ~ T1a⁏ea ⊢ (open x ta) ∶ T2a〉 ∼(trf_local_trm typing_mode Cond TL)∼> 〈Gb § x / v_let ~ T1b⁏eb ⊢ (open x tb) ∶ T2b〉
    ) ->
    ty_stack Ga ea T2a fs T3a ->
    ty_stack Gb eb T2b fs T3b ->
    〈Ga⁏ea ⊢ (stack_cons (frame_let ta) fs) ∶ (T1a, T3a)〉 ∼(Cond TrfContextTy _ _)∼∼(trf_lift_stack Cond TL)∼> 〈Gb⁏eb ⊢ (stack_cons (frame_let tb) fs) ∶ (T1b, T3b)〉
| trf_lift_stack_n Ga ea Gb eb fsa fsb t T1a T1b T2a T2b T3a T3b L:
    〈Ga⁏ea ⊢ fsa ∶ (T2a,T3a)〉 ∼(trf_lift_stack Cond TL)∼> 〈Gb⁏eb ⊢ fsb ∶ (T2b,T3b)〉 ->
    (forall x, x \notin L ->
      Ga § x / v_let ~ T1a ⁏ea ⊢ open x t ∶ T2a
    ) ->
    (forall x, x \notin L ->
      Gb § x / v_let ~ T1b ⁏eb ⊢ open x t ∶ T2b
    ) ->
    〈Ga⁏ea ⊢ (stack_cons (frame_let t) fsa) ∶ (T1a,T3a)〉 ∼(Cond TrfContextTy _ _)∼∼(trf_lift_stack Cond TL)∼> 〈Gb⁏eb ⊢ (stack_cons (frame_let t) fsb) ∶ (T1b,T3b)〉.

Inductive trf_lift_idtyp_stack (TL: TermTransform): TransformStack :=
| trf_lift_idtyp_stack_e Ga ea fs ta tb T1a T2a T3a L:
    (forall x, x \notin L ->
      〈Ga § x / v_let ~ T1a⁏ea ⊢ (open x ta) ∶ T2a〉 ∼(trf_local_idtyp_trm typing_mode TL)∼> 〈Ga § x / v_let ~ T1a⁏ea ⊢ (open x tb) ∶ T2a〉
    ) ->
    ty_stack Ga ea T2a fs T3a ->
    〈Ga⁏ea ⊢ (stack_cons (frame_let ta) fs) ∶ (T1a, T3a)〉 ∼(trf_lift_idtyp_stack TL)∼> 〈Ga⁏ea ⊢ (stack_cons (frame_let tb) fs) ∶ (T1a, T3a)〉
| trf_lift_idtyp_stack_n Ga ea fsa fsb t T1a T2a T3a L:
    〈Ga⁏ea ⊢ fsa ∶ (T2a,T3a)〉 ∼(trf_lift_idtyp_stack TL)∼> 〈Ga⁏ea ⊢ fsb ∶ (T2a,T3a)〉 ->
    (forall x, x \notin L ->
      Ga § x / v_let ~ T1a ⁏ea ⊢ open x t ∶ T2a
    ) ->
    〈Ga⁏ea ⊢ (stack_cons (frame_let t) fsa) ∶ (T1a,T3a)〉 ∼(trf_lift_idtyp_stack TL)∼> 〈Ga⁏ea ⊢ (stack_cons (frame_let t) fsb) ∶ (T1a,T3a)〉.

Inductive trf_lift_item (Cond: LiftCond) (TL: TermTransform): TransformItem :=
| trf_lift_item_fun Ga Gb ea eb y ta tb Sa Sb Ta Tb L:
    mode_has_fun' typing_mode = true ->
    ctx_binds y (typ_fun Sa Ta) Ga ->
    ctx_binds y (typ_fun Sb Tb) Gb ->
    (forall x, x \notin L ->
       〈(Ga § x / v_par ~ Sa) ⁏ ea ⊢  (open x ta) ∶ (open x Ta)〉 ∼(trf_local_trm typing_mode Cond TL)∼> 〈(Gb § x / v_par ~ Sb) ⁏ eb ⊢ (open x tb) ∶ (open x Tb)〉
    ) ->
    all_tfree_k Ga ta v_ref ->
    all_tfree_k Gb tb v_ref ->
    〈Ga⁏ea ⊢ (item_fun ta) ∶ y〉 ∼(Cond TrfContextTy _ _)∼∼(trf_lift_item Cond TL)∼> 〈Gb⁏eb ⊢ (item_fun tb) ∶ y〉
| trf_lift_item_obj Ga Gb ea eb y dsa dsb Ua Ub Sa Sb:
    ctx_binds y (typ_objref Ua Sa) Ga ->
    ctx_binds y (typ_objref Ub Sb) Gb ->
    〈Ga§§(objctx_heap y Ua)⁏ea ⊢ dsa ∶ (open y Ua)〉 ∼(trf_local_defs typing_mode Cond TL )∼> 〈Gb§§(objctx_heap y Ub)⁏eb ⊢ dsb ∶ (open y Ub)〉 ->
    defs_varkinds Ga dsa ->
    defs_varkinds Gb dsb ->
    〈Ga⁏ea ⊢ (item_obj dsa) ∶ y〉 ∼(Cond TrfContextTy _ _)∼∼(trf_lift_item Cond TL)∼> 〈Gb⁏eb ⊢ (item_obj dsb) ∶ y〉.

Inductive trf_lift_idtyp_item (TL: TermTransform): TransformItem :=
| trf_lift_idtyp_item_fun G e y ta tb S T L:
    mode_has_fun' typing_mode = true ->
    ctx_binds y (typ_fun S T) G ->
    (forall x, x \notin L ->
       〈(G § x / v_par ~ S) ⁏ e ⊢  (open x ta) ∶ (open x T)〉 ∼(trf_local_idtyp_trm typing_mode TL)∼> 〈(G § x / v_par ~ S) ⁏ e ⊢ (open x tb) ∶ (open x T)〉
    ) ->
    all_tfree_k G ta v_ref ->
    all_tfree_k G tb v_ref ->
    〈G⁏e ⊢ (item_fun ta) ∶ y〉 ∼(trf_lift_idtyp_item TL)∼> 〈G⁏e ⊢ (item_fun tb) ∶ y〉
| trf_lift_idtyp_item_obj G e y dsa dsb U S:
    ctx_binds y (typ_objref U S) G ->
    〈G§§(objctx_heap y U)⁏e ⊢ dsa ∶ (open y U)〉 ∼(trf_local_idtyp_defs typing_mode TL )∼> 〈G§§(objctx_heap y U)⁏e ⊢ dsb ∶ (open y U)〉 ->
    defs_varkinds G dsa ->
    defs_varkinds G dsb ->
    〈G⁏e ⊢ (item_obj dsa) ∶ y〉 ∼(trf_lift_idtyp_item TL)∼> 〈G⁏e ⊢ (item_obj dsb) ∶ y〉.

Inductive trf_lift_heap (Cond: LiftCond) (TL: TermTransform): TransformHeap :=
| trf_lift_heap_e Ga Gb ea eb ita itb S x:

    (forall y, y \in dom S ->
      ty_item_s typing_mode Ga ea S y
    ) ->
    (forall y, y \in dom S ->
      ty_item_s typing_mode Gb eb S y
    ) ->

    〈Ga⁏ea ⊢ ita ∶ x〉 ∼(trf_lift_item Cond TL)∼> 〈Gb⁏eb ⊢ itb ∶ x〉 ->
    〈ea ⊢ (S & x ~ ita) ∶ Ga〉 ∼(Cond _ _ _)∼∼(trf_lift_heap Cond TL)∼> 〈eb ⊢ (S & x ~ itb) ∶ Gb〉
| trf_lift_heap_n Ga Gb ea eb Sa Sb x it:
    〈ea ⊢ Sa ∶ Ga〉 ∼(trf_lift_heap Cond TL)∼> 〈eb ⊢ Sb ∶ Gb〉 ->
    ty_item_s typing_mode Ga ea (x ~ it) x ->
    ty_item_s typing_mode Gb eb (x ~ it) x ->
    〈ea ⊢ (Sa & x ~ it) ∶ Ga〉 ∼(Cond _ _ _)∼∼(trf_lift_heap Cond TL)∼> 〈eb ⊢ (Sb & x ~ it) ∶ Gb〉.

Inductive trf_lift_idtyp_heap (TL: TermTransform): TransformHeap :=
| trf_lift_idtyp_heap_e G e ita itb S x:

    (forall y, y \in dom S ->
      ty_item_s typing_mode G e S y
    ) ->

    〈G⁏e ⊢ ita ∶ x〉 ∼(trf_lift_idtyp_item TL)∼> 〈G⁏e ⊢ itb ∶ x〉 ->
    〈e ⊢ (S & x ~ ita) ∶ G〉 ∼(trf_lift_idtyp_heap TL)∼> 〈e ⊢ (S & x ~ itb) ∶ G〉
| trf_lift_idtyp_heap_n G e Sa Sb x it:
    〈e ⊢ Sa ∶ G〉 ∼(trf_lift_idtyp_heap TL)∼> 〈e ⊢ Sb ∶ G〉 ->
    ty_item_s typing_mode G e (x ~ it) x ->
    〈e ⊢ (Sa & x ~ it) ∶ G〉 ∼(trf_lift_idtyp_heap TL)∼> 〈e ⊢ (Sb & x ~ it) ∶ G〉.

Inductive trf_lift_conf (Cond: LiftCond) (TL: TermTransform): TransformConfig :=

| trf_lift_conf_focus Ga Gb Ta Tb Ca Cb:
    〈Ga ⊢ Ca ∶ Ta〉 ∼(trf_focus_conf Cond (trf_local_trm typing_mode Cond TL))∼> 〈Gb ⊢ Cb ∶ Tb〉 ->
    〈Ga ⊢ Ca ∶ Ta〉 ∼(Cond _ _ _)∼∼(trf_lift_conf Cond TL)∼> 〈Gb ⊢ Cb ∶ Tb〉

| trf_lift_conf_heap Ga Gb e fs Sa Sb t Tta Ttb Ta Tb Lva Lvb:
    ty_config_accessories Ga e fs Sa t Ta Lva ->
    ty_config_accessories Gb e fs Sb t Tb Lvb ->
    heap_correspond_accessories Ga e Sa ->
    heap_correspond_accessories Gb e Sb ->
    〈e ⊢ Sa ∶ Ga〉 ∼(trf_lift_heap Cond TL)∼> 〈e ⊢ Sb ∶ Gb〉 ->
    ty_stack Ga e Tta fs Ta ->
    ty_stack Gb e Ttb fs Tb ->
    Ga⁏e ⊢ t ∶ Tta ->
    Gb⁏e ⊢ t ∶ Ttb ->
    〈Ga ⊢ (t; fs; Sa; e; Lva) ∶ Ta〉 ∼(Cond _ _ _)∼∼(trf_lift_conf Cond TL)∼> 〈Gb ⊢ (t; fs; Sb; e; Lvb) ∶ Tb〉

| trf_lift_conf_stack Ga Gb e fsa fsb S t Tta Ttb Ta Tb Lva Lvb:
    ty_config_accessories Ga e fsa S t Ta Lva ->
    ty_config_accessories Gb e fsb S t Tb Lvb ->
    heap_correspond Ga e S ->
    heap_correspond Gb e S ->
    〈Ga⁏e ⊢ fsa ∶ (Tta,Ta)〉 ∼(trf_lift_stack Cond TL)∼> 〈Gb⁏e ⊢ fsb ∶ (Ttb,Tb)〉 ->
    Ga⁏e ⊢ t ∶ Tta ->
    Gb⁏e ⊢ t ∶ Ttb ->
    〈Ga ⊢ (t; fsa; S; e; Lva) ∶ Ta〉 ∼(Cond _ _ _)∼∼(trf_lift_conf Cond TL)∼> 〈Gb ⊢ (t; fsb; S; e; Lvb) ∶ Tb〉.

Inductive trf_lift_idtyp_conf (TL: TermTransform): TransformConfig :=

| trf_lift_idtyp_conf_focus G T Ca Cb:
    〈G ⊢ Ca ∶ T〉 ∼(trf_focus_idtyp_conf (trf_local_idtyp_trm typing_mode TL))∼> 〈G ⊢ Cb ∶ T〉 ->
    〈G ⊢ Ca ∶ T〉 ∼(trf_lift_idtyp_conf TL)∼> 〈G ⊢ Cb ∶ T〉

| trf_lift_idtyp_conf_heap G e fs Sa Sb t Tt T Lva Lvb:
    ty_config_accessories G e fs Sa t T Lva ->
    ty_config_accessories G e fs Sb t T Lvb ->
    heap_correspond_accessories G e Sa ->
    heap_correspond_accessories G e Sb ->
    〈e ⊢ Sa ∶ G〉 ∼(trf_lift_idtyp_heap TL)∼> 〈e ⊢ Sb ∶ G〉 ->
    ty_stack G e Tt fs T ->
    G⁏e ⊢ t ∶ Tt ->
    〈G ⊢ (t; fs; Sa; e; Lva) ∶ T〉 ∼(trf_lift_idtyp_conf TL)∼> 〈G ⊢ (t; fs; Sb; e; Lvb) ∶ T〉

| trf_lift_idtyp_conf_stack G e fsa fsb S t Tt T Lva Lvb:
    ty_config_accessories G e fsa S t T Lva ->
    ty_config_accessories G e fsb S t T Lvb ->
    heap_correspond G e S ->
    〈G⁏e ⊢ fsa ∶ (Tt,T)〉 ∼(trf_lift_idtyp_stack TL)∼> 〈G⁏e ⊢ fsb ∶ (Tt,T)〉 ->
    G⁏e ⊢ t ∶ Tt ->
    〈G ⊢ (t; fsa; S; e; Lva) ∶ T〉 ∼(trf_lift_idtyp_conf TL)∼> 〈G ⊢ (t; fsb; S; e; Lvb) ∶ T〉.

Class TransformConfigReducesTo1(trf1 trf2: TransformConfig) :=
  trf_config_reduces_to_1 Ga1 Gb1 Ta Tb Ca1 Cb1 Ga2 Gb2 Ca2 Cb2 :
    〈Ga1 ⊢ Ca1 ∶ Ta〉 ∼trf1∼> 〈Gb1 ⊢ Cb1 ∶ Tb〉 ->
    Ga1 ⊢ Ca1 ∶ Ta ↦ Ga2 ⊢ Ca2 ->
    Gb1 ⊢ Cb1 ∶ Tb ↦ Gb2 ⊢ Cb2 ->
    〈Ga2 ⊢ Ca2 ∶ Ta〉 ∼trf2∼> 〈Gb2 ⊢ Cb2 ∶ Tb〉.

Class TransformConfigReducesTo(trf1 trf2: TransformConfig) :=
  trf_config_reduces_to Ga1 Gb1 Ta Tb Ca1 Cb1 :
    〈Ga1 ⊢ Ca1 ∶ Ta〉 ∼trf1∼> 〈Gb1 ⊢ Cb1 ∶ Tb〉 ->
    exists n1 n2 Ga2 Gb2 Ca2 Cb2,
    Ga1 ⊢ Ca1 ∶ Ta ⊣ n1 ↦* Ga2 ⊢ Ca2 /\
    Gb1 ⊢ Cb1 ∶ Tb ⊣ n2 ↦* Gb2 ⊢ Cb2 /\
    〈Ga2 ⊢ Ca2 ∶ Ta〉 ∼trf2∼> 〈Gb2 ⊢ Cb2 ∶ Tb〉.

Class TransformConfigReducesToShort(trf1 trf2: TransformConfig) :=
  trf_config_reduces_to_short Ga1 Gb1 Ta Tb Ca1 Cb1 :
    〈Ga1 ⊢ Ca1 ∶ Ta〉 ∼trf1∼> 〈Gb1 ⊢ Cb1 ∶ Tb〉 ->
    exists n1 n2 Ga2 Gb2 Ca2 Cb2,
    n2 <= n1 /\
    Ga1 ⊢ Ca1 ∶ Ta ⊣ n1 ↦* Ga2 ⊢ Ca2 /\
    Gb1 ⊢ Cb1 ∶ Tb ⊣ n2 ↦* Gb2 ⊢ Cb2 /\
    〈Ga2 ⊢ Ca2 ∶ Ta〉 ∼trf2∼> 〈Gb2 ⊢ Cb2 ∶ Tb〉.

Class TransformConfigReducesToShortIfTerminates(trf1 trf2: TransformConfig) :=
  trf_config_reduces_to_short_if_terminates Ga1 Gb1 Ta Tb Ca1 Cb1 :
    〈Ga1 ⊢ Ca1 ∶ Ta〉 ∼trf1∼> 〈Gb1 ⊢ Cb1 ∶ Tb〉 ->
    config_terminates Ca1 ->
    exists n1 n2 Ga2 Gb2 Ca2 Cb2,
    n2 <= n1 /\
    Ga1 ⊢ Ca1 ∶ Ta ⊣ n1 ↦* Ga2 ⊢ Ca2 /\
    Gb1 ⊢ Cb1 ∶ Tb ⊣ n2 ↦* Gb2 ⊢ Cb2 /\
    〈Ga2 ⊢ Ca2 ∶ Ta〉 ∼trf2∼> 〈Gb2 ⊢ Cb2 ∶ Tb〉.

Definition TransformCondTerminates (TEa: TypedElement ctx typ config) :=
  match TEa with
    〈_ ⊢ C ∶ _〉 => config_terminates C
  end.

Definition TransformIsAnswer (TEa: TypedElement ctx typ config) :=
  match TEa with
    〈_ ⊢ C ∶ _〉 => answer C
  end.

End WithTypingMode.
