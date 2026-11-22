Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping InertTightSubtyping GeneralToTight TightTyping InvertibleTyping RecordTypes InertContext PreciseTyping OperationalSemantics Substitution Weakening HeapCorrespondence HeapUpdate CanonicalForms Narrowing EnvCorrespondence EWeakening ConfigTyping ConfigVarkinds TFree Deref.

Require Import Logic.Classical_Prop Logic.Classical_Pred_Type.

Notation "x @@ n -> L" := (forall (n:x), L)  (only parsing, at level 99, L at level 200, n at level 98).

Reserved Notation "F1 ⊢ C1 ∶ T1 ↦ F2 ⊢ C2"
         (at level 40, C1 at level 59, T1 at level 39,
          F2 at level 39, C2 at level 39).

Notation ref_read_term_type C Tstrip w1 Tcap :=
  (typ_and Tstrip (typ_cap_adapt C w1 Tcap)) (only parsing).

Notation ref_read_ref_type C R1 Tstrip w1 Tcap :=
  (typ_objref R1 (typ_cap_marker C (typ_or Tcap (typ_sel (avar_f w1) (typ_label_refcap C) (avar_b 0))))) (only parsing).

Notation rodot_read_term_type Tstrip w1 Tcap :=
  (ref_read_term_type typ_refcap_mutability Tstrip w1 Tcap) (only parsing).

Notation rodot_read_ref_type R1 Tstrip w1 Tcap :=
  (ref_read_ref_type typ_refcap_mutability R1 Tstrip w1 Tcap) (only parsing).

Notation typ_read_ref typing_mode G e fs T0 T2 R1 R2 w1 T3 Tcap := (
  match (mode_viewpoint_adaptation' typing_mode) with
  | mode_viewpoint_adaptation_same =>

      T2 = (typ_objref R1 R2)
  | mode_viewpoint_adapt_mutability =>
      exists Tstrip Tcap,
        G ⁏ e ⊢ T3 ∶icp Tstrip /\
        G ⁏ e ⊢ T3 ∶cpb ⟦ typ_refcap_mutability ⟧ Tcap /\
        ty_stack G e (rodot_read_term_type Tstrip w1 Tcap) fs T0 /\

        T2 = (rodot_read_ref_type R1 Tstrip w1 Tcap)
  end) (only parsing).

Notation inert_G_for_obj_loc typing_mode G w y T:= (inert_G_for_item G w y (typ_objref_loc typing_mode T)).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive typed_red : ctx -> config -> typ -> ctx -> config -> Prop :=












| tred_read_obj : forall (F F' : ctx) (w1 w2 y1 y2 : var) (a : fld_label)
                  (T0 T2 T3 T4 R1 R2 : typ) (yd : defs) (t0 : trm)
                  (fs : stack) (e :renv) (Sigma : heap) Lv,
    inert F @@ Hin ->
    fresh_in_config (w2 :: nil)%list (t0 ; fs ; Sigma ; e; Lv) @@ Hfrw2 ->
    (w2 \notin ctx_fv F /\ w2 \notin fv T2) @@ Hfrfvw2 ->
    t0 = trm_read (avar_f w1) a ->

    ty_config F (t0 ; fs ; Sigma ; e; Lv) T0 @@ Htyc ->
    F⁏e ⊢ w1 ∶ typ_rcd (dec_fld a T4 T3) @@ Htypw1 ->
    binds w1 y1 e @@ Hbwye ->
    ctx_binds_k_after y2 v_loc (typ_objref R1 R2) F F' @@ Hby2G ->

    binds y1 (item_obj yd) Sigma @@ Hby1S ->
    defs_has yd (def_fld a (avar_f y2)) @@ Hhas ->
    typ_read_ref typing_mode F e fs T0 T2 R1 R2 w1 T3 Tcap @@ Htcor ->
    nothing_fresh_in_config T2 (t0 ; fs ; Sigma ; e ; Lv) @@ Hnfr ->
    closed T2 @@ HclT2 ->
    F ⊢ (t0 ; fs ; Sigma ; e ; Lv) ∶ T0 ↦
      F § w2 / v_ref ~ T2 ⊢ (trm_var (avar_f w2) ; fs ; Sigma ; e & w2 ~ y2; fv_config (t0 ; fs ; Sigma ; e ; Lv))


| tred_read_fun : forall (F F' : ctx) (w1 w2 y1 y2 : var) (a : fld_label)
                  (T0 T3 T4 S T : typ) (yd : defs) (t0 : trm)
                  (fs : stack) (e :renv) (Sigma : heap) Lv,
    mode_has_fun typing_mode @@ Hmode ->
    inert F @@ Hin ->
    fresh_in_config (w2 :: nil)%list (t0 ; fs ; Sigma ; e ; Lv) @@ Hfrw2 ->
    t0 = trm_read (avar_f w1) a ->
    ty_config F (t0 ; fs ; Sigma ; e; Lv) T0 @@ Htyc ->
    F ⁏ e ⊢ w1 ∶ typ_rcd (dec_fld a T4 T3) @@ Htypw1 ->
    binds w1 y1 e @@ Hbwye ->
    ctx_binds_k_after y2 v_loc (typ_fun S T) F F' @@ Hbk ->
    binds y1 (item_obj yd) Sigma @@ Hby1S ->
    defs_has yd (def_fld a (avar_f y2)) @@ Hhas ->
    F ⊢ (t0 ; fs ; Sigma ; e ; Lv) ∶ T0 ↦ F § w2 / v_ref ~ (typ_fun S T)
      ⊢ (trm_var (avar_f w2) ; fs ; Sigma ; e & w2 ~ y2; fv_config (t0 ; fs ; Sigma ; e ; Lv))










| tred_write : forall (F : ctx) (w1 w3 y1 y3 : var) (a : fld_label)
               (T0  : typ) (t0 : trm)
               (fs : stack) (e : renv) (Sigma1 Sigma2 : heap) Lv,
    inert F @@ Hin ->
    t0 = trm_write (avar_f w1) a (avar_f w3) ->
    ty_config F (t0 ; fs ; Sigma1 ; e; Lv) T0 @@ Htyc ->
    binds w1 y1 e @@ Hbw1y1e ->
    binds w3 y3 e @@ Hbw3y3e ->
    heap_update Sigma1 y1 a y3 Sigma2 @@ Hupd ->
    F ⊢ (t0 ; fs ; Sigma1 ; e ; Lv) ∶ T0 ↦
      F ⊢ (trm_var (avar_f w3) ; fs ; Sigma2 ; e; fv_config (t0 ; fs ; Sigma1 ; e ; Lv))








| tred_call : forall (F : ctx) (r w1 w2 y z: var) (m : met_label)
                   (T0: typ) (yd : defs) (t t0 : trm)
                   (fs : stack) (e : renv) (Sigma : heap) Lv,
    inert F @@ Hin ->
    t0 = trm_call (avar_f w1) m (avar_f w2) ->
    ty_config F (t0 ; fs ; Sigma ; e; Lv) T0 @@ Htyc ->
    binds w1 y e @@ Hbw1ye ->

    binds y (item_obj yd) Sigma @@ HbyS ->
    defs_has yd (def_met m t) @@ Hhas ->
    F ⊢ (t0 ; fs ; Sigma ; e ; Lv) ∶ T0 ↦ F ⊢ (open_met w2 w1 t ; fs ; Sigma ; e; fv_config (t0 ; fs ; Sigma ; e ; Lv))


| tred_apply : forall (F : ctx) (x y z : var) (T0 : typ) (t t0 : trm)
                   (fs : stack) (e : renv) (Sigma : heap) Lv,
    mode_has_fun typing_mode @@ Hmode ->
    inert F @@ Hin ->
    t0 = trm_apply (avar_f x) (avar_f z) ->
    ty_config F (t0 ; fs ; Sigma ; e; Lv) T0 @@ Htyc ->
    binds x y e @@ Hbxye ->
    binds y (item_fun t) Sigma @@ HbyS ->
    F ⊢ (t0 ; fs ; Sigma ; e; Lv) ∶ T0 ↦ F ⊢ (open z t ; fs ; Sigma ; e; fv_config (t0 ; fs ; Sigma ; e; Lv))








| tred_let_obj : forall (F : ctx) (R : typ) (d : defs) (t t0 : trm) (w y : var)
                 (fs : stack) (e : renv) (Sigma : heap) (T0 : typ) Lv,
    inert F @@ Hin ->
    fresh_in_config (y :: w :: nil)%list (t0 ; fs ; Sigma ; e; Lv) @@ Hfr ->
    (y \notin ctx_fv F \u fv R) @@ Hfry ->
    (w \notin ctx_fv F \u fv R) @@ Hfrw ->
    t0 = (trm_lit (lit_obj R d) t) ->
    ty_config F (t0 ; fs ; Sigma ; e; Lv) T0 @@ Htyc ->
    F ⊢ (t0 ; fs ; Sigma ; e ; Lv) ∶ T0 ↦
      (inert_G_for_obj_loc typing_mode F w y R) ⊢
      (open w t
            ; fs
            ; Sigma & y ~ (item_obj (deref_defs (e & w ~ y) (open w d)))
            ; e & w ~ y; fv_config (t0 ; fs ; Sigma ; e ; Lv))


| tred_let_fun : forall (F : ctx) (t0 t1 t2 : trm) (T A A1 T0 : typ) (w y : var)
                 (fs : stack) (e : renv) (Sigma : heap) (L : vars) Lv,
    mode_has_fun typing_mode @@ Hmode ->
    inert F @@ Hin ->
    fresh_in_config (y :: w :: nil)%list (t0 ; fs ; Sigma ; e; Lv) @@ Hfr ->
    y <> w @@ Hnyw ->
    (y \notin ctx_fv F \u fv A1) @@ Hfry ->
    (w \notin ctx_fv F \u fv A1) @@ Hfrw ->
    t0 = (trm_lit (lit_fun T t1) t2) ->
    F ⁏ e ⊢ lit_fun T t1 ∶ A1 ->
    (forall x : var,
        x \notin L -> F § x / v_let ~ A1 ⁏ e ⊢ open x t2 ∶ A) ->
    heap_correspond F e Sigma ->
    ty_stack F e A fs T0 @@ Htys ->
    all_tfree_k_stack F fs v_ref @@ Htfs ->
    all_tfree_k_trm F t0 v_ref @@Htft ->
    ty_config F (t0 ; fs ; Sigma ; e; Lv) T0 @@ Htyc ->
    nothing_fresh_in_config A1 (t0 ; fs ; Sigma ; e ; Lv) @@ Hnfr ->
    closed A1 @@ HclT2 ->
    F ⊢ (t0 ; fs ; Sigma ; e ; Lv) ∶ T0 ↦
      (F § y / v_loc ~ A1 § w / v_ref ~ A1) ⊢
      (open w t2 ; fs ; Sigma & y ~ item_fun t1 ; e & w ~ y; fv_config (t0 ; fs ; Sigma ; e ; Lv))







| tred_let_push : forall (F : ctx) (t0 t1 t2 : trm) (fs : stack)
                  (e : renv) (Sigma : heap) (T0 : typ) Lv,
    inert F @@ Hin ->
    t0 = (trm_let t1 t2) ->
    ty_config F (t0 ; fs ; Sigma ; e; Lv) T0 @@ Htyc ->
    F ⊢ (t0 ; fs ; Sigma ; e ; Lv) ∶ T0 ↦
      F ⊢ (t1 ; (stack_cons (frame_let t2) fs) ; Sigma ; e; fv_config (t0 ; fs ; Sigma ; e ; Lv))






| tred_let_var : forall (F : ctx) (w : var) (fs1 fs2 : stack) (t : trm)
                 (e : renv) (Sigma : heap) (T0 : typ) Lv,
    inert F @@ Hin ->

    ty_config F (trm_var (avar_f w) ; fs1 ; Sigma ; e; Lv) T0 @@ Htyc ->
    fs1 = (stack_cons (frame_let t) fs2) ->
    F ⊢ (trm_var (avar_f w) ; fs1 ; Sigma ; e ; Lv) ∶ T0 ↦
      F ⊢ ((open w t) ; fs2 ; Sigma ; e; fv_config (trm_var (avar_f w) ; fs1 ; Sigma ; e ; Lv))


where "F1 ⊢ C1 ∶ T1 ↦ F2 ⊢ C2" := (typed_red F1 C1 T1 F2 C2).

Reserved Notation "F1 ⊢ C1 ∶ T1 ⊣ n ↦* F2 ⊢ C2"
         (at level 40, C1 at level 59, T1 at level 39,
          n at level 41, F2 at level 39, C2 at level 39).

Inductive typed_red_closure :
  ctx -> config -> typ -> nat -> ctx -> config -> Prop :=

| typed_red_refl: forall (F : ctx) (C : config) (T : typ),
    F ⊢ C ∶ T ⊣0↦* F ⊢ C

| typed_red_step : forall (F1 F2 F3 : ctx) (C1 C2 C3 : config) (T : typ) (n : nat),
    F1 ⊢ C1 ∶ T ⊣n↦* F2 ⊢ C2 ->
    F2 ⊢ C2 ∶ T ↦ F3 ⊢ C3 ->
    F1 ⊢ C1 ∶ T ⊣(S n)↦* F3 ⊢ C3

where "F1 ⊢ C1 ∶ T1 ⊣ n ↦* F2 ⊢ C2" :=
        (typed_red_closure F1 C1 T1 n F2 C2).

End WithTypingMode.

Notation "F1 ⊢ C1 ∶ T1 ↦ F2 ⊢ C2" := (typed_red _ F1 C1 T1 F2 C2)
         (at level 40, C1 at level 59, T1 at level 39,
          F2 at level 39, C2 at level 39).

Notation "F1 ⊢ C1 ∶ T1 ⊣ n ↦* F2 ⊢ C2" :=
    (typed_red_closure _ F1 C1 T1 n F2 C2)
        (at level 40, C1 at level 59, T1 at level 39,
          n at level 41, F2 at level 39, C2 at level 39).
