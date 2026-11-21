Require Import Metalib.Metatheory.

From Stdlib Require Import List.

Definition varEI : Set := var.

Definition blame_label : Set := var.

Inductive modality : Set :=
 | mod_unsafe : modality
 | mod_safe : modality
 | mod_non_nullable : modality  .

Inductive label : Set :=
 | label_name (l:blame_label)
 | label_not_label (l:blame_label)  .

Inductive typ : Set :=
 | typ_null : typ
 | typ_mod_arrow (M:modality) (T:typ) (U:typ)  .

Inductive trm : Set :=
 | t_var_b (_:nat)
 | t_var_f (x:var)
 | t_null : trm
 | t_abs (T:typ) (t:trm)
 | t_app (s:trm) (t:trm)
 | t_app_safe (f:trm) (s:trm) (t:trm)
 | t_cast (s:trm) (V:typ) (p:label) (T:typ)  .

Inductive typI : Set :=
 | typI_null : typI
 | typI_unsafe_arrow (Ti:typI) (Ui:typI)  .

Inductive typE : Set :=
 | typE_null : typE
 | typE_nonnull_arrow (Te:typE) (Ue:typE)
 | typE_safe_arrow (Te:typE) (Ue:typE)  .

Inductive mode : Set :=
 | mode_explicit : mode
 | mode_implicit : mode  .

Inductive trmEI : Set :=
 | tei_var_b (_:nat)
 | tei_var_f (xei:varEI)
 | tei_null (m:mode)
 | tei_abs_exp (Te:typE) (tei:trmEI)
 | tei_abs_imp (Ti:typI) (sei:trmEI) (Ui:typI)
 | tei_app (sei:trmEI) (tei:trmEI) (m:mode)
 | tei_app_safe (sei:trmEI) (tei:trmEI) (uei:trmEI) (m:mode)
 | tei_cast_exp (sei:trmEI) (Ve:typE) (Te:typE)
 | tei_cast_imp (sei:trmEI) (Vi:typI) (p:label) (Ti:typI)
 | tei_import_exp (Te:typE) (tei:trmEI) (Ti:typI) (uei:trmEI)
 | tei_import_imp (Ti:typI) (tei:trmEI) (Te:typE) (uei:trmEI)  .

Definition ctxE : Set := list ( atom * typE ).

Definition ctxI : Set := list ( atom * typI ).

Fixpoint open_trmEI_wrt_trmEI_rec (k:nat) (tei_5:trmEI) (tei__6:trmEI) {struct tei__6}: trmEI :=
  match tei__6 with
  | (tei_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => tei_var_b nat
        | inleft (right _) => tei_5
        | inright _ => tei_var_b (nat - 1)
      end
  | (tei_var_f xei) => tei_var_f xei
  | (tei_null m) => tei_null m
  | (tei_abs_exp Te tei) => tei_abs_exp Te (open_trmEI_wrt_trmEI_rec (S k) tei_5 tei)
  | (tei_abs_imp Ti sei Ui) => tei_abs_imp Ti (open_trmEI_wrt_trmEI_rec (S k) tei_5 sei) Ui
  | (tei_app sei tei m) => tei_app (open_trmEI_wrt_trmEI_rec k tei_5 sei) (open_trmEI_wrt_trmEI_rec k tei_5 tei) m
  | (tei_app_safe sei tei uei m) => tei_app_safe (open_trmEI_wrt_trmEI_rec k tei_5 sei) (open_trmEI_wrt_trmEI_rec k tei_5 tei) (open_trmEI_wrt_trmEI_rec k tei_5 uei) m
  | (tei_cast_exp sei Ve Te) => tei_cast_exp (open_trmEI_wrt_trmEI_rec k tei_5 sei) Ve Te
  | (tei_cast_imp sei Vi p Ti) => tei_cast_imp (open_trmEI_wrt_trmEI_rec k tei_5 sei) Vi p Ti
  | (tei_import_exp Te tei Ti uei) => tei_import_exp Te (open_trmEI_wrt_trmEI_rec k tei_5 tei) Ti (open_trmEI_wrt_trmEI_rec (S k) tei_5 uei)
  | (tei_import_imp Ti tei Te uei) => tei_import_imp Ti (open_trmEI_wrt_trmEI_rec k tei_5 tei) Te (open_trmEI_wrt_trmEI_rec (S k) tei_5 uei)
end.

Definition open_trmEI_wrt_trmEI tei_5 tei__6 := open_trmEI_wrt_trmEI_rec 0 tei__6 tei_5.

Inductive isExplicit : trmEI -> Prop :=
 | exp_var : forall (xei:varEI),
     isExplicit (tei_var_f xei)
 | exp_null :
     isExplicit (tei_null mode_explicit)
 | exp_abs : forall (L:vars) (Te:typE) (tei:trmEI),
      ( forall xei , xei \notin  L  -> isExplicit  ( open_trmEI_wrt_trmEI tei (tei_var_f xei) )  )  ->
     isExplicit (tei_abs_exp Te tei)
 | exp_app : forall (sei tei:trmEI),
     isExplicit sei ->
     isExplicit tei ->
     isExplicit (tei_app sei tei mode_explicit)
 | exp_safe_app : forall (sei tei uei:trmEI),
     isExplicit sei ->
     isExplicit tei ->
     isExplicit uei ->
     isExplicit (tei_app_safe sei tei uei mode_explicit)
 | exp_cast : forall (tei:trmEI) (Ve Te:typE),
     isExplicit tei ->
     isExplicit (tei_cast_exp tei Ve Te)
 | exp_import : forall (L:vars) (Te:typE) (tei:trmEI) (Ti:typI) (uei:trmEI),
     isImplicit tei ->
      ( forall xei , xei \notin  L  -> isExplicit  ( open_trmEI_wrt_trmEI uei (tei_var_f xei) )  )  ->
     isExplicit (tei_import_exp Te tei Ti uei)
with isImplicit : trmEI -> Prop :=
 | imp_var : forall (xei:varEI),
     isImplicit (tei_var_f xei)
 | imp_null :
     isImplicit (tei_null mode_implicit)
 | imp_abs : forall (L:vars) (Ti:typI) (tei:trmEI) (Ui:typI),
      ( forall xei , xei \notin  L  -> isImplicit  ( open_trmEI_wrt_trmEI tei (tei_var_f xei) )  )  ->
     isImplicit (tei_abs_imp Ti tei Ui)
 | imp_app : forall (sei tei:trmEI),
     isImplicit sei ->
     isImplicit tei ->
     isImplicit (tei_app sei tei mode_implicit)
 | imp_safe_app : forall (sei tei uei:trmEI),
     isImplicit sei ->
     isImplicit tei ->
     isImplicit uei ->
     isImplicit (tei_app_safe sei tei uei mode_implicit)
 | imp_cast : forall (tei:trmEI) (Vi:typI) (p:label) (Ti:typI),
     isImplicit tei ->
     isImplicit (tei_cast_imp tei Vi p Ti)
 | imp_import : forall (L:vars) (Ti:typI) (tei:trmEI) (Te:typE) (uei:trmEI),
     isExplicit tei ->
      ( forall xei , xei \notin  L  -> isImplicit  ( open_trmEI_wrt_trmEI uei (tei_var_f xei) )  )  ->
     isImplicit (tei_import_imp Ti tei Te uei).

Inductive nullify : typI -> typE -> Prop :=
 | nullify_null :
     nullify typI_null typE_null
 | nullify_arrow : forall (Vi Ti:typI) (Ve Te:typE),
     nullify Vi Ve ->
     nullify Ti Te ->
     nullify (typI_unsafe_arrow Vi Ti) (typE_safe_arrow Ve Te).

Inductive erase : typE -> typI -> Prop :=
 | erase_null :
     erase typE_null typI_null
 | erase_arrow1 : forall (Ve Te:typE) (Vi Ti:typI),
     erase Ve Vi ->
     erase Te Ti ->
     erase (typE_safe_arrow Ve Te) (typI_unsafe_arrow Vi Ti)
 | erase_arrow2 : forall (Ve Te:typE) (Vi Ti:typI),
     erase Ve Vi ->
     erase Te Ti ->
     erase (typE_nonnull_arrow Ve Te) (typI_unsafe_arrow Vi Ti).

Inductive compatI : typI -> typI -> Prop :=
 | compatI_null_refl :
     compatI typI_null typI_null
 | compatI_null : forall (Ti1 Ti2:typI),
     compatI typI_null (typI_unsafe_arrow Ti1 Ti2)
 | compatI_arrow : forall (Vi Ti Vi' Ti':typI),
     compatI Vi' Vi ->
     compatI Ti Ti' ->
     compatI (typI_unsafe_arrow Vi Ti) (typI_unsafe_arrow Vi' Ti').

Inductive ssub : typE -> typE -> Prop :=
 | ssub_null :
     ssub typE_null typE_null
 | ssub_null_arrow : forall (Ve Te:typE),
     ssub typE_null (typE_safe_arrow Ve Te)
 | ssub_arrow1 : forall (Ve Te Ve' Te':typE),
     ssub Ve' Ve ->
     ssub Te Te' ->
     ssub (typE_nonnull_arrow Ve Te) (typE_nonnull_arrow Ve' Te')
 | ssub_arrow2 : forall (Ve Te Ve' Te':typE),
     ssub Ve' Ve ->
     ssub Te Te' ->
     ssub (typE_nonnull_arrow Ve Te) (typE_safe_arrow Ve' Te')
 | ssub_safe_arrow : forall (Ve Te Ve' Te':typE),
     ssub Ve' Ve ->
     ssub Te Te' ->
     ssub (typE_safe_arrow Ve Te) (typE_safe_arrow Ve' Te').

Inductive typingE : ctxE -> trmEI -> typE -> Prop :=
 | typingE_var : forall (Ge:ctxE) (xei:varEI) (Te:typE),
      uniq  Ge  ->
      binds  xei Te Ge  ->
     typingE Ge (tei_var_f xei) Te
 | typingE_null : forall (Ge:ctxE),
      uniq  Ge  ->
     typingE Ge (tei_null mode_explicit) typE_null
 | typingE_abs : forall (L:vars) (Ge:ctxE) (Ve:typE) (sei:trmEI) (Te:typE),
      ( forall xei , xei \notin  L  -> isExplicit  ( open_trmEI_wrt_trmEI sei (tei_var_f xei) )  )  ->
      ( forall xei , xei \notin  L  -> typingE  (( xei ~ Ve )++ Ge )   ( open_trmEI_wrt_trmEI sei (tei_var_f xei) )  Te )  ->
     typingE Ge (tei_abs_exp Ve sei) (typE_nonnull_arrow Ve Te)
 | typingE_app : forall (Ge:ctxE) (sei tei:trmEI) (Te Ve:typE),
     isExplicit sei ->
     isExplicit tei ->
     typingE Ge sei (typE_nonnull_arrow Ve Te) ->
     typingE Ge tei Ve ->
     typingE Ge (tei_app sei tei mode_explicit) Te
 | typingE_safe_app : forall (Ge:ctxE) (fei sei tei:trmEI) (Te Ve:typE),
     typingE Ge fei (typE_safe_arrow Ve Te) ->
     typingE Ge sei Ve ->
     typingE Ge tei Te ->
     typingE Ge (tei_app_safe fei sei tei mode_explicit) Te
 | typingE_cast : forall (Ge:ctxE) (sei:trmEI) (Ve Te:typE),
     isExplicit sei ->
     typingE Ge sei Ve ->
     ssub Ve Te ->
     typingE Ge  ( (tei_cast_exp sei Ve Te) )  Te
 | typingE_import : forall (L:vars) (Ge:ctxE) (Te:typE) (tei:trmEI) (Ti:typI) (uei:trmEI) (Ve:typE),
     isImplicit tei ->
      ( forall xei , xei \notin  L  -> isExplicit  ( open_trmEI_wrt_trmEI uei (tei_var_f xei) )  )  ->
      ( forall xei , xei \notin  L  -> typingE  (( xei ~ Te )++ Ge )   ( open_trmEI_wrt_trmEI uei (tei_var_f xei) )  Ve )  ->
     typingI  nil  tei Ti ->
     nullify Ti Te ->
     typingE Ge  ( (tei_import_exp Te tei Ti uei) )  Ve
with typingI : ctxI -> trmEI -> typI -> Prop :=
 | typingI_var : forall (Gi:ctxI) (xei:varEI) (Ti:typI),
      uniq  Gi  ->
      binds  xei Ti Gi  ->
     typingI Gi (tei_var_f xei) Ti
 | typingI_null : forall (Gi:ctxI),
      uniq  Gi  ->
     typingI Gi (tei_null mode_implicit) typI_null
 | typingI_abs : forall (L:vars) (Gi:ctxI) (Vi:typI) (sei:trmEI) (Ti:typI),
      ( forall xei , xei \notin  L  -> isImplicit  ( open_trmEI_wrt_trmEI sei (tei_var_f xei) )  )  ->
      ( forall xei , xei \notin  L  -> typingI  (( xei ~ Vi )++ Gi )   ( open_trmEI_wrt_trmEI sei (tei_var_f xei) )  Ti )  ->
     typingI Gi  ( (tei_abs_imp Vi sei Ti) )   ( (typI_unsafe_arrow Vi Ti) )
 | typingI_app : forall (Gi:ctxI) (sei tei:trmEI) (Ti Vi:typI),
     isImplicit sei ->
     isImplicit tei ->
     typingI Gi sei (typI_unsafe_arrow Vi Ti) ->
     typingI Gi tei Vi ->
     typingI Gi (tei_app sei tei mode_implicit) Ti
 | typingI_safi_app : forall (Gi:ctxI) (fei sei tei:trmEI) (Ti Vi:typI),
     isImplicit fei ->
     isImplicit sei ->
     isImplicit tei ->
     typingI Gi fei (typI_unsafe_arrow Vi Ti) ->
     typingI Gi sei Vi ->
     typingI Gi tei Ti ->
     typingI Gi (tei_app_safe fei sei tei mode_implicit) Ti
 | typingI_cast : forall (Gi:ctxI) (sei:trmEI) (Vi:typI) (p:label) (Ti:typI),
     isImplicit sei ->
     typingI Gi sei Vi ->
     compatI Vi Ti ->
     typingI Gi (tei_cast_imp sei Vi p Ti) Ti
 | typingI_import : forall (L:vars) (Gi:ctxI) (Ti:typI) (tei:trmEI) (Te:typE) (uei:trmEI) (Vi:typI),
     isExplicit tei ->
      ( forall xei , xei \notin  L  -> isImplicit  ( open_trmEI_wrt_trmEI uei (tei_var_f xei) )  )  ->
      ( forall xei , xei \notin  L  -> typingI  (( xei ~ Ti )++ Gi )   ( open_trmEI_wrt_trmEI uei (tei_var_f xei) )  Vi )  ->
     typingE  nil  tei Te ->
     erase Te Ti ->
     typingI Gi  ( (tei_import_imp Ti tei Te uei) )  Vi.
