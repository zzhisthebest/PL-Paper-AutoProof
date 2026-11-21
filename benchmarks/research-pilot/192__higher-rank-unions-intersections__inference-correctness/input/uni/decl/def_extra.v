Require Import Bool.

Require Import Metalib.Metatheory.

Require Import List.

Require Import uni.prop_ln.

Require Export uni.def_ott.

Inductive d_sub : denv -> typ -> typ -> Prop :=
  | d_sub__top : forall (Ψ:denv) (A:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ A ->
      d_sub Ψ A typ_top
  | d_sub__bot : forall (Ψ:denv) (B:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ B ->
      d_sub Ψ typ_bot B
  | d_sub__unit : forall (Ψ:denv),
      d_wf_env Ψ ->
      d_sub Ψ typ_unit typ_unit
  | d_sub__tvar : forall (Ψ:denv) (X:typvar),
      d_wf_env Ψ ->
      d_wf_typ Ψ (typ_var_f X) ->
      d_sub Ψ (typ_var_f X) (typ_var_f X)
  | d_sub__arrow : forall (Ψ:denv) (A1 A2 B1 B2:typ),
      d_sub Ψ B1 A1 ->
      d_sub Ψ A2 B2 ->
      d_sub Ψ (typ_arrow A1 A2) (typ_arrow B1 B2)
  | d_sub__all : forall (L:vars) (Ψ:denv) (A B:typ),
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ B (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub  ( X ~ dbind_stvar_empty  ++  Ψ )   ( open_typ_wrt_typ A (typ_var_f X) )   ( open_typ_wrt_typ B (typ_var_f X) )  )  ->
      d_sub Ψ (typ_all A) (typ_all B)
  | d_sub__alll : forall (L:vars) (Ψ:denv) (A B T:typ),
      d_wneq_all Ψ B ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      d_mono_typ Ψ T ->
      d_sub Ψ  (open_typ_wrt_typ  A   T )  B ->
      d_sub Ψ (typ_all A) B
  | d_sub__intersection1 : forall (Ψ:denv) (A B1 B2:typ),
      d_sub Ψ A B1 ->
      d_sub Ψ A B2 ->
      d_sub Ψ A (typ_intersection B1 B2)
  | d_sub__intersection2 : forall (Ψ:denv) (A1 A2 B:typ),
      d_sub Ψ A1 B ->
      d_wf_typ Ψ A2 ->
      d_sub Ψ (typ_intersection A1 A2) B
  | d_sub__intersection3 : forall (Ψ:denv) (A1 A2 B:typ),
      d_sub Ψ A2 B ->
      d_wf_typ Ψ A1 ->
      d_sub Ψ (typ_intersection A1 A2) B
  | d_sub__union1 : forall (Ψ:denv) (A B1 B2:typ),
      d_sub Ψ A B1 ->
      d_wf_typ Ψ B2 ->
      d_sub Ψ A (typ_union B1 B2)
  | d_sub__union2 : forall (Ψ:denv) (A B1 B2:typ),
      d_sub Ψ A B2 ->
      d_wf_typ Ψ B1 ->
      d_sub Ψ A (typ_union B1 B2)
  | d_sub__union3 : forall (Ψ:denv) (A1 A2 B:typ),
      d_sub Ψ A1 B ->
      d_sub Ψ A2 B ->
      d_sub Ψ (typ_union A1 A2) B.

Inductive d_sub_alt : denv -> typ -> typ -> Prop :=
  | d_sub_alt__top : forall (Ψ:denv) (A:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ A ->
      d_sub_alt Ψ A typ_top
  | d_sub_alt__bot : forall (Ψ:denv) (B:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ B ->
      d_sub_alt Ψ typ_bot B
  | d_sub_alt__unit : forall (Ψ:denv),
      d_wf_env Ψ ->
      d_sub_alt Ψ typ_unit typ_unit
  | d_sub_alt__tvar : forall (Ψ:denv) (X:typvar),
      d_wf_env Ψ ->
      d_wf_typ Ψ (typ_var_f X) ->
      d_sub_alt Ψ (typ_var_f X) (typ_var_f X)
  | d_sub_alt__arrow : forall (Ψ:denv) (A1 A2 B1 B2:typ),
      d_sub_alt Ψ B1 A1 ->
      d_sub_alt Ψ A2 B2 ->
      d_sub_alt Ψ (typ_arrow A1 A2) (typ_arrow B1 B2)
  | d_sub_alt__all : forall (L:vars) (Ψ:denv) (A B:typ),
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ B (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub_alt  ( X ~ dbind_stvar_empty  ++  Ψ )   ( open_typ_wrt_typ A (typ_var_f X) )   ( open_typ_wrt_typ B (typ_var_f X) )  )  ->
      d_sub_alt Ψ (typ_all A) (typ_all B)
  | d_sub_alt__alll : forall (L:vars) (Ψ:denv) (A B T:typ),
      neq_all B ->
      neq_intersection B ->
      neq_union B ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      d_mono_typ Ψ T ->
      d_sub_alt Ψ  (open_typ_wrt_typ  A   T )  B ->
      d_sub_alt Ψ (typ_all A) B
  | d_sub_alt__intersection1 : forall (Ψ:denv) (A B1 B2:typ),
      d_sub_alt Ψ A B1 ->
      d_sub_alt Ψ A B2 ->
      d_sub_alt Ψ A (typ_intersection B1 B2)
  | d_sub_alt__intersection2 : forall (Ψ:denv) (A1 A2 B:typ),
      d_sub_alt Ψ A1 B ->
      d_wf_typ Ψ A2 ->
      d_sub_alt Ψ (typ_intersection A1 A2) B
  | d_sub_alt__intersection3 : forall (Ψ:denv) (A1 A2 B:typ),
      d_sub_alt Ψ A2 B ->
      d_wf_typ Ψ A1 ->
      d_sub_alt Ψ (typ_intersection A1 A2) B
  | d_sub_alt__union1 : forall (Ψ:denv) (A B1 B2:typ),
      d_sub_alt Ψ A B1 ->
      d_wf_typ Ψ B2 ->
      d_sub_alt Ψ A (typ_union B1 B2)
  | d_sub_alt__union2 : forall (Ψ:denv) (A B1 B2:typ),
      d_sub_alt Ψ A B2 ->
      d_wf_typ Ψ B1 ->
      d_sub_alt Ψ A (typ_union B1 B2)
  | d_sub_alt__union3 : forall (Ψ:denv) (A1 A2 B:typ),
      d_sub_alt Ψ A1 B ->
      d_sub_alt Ψ A2 B ->
      d_sub_alt Ψ (typ_union A1 A2) B.

Inductive d_inftapp : denv -> typ -> typ -> typ -> Prop :=
  | d_inftapp__bot : forall (Ψ:denv) (B:typ),
      d_wf_tenv Ψ ->
      d_wf_typ Ψ B ->
      d_inftapp Ψ typ_bot B typ_bot
  | d_inftapp__all : forall (Ψ:denv) (A B:typ),
      d_wf_tenv Ψ ->
      d_wf_typ Ψ (typ_all A) ->
      d_wf_typ Ψ B ->
      d_inftapp Ψ (typ_all A) B (open_typ_wrt_typ  A B )
  | d_inftapp__intersection1 : forall (Ψ:denv) (A1 A2 B C:typ),
      d_wf_typ Ψ A2 ->
      d_inftapp Ψ A1 B C ->
      d_inftapp Ψ (typ_intersection A1 A2) B C
  | d_inftapp__intersection2 : forall (Ψ:denv) (A1 A2 B C:typ),
      d_wf_typ Ψ A1 ->
      d_inftapp Ψ A2 B C ->
      d_inftapp Ψ (typ_intersection A1 A2) B C
  | d_inftapp__union : forall (Ψ:denv) (A1 A2 B C1 C2:typ),
      d_inftapp Ψ A1 B C1 ->
      d_inftapp Ψ A2 B C2 ->
      d_inftapp Ψ (typ_union A1 A2) B (typ_union C1 C2).

Inductive d_infabs : denv -> typ -> typ -> typ -> Prop :=
  | d_infabs__bot : forall (Ψ:denv),
      d_wf_tenv Ψ ->
      d_infabs Ψ typ_bot typ_top typ_bot
  | d_infabs__arr : forall (Ψ:denv) (A B:typ),
      d_wf_tenv Ψ ->
      d_wf_typ Ψ A ->
      d_wf_typ Ψ B ->
      d_infabs Ψ (typ_arrow A B) A B
  | d_infabs__all : forall (Ψ:denv) (A B C T:typ),
      d_mono_typ Ψ T ->
      d_wf_typ Ψ (typ_all A) ->
      d_infabs Ψ  (open_typ_wrt_typ  A  T ) B C ->
      d_infabs Ψ (typ_all A) B C
  | d_infabs__intersection1 : forall (Ψ:denv) (A1 A2 B C:typ),
      d_wf_typ Ψ A2 ->
      d_infabs Ψ A1 B C ->
      d_infabs Ψ (typ_intersection A1 A2) B C
  | d_infabs__intersection2 : forall (Ψ:denv) (A1 A2 B C:typ),
      d_wf_typ Ψ A1 ->
      d_infabs Ψ A2 B C->
      d_infabs Ψ (typ_intersection A1 A2) B C
  | d_infabs__union : forall (Ψ:denv) (A1 A2 B1 B2 C1 C2:typ),
      d_infabs Ψ A1 B1 C1 ->
      d_infabs Ψ A2 B2 C2 ->
      d_infabs Ψ (typ_union A1 A2) (typ_intersection B1 B2) (typ_union C1 C2).

Inductive typing_mode :=
  | typingmode__inf
  | typingmode__chk.

Inductive d_chk_inf : denv -> exp -> typing_mode -> typ -> Prop :=
  | d_chk_inf__inf_var : forall (Ψ:denv) (x:expvar) (A:typ),
      d_wf_tenv Ψ ->
      binds ( x )  ( (dbind_typ A) ) ( Ψ )  ->
      d_chk_inf Ψ (exp_var_f x) typingmode__inf A
  | d_chk_inf__inf_anno : forall (Ψ:denv) (e:exp) (A:typ),
      d_wf_typ Ψ A ->
      d_chk_inf Ψ e typingmode__chk A ->
      d_chk_inf Ψ  ( (exp_anno e A) )  typingmode__inf A
  | d_chk_inf__inf_unit : forall (Ψ:denv),
      d_wf_tenv Ψ ->
      d_chk_inf Ψ exp_unit typingmode__inf typ_unit
  | d_chk_inf__inf_app : forall (Ψ:denv) (e1 e2:exp) (A B C:typ),
      d_chk_inf Ψ e1 typingmode__inf A ->
      d_infabs Ψ A B C ->
      d_chk_inf Ψ e2 typingmode__chk B ->
      d_chk_inf Ψ  ( (exp_app e1 e2) ) typingmode__inf C
  | d_chk_inf__inf_abs_mono : forall (L:vars) (Ψ:denv) (e:exp) (A B:typ),
      d_mono_typ Ψ (typ_arrow A B) ->
      ( forall x , x \notin  L  -> d_chk_inf  ( x ~ (dbind_typ A)  ++  Ψ )   ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk B ) ->
      d_chk_inf Ψ (exp_abs e) typingmode__inf (typ_arrow A B)
  | d_chk_inf__inf_tabs : forall (L:vars) (Ψ:denv) (e:exp) (A:typ),
      ( forall X, X `notin` L -> s_in X (open_typ_wrt_typ A (typ_var_f X)) ) ->
      ( forall X , X \notin  L  -> d_chk_inf  ( X ~ dbind_tvar_empty  ++  Ψ ) ( open_exp_wrt_typ e (typ_var_f X) ) typingmode__chk ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      d_chk_inf Ψ (exp_tabs (exp_anno e A)) typingmode__inf (typ_all A)
  | d_chk_inf__inf_tapp : forall (Ψ:denv) (e1:exp) (A B C:typ),
      d_wf_typ Ψ B ->
      d_chk_inf Ψ e1 typingmode__inf A ->
      d_inftapp Ψ A B C ->
      d_chk_inf Ψ (exp_tapp e1 B) typingmode__inf C
  | d_chk_inf__chk_abstop : forall (L:vars) (Ψ:denv) (e:exp),
      ( forall x , x \notin  L  -> d_chk_inf  ( x ~ (dbind_typ typ_bot)  ++  Ψ )   ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk typ_top )  ->
      d_chk_inf Ψ (exp_abs e) typingmode__chk typ_top
  | d_chk_inf__chk_abs : forall (L:vars) (Ψ:denv) (e:exp) (A1 A2:typ),
      d_wf_typ Ψ A1 ->
      ( forall x , x \notin  L  -> d_chk_inf  ( x ~ (dbind_typ A1)  ++  Ψ )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk A2 )  ->
      d_chk_inf Ψ (exp_abs e) typingmode__chk (typ_arrow A1 A2)

  | d_chk_inf__chk_sub : forall (Ψ:denv) (e:exp) (A B:typ),
      d_chk_inf Ψ e typingmode__inf B ->
      d_sub Ψ B A ->
      d_chk_inf Ψ e typingmode__chk A
  | d_chk_inf__chk_inter : forall (Ψ:denv) (e:exp) (A1 A2:typ),
      d_chk_inf Ψ e typingmode__chk A1 ->
      d_chk_inf Ψ e typingmode__chk A2 ->
      d_chk_inf Ψ e typingmode__chk (typ_intersection A1 A2)
  | d_chk_inf__chk_union1 : forall (Ψ:denv) (e:exp) (A1 A2:typ),
      d_chk_inf Ψ e typingmode__chk A1 ->
      d_wf_typ Ψ A2 ->
      d_chk_inf Ψ e typingmode__chk (typ_union A1 A2)
  | d_chk_inf__chk_union2 : forall (Ψ:denv) (e:exp) (A1 A2:typ),
      d_chk_inf Ψ e typingmode__chk A2 ->
      d_wf_typ Ψ A1 ->
      d_chk_inf Ψ e typingmode__chk (typ_union A1 A2).
