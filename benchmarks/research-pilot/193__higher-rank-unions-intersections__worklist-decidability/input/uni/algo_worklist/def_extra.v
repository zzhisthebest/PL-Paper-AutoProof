Require Import Bool.

Require Import Metalib.Metatheory.

Require Import List.

Require Import uni.prop_ln.

Require Export uni.def_ott.

Require Export uni.decl_worklist.def.

Fixpoint awl_app (Γ1 Γ2 : aworklist) :=
  match Γ1 with
    | aworklist_empty => Γ2
    | aworklist_cons_var Γ1' X b => aworklist_cons_var (awl_app Γ1' Γ2) X b
    | aworklist_cons_work Γ1' w => aworklist_cons_work (awl_app Γ1' Γ2) w
  end.

Inductive aworklist_subst : aworklist -> typvar -> typ -> aworklist -> aworklist -> Prop :=
  | a_ws__stop : forall Γ X A ,
      aworklist_subst (aworklist_cons_var Γ X (abind_etvar_empty)) X A Γ aworklist_empty
  | a_ws__var_stay : forall Γ X Y A B Γ1 Γ2,
      aworklist_subst Γ X A Γ1 Γ2 ->
      aworklist_subst (aworklist_cons_var Γ Y (abind_var_typ B)) X A Γ1 (aworklist_cons_var Γ2 Y (abind_var_typ B))
  | a_ws__tvar_stay : forall Γ X Y A Γ1 Γ2,
      aworklist_subst Γ X A Γ1 Γ2 ->
      Y <> X ->
      Y `notin` ftvar_in_typ A ->
      aworklist_subst (aworklist_cons_var Γ Y (abind_tvar_empty)) X A Γ1 (aworklist_cons_var Γ2 Y (abind_tvar_empty))
  | a_ws__stvar_stay : forall Γ X Y A Γ1 Γ2,
      aworklist_subst Γ X A Γ1 Γ2 ->
      Y <> X ->
      Y `notin` ftvar_in_typ A ->
      aworklist_subst (aworklist_cons_var Γ Y (abind_stvar_empty)) X A Γ1 (aworklist_cons_var Γ2 Y (abind_stvar_empty))
  | a_ws__work_stay : forall Γ X A w Γ1 Γ2,
      aworklist_subst Γ X A Γ1 Γ2 ->
      aworklist_subst (aworklist_cons_work Γ w) X A  Γ1 (aworklist_cons_work Γ2 w)
  | a_ws__etvar_stay : forall Γ X Y A Γ1 Γ2,
      aworklist_subst Γ X A Γ1 Γ2 ->
      Y <> X ->
      Y `notin` ftvar_in_typ A ->
      aworklist_subst (aworklist_cons_var Γ Y (abind_etvar_empty)) X A Γ1 (aworklist_cons_var Γ2 Y (abind_etvar_empty))
  | a_ws__etvar_move : forall Γ1 Γ2 X Y A  Γ'1 Γ'2,
      aworklist_subst (awl_app Γ2 (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty)) X A Γ'1 Γ'2 ->
      Y <> X ->
      Y `in` ftvar_in_typ A ->
      aworklist_subst (aworklist_cons_var (awl_app Γ2 (aworklist_cons_var Γ1 X abind_etvar_empty)) Y (abind_etvar_empty)) X A Γ'1 Γ'2.

Inductive a_wl_red : aworklist -> Prop :=
  | a_wl_red__empty : a_wl_red aworklist_empty
  | a_wl_red__gc_var : forall (Γ:aworklist) (X:typvar) (b:abind),
      a_wl_red Γ ->
      a_wl_red (aworklist_cons_var Γ X b)
  | a_wl_red__sub_top : forall (Γ:aworklist) (B1:typ),
      a_wl_red Γ ->
      a_wl_red (aworklist_cons_work Γ (work_sub B1 typ_top))
  | a_wl_red__sub_bot : forall (Γ:aworklist) (A:typ),
      a_wl_red Γ ->
      a_wl_red (aworklist_cons_work Γ (work_sub typ_bot A))
  | a_wl_red__sub_unit : forall (Γ:aworklist),
      a_wl_red Γ ->
      a_wl_red (aworklist_cons_work Γ (work_sub typ_unit typ_unit))
  | a_wl_red__sub_tvar : forall (Γ:aworklist) (X:typvar),
      a_wl_red Γ ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_var_f X) (typ_var_f X)))
  | a_wl_red__subarrow : forall (Γ:aworklist) (B1 B2 A1 A2:typ),
      a_wl_red (aworklist_cons_work (aworklist_cons_work Γ (work_sub A1 B1)) (work_sub B2 A2)) ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_arrow B1 B2) (typ_arrow A1 A2)))
  | a_wl_red__sub_alll : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
      a_wneq_all (awl_to_aenv Γ) A1 ->
      ( forall X , X \notin  L  -> a_wl_red (aworklist_cons_work (aworklist_cons_var Γ X abind_etvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )  A1)) )  ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_all B1) A1))
  | a_wl_red__sub_all : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
      ( forall X , X \notin  L  -> a_wl_red (aworklist_cons_work (aworklist_cons_var Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )  ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_all B1) (typ_all A1)))
  | a_wl_red__sub_arrow1 : forall (L:vars) (Γ:aworklist) (X:typvar) (A1 A2:typ),
      binds ( X )  ( abind_etvar_empty ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ1 Γ2,
      (aworklist_subst (aworklist_cons_work (aworklist_cons_var (aworklist_cons_var Γ X1 abind_etvar_empty) X2 abind_etvar_empty) (work_sub (typ_var_f X) (typ_arrow A1 A2))) X (typ_arrow (typ_var_f X1) (typ_var_f X2)) Γ1 Γ2) ->
      (a_wl_red  (awl_app (subst_typ_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) Γ1 )   ) ) ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_var_f X) (typ_arrow A1 A2)))
  | a_wl_red__sub_arrow2 : forall (L:vars) (Γ:aworklist) (A1 A2:typ) (X:typvar),
      binds ( X )  ( abind_etvar_empty ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ1 Γ2,
      (aworklist_subst (aworklist_cons_work (aworklist_cons_var (aworklist_cons_var Γ X1 abind_etvar_empty) X2 abind_etvar_empty) (work_sub (typ_arrow A1 A2) (typ_var_f X))) X (typ_arrow (typ_var_f X1) (typ_var_f X2)) Γ1 Γ2) ->
      (a_wl_red  (awl_app (subst_typ_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) Γ1 )   ) ) ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_arrow A1 A2) (typ_var_f X)))
  | a_wl_red__sub_etvarmono1 : forall (Γ Γ1 Γ2:aworklist) (X:typvar) (A:typ),
      binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
      a_mono_typ  ( awl_to_aenv  Γ  )  A ->
      X `notin` ftvar_in_typ A ->
      (aworklist_subst  Γ  X A Γ1 Γ2) ->
      a_wl_red   (awl_app (subst_typ_in_aworklist A X Γ2) Γ1 ) ->
      a_wl_red (aworklist_cons_work Γ (work_sub A (typ_var_f X)))
  | a_wl_red__sub_etvarmono2 : forall (Γ Γ1 Γ2:aworklist) (X:typvar) (B:typ),
      binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
      a_mono_typ  ( awl_to_aenv  Γ  )  B ->
      X `notin` ftvar_in_typ B ->
      (aworklist_subst  Γ  X B Γ1 Γ2) ->
      a_wl_red   (awl_app (subst_typ_in_aworklist B X Γ2) Γ1 ) ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_var_f X) B))
  | a_wl_red__sub_intersection1 : forall (Γ:aworklist) (A1 B1 B2:typ),
      a_wl_red (aworklist_cons_work (aworklist_cons_work Γ (work_sub A1 B1)) (work_sub A1 B2)) ->
      a_wl_red (aworklist_cons_work Γ (work_sub A1 (typ_intersection B1 B2)))
  | a_wl_red__sub_intersection2 : forall (Γ:aworklist) (B1 B2 A1:typ),
      a_wl_red (aworklist_cons_work Γ (work_sub B1 A1)) ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_intersection B1 B2) A1))
  | a_wl_red__sub_intersection3 : forall (Γ:aworklist) (B1 B2 A1:typ),
      a_wl_red (aworklist_cons_work Γ (work_sub B2 A1)) ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_intersection B1 B2) A1))
  | a_wl_red__sub_union1 : forall (Γ:aworklist) (B1 A1 A2:typ),
      a_wl_red (aworklist_cons_work Γ (work_sub B1 A1)) ->
      a_wl_red (aworklist_cons_work Γ (work_sub B1 (typ_union A1 A2)))
  | a_wl_red__sub_union2 : forall (Γ:aworklist) (B1 A1 A2:typ),
      a_wl_red (aworklist_cons_work Γ (work_sub B1 A2)) ->
      a_wl_red (aworklist_cons_work Γ (work_sub B1 (typ_union A1 A2)))
  | a_wl_red__sub_union3 : forall (Γ:aworklist) (B1 B2 A1:typ),
      a_wl_red (aworklist_cons_work (aworklist_cons_work Γ (work_sub B1 A1)) (work_sub B2 A1)) ->
      a_wl_red (aworklist_cons_work Γ (work_sub (typ_union B1 B2) A1))
  | a_wl_red__chk_sub : forall (Γ:aworklist) (e:exp) (A1:typ),
      a_wl_red (aworklist_cons_work Γ (work_infer e (conts_sub A1))) ->
      a_wl_red (aworklist_cons_work Γ (work_check e A1))
  | a_wl_red__chk_absarrow : forall (L:vars) (Γ:aworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_cons_work (aworklist_cons_var Γ x (abind_var_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
      a_wl_red (aworklist_cons_work Γ (work_check (exp_abs e) (typ_arrow A1 A2)))
  | a_wl_red__chk_absetvar : forall (L:vars) (Γ:aworklist) (e:exp) (X:typvar),
      binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
      (  forall x, x `notin` L -> forall X1, X1 `notin` (L `union` (singleton x)) -> forall X2, X2 `notin` (L `union` singleton x `union` singleton X1) -> forall Γ1 Γ2,
            (aworklist_subst (aworklist_cons_work (aworklist_cons_var (aworklist_cons_var (aworklist_cons_var Γ X1 abind_etvar_empty) X2 abind_etvar_empty) x (abind_var_typ (typ_var_f X1)))  (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2))) X
                  (typ_arrow (typ_var_f X1) (typ_var_f X2))   Γ1  Γ2)  ->
            a_wl_red  (   (awl_app (subst_typ_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) Γ1 ) )  ) ->
      a_wl_red (aworklist_cons_work Γ (work_check (exp_abs e) (typ_var_f X)))
  | a_wl_red__chk_abstop : forall (L:vars) (Γ:aworklist) (e:exp),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_cons_work (aworklist_cons_var Γ x (abind_var_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
      a_wl_red (aworklist_cons_work Γ (work_check (exp_abs e) typ_top))
  | a_wl_red__chk_inter : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
      a_wl_red (aworklist_cons_work (aworklist_cons_work Γ (work_check e A1)) (work_check e A2)) ->
      a_wl_red (aworklist_cons_work Γ (work_check e (typ_intersection A1 A2)))
  | a_wl_red__chk_union1 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
      a_wl_red (aworklist_cons_work Γ (work_check e A1)) ->
      a_wl_red (aworklist_cons_work Γ (work_check e (typ_union A1 A2)))
  | a_wl_red__chk_union2 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
      a_wl_red (aworklist_cons_work Γ (work_check e A2)) ->
      a_wl_red (aworklist_cons_work Γ (work_check e (typ_union A1 A2)))
  | a_wl_red__inf_var : forall (Γ:aworklist) (x:expvar) (cs:conts) (A:typ),
      binds ( x )  ( (abind_var_typ A) ) (  ( awl_to_aenv  Γ  )  )  ->
      a_wl_red (aworklist_cons_work Γ (work_applys cs A)) ->
      a_wl_red (aworklist_cons_work Γ (work_infer (exp_var_f x) cs))
  | a_wl_red__inf_anno : forall (Γ:aworklist) (e:exp) (A:typ) (cs:conts),
      a_wl_red (aworklist_cons_work (aworklist_cons_work Γ (work_applys cs A)) (work_check e A)) ->
      a_wl_red (aworklist_cons_work Γ (work_infer  ( (exp_anno e A) )  cs))
  | a_wl_red__inf_tabs : forall (L:vars) (Γ:aworklist) (e:exp) (A:typ) (cs:conts),
      ( forall X , X \notin  L  ->
        a_wl_red (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work Γ (work_applys cs  ( (typ_all A) ) )) X abind_tvar_empty) (work_check  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) )) )  ->
      a_wl_red (aworklist_cons_work Γ (work_infer (exp_tabs (exp_anno e A)) cs))
  | a_wl_red__inf_abs_mono : forall (L:vars) (Γ:aworklist) (e:exp) (cs:conts),
    (forall x, x `notin` L -> forall X1, X1 `notin` (L `union` singleton x) -> forall X2, X2 `notin` (L `union` singleton x `union` singleton X1) ->
        a_wl_red (aworklist_cons_work (aworklist_cons_var (aworklist_cons_work (aworklist_cons_var (aworklist_cons_var Γ X1 abind_etvar_empty) X2 abind_etvar_empty) (work_applys cs (typ_arrow (typ_var_f X1) (typ_var_f X2)))) x (abind_var_typ (typ_var_f X1)) ) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2)))
        ) ->
    a_wl_red (aworklist_cons_work Γ (work_infer (exp_abs e) cs))
  | a_wl_red__inf_unit : forall (Γ:aworklist) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_applys cs typ_unit)) ->
      a_wl_red (aworklist_cons_work Γ (work_infer exp_unit cs))
  | a_wl_red__inf_app : forall (Γ:aworklist) (e1 e2:exp) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_infer e1  (  (conts_infabs  (  (contd_infapp e2 cs)  ) )  ) )) ->
      a_wl_red (aworklist_cons_work Γ (work_infer  ( (exp_app e1 e2) )  cs))
  | a_wl_red__infapp : forall (Γ:aworklist) (A B:typ) (e:exp) (cs:conts),
      a_wl_red (aworklist_cons_work (aworklist_cons_work Γ (work_applys cs B) ) (work_check e A)) ->
      a_wl_red (aworklist_cons_work Γ (work_infapp A B e cs))
  | a_wl_red__infabs_arr : forall (Γ:aworklist) (A B:typ) (cd:contd),
      a_wl_red (aworklist_cons_work Γ (work_applyd cd A B)) ->
      a_wl_red (aworklist_cons_work Γ (work_infabs (typ_arrow A B) cd))
  | a_wl_red__infabs_bot : forall (Γ:aworklist) (cd:contd),
      a_wl_red (aworklist_cons_work Γ (work_infabs (typ_arrow typ_top typ_bot) cd)) ->
      a_wl_red (aworklist_cons_work Γ (work_infabs typ_bot cd))
  | a_wl_red__infabs_all : forall (L:vars) (Γ:aworklist) (A:typ) (cd:contd),
      (forall X, X `notin` L -> a_wl_red (aworklist_cons_work  (aworklist_cons_var Γ X abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) cd)) ) ->
      a_wl_red (aworklist_cons_work Γ (work_infabs (typ_all A) cd))
  | a_wl_red__infabs_inter1 : forall (Γ:aworklist) (A1 A2:typ) (cd:contd),
      a_wl_red (aworklist_cons_work Γ (work_infabs A1 cd)) ->
      a_wl_red (aworklist_cons_work Γ (work_infabs (typ_intersection A1 A2) cd))
  | a_wl_red__infabs_inter2 : forall (Γ:aworklist) (A1 A2:typ) (cd:contd),
      a_wl_red (aworklist_cons_work Γ (work_infabs A2 cd)) ->
      a_wl_red (aworklist_cons_work Γ (work_infabs (typ_intersection A1 A2) cd))
  | a_wl_red__infabs_union : forall (Γ:aworklist) (A1 A2:typ) (cd:contd),
      a_wl_red (aworklist_cons_work Γ (work_infabs A1  (  (contd_infabsunion A2 cd)  ) )) ->
      a_wl_red (aworklist_cons_work Γ (work_infabs (typ_union A1 A2) cd))
  | a_wl_red__infabsunion : forall (Γ:aworklist) (B1 C1 A2:typ) (cd:contd),
      a_wl_red (aworklist_cons_work Γ (work_infabs A2  (  (contd_unioninfabs B1 C1 cd)  ) )) ->
      a_wl_red (aworklist_cons_work Γ (work_infabsunion B1 C1 A2 cd))
  | a_wl_red__unioninfabs : forall (Γ:aworklist) (B2 C2 B1 C1:typ) (cd:contd),
      a_wl_red (aworklist_cons_work Γ (work_applyd cd (typ_intersection B1 B2)  ( (typ_union C1 C2) ) )) ->
      a_wl_red (aworklist_cons_work Γ (work_unioninfabs B1 C1 B2 C2 cd))
  | a_wl_red__infabs_etvar : forall (L:vars) (Γ:aworklist) (X:typvar) (cd:contd),
      binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ1 Γ2,
          (aworklist_subst (aworklist_cons_work (aworklist_cons_var (aworklist_cons_var Γ X1 abind_etvar_empty) X2 abind_etvar_empty) (work_infabs (typ_arrow (typ_var_f X1) (typ_var_f X2)) cd))  X   (typ_arrow (typ_var_f X1) (typ_var_f X2))   Γ1 Γ2) ->
        a_wl_red ( (awl_app (subst_typ_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) Γ1 )  )
      ) ->
    a_wl_red (aworklist_cons_work Γ (work_infabs (typ_var_f X) cd))
  | a_wl_red__inf_tapp : forall (Γ:aworklist) (e:exp) (B:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_infer e (conts_inftapp B cs))) ->
      a_wl_red (aworklist_cons_work Γ (work_infer (exp_tapp e B) cs))
  | a_wl_red__inftapp_all : forall (Γ:aworklist) (A B:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_applys cs  (open_typ_wrt_typ  A   B ) )) ->
      a_wl_red (aworklist_cons_work Γ (work_inftapp (typ_all A) B cs))
  | a_wl_red__inftapp_bot : forall (Γ:aworklist) (B:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_applys cs typ_bot)) ->
      a_wl_red (aworklist_cons_work Γ (work_inftapp typ_bot B cs))
  | a_wl_red__inftapp_inter1 : forall (Γ:aworklist) (A1 A2 B:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_inftapp A1 B cs)) ->
      a_wl_red (aworklist_cons_work Γ (work_inftapp (typ_intersection A1 A2) B cs))
  | a_wl_red__inftapp_inter2 : forall (Γ:aworklist) (A1 A2 B:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_inftapp A2 B cs)) ->
      a_wl_red (aworklist_cons_work Γ (work_inftapp (typ_intersection A1 A2) B cs))
  | a_wl_red__inftapp_union : forall (Γ:aworklist) (A1 A2 B:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_inftapp A1 B  (  (conts_inftappunion A2 B cs)  ) )) ->
      a_wl_red (aworklist_cons_work Γ (work_inftapp (typ_union A1 A2) B cs))
  | a_wl_red__inftappunion : forall (Γ:aworklist) (C1 A2 B:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_inftapp A2 B  (  (conts_unioninftapp C1 cs)  ) )) ->
      a_wl_red (aworklist_cons_work Γ (work_inftappunion C1 A2 B cs))
  | a_wl_red__unioninftapp : forall (Γ:aworklist) (C2 C1:typ) (cs:conts),
      a_wl_red (aworklist_cons_work Γ (work_applys cs (typ_union C1 C2))) ->
      a_wl_red (aworklist_cons_work Γ (work_unioninftapp C1 C2 cs))
  | a_wl_red__applys : forall (Γ:aworklist) (w:work) (A:typ) (cs:conts),
      apply_conts cs A w ->
      a_wl_red (aworklist_cons_work Γ w) ->
      a_wl_red (aworklist_cons_work Γ (work_applys cs A))
  | a_wl_red__applyd : forall (Γ:aworklist) (w:work) (A B:typ) (cd:contd),
      apply_contd cd A B w ->
      a_wl_red (aworklist_cons_work Γ w) ->
      a_wl_red (aworklist_cons_work Γ (work_applyd cd A B)).

Declare Scope aworklist_scope.

Delimit Scope aworklist_scope with aworklist.

Bind Scope aworklist_scope with aworklist.

Notation " X ~ᵃ b ; Γ " :=
  (aworklist_cons_var Γ X b)
    (at level 58, b at next level, right associativity) : aworklist_scope.

Notation " X ~ᵃ □ ;ᵃ Γ " :=
  (aworklist_cons_var Γ X abind_tvar_empty)
    (at level 58, right associativity) : aworklist_scope.

Notation " X ~ᵃ ■ ;ᵃ Γ " :=
  (aworklist_cons_var Γ X abind_stvar_empty)
    (at level 58, right associativity) : aworklist_scope.

Notation " X ~ᵃ ⬒ ;ᵃ Γ " :=
  (aworklist_cons_var Γ X abind_etvar_empty)
    (at level 58, right associativity) : aworklist_scope.

Notation " X ~ᵃ A ;ᵃ Γ " :=
  (aworklist_cons_var Γ X (abind_var_typ A))
    (at level 58, A at next level, right associativity) : aworklist_scope.

Notation " w ⫤ᵃ Γ " :=
  (aworklist_cons_work Γ w)
    (at level 58, right associativity) : aworklist_scope.

Notation " Γ2 ⧺ Γ1 " :=
  (awl_app Γ2 Γ1)
    (at level 58, right associativity) : aworklist_scope.

Notation " Γ ⟶ᵃʷ⁎⋅ " :=
  (a_wl_red Γ)
    (at level 58, no associativity) : type_scope.

Notation " ⊢ᵃʷₜ Γ " :=
  (a_wf_twl Γ)
    (at level 58, no associativity) : type_scope.

Notation " ⊢ᵃʷₛ Γ " :=
  (a_wf_wl Γ)
    (at level 58, no associativity) : type_scope.

Notation " ⊢ᵃʷ Γ " :=
  (a_wf_wwl Γ)
    (at level 58, no associativity) : type_scope.

Notation " ⌊ Γ ⌋ᵃ " :=
  (awl_to_aenv Γ)
    (at level 49, no associativity) : type_scope.
