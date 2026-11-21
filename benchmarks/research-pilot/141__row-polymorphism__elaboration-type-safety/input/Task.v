Require Export Metalib.Metatheory.

Require Import Row_inf.

Require Import Fii_inf.

Require Import Infrastructure.

Require Import Disjoint.

Set Implicit Arguments.

Inductive bot_trans_r : PContext -> rtyp -> sty -> Prop :=
 | bot_trans_r_var : forall (Ptx:PContext) (a b:typvar),
      binds ( a ) ( b ) ( Ptx )  ->
     bot_trans_r Ptx (r_TyVar_f a) (sty_var_f b)
 | bot_trans_r_empty : forall (Ptx:PContext),
     bot_trans_r Ptx r_Empty sty_top
 | bot_trans_r_record : forall (Ptx:PContext) (l:i) (rt5:rt),
     lc_rt rt5 ->
     bot_trans_r Ptx (r_SingleField l rt5) (sty_rcd l sty_bot)
 | bot_trans_r_merge : forall (Ptx:PContext) (r1 r2:rtyp) (A B:sty),
     bot_trans_r Ptx r1 A ->
     bot_trans_r Ptx r2 B ->
     bot_trans_r Ptx (r_Merge r1 r2) (sty_and A B).

Inductive trans_rt : PContext -> rt -> sty -> Prop :=
 | trans_rt_nat : forall (Ptx:PContext),
     trans_rt Ptx rt_Base sty_nat
 | trans_rt_arrow : forall (Ptx:PContext) (rt1 rt2:rt) (A B:sty),
     trans_rt Ptx rt1 A ->
     trans_rt Ptx rt2 B ->
     trans_rt Ptx (rt_Fun rt1 rt2) (sty_arrow A B)
 | trans_rt_all : forall (L:vars) (Ptx:PContext) (R:rlist) (rt5:rt) (B A:sty),
      trans_rlist Ptx R B ->
      ( forall b , b \notin  L  ->
        ( forall a , a \notin L \u {{b}} ->
            trans_rt  (( a ~ b )++ Ptx )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )
              ( open_sty_wrt_sty   ( open_sty_wrt_sty_rec 1 (sty_var_f a) A ) (sty_var_f b)  )  )  )  ->
      trans_rt Ptx (rt_ConQuan R rt5) (sty_all B (sty_all B A))
 | trans_rt_record : forall (Ptx:PContext) (r:rtyp) (A:sty),
     trans_r  Ptx r A ->
     trans_rt Ptx (rt_Record r) A


with trans_r : PContext -> rtyp -> sty -> Prop :=
 | trans_r_empty : forall (Ptx:PContext),
     trans_r Ptx r_Empty sty_top
 | trans_r_tvar : forall (Ptx:PContext) (a b:typvar),
    binds ( a ) ( b ) ( Ptx )  ->
     trans_r Ptx (r_TyVar_f a) (sty_var_f a)
 | trans_r_record : forall (Ptx:PContext) (l:i) (rt5:rt) (A:sty),
     trans_rt Ptx rt5 A ->
     trans_r Ptx (r_SingleField l rt5) (sty_rcd l A)
 | trans_r_merge : forall (Ptx:PContext) (r1 r2:rtyp) (A B:sty),
     trans_r Ptx r1 A ->
     trans_r Ptx r2 B ->

     trans_r Ptx (r_Merge r1 r2) (sty_and A B)


with trans_rlist : PContext -> rlist -> sty -> Prop :=
 | trans_rlist_empty : forall (Ptx:PContext),
     trans_rlist Ptx R_Empty sty_top
 | trans_rlist_cons : forall (Ptx:PContext) (r:rtyp) (R:rlist) (A1 A2 B:sty),
     trans_r Ptx r A1 ->
     bot_trans_r Ptx r A2 ->
     trans_rlist Ptx R B ->
     trans_rlist Ptx (R_Cons r R) (sty_and  ( (sty_and A1 A2) )  B).

Inductive trans_Ttx : PContext -> TContext -> stctx -> Prop :=
  | trans_Ttx_nil :
      trans_Ttx nil nil nil
  | trans_Ttx_cons : forall Ptx Ttx DD a b R A,
      trans_Ttx Ptx Ttx DD ->
      trans_rlist Ptx R A ->
      a \notin dom DD \u dom Ttx \u dom Ptx \u fv_Ptx Ptx ->
      b \notin dom Ptx \u dom Ttx \u dom ((a ~ A) ++ DD) \u fv_Ptx Ptx ->
      trans_Ttx ((a~b)++Ptx) ((a ~ R)++Ttx) ((b ~ A ) ++ (a ~ A) ++ DD)
.

Inductive trans_Gtx : PContext -> GContext -> stctx -> Prop :=
  | trans_Gtx_nil : forall Ptx,
      trans_Gtx Ptx nil nil
  | trans_Gtx_cons : forall Ptx Gtx GG A x rt,
      trans_Gtx Ptx Gtx GG ->
      trans_rt Ptx rt A ->
      x \notin fv_Ptx Ptx ->
      trans_Gtx Ptx ((x ~ rt) ++ Gtx) ((x ~ A ) ++ GG)
.

Inductive wtt : PContext -> TContext -> GContext -> rexp -> rt -> sexp -> Prop :=
 | wtt_Eq : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (rt':rt) (ee:sexp) (rt5:rt) (A:sty),
     wtt Ptx Ttx Gtx re rt5 ee ->
     teq Ttx rt5 rt' ->
     trans_rt Ptx  rt' A ->
     wtt Ptx Ttx Gtx re rt' (sexp_anno ee A)
 | wtt_Var : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (x:expvar) (rt5:rt),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wfp Ttx Ptx ->
     binds  x   rt5   Gtx  ->
     wtt Ptx Ttx Gtx (re_Var_f x) rt5 (sexp_var_f x)
 | wtt_Lit : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (x:nat),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wfp Ttx Ptx ->
     wtt Ptx Ttx Gtx (re_Lit x) rt_Base (sexp_lit x)
 | wtt_ArrowI : forall (L:vars) (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (rt5:rt) (re:rexp) (rt':rt) (ee:sexp) (A B:sty),
     wfrt Ttx rt5 ->
      ( forall x , x \notin  L  -> wtt Ptx Ttx  (( x ~ rt5 )++ Gtx )   ( open_rexp_wrt_rexp re (re_Var_f x) )  rt'  ( open_sexp_wrt_sexp ee (sexp_var_f x) )  )  ->
      trans_rt Ptx  rt5 A ->
      trans_rt Ptx  rt' B ->
      wtt Ptx Ttx Gtx (re_Abs rt5 re) (rt_Fun rt5 rt')
          (sexp_anno  ( (sexp_abs ee) )  (sty_arrow  A B ))
 | wtt_ArrowE : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (rt':rt) (ee1 ee2:sexp) (rt5:rt),
     wtt Ptx Ttx Gtx re1 (rt_Fun rt5 rt') ee1 ->
     wtt Ptx Ttx Gtx re2 rt5 ee2 ->
     wtt Ptx Ttx Gtx (re_App re1 re2) rt' (sexp_app ee1 ee2)
 | wtt_Base : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (l:i) (re:rexp) (rt5:rt) (ee:sexp),
     wtt Ptx Ttx Gtx re rt5 ee ->
     wtt Ptx Ttx Gtx (re_SingleField l re) (rt_Record (r_SingleField l rt5)) (sexp_rcd l ee)
 | wtt_Empty : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wfp Ttx Ptx ->
     wtt Ptx Ttx Gtx re_Empty (rt_Record r_Empty) sexp_top
 | wtt_Merge : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (r1 r2:rtyp) (ee1 ee2:sexp),
     wtt Ptx Ttx Gtx re1 (rt_Record r1) ee1 ->
     wtt Ptx Ttx Gtx re2 (rt_Record r2) ee2 ->
     cmp Ttx r1 r2 ->
     wtt Ptx Ttx Gtx (re_Merge re1 re2) (rt_Record (r_Merge r1 r2)) (sexp_merge ee1 ee2)
 | wtt_Restr : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (r:rtyp) (ee:sexp) (rt5:rt) (A:sty),
     wtt Ptx Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     trans_r Ptx r A ->
     wtt Ptx Ttx Gtx (re_Res re l) (rt_Record r) (sexp_anno ee  A )
 | wtt_Select : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (rt5:rt) (ee:sexp) (r:rtyp) (A:sty),
     wtt Ptx Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     trans_rt Ptx rt5 A ->
     wtt Ptx Ttx Gtx (re_Selection re l) rt5 (sexp_proj  ( (sexp_anno ee (sty_rcd l  A )) )  l)

 | wtt_AllI : forall (L:vars) (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (R:rlist) (re:rexp) (rt5:rt) (ee:sexp) (A:sty),
     wfcl Ttx R ->
     trans_rlist Ptx R A ->
     ( forall a b , a \notin  L  ->
               b \notin L \u {{a}} ->
               wtt  ((a~b) ++ Ptx) (( a ~ R )++ Ttx )  Gtx
                    ( open_rexp_wrt_rtyp re (r_TyVar_f a) )
                    ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )
                    (open_sexp_wrt_sty  ( open_sexp_wrt_sty_rec 1 (sty_var_f a) ee) (sty_var_f b) ) ) ->
     wtt Ptx Ttx Gtx (re_ConTyAbs R re) (rt_ConQuan R rt5) (sexp_tabs  A (sexp_tabs A  ee))
 | wtt_AllE : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (r:rtyp) (rt5:rt) (ee:sexp) (R:rlist) (A B : sty),
     wtt Ptx Ttx Gtx re (rt_ConQuan R rt5) ee ->
     cmpList Ttx r R ->
     trans_r Ptx r A ->
     bot_trans_r Ptx r B ->
     wtt Ptx Ttx Gtx (re_ConTyApp re r)  (open_rt_wrt_rtyp  rt5   r )  (sexp_tapp (sexp_tapp ee A) B ).

Scheme trans_rt_ind' := Induction for trans_rt Sort Prop
  with trans_r_ind'  := Induction for trans_r  Sort Prop
  with trans_rlist_ind'  := Induction for trans_rlist Sort Prop.

Combined Scheme trans_rt_mutind from trans_rt_ind', trans_r_ind', trans_rlist_ind'.

Scheme wfrt_ind' := Induction for wfrt Sort Prop
  with wfr_ind'  := Induction for wfr  Sort Prop
  with wfcl_ind'  := Induction for wfcl Sort Prop.

Combined Scheme wfrt_mutind from wfrt_ind', wfr_ind', wfcl_ind'.

Scheme teq_ind' := Induction for teq  Sort Prop
  with ceq_ind'  := Induction for ceq Sort Prop.

Combined Scheme teq_ceq_mutind from teq_ind', ceq_ind'.

Inductive label_in_rtyp : i -> rtyp -> Prop :=
  | label_in_rtyp_rcd : forall l rt,
      label_in_rtyp l (r_SingleField l rt)
  | label_in_rtyp_merge_l : forall l rt1 rt2,
      label_in_rtyp l rt1 ->
      label_in_rtyp l (r_Merge rt1 rt2)
  | label_in_rtyp_merge_r : forall l rt1 rt2,
      label_in_rtyp l rt2 ->
      label_in_rtyp l (r_Merge rt1 rt2)

.

Inductive label_in_rlist : i -> rlist -> Prop :=
  | label_in_rlist_head : forall l r R,
      label_in_rtyp l r ->
      label_in_rlist l (R_Cons r R)
  | label_in_rlist_tail : forall l r R,
      label_in_rlist l R ->
      label_in_rlist l (R_Cons r R)
.

Inductive label_notin_rtyp : i -> rtyp -> Prop :=
  | label_notin_rtyp_bvar : forall l i,
      label_notin_rtyp l (r_TyVar_b i)
  | label_notin_rtyp_fvar : forall l x,
      label_notin_rtyp l (r_TyVar_f x)
  | label_notin_rypt_empty : forall l,
      label_notin_rtyp l r_Empty
  | label_notin_rypt_singlefield : forall l l2 rt,
      l <> l2 ->
      label_notin_rtyp l (r_SingleField l2 rt)
  | label_notin_rypt_merge : forall l r1 r2,
      label_notin_rtyp l r1 ->
      label_notin_rtyp l r2 ->
      label_notin_rtyp l  (r_Merge r1 r2)
.

Inductive tvar_in_rtyp : typvar -> rtyp -> Prop :=
  | tvar_in_rtyp_rcd : forall a,
      tvar_in_rtyp a (r_TyVar_f a )
  | tvar_in_rtyp_merge_a : forall a rt1 rt2,
      tvar_in_rtyp a rt1 ->
      tvar_in_rtyp a (r_Merge rt1 rt2)
  | tvar_in_rtyp_merge_r : forall a rt1 rt2,
      tvar_in_rtyp a rt2 ->
      tvar_in_rtyp a (r_Merge rt1 rt2)
.

Theorem translation_well_formed : forall Ptx Ttx Gtx e t E A DD GG,
    wtt Ptx Ttx Gtx e t E ->
    trans_Ttx Ptx Ttx DD ->
    trans_Gtx Ptx Gtx GG ->
    trans_rt Ptx t A ->
    has_type DD GG E Inf A.
