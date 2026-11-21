Require Export Metalib.Metatheory.
(** syntax *)
Definition tmvar := var. (*r variables *)
Definition covar := var. (*r coercion variables *)
Definition datacon := atom.
Definition const := atom.
Inductive relflag : Set :=  (*r relevance flag *)
 | Rel : relflag
 | Irrel : relflag.

Inductive role : Set :=  (*r Role *)
 | Nom : role
 | Rep : role.

Inductive appflag : Set :=  (*r applicative flag *)
 | Role (R:role)
 | Rho (rho:relflag).

Inductive App : Set :=
 | A_Tm (nu:appflag)
 | A_Co : App.

Inductive Apps : Set :=
 | A_nil : Apps
 | A_cons (App5:App) (Apps5:Apps).

Inductive constraint : Set :=  (*r props *)
 | Eq (a:tm) (b:tm) (A:tm) (R:role)
with tm : Set :=  (*r types and kinds *)
 | a_Star : tm
 | a_Var_b (_:nat)
 | a_Var_f (x:tmvar)
 | a_Abs (rho:relflag) (A:tm) (b:tm)
 | a_UAbs (rho:relflag) (b:tm)
 | a_App (a:tm) (nu:appflag) (b:tm)
 | a_Pi (rho:relflag) (A:tm) (B:tm)
 | a_CAbs (phi:constraint) (b:tm)
 | a_UCAbs (b:tm)
 | a_CApp (a:tm) (g:co)
 | a_CPi (phi:constraint) (B:tm)
 | a_Conv (a:tm) (R:role) (g:co)
 | a_Fam (F:const)
 | a_Bullet : tm
 | a_Pattern (R:role) (a:tm) (F:const) (Apps5:Apps) (b1:tm) (b2:tm)
 | a_DataCon (K:datacon)
 | a_Case (a:tm) (brs5:brs)
 | a_Sub (R:role) (a:tm)
 | a_Coerce : tm
 | a_SrcApp (a:tm) (b:tm)
with brs : Set :=  (*r case branches *)
 | br_None : brs
 | br_One (K:datacon) (a:tm) (brs5:brs)
with co : Set :=  (*r explicit coercions *)
 | g_Triv : co
 | g_Var_b (_:nat)
 | g_Var_f (c:covar)
 | g_Beta (a:tm) (b:tm)
 | g_Refl (a:tm)
 | g_Refl2 (a:tm) (b:tm) (g:co)
 | g_Sym (g:co)
 | g_Trans (g1:co) (g2:co)
 | g_Sub (g:co)
 | g_PiCong (rho:relflag) (R:role) (g1:co) (g2:co)
 | g_AbsCong (rho:relflag) (R:role) (g1:co) (g2:co)
 | g_AppCong (g1:co) (rho:relflag) (R:role) (g2:co)
 | g_PiFst (g:co)
 | g_CPiFst (g:co)
 | g_IsoSnd (g:co)
 | g_PiSnd (g1:co) (g2:co)
 | g_CPiCong (g1:co) (g3:co)
 | g_CAbsCong (g1:co) (g3:co) (g4:co)
 | g_CAppCong (g:co) (g1:co) (g2:co)
 | g_CPiSnd (g:co) (g1:co) (g2:co)
 | g_Cast (g1:co) (R:role) (g2:co)
 | g_EqCong (g1:co) (A:tm) (g2:co)
 | g_IsoConv (phi1:constraint) (phi2:constraint) (g:co)
 | g_Eta (a:tm)
 | g_Left (g:co) (g':co)
 | g_Right (g:co) (g':co).

Definition roles : Set := list role.

Inductive sort : Set :=  (*r binding classifier *)
 | Tm (A:tm)
 | Co (phi:constraint).

Inductive sig_sort : Set :=  (*r signature classifier *)
 | Cs (A:tm) (Rs:roles)
 | Ax (p:tm) (a:tm) (A:tm) (R:role) (Rs:roles).

Inductive pattern_arg : Set :=  (*r Pattern arguments *)
 | p_Tm (nu:appflag) (a:tm)
 | p_Co (g:co).

Definition role_context : Set := list ( atom * role ).

Definition context : Set := list ( atom * sort ).

Definition available_props : Type := atoms.

Definition sig : Set := list (atom * sig_sort).

Definition pattern_args : Set := list pattern_arg.

Fixpoint open_constraint_wrt_co_rec (k:nat) (g5:co) (phi5:constraint) : constraint :=
  match phi5 with
  | (Eq a b A R) => Eq (open_tm_wrt_co_rec k g5 a) (open_tm_wrt_co_rec k g5 b) (open_tm_wrt_co_rec k g5 A) R
end
with open_co_wrt_co_rec (k:nat) (g_5:co) (g__6:co) {struct g__6}: co :=
  match g__6 with
  | g_Triv => g_Triv
  | (g_Var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => g_Var_b nat
        | inleft (right _) => g_5
        | inright _ => g_Var_b (nat - 1)
      end
  | (g_Var_f c) => g_Var_f c
  | (g_Beta a b) => g_Beta (open_tm_wrt_co_rec k g_5 a) (open_tm_wrt_co_rec k g_5 b)
  | (g_Refl a) => g_Refl (open_tm_wrt_co_rec k g_5 a)
  | (g_Refl2 a b g) => g_Refl2 (open_tm_wrt_co_rec k g_5 a) (open_tm_wrt_co_rec k g_5 b) (open_co_wrt_co_rec k g_5 g)
  | (g_Sym g) => g_Sym (open_co_wrt_co_rec k g_5 g)
  | (g_Trans g1 g2) => g_Trans (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_Sub g) => g_Sub (open_co_wrt_co_rec k g_5 g)
  | (g_PiCong rho R g1 g2) => g_PiCong rho R (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_AbsCong rho R g1 g2) => g_AbsCong rho R (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_AppCong g1 rho R g2) => g_AppCong (open_co_wrt_co_rec k g_5 g1) rho R (open_co_wrt_co_rec k g_5 g2)
  | (g_PiFst g) => g_PiFst (open_co_wrt_co_rec k g_5 g)
  | (g_CPiFst g) => g_CPiFst (open_co_wrt_co_rec k g_5 g)
  | (g_IsoSnd g) => g_IsoSnd (open_co_wrt_co_rec k g_5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec (S k) g_5 g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec (S k) g_5 g3) (open_co_wrt_co_rec k g_5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_Cast g1 R g2) => g_Cast (open_co_wrt_co_rec k g_5 g1) R (open_co_wrt_co_rec k g_5 g2)
  | (g_EqCong g1 A g2) => g_EqCong (open_co_wrt_co_rec k g_5 g1) (open_tm_wrt_co_rec k g_5 A) (open_co_wrt_co_rec k g_5 g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (open_constraint_wrt_co_rec k g_5 phi1) (open_constraint_wrt_co_rec k g_5 phi2) (open_co_wrt_co_rec k g_5 g)
  | (g_Eta a) => g_Eta (open_tm_wrt_co_rec k g_5 a)
  | (g_Left g g') => g_Left (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g')
  | (g_Right g g') => g_Right (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g')
end
with open_brs_wrt_co_rec (k:nat) (g5:co) (brs_6:brs) {struct brs_6}: brs :=
  match brs_6 with
  | br_None => br_None
  | (br_One K a brs5) => br_One K (open_tm_wrt_co_rec k g5 a) (open_brs_wrt_co_rec k g5 brs5)
end
with open_tm_wrt_co_rec (k:nat) (g5:co) (a5:tm) {struct a5}: tm :=
  match a5 with
  | a_Star => a_Star
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Abs rho A b) => a_Abs rho (open_tm_wrt_co_rec k g5 A) (open_tm_wrt_co_rec k g5 b)
  | (a_UAbs rho b) => a_UAbs rho (open_tm_wrt_co_rec k g5 b)
  | (a_App a nu b) => a_App (open_tm_wrt_co_rec k g5 a) nu (open_tm_wrt_co_rec k g5 b)
  | (a_Pi rho A B) => a_Pi rho (open_tm_wrt_co_rec k g5 A) (open_tm_wrt_co_rec k g5 B)
  | (a_CAbs phi b) => a_CAbs (open_constraint_wrt_co_rec k g5 phi) (open_tm_wrt_co_rec (S k) g5 b)
  | (a_UCAbs b) => a_UCAbs (open_tm_wrt_co_rec (S k) g5 b)
  | (a_CApp a g) => a_CApp (open_tm_wrt_co_rec k g5 a) (open_co_wrt_co_rec k g5 g)
  | (a_CPi phi B) => a_CPi (open_constraint_wrt_co_rec k g5 phi) (open_tm_wrt_co_rec (S k) g5 B)
  | (a_Conv a R g) => a_Conv (open_tm_wrt_co_rec k g5 a) R (open_co_wrt_co_rec k g5 g)
  | (a_Fam F) => a_Fam F
  | a_Bullet => a_Bullet
  | (a_Pattern R a F Apps5 b1 b2) => a_Pattern R (open_tm_wrt_co_rec k g5 a) F Apps5 (open_tm_wrt_co_rec k g5 b1) (open_tm_wrt_co_rec k g5 b2)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (open_tm_wrt_co_rec k g5 a) (open_brs_wrt_co_rec k g5 brs5)
  | (a_Sub R a) => a_Sub R (open_tm_wrt_co_rec k g5 a)
  | a_Coerce => a_Coerce
  | (a_SrcApp a b) => a_SrcApp (open_tm_wrt_co_rec k g5 a) (open_tm_wrt_co_rec k g5 b)
end.

Fixpoint open_tm_wrt_tm_rec (k:nat) (a5:tm) (a_6:tm) {struct a_6}: tm :=
  match a_6 with
  | a_Star => a_Star
  | (a_Var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => a5
        | inright _ => a_Var_b (nat - 1)
      end
  | (a_Var_f x) => a_Var_f x
  | (a_Abs rho A b) => a_Abs rho (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_UAbs rho b) => a_UAbs rho (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_App a nu b) => a_App (open_tm_wrt_tm_rec k a5 a) nu (open_tm_wrt_tm_rec k a5 b)
  | (a_Pi rho A B) => a_Pi rho (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_CAbs phi b) => a_CAbs (open_constraint_wrt_tm_rec k a5 phi) (open_tm_wrt_tm_rec k a5 b)
  | (a_UCAbs b) => a_UCAbs (open_tm_wrt_tm_rec k a5 b)
  | (a_CApp a g) => a_CApp (open_tm_wrt_tm_rec k a5 a) (open_co_wrt_tm_rec k a5 g)
  | (a_CPi phi B) => a_CPi (open_constraint_wrt_tm_rec k a5 phi) (open_tm_wrt_tm_rec k a5 B)
  | (a_Conv a R g) => a_Conv (open_tm_wrt_tm_rec k a5 a) R (open_co_wrt_tm_rec k a5 g)
  | (a_Fam F) => a_Fam F
  | a_Bullet => a_Bullet
  | (a_Pattern R a F Apps5 b1 b2) => a_Pattern R (open_tm_wrt_tm_rec k a5 a) F Apps5 (open_tm_wrt_tm_rec k a5 b1) (open_tm_wrt_tm_rec k a5 b2)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (open_tm_wrt_tm_rec k a5 a) (open_brs_wrt_tm_rec k a5 brs5)
  | (a_Sub R a) => a_Sub R (open_tm_wrt_tm_rec k a5 a)
  | a_Coerce => a_Coerce
  | (a_SrcApp a b) => a_SrcApp (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
end
with open_constraint_wrt_tm_rec (k:nat) (a5:tm) (phi5:constraint) : constraint :=
  match phi5 with
  | (Eq a b A R) => Eq (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) (open_tm_wrt_tm_rec k a5 A) R
end
with open_co_wrt_tm_rec (k:nat) (a5:tm) (g_5:co) {struct g_5}: co :=
  match g_5 with
  | g_Triv => g_Triv
  | (g_Var_b nat) => g_Var_b nat
  | (g_Var_f c) => g_Var_f c
  | (g_Beta a b) => g_Beta (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
  | (g_Refl a) => g_Refl (open_tm_wrt_tm_rec k a5 a)
  | (g_Refl2 a b g) => g_Refl2 (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) (open_co_wrt_tm_rec k a5 g)
  | (g_Sym g) => g_Sym (open_co_wrt_tm_rec k a5 g)
  | (g_Trans g1 g2) => g_Trans (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_Sub g) => g_Sub (open_co_wrt_tm_rec k a5 g)
  | (g_PiCong rho R g1 g2) => g_PiCong rho R (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec (S k) a5 g2)
  | (g_AbsCong rho R g1 g2) => g_AbsCong rho R (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec (S k) a5 g2)
  | (g_AppCong g1 rho R g2) => g_AppCong (open_co_wrt_tm_rec k a5 g1) rho R (open_co_wrt_tm_rec k a5 g2)
  | (g_PiFst g) => g_PiFst (open_co_wrt_tm_rec k a5 g)
  | (g_CPiFst g) => g_CPiFst (open_co_wrt_tm_rec k a5 g)
  | (g_IsoSnd g) => g_IsoSnd (open_co_wrt_tm_rec k a5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g3) (open_co_wrt_tm_rec k a5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_Cast g1 R g2) => g_Cast (open_co_wrt_tm_rec k a5 g1) R (open_co_wrt_tm_rec k a5 g2)
  | (g_EqCong g1 A g2) => g_EqCong (open_co_wrt_tm_rec k a5 g1) (open_tm_wrt_tm_rec k a5 A) (open_co_wrt_tm_rec k a5 g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (open_constraint_wrt_tm_rec k a5 phi1) (open_constraint_wrt_tm_rec k a5 phi2) (open_co_wrt_tm_rec k a5 g)
  | (g_Eta a) => g_Eta (open_tm_wrt_tm_rec k a5 a)
  | (g_Left g g') => g_Left (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g')
  | (g_Right g g') => g_Right (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g')
end
with open_brs_wrt_tm_rec (k:nat) (a5:tm) (brs_6:brs) {struct brs_6}: brs :=
  match brs_6 with
  | br_None => br_None
  | (br_One K a brs5) => br_One K (open_tm_wrt_tm_rec k a5 a) (open_brs_wrt_tm_rec k a5 brs5)
end.

Definition open_co_wrt_tm a5 g_5 := open_co_wrt_tm_rec 0 g_5 a5.

Definition open_co_wrt_co g_5 g__6 := open_co_wrt_co_rec 0 g__6 g_5.

Definition open_tm_wrt_tm a5 a_6 := open_tm_wrt_tm_rec 0 a_6 a5.

Definition open_tm_wrt_co g5 a5 := open_tm_wrt_co_rec 0 a5 g5.

Inductive lc_co : co -> Prop :=    (* defn lc_co *)
 | lc_g_Triv :
     (lc_co g_Triv)
 | lc_g_Var_f : forall (c:covar),
     (lc_co (g_Var_f c))
 | lc_g_Beta : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_co (g_Beta a b))
 | lc_g_Refl : forall (a:tm),
     (lc_tm a) ->
     (lc_co (g_Refl a))
 | lc_g_Refl2 : forall (a b:tm) (g:co),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_co g) ->
     (lc_co (g_Refl2 a b g))
 | lc_g_Sym : forall (g:co),
     (lc_co g) ->
     (lc_co (g_Sym g))
 | lc_g_Trans : forall (g1 g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_Trans g1 g2))
 | lc_g_Sub : forall (g:co),
     (lc_co g) ->
     (lc_co (g_Sub g))
 | lc_g_PiCong : forall (rho:relflag) (R:role) (g1 g2:co),
     (lc_co g1) ->
      ( forall x , lc_co  ( open_co_wrt_tm g2 (a_Var_f x) )  )  ->
     (lc_co (g_PiCong rho R g1 g2))
 | lc_g_AbsCong : forall (rho:relflag) (R:role) (g1 g2:co),
     (lc_co g1) ->
      ( forall x , lc_co  ( open_co_wrt_tm g2 (a_Var_f x) )  )  ->
     (lc_co (g_AbsCong rho R g1 g2))
 | lc_g_AppCong : forall (g1:co) (rho:relflag) (R:role) (g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_AppCong g1 rho R g2))
 | lc_g_PiFst : forall (g:co),
     (lc_co g) ->
     (lc_co (g_PiFst g))
 | lc_g_CPiFst : forall (g:co),
     (lc_co g) ->
     (lc_co (g_CPiFst g))
 | lc_g_IsoSnd : forall (g:co),
     (lc_co g) ->
     (lc_co (g_IsoSnd g))
 | lc_g_PiSnd : forall (g1 g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_PiSnd g1 g2))
 | lc_g_CPiCong : forall (g1 g3:co),
     (lc_co g1) ->
      ( forall c , lc_co  ( open_co_wrt_co g3 (g_Var_f c) )  )  ->
     (lc_co (g_CPiCong g1 g3))
 | lc_g_CAbsCong : forall (g1 g3 g4:co),
     (lc_co g1) ->
      ( forall c , lc_co  ( open_co_wrt_co g3 (g_Var_f c) )  )  ->
     (lc_co g4) ->
     (lc_co (g_CAbsCong g1 g3 g4))
 | lc_g_CAppCong : forall (g g1 g2:co),
     (lc_co g) ->
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_CAppCong g g1 g2))
 | lc_g_CPiSnd : forall (g g1 g2:co),
     (lc_co g) ->
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_CPiSnd g g1 g2))
 | lc_g_Cast : forall (g1:co) (R:role) (g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_Cast g1 R g2))
 | lc_g_EqCong : forall (g1:co) (A:tm) (g2:co),
     (lc_co g1) ->
     (lc_tm A) ->
     (lc_co g2) ->
     (lc_co (g_EqCong g1 A g2))
 | lc_g_IsoConv : forall (phi1 phi2:constraint) (g:co),
     (lc_constraint phi1) ->
     (lc_constraint phi2) ->
     (lc_co g) ->
     (lc_co (g_IsoConv phi1 phi2 g))
 | lc_g_Eta : forall (a:tm),
     (lc_tm a) ->
     (lc_co (g_Eta a))
 | lc_g_Left : forall (g g':co),
     (lc_co g) ->
     (lc_co g') ->
     (lc_co (g_Left g g'))
 | lc_g_Right : forall (g g':co),
     (lc_co g) ->
     (lc_co g') ->
     (lc_co (g_Right g g'))
with lc_brs : brs -> Prop :=    (* defn lc_brs *)
 | lc_br_None :
     (lc_brs br_None)
 | lc_br_One : forall (K:datacon) (a:tm) (brs5:brs),
     (lc_tm a) ->
     (lc_brs brs5) ->
     (lc_brs (br_One K a brs5))
with lc_tm : tm -> Prop :=    (* defn lc_tm *)
 | lc_a_Star :
     (lc_tm a_Star)
 | lc_a_Var_f : forall (x:tmvar),
     (lc_tm (a_Var_f x))
 | lc_a_Abs : forall (rho:relflag) (A b:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_Abs rho A b))
 | lc_a_UAbs : forall (rho:relflag) (b:tm),
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_UAbs rho b))
 | lc_a_App : forall (a:tm) (nu:appflag) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a nu b))
 | lc_a_Pi : forall (rho:relflag) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi rho A B))
 | lc_a_CAbs : forall (phi:constraint) (b:tm),
     (lc_constraint phi) ->
      ( forall c , lc_tm  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     (lc_tm (a_CAbs phi b))
 | lc_a_UCAbs : forall (b:tm),
      ( forall c , lc_tm  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     (lc_tm (a_UCAbs b))
 | lc_a_CApp : forall (a:tm) (g:co),
     (lc_tm a) ->
     (lc_co g) ->
     (lc_tm (a_CApp a g))
 | lc_a_CPi : forall (phi:constraint) (B:tm),
     (lc_constraint phi) ->
      ( forall c , lc_tm  ( open_tm_wrt_co B (g_Var_f c) )  )  ->
     (lc_tm (a_CPi phi B))
 | lc_a_Conv : forall (a:tm) (R:role) (g:co),
     (lc_tm a) ->
     (lc_co g) ->
     (lc_tm (a_Conv a R g))
 | lc_a_Fam : forall (F:const),
     (lc_tm (a_Fam F))
 | lc_a_Bullet :
     (lc_tm a_Bullet)
 | lc_a_Pattern : forall (R:role) (a:tm) (F:const) (Apps5:Apps) (b1 b2:tm),
     (lc_tm a) ->
     (lc_tm b1) ->
     (lc_tm b2) ->
     (lc_tm (a_Pattern R a F Apps5 b1 b2))
 | lc_a_DataCon : forall (K:datacon),
     (lc_tm (a_DataCon K))
 | lc_a_Case : forall (a:tm) (brs5:brs),
     (lc_tm a) ->
     (lc_brs brs5) ->
     (lc_tm (a_Case a brs5))
 | lc_a_Sub : forall (R:role) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Sub R a))
 | lc_a_Coerce :
     (lc_tm a_Coerce)
 | lc_a_SrcApp : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_SrcApp a b))
with lc_constraint : constraint -> Prop :=    (* defn lc_constraint *)
 | lc_Eq : forall (a b A:tm) (R:role),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm A) ->
     (lc_constraint (Eq a b A R)).

(* defns LC_sort *)
Fixpoint fv_tm_tm_co (g_5:co) : vars :=
  match g_5 with
  | g_Triv => {}
  | (g_Var_b nat) => {}
  | (g_Var_f c) => {}
  | (g_Beta a b) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b)
  | (g_Refl a) => (fv_tm_tm_tm a)
  | (g_Refl2 a b g) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b) \u (fv_tm_tm_co g)
  | (g_Sym g) => (fv_tm_tm_co g)
  | (g_Trans g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_Sub g) => (fv_tm_tm_co g)
  | (g_PiCong rho R g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_AbsCong rho R g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_AppCong g1 rho R g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_PiFst g) => (fv_tm_tm_co g)
  | (g_CPiFst g) => (fv_tm_tm_co g)
  | (g_IsoSnd g) => (fv_tm_tm_co g)
  | (g_PiSnd g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_CPiCong g1 g3) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g3)
  | (g_CAbsCong g1 g3 g4) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g3) \u (fv_tm_tm_co g4)
  | (g_CAppCong g g1 g2) => (fv_tm_tm_co g) \u (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_CPiSnd g g1 g2) => (fv_tm_tm_co g) \u (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_Cast g1 R g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_EqCong g1 A g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_tm A) \u (fv_tm_tm_co g2)
  | (g_IsoConv phi1 phi2 g) => (fv_tm_tm_constraint phi1) \u (fv_tm_tm_constraint phi2) \u (fv_tm_tm_co g)
  | (g_Eta a) => (fv_tm_tm_tm a)
  | (g_Left g g') => (fv_tm_tm_co g) \u (fv_tm_tm_co g')
  | (g_Right g g') => (fv_tm_tm_co g) \u (fv_tm_tm_co g')
end
with fv_tm_tm_brs (brs_6:brs) : vars :=
  match brs_6 with
  | br_None => {}
  | (br_One K a brs5) => (fv_tm_tm_tm a) \u (fv_tm_tm_brs brs5)
end
with fv_tm_tm_tm (a5:tm) : vars :=
  match a5 with
  | a_Star => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_Abs rho A b) => (fv_tm_tm_tm A) \u (fv_tm_tm_tm b)
  | (a_UAbs rho b) => (fv_tm_tm_tm b)
  | (a_App a nu b) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b)
  | (a_Pi rho A B) => (fv_tm_tm_tm A) \u (fv_tm_tm_tm B)
  | (a_CAbs phi b) => (fv_tm_tm_constraint phi) \u (fv_tm_tm_tm b)
  | (a_UCAbs b) => (fv_tm_tm_tm b)
  | (a_CApp a g) => (fv_tm_tm_tm a) \u (fv_tm_tm_co g)
  | (a_CPi phi B) => (fv_tm_tm_constraint phi) \u (fv_tm_tm_tm B)
  | (a_Conv a R g) => (fv_tm_tm_tm a) \u (fv_tm_tm_co g)
  | (a_Fam F) => {}
  | a_Bullet => {}
  | (a_Pattern R a F Apps5 b1 b2) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b1) \u (fv_tm_tm_tm b2)
  | (a_DataCon K) => {}
  | (a_Case a brs5) => (fv_tm_tm_tm a) \u (fv_tm_tm_brs brs5)
  | (a_Sub R a) => (fv_tm_tm_tm a)
  | a_Coerce => {}
  | (a_SrcApp a b) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b)
end
with fv_tm_tm_constraint (phi5:constraint) : vars :=
  match phi5 with
  | (Eq a b A R) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b) \u (fv_tm_tm_tm A)
end.

Fixpoint tm_subst_tm_co (a5:tm) (x5:tmvar) (g_5:co) {struct g_5} : co :=
  match g_5 with
  | g_Triv => g_Triv
  | (g_Var_b nat) => g_Var_b nat
  | (g_Var_f c) => g_Var_f c
  | (g_Beta a b) => g_Beta (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b)
  | (g_Refl a) => g_Refl (tm_subst_tm_tm a5 x5 a)
  | (g_Refl2 a b g) => g_Refl2 (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b) (tm_subst_tm_co a5 x5 g)
  | (g_Sym g) => g_Sym (tm_subst_tm_co a5 x5 g)
  | (g_Trans g1 g2) => g_Trans (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_Sub g) => g_Sub (tm_subst_tm_co a5 x5 g)
  | (g_PiCong rho R g1 g2) => g_PiCong rho R (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_AbsCong rho R g1 g2) => g_AbsCong rho R (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_AppCong g1 rho R g2) => g_AppCong (tm_subst_tm_co a5 x5 g1) rho R (tm_subst_tm_co a5 x5 g2)
  | (g_PiFst g) => g_PiFst (tm_subst_tm_co a5 x5 g)
  | (g_CPiFst g) => g_CPiFst (tm_subst_tm_co a5 x5 g)
  | (g_IsoSnd g) => g_IsoSnd (tm_subst_tm_co a5 x5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g3) (tm_subst_tm_co a5 x5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_Cast g1 R g2) => g_Cast (tm_subst_tm_co a5 x5 g1) R (tm_subst_tm_co a5 x5 g2)
  | (g_EqCong g1 A g2) => g_EqCong (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_co a5 x5 g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (tm_subst_tm_constraint a5 x5 phi1) (tm_subst_tm_constraint a5 x5 phi2) (tm_subst_tm_co a5 x5 g)
  | (g_Eta a) => g_Eta (tm_subst_tm_tm a5 x5 a)
  | (g_Left g g') => g_Left (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g')
  | (g_Right g g') => g_Right (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g')
end
with tm_subst_tm_brs (a5:tm) (x5:tmvar) (brs_6:brs) {struct brs_6} : brs :=
  match brs_6 with
  | br_None => br_None
  | (br_One K a brs5) => br_One K (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_brs a5 x5 brs5)
end
with tm_subst_tm_tm (a5:tm) (x5:tmvar) (a_6:tm) {struct a_6} : tm :=
  match a_6 with
  | a_Star => a_Star
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => (if eq_var x x5 then a5 else (a_Var_f x))
  | (a_Abs rho A b) => a_Abs rho (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_tm a5 x5 b)
  | (a_UAbs rho b) => a_UAbs rho (tm_subst_tm_tm a5 x5 b)
  | (a_App a nu b) => a_App (tm_subst_tm_tm a5 x5 a) nu (tm_subst_tm_tm a5 x5 b)
  | (a_Pi rho A B) => a_Pi rho (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_tm a5 x5 B)
  | (a_CAbs phi b) => a_CAbs (tm_subst_tm_constraint a5 x5 phi) (tm_subst_tm_tm a5 x5 b)
  | (a_UCAbs b) => a_UCAbs (tm_subst_tm_tm a5 x5 b)
  | (a_CApp a g) => a_CApp (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_co a5 x5 g)
  | (a_CPi phi B) => a_CPi (tm_subst_tm_constraint a5 x5 phi) (tm_subst_tm_tm a5 x5 B)
  | (a_Conv a R g) => a_Conv (tm_subst_tm_tm a5 x5 a) R (tm_subst_tm_co a5 x5 g)
  | (a_Fam F) => a_Fam F
  | a_Bullet => a_Bullet
  | (a_Pattern R a F Apps5 b1 b2) => a_Pattern R (tm_subst_tm_tm a5 x5 a) F Apps5 (tm_subst_tm_tm a5 x5 b1) (tm_subst_tm_tm a5 x5 b2)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_brs a5 x5 brs5)
  | (a_Sub R a) => a_Sub R (tm_subst_tm_tm a5 x5 a)
  | a_Coerce => a_Coerce
  | (a_SrcApp a b) => a_SrcApp (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b)
end
with tm_subst_tm_constraint (a5:tm) (x5:tmvar) (phi5:constraint) {struct phi5} : constraint :=
  match phi5 with
  | (Eq a b A R) => Eq (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b) (tm_subst_tm_tm a5 x5 A) R
end.

Definition min (r1 : role) (r2 : role) : role :=
  match r1 , r2 with
  | Nom, _   => Nom
  | _  , Nom => Nom
  | Rep, Rep => Rep
  end.

Definition param (r1 : role) (r2 : role) := min r1 r2.

Definition app_role (rr : appflag) (r1 : role) : role :=
  match rr with
  | Rho _ => Nom
  | Role r => param r r1
  end.

Fixpoint apply_pattern_args (a : tm) (args : pattern_args) : tm :=
  match args with
  | nil => a
  | (p_Tm nu b :: rest) =>
    apply_pattern_args (a_App a nu b) rest
  | (p_Co g :: rest) =>
    apply_pattern_args (a_CApp a g) rest
  end.

Fixpoint A_snoc (xs : Apps) (x : App)  : Apps :=
  match xs with
  | A_nil => A_cons x A_nil
  | A_cons y ys => (A_cons y (A_snoc ys x))
  end.

Definition Star : atom := proj1_sig (atom_fresh empty).
Definition Fix : atom := proj1_sig (atom_fresh (singleton Star)).
Definition FixVar1 : atom := proj1_sig (atom_fresh (singleton Star \u singleton Fix)).
Definition FixVar2 : atom := proj1_sig (atom_fresh (singleton Star \u singleton Fix \u singleton FixVar1)).

Definition FixPat : tm := a_App (a_App (a_Fam Fix) (Rho Irrel) a_Bullet) (Role Nom) (a_Var_f FixVar2).

Definition FixDef : tm := a_App (a_Var_f FixVar2) (Rho Rel)
                              (a_App (a_App (a_Fam Fix) (Rho Irrel) a_Bullet) (Rho Rel) (a_Var_f FixVar2)).

Definition FixTy : tm  := a_Pi Irrel a_Star
                             (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1)) (a_Var_b 1)).

Definition toplevel : sig := Fix ~ Ax FixPat FixDef FixTy Nom [Nom].

(** definitions *)

(* defns JSubRole *)
Inductive SubRole : role -> role -> Prop :=    (* defn SubRole *)
 | NomBot : forall (R:role),
     SubRole Nom R
 | RepTop : forall (R:role),
     SubRole R Rep
 | Refl : forall (R:role),
     SubRole R R
 | Trans : forall (R1 R3 R2:role),
     SubRole R1 R2 ->
     SubRole R2 R3 ->
     SubRole R1 R3.

(* defns JRolePath *)
Inductive RolePath : tm -> roles -> Prop :=    (* defn RolePath *)
 | RolePath_AbsConst : forall (F:const) (Rs:roles) (A:tm),
      binds  F  ( (Cs A Rs) )   toplevel   ->
     RolePath (a_Fam F) Rs
 | RolePath_Const : forall (F:const) (Rs:roles) (p a A:tm) (R1:role),
      binds  F  ( (Ax p a A R1 Rs) )   toplevel   ->
     RolePath (a_Fam F) Rs
 | RolePath_TApp : forall (a:tm) (R1:role) (b:tm) (Rs:roles),
     lc_tm b ->
     RolePath a  ( R1 :: Rs )  ->
     RolePath (a_App a (Role R1) b) Rs
 | RolePath_App : forall (a b:tm) (Rs:roles),
     lc_tm b ->
     RolePath a  ( Nom :: Rs )  ->
     RolePath (a_App a (Rho Rel) b) Rs
 | RolePath_IApp : forall (a:tm) (Rs:roles),
     RolePath a Rs ->
     RolePath (a_App a (Rho Irrel) a_Bullet) Rs
 | RolePath_CApp : forall (a:tm) (Rs:roles),
     RolePath a Rs ->
     RolePath (a_CApp a g_Triv) Rs.

(* defns JAppsPath *)
Inductive AppsPath : role -> tm -> const -> Apps -> Prop :=    (* defn AppsPath *)
 | AppsPath_AbsConst : forall (R:role) (F:const) (A:tm) (Rs:roles),
      binds  F  ( (Cs A Rs) )   toplevel   ->
     AppsPath R (a_Fam F) F A_nil
 | AppsPath_Const : forall (R:role) (F:const) (p a A:tm) (R1:role) (Rs:roles),
      binds  F  ( (Ax p a A R1 Rs) )   toplevel   ->
      not (  ( SubRole R1 R )  )  ->
     AppsPath R (a_Fam F) F A_nil
 | AppsPath_App : forall (R:role) (a:tm) (R1:role) (b':tm) (F:const) (Apps5:Apps),
     lc_tm b' ->
     AppsPath R a F Apps5 ->
     AppsPath R  ( (a_App a (Role R1) b') )  F  (  (A_snoc  Apps5   (A_Tm (Role R1)) )  )
 | AppsPath_IApp : forall (R:role) (a b:tm) (F:const) (Apps5:Apps),
     lc_tm b ->
     AppsPath R a F Apps5 ->
     AppsPath R  ( (a_App a (Rho Irrel) b) )  F  (  (A_snoc  Apps5   (A_Tm (Rho Irrel)) )  )
 | AppsPath_CApp : forall (R:role) (a:tm) (F:const) (Apps5:Apps),
     AppsPath R a F Apps5 ->
     AppsPath R  ( (a_CApp a g_Triv) )  F  (  (A_snoc  Apps5   A_Co )  ) .

(* defns JSat *)
Inductive AppRoles : Apps -> roles -> Prop :=    (* defn AppRoles *)
 | AR_nil :
     AppRoles A_nil  nil
 | AR_consTApp : forall (R1:role) (Apps5:Apps) (Rs:roles),
     AppRoles Apps5 Rs ->
     AppRoles (A_cons (A_Tm (Role R1)) Apps5)  ( R1 :: Rs )
 | AR_consApp : forall (Apps5:Apps) (Rs:roles),
     AppRoles Apps5 Rs ->
     AppRoles (A_cons (A_Tm (Rho Rel)) Apps5)  ( Nom :: Rs )
 | AR_consIApp : forall (Apps5:Apps) (Rs:roles),
     AppRoles Apps5 Rs ->
     AppRoles (A_cons (A_Tm (Rho Irrel)) Apps5) Rs
 | AR_consCApp : forall (Apps5:Apps) (Rs:roles),
     AppRoles Apps5 Rs ->
     AppRoles (A_cons A_Co Apps5) Rs
with SatApp : const -> Apps -> Prop :=    (* defn SatApp *)
 | Sat_Const : forall (F:const) (Apps5:Apps) (A:tm) (Rs:roles),
      binds  F  ( (Cs A Rs) )   toplevel   ->
     AppRoles Apps5 Rs ->
     SatApp F Apps5
 | Sat_Axiom : forall (F:const) (Apps5:Apps) (p a0 A1:tm) (R1:role) (Rs:roles),
      binds  F  ( (Ax p a0 A1 R1 Rs) )   toplevel   ->
      not (  ( SubRole R1 Nom )  )  ->
     AppRoles Apps5 Rs ->
     SatApp F Apps5.

(* defns JPatCtx *)
Inductive Rename : tm -> tm -> tm -> tm -> available_props -> available_props -> Prop :=    (* defn Rename *)
 | Rename_Base : forall (F:const) (a:tm) (D:available_props),
     lc_tm a ->
     Rename (a_Fam F) a (a_Fam F) a D  AtomSetImpl.empty
 | Rename_AppRel : forall (p1:tm) (R:role) (x:tmvar) (a1 p2:tm) (y:tmvar) (a2:tm) (D D':available_props),
     Rename p1 a1 p2 a2 D D' ->
      ~ AtomSetImpl.In  y    (  ( D  `union`  D' )  )   ->
     Rename  ( (a_App p1 (Role R) (a_Var_f x)) )  a1  ( (a_App p2 (Role R) (a_Var_f y)) )   (  (tm_subst_tm_tm  (a_Var_f y)   x   a2 )  )  D  (  (singleton  y  \u  D' )  )
 | Rename_AppIrrel : forall (p1 a1 p2 a2:tm) (D D':available_props),
     Rename p1 a1 p2 a2 D D' ->
     Rename  ( (a_App p1 (Rho Irrel) a_Bullet) )  a1  ( (a_App p2 (Rho Irrel) a_Bullet) )  a2 D D'
 | Rename_CApp : forall (p1 a1 p2 a2:tm) (D D':available_props),
     Rename p1 a1 p2 a2 D D' ->
     Rename  ( (a_CApp p1 g_Triv) )  a1  ( (a_CApp p2 g_Triv) )  a2 D D'.

(* defns JMatchSubst *)
Inductive MatchSubst : tm -> tm -> tm -> tm -> Prop :=    (* defn MatchSubst *)
 | MatchSubst_Const : forall (F:const) (b:tm),
     lc_tm b ->
     MatchSubst (a_Fam F) (a_Fam F) b b
 | MatchSubst_AppRelR : forall (a1:tm) (R:role) (a p1:tm) (x:tmvar) (b1 b2:tm),
     lc_tm a ->
     MatchSubst a1 p1 b1 b2 ->
     MatchSubst  ( (a_App a1 (Role R) a) )   ( (a_App p1 (Role R) (a_Var_f x)) )  b1  (  (tm_subst_tm_tm  a   x   b2 )  )
 | MatchSubst_AppIrrel : forall (a1 a p1 b1 b2:tm),
     lc_tm a ->
     MatchSubst a1 p1 b1 b2 ->
     MatchSubst  ( (a_App a1 (Rho Irrel) a) )   ( (a_App p1 (Rho Irrel) a_Bullet) )  b1 b2
 | MatchSubst_CApp : forall (a1 a2 b1 b2:tm),
     MatchSubst a1 a2 b1 b2 ->
     MatchSubst  ( (a_CApp a1 g_Triv) )   ( (a_CApp a2 g_Triv) )  b1 b2.

(* defns JIsPattern *)
Inductive tm_pattern_agree : tm -> tm -> Prop :=    (* defn tm_pattern_agree *)
 | tm_pattern_agree_Const : forall (F:const),
     tm_pattern_agree (a_Fam F) (a_Fam F)
 | tm_pattern_agree_AppRelR : forall (a1:tm) (R:role) (a2 p1:tm) (x:tmvar),
     lc_tm a2 ->
     tm_pattern_agree a1 p1 ->
     tm_pattern_agree  ( (a_App a1 (Role R) a2) )   ( (a_App p1 (Role R) (a_Var_f x)) )
 | tm_pattern_agree_AppIrrel : forall (a1 a p1:tm),
     lc_tm a ->
     tm_pattern_agree a1 p1 ->
     tm_pattern_agree  ( (a_App a1 (Rho Irrel) a) )   ( (a_App p1 (Rho Irrel) a_Bullet) )
 | tm_pattern_agree_CApp : forall (a1 p1:tm),
     tm_pattern_agree a1 p1 ->
     tm_pattern_agree  ( (a_CApp a1 g_Triv) )   ( (a_CApp p1 g_Triv) ) .

(* defns JTmSubPatternAgree *)
Inductive tm_subpattern_agree : tm -> tm -> Prop :=    (* defn tm_subpattern_agree *)
 | tm_subpattern_agree_Base : forall (a p:tm),
     tm_pattern_agree a p ->
     tm_subpattern_agree a p
 | tm_subpattern_agree_AppRelR : forall (a p:tm) (R:role) (x:tmvar),
     tm_subpattern_agree a p ->
     tm_subpattern_agree a  ( (a_App p (Role R) (a_Var_f x)) )
 | tm_subpattern_agree_AppIrrel : forall (a p:tm),
     tm_subpattern_agree a p ->
     tm_subpattern_agree a  ( (a_App p (Rho Irrel) a_Bullet) )
 | tm_subpattern_agree_CAppp : forall (a p:tm),
     tm_subpattern_agree a p ->
     tm_subpattern_agree a  ( (a_CApp p g_Triv) ) .

(* defns JSubTmPatternAgree *)
Inductive subtm_pattern_agree : tm -> tm -> Prop :=    (* defn subtm_pattern_agree *)
 | subtm_pattern_agree_Base : forall (a p:tm),
     tm_pattern_agree a p ->
     subtm_pattern_agree a p
 | subtm_pattern_agree_App : forall (a:tm) (nu:appflag) (a2 p:tm),
     lc_tm a2 ->
     subtm_pattern_agree a p ->
     subtm_pattern_agree (a_App a nu a2) p
 | subtm_pattern_agree_CAppp : forall (a p:tm),
     subtm_pattern_agree a p ->
     subtm_pattern_agree (a_CApp a g_Triv) p.

(* defns JValuePath *)
Inductive ValuePath : tm -> const -> Prop :=    (* defn ValuePath *)
 | ValuePath_AbsConst : forall (F:const) (A:tm) (Rs:roles),
      binds  F  ( (Cs A Rs) )   toplevel   ->
     ValuePath (a_Fam F) F
 | ValuePath_Const : forall (F:const) (p a A:tm) (R1:role) (Rs:roles),
      binds  F  ( (Ax p a A R1 Rs) )   toplevel   ->
     ValuePath (a_Fam F) F
 | ValuePath_App : forall (a:tm) (nu:appflag) (b':tm) (F:const),
     lc_tm b' ->
     ValuePath a F ->
     ValuePath  ( (a_App a nu b') )  F
 | ValuePath_CApp : forall (a:tm) (F:const),
     ValuePath a F ->
     ValuePath  ( (a_CApp a g_Triv) )  F.

(* defns JCasePath *)
Inductive CasePath : role -> tm -> const -> Prop :=    (* defn CasePath *)
 | CasePath_AbsConst : forall (R:role) (a:tm) (F:const) (A:tm) (Rs:roles),
     ValuePath a F ->
      binds  F  ( (Cs A Rs) )   toplevel   ->
     CasePath R a F
 | CasePath_Const : forall (R:role) (a:tm) (F:const) (p b A:tm) (R1:role) (Rs:roles),
     ValuePath a F ->
      binds  F  ( (Ax p b A R1 Rs) )   toplevel   ->
      not (  ( SubRole R1 R )  )  ->
     CasePath R a F
 | CasePath_UnMatch : forall (R:role) (a:tm) (F:const) (p b A:tm) (R1:role) (Rs:roles),
     ValuePath a F ->
      binds  F  ( (Ax p b A R1 Rs) )   toplevel   ->
      not (  ( subtm_pattern_agree a p )  )  ->
     CasePath R a F.

(* defns JApplyArgs *)
Inductive ApplyArgs : tm -> tm -> tm -> Prop :=    (* defn ApplyArgs *)
 | ApplyArgs_Const : forall (F:const) (b:tm),
     lc_tm b ->
     ApplyArgs (a_Fam F) b b
 | ApplyArgs_AppRole : forall (a:tm) (R:role) (a' b b':tm),
     lc_tm a' ->
     ApplyArgs a b b' ->
     ApplyArgs  ( (a_App a (Role R) a') )  b  ( (a_App b' (Rho Rel) a') )
 | ApplyArgs_AppRho : forall (a:tm) (rho:relflag) (a' b b':tm),
     lc_tm a' ->
     ApplyArgs a b b' ->
     ApplyArgs  ( (a_App a (Rho rho) a') )  b  ( (a_App b' (Rho rho) a') )
 | ApplyArgs_CApp : forall (a b b':tm),
     ApplyArgs a b b' ->
     ApplyArgs (a_CApp a g_Triv) b (a_CApp b' g_Triv).

(* defns JValue *)
Inductive Value : role -> tm -> Prop :=    (* defn Value *)
 | Value_Star : forall (R:role),
     Value R a_Star
 | Value_Pi : forall (R:role) (rho:relflag) (A B:tm),
     lc_tm A ->
     lc_tm (a_Pi rho A B) ->
     Value R (a_Pi rho A B)
 | Value_CPi : forall (R:role) (phi:constraint) (B:tm),
     lc_constraint phi ->
     lc_tm (a_CPi phi B) ->
     Value R (a_CPi phi B)
 | Value_AbsRel : forall (R:role) (A a:tm),
     lc_tm A ->
     lc_tm (a_Abs Rel A a) ->
     Value R (a_Abs Rel A a)
 | Value_UAbsRel : forall (R:role) (a:tm),
     lc_tm (a_UAbs Rel a) ->
     Value R (a_UAbs Rel a)
 | Value_UAbsIrrel : forall (L:vars) (R:role) (a:tm),
      ( forall x , x \notin  L  -> Value R  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     Value R (a_UAbs Irrel a)
 | Value_CAbs : forall (R:role) (phi:constraint) (a:tm),
     lc_constraint phi ->
     lc_tm (a_CAbs phi a) ->
     Value R (a_CAbs phi a)
 | Value_UCAbs : forall (R:role) (a:tm),
     lc_tm (a_UCAbs a) ->
     Value R (a_UCAbs a)
 | Value_Path : forall (R:role) (a:tm) (F:const),
     CasePath R a F ->
     Value R a.

(* defns JValueType *)
Inductive roleing : role_context -> tm -> role -> Prop :=    (* defn roleing *)
 | role_a_Bullet : forall (W:role_context) (R:role),
      uniq  W  ->
     roleing W a_Bullet R
 | role_a_Star : forall (W:role_context) (R:role),
      uniq  W  ->
     roleing W a_Star R
 | role_a_Var : forall (W:role_context) (x:tmvar) (R1 R:role),
      uniq  W  ->
      binds  x   R   W  ->
     SubRole R R1 ->
     roleing W (a_Var_f x) R1
 | role_a_Abs : forall (L:vars) (W:role_context) (rho:relflag) (a:tm) (R:role),
      ( forall x , x \notin  L  -> roleing  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm a (a_Var_f x) )  R )  ->
     roleing W  ( (a_UAbs rho a) )  R
 | role_a_App : forall (W:role_context) (a:tm) (rho:relflag) (b:tm) (R:role),
     roleing W a R ->
     roleing W b Nom ->
     roleing W  ( (a_App a (Rho rho) b) )  R
 | role_a_TApp : forall (W:role_context) (a:tm) (R1:role) (b:tm) (R:role),
     roleing W a R ->
     roleing W b  (param R1   R )  ->
     roleing W (a_App a (Role R1) b) R
 | role_a_Pi : forall (L:vars) (W:role_context) (rho:relflag) (A B:tm) (R:role),
     roleing W A R ->
      ( forall x , x \notin  L  -> roleing  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm B (a_Var_f x) )  R )  ->
     roleing W  ( (a_Pi rho A B) )  R
 | role_a_CPi : forall (L:vars) (W:role_context) (a b A:tm) (R1:role) (B:tm) (R:role),
     roleing W a R1 ->
     roleing W b R1 ->
     roleing W A Rep ->
      ( forall c , c \notin  L  -> roleing W  ( open_tm_wrt_co B (g_Var_f c) )  R )  ->
     roleing W  ( (a_CPi (Eq a b A R1) B) )  R
 | role_a_CAbs : forall (L:vars) (W:role_context) (b:tm) (R:role),
      ( forall c , c \notin  L  -> roleing W  ( open_tm_wrt_co b (g_Var_f c) )  R )  ->
     roleing W  ( (a_UCAbs b) )  R
 | role_a_CApp : forall (W:role_context) (a:tm) (R:role),
     roleing W a R ->
     roleing W  ( (a_CApp a g_Triv) )  R
 | role_a_Const : forall (W:role_context) (F:const) (R:role) (A:tm) (Rs:roles),
      uniq  W  ->
      binds  F  ( (Cs A Rs) )   toplevel   ->
     roleing W (a_Fam F) R
 | role_a_Fam : forall (W:role_context) (F:const) (R1:role) (p a A:tm) (R:role) (Rs:roles),
      uniq  W  ->
      binds  F  ( (Ax p a A R Rs) )   toplevel   ->
     roleing W (a_Fam F) R1
 | role_a_Pattern : forall (W:role_context) (a:tm) (F:const) (Apps5:Apps) (b1 b2:tm) (R1:role),
     roleing W a Nom ->
     roleing W b1 R1 ->
     roleing W b2 R1 ->
     roleing W (a_Pattern Nom a F Apps5 b1 b2) R1.

(* defns JChk *)
Inductive RhoCheck : relflag -> tmvar -> tm -> Prop :=    (* defn RhoCheck *)
 | Rho_Rel : forall (x:tmvar) (A:tm),
      True  ->
     RhoCheck Rel x A
 | Rho_IrrRel : forall (x:tmvar) (A:tm),
      ~ AtomSetImpl.In  x    (fv_tm_tm_tm  A )   ->
     RhoCheck Irrel x A.

(* defns Jpar *)
Inductive Par : role_context -> tm -> tm -> role -> Prop :=    (* defn Par *)
 | Par_Refl : forall (W:role_context) (a:tm) (R:role),
     roleing W a R ->
     Par W a a R
 | Par_Beta : forall (W:role_context) (a:tm) (rho:relflag) (b a' b':tm) (R:role),
     Par W a  ( (a_UAbs rho a') )  R ->
     Par W b b' Nom ->
     Par W (a_App a (Rho rho) b)  (open_tm_wrt_tm  a'   b' )  R
 | Par_App : forall (W:role_context) (a:tm) (nu:appflag) (b a' b':tm) (R:role),
     Par W a a' R ->
     Par W b b'  (  app_role  nu   R  )  ->
     Par W (a_App a nu b) (a_App a' nu b') R
 | Par_CBeta : forall (W:role_context) (a a':tm) (R:role),
     Par W a  ( (a_UCAbs a') )  R ->
     Par W (a_CApp a g_Triv)  (open_tm_wrt_co  a'   g_Triv )  R
 | Par_CApp : forall (W:role_context) (a a':tm) (R:role),
     Par W a a' R ->
     Par W (a_CApp a g_Triv) (a_CApp a' g_Triv) R
 | Par_Abs : forall (L:vars) (W:role_context) (rho:relflag) (a a':tm) (R:role),
      ( forall x , x \notin  L  -> Par  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm a' (a_Var_f x) )  R )  ->
     Par W (a_UAbs rho a) (a_UAbs rho a') R
 | Par_Pi : forall (L:vars) (W:role_context) (rho:relflag) (A B A' B':tm) (R:role),
     Par W A A' R ->
      ( forall x , x \notin  L  -> Par  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm B' (a_Var_f x) )  R )  ->
     Par W (a_Pi rho A B) (a_Pi rho A' B') R
 | Par_CAbs : forall (L:vars) (W:role_context) (a a':tm) (R:role),
      ( forall c , c \notin  L  -> Par W  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co a' (g_Var_f c) )  R )  ->
     Par W (a_UCAbs a) (a_UCAbs a') R
 | Par_CPi : forall (L:vars) (W:role_context) (a b A:tm) (R1:role) (B a' b' A' B':tm) (R:role),
     Par W A A' Rep ->
     Par W a a' R1 ->
     Par W b b' R1 ->
      ( forall c , c \notin  L  -> Par W  ( open_tm_wrt_co B (g_Var_f c) )   ( open_tm_wrt_co B' (g_Var_f c) )  R )  ->
     Par W (a_CPi (Eq a b A R1) B) (a_CPi (Eq a' b' A' R1) B') R
 | Par_AxiomBase : forall (W:role_context) (F:const) (b:tm) (R:role) (A:tm) (R1:role) (Rs:roles),
      binds  F  ( (Ax (a_Fam F) b A R1 Rs) )   toplevel   ->
     SubRole R1 R ->
      uniq  W  ->
     Par W (a_Fam F) b R
 | Par_AxiomApp : forall (W:role_context) (a:tm) (nu:appflag) (a1 a2:tm) (R:role) (F:const) (p b A:tm) (R1:role) (Rs:roles) (a' a1' p' b':tm) (D':available_props),
      binds  F  ( (Ax p b A R1 Rs) )   toplevel   ->
      tm_subpattern_agree a p  /\   not (  ( tm_pattern_agree a p )  )   ->
     Par W a a' R ->
     Par W a1 a1'  (  app_role  nu   R  )  ->
     Rename p b p' b'  (  (  (dom  W )   `union`   (fv_tm_tm_tm  p )  )  )  D' ->
     MatchSubst  ( (a_App a' nu a1') )  p' b' a2 ->
     SubRole R1 R ->
     Par W (a_App a nu a1) a2 R
 | Par_AxiomCApp : forall (W:role_context) (a a2:tm) (R:role) (F:const) (p b A:tm) (R1:role) (Rs:roles) (a' p' b':tm) (D':available_props),
      binds  F  ( (Ax p b A R1 Rs) )   toplevel   ->
      tm_subpattern_agree a p  /\   not (  ( tm_pattern_agree a p )  )   ->
     Par W a a' R ->
     Rename p b p' b'  (  (  (dom  W )   `union`   (fv_tm_tm_tm  p )  )  )  D' ->
     MatchSubst  ( (a_CApp a' g_Triv) )  p' b' a2 ->
     SubRole R1 R ->
     Par W (a_CApp a g_Triv) a2 R
 | Par_Pattern : forall (W:role_context) (a:tm) (F:const) (Apps5:Apps) (b1 b2 a' b1' b2':tm) (R0:role),
     Par W a a' Nom ->
     Par W b1 b1' R0 ->
     Par W b2 b2' R0 ->
     Par W  ( (a_Pattern Nom a F Apps5 b1 b2) )   ( (a_Pattern Nom a' F Apps5 b1' b2') )  R0
 | Par_PatternTrue : forall (W:role_context) (a:tm) (F:const) (Apps5:Apps) (b1 b2 b:tm) (R0:role) (a' b1' b2':tm) (Apps':Apps),
     Par W a a' Nom ->
     Par W b1 b1' R0 ->
     Par W b2 b2' R0 ->
     AppsPath Nom a' F Apps5 ->
     ApplyArgs a' b1' b ->
      ( SatApp F Apps' )  ->
     Par W  ( (a_Pattern Nom a F Apps5 b1 b2) )  (a_CApp b g_Triv) R0
 | Par_PatternFalse : forall (W:role_context) (a:tm) (F:const) (Apps5:Apps) (b1 b2 b2':tm) (R0:role) (a' b1':tm),
     Par W a a' Nom ->
     Par W b1 b1' R0 ->
     Par W b2 b2' R0 ->
     Value Nom a' ->
      not (  ( AppsPath Nom a' F Apps5 )  )  ->
     Par W  ( (a_Pattern Nom a F Apps5 b1 b2) )  b2' R0
with MultiPar : role_context -> tm -> tm -> role -> Prop :=    (* defn MultiPar *)
 | MP_Refl : forall (W:role_context) (a:tm) (R:role),
     lc_tm a ->
     MultiPar W a a R
 | MP_Step : forall (W:role_context) (a a':tm) (R:role) (b:tm),
     Par W a b R ->
     MultiPar W b a' R ->
     MultiPar W a a' R
with joins : role_context -> tm -> tm -> role -> Prop :=    (* defn joins *)
 | join : forall (W:role_context) (a1 a2:tm) (R:role) (b:tm),
     MultiPar W a1 b R ->
     MultiPar W a2 b R ->
     joins W a1 a2 R.

(* defns Jbeta *)
Inductive Beta : tm -> tm -> role -> Prop :=    (* defn Beta *)
 | Beta_AppAbs : forall (rho:relflag) (v b:tm) (R:role),
     lc_tm b ->
     Value R  ( (a_UAbs rho v) )  ->
     Beta (a_App  ( (a_UAbs rho v) )  (Rho rho) b)  (open_tm_wrt_tm  v   b )  R
 | Beta_CAppCAbs : forall (a':tm) (R:role),
     lc_tm (a_UCAbs a') ->
     Beta (a_CApp  ( (a_UCAbs a') )  g_Triv)  (open_tm_wrt_co  a'   g_Triv )  R
 | Beta_Axiom : forall (a b':tm) (R:role) (F:const) (p b A:tm) (R1:role) (Rs:roles) (p1 b1:tm) (D':available_props),
      binds  F  ( (Ax p b A R1 Rs) )   toplevel   ->
     Rename p b p1 b1  (  (  (fv_tm_tm_tm  a )   `union`   (fv_tm_tm_tm  p )  )  )  D' ->
     MatchSubst a p1 b1 b' ->
     SubRole R1 R ->
     Beta a b' R
 | Beta_PatternTrue : forall (a:tm) (F:const) (Apps5:Apps) (b1 b2 b1':tm) (R:role) (Apps':Apps),
     lc_tm b2 ->
     AppsPath Nom a F Apps5 ->
     ApplyArgs a b1 b1' ->
      ( SatApp F Apps' )  ->
     Beta  ( (a_Pattern Nom a F Apps5 b1 b2) )  (a_CApp b1' g_Triv) R
 | Beta_PatternFalse : forall (a:tm) (F:const) (Apps5:Apps) (b1 b2:tm) (R:role),
     lc_tm b1 ->
     lc_tm b2 ->
     Value Nom a ->
      not (  ( AppsPath Nom a F Apps5 )  )  ->
     Beta  ( (a_Pattern Nom a F Apps5 b1 b2) )  b2 R
with reduction_in_one : tm -> tm -> role -> Prop :=    (* defn reduction_in_one *)
 | E_AbsTerm : forall (L:vars) (a a':tm) (R:role),
      ( forall x , x \notin  L  -> reduction_in_one  ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm a' (a_Var_f x) )  R )  ->
     reduction_in_one (a_UAbs Irrel a) (a_UAbs Irrel a') R
 | E_AppLeft : forall (a:tm) (nu:appflag) (b a':tm) (R:role),
     lc_tm b ->
     reduction_in_one a a' R ->
     reduction_in_one (a_App a nu b) (a_App a' nu b) R
 | E_CAppLeft : forall (a a':tm) (R:role),
     reduction_in_one a a' R ->
     reduction_in_one (a_CApp a g_Triv) (a_CApp a' g_Triv) R
 | E_Pattern : forall (a:tm) (F:const) (Apps5:Apps) (b1 b2 a':tm) (R:role),
     lc_tm b1 ->
     lc_tm b2 ->
     reduction_in_one a a' Nom ->
     reduction_in_one  ( (a_Pattern Nom a F Apps5 b1 b2) )   ( (a_Pattern Nom a' F Apps5 b1 b2) )  R
 | E_Prim : forall (a b:tm) (R:role),
     Beta a b R ->
     reduction_in_one a b R
with reduction : tm -> tm -> role -> Prop :=    (* defn reduction *)
 | Equal : forall (a:tm) (R:role),
     lc_tm a ->
     reduction a a R
 | Step : forall (a a':tm) (R:role) (b:tm),
     reduction_in_one a b R ->
     reduction b a' R ->
     reduction a a' R.

(* defns JBranchTyping *)
Inductive BranchTyping : context -> Apps -> role -> tm -> tm -> tm -> pattern_args -> tm -> tm -> tm -> Prop :=    (* defn BranchTyping *)
 | BranchTyping_Base : forall (G:context) (a A b:tm) (pattern_args5:pattern_args) (C1 C2:tm),
     lc_tm a ->
     lc_tm b ->
     lc_tm A ->
      uniq  G  ->
      (  (open_tm_wrt_co  C1   g_Triv )   =  C2 )  ->
     BranchTyping G A_nil Nom a A b pattern_args5 A (a_CPi  ( (Eq a  (apply_pattern_args  b   pattern_args5 )  A Nom) )  C1) C2
 | BranchTyping_PiRole : forall (L:vars) (G:context) (R:role) (Apps5:Apps) (a A1 b:tm) (pattern_args5:pattern_args) (A B C C':tm),
      ( forall x , x \notin  L  -> BranchTyping  (( x ~ Tm  A ) ++  G )  Apps5 Nom a A1 b  ( pattern_args5  ++ [  (p_Tm (Role R) (a_Var_f x))  ])   ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm C (a_Var_f x) )  C' )  ->
     BranchTyping G  ( (A_cons (A_Tm (Role R)) Apps5) )  Nom a A1 b pattern_args5 (a_Pi Rel A B) (a_Pi Rel A C) C'
 | BranchTyping_PiRel : forall (L:vars) (G:context) (Apps5:Apps) (a A1 b:tm) (pattern_args5:pattern_args) (A B C C':tm),
      ( forall x , x \notin  L  -> BranchTyping  (( x ~ Tm  A ) ++  G )  Apps5 Nom a A1 b  ( pattern_args5  ++ [  (p_Tm (Rho Rel) (a_Var_f x))  ])   ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm C (a_Var_f x) )  C' )  ->
     BranchTyping G  ( (A_cons (A_Tm (Rho Rel)) Apps5) )  Nom a A1 b pattern_args5 (a_Pi Rel A B) (a_Pi Rel A C) C'
 | BranchTyping_PiIrrel : forall (L:vars) (G:context) (Apps5:Apps) (a A1 b:tm) (pattern_args5:pattern_args) (A B C C':tm),
      ( forall x , x \notin  L  -> BranchTyping  (( x ~ Tm  A ) ++  G )  Apps5 Nom a A1 b  ( pattern_args5  ++ [  (p_Tm (Rho Irrel) a_Bullet)  ])   ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm C (a_Var_f x) )  C' )  ->
     BranchTyping G  ( (A_cons (A_Tm (Rho Irrel)) Apps5) )  Nom a A1 b pattern_args5 (a_Pi Irrel A B) (a_Pi Irrel A C) C'
 | BranchTyping_CPi : forall (L:vars) (G:context) (Apps5:Apps) (a A b:tm) (pattern_args5:pattern_args) (phi:constraint) (B C C':tm),
      ( forall c , c \notin  L  -> BranchTyping  (( c ~ Co  phi ) ++  G )  Apps5 Nom a A b  ( pattern_args5  ++ [  (p_Co g_Triv)  ])   ( open_tm_wrt_co B (g_Var_f c) )   ( open_tm_wrt_co C (g_Var_f c) )  C' )  ->
     BranchTyping G  ( (A_cons A_Co Apps5) )  Nom a A b pattern_args5 (a_CPi phi B) (a_CPi phi C) C'.

(* defns Jett *)
Inductive PropWff : context -> constraint -> Prop :=    (* defn PropWff *)
 | E_Wff : forall (G:context) (a b A:tm) (R:role),
     Typing G a A ->
     Typing G b A ->
      ( Typing G A a_Star )  ->
     PropWff G (Eq a b A R)
with Typing : context -> tm -> tm -> Prop :=    (* defn Typing *)
 | E_Star : forall (G:context),
     Ctx G ->
     Typing G a_Star a_Star
 | E_Var : forall (G:context) (x:tmvar) (A:tm),
     Ctx G ->
      binds  x  (Tm  A )  G  ->
     Typing G (a_Var_f x) A
 | E_Pi : forall (L:vars) (G:context) (rho:relflag) (A B:tm),
      ( forall x , x \notin  L  -> Typing  (( x ~ Tm  A ) ++  G )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Star )  ->
     Typing G A a_Star ->
     Typing G (a_Pi rho A B) a_Star
 | E_Abs : forall (L:vars) (G:context) (rho:relflag) (a A B:tm),
      ( forall x , x \notin  L  -> Typing  (( x ~ Tm  A ) ++  G )   ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
      ( Typing G A a_Star )  ->
      ( forall x , x \notin  L  -> RhoCheck rho x  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     Typing G (a_UAbs rho a)  ( (a_Pi rho A B) )
 | E_App : forall (G:context) (b a B A:tm),
     Typing G b (a_Pi Rel A B) ->
     Typing G a A ->
     Typing G (a_App b (Rho Rel) a)  (open_tm_wrt_tm  B   a )
 | E_TApp : forall (G:context) (b:tm) (R:role) (a B A:tm) (Rs:roles),
     Typing G b (a_Pi Rel A B) ->
     Typing G a A ->
     RolePath b  ( R :: Rs )  ->
     Typing G (a_App b (Role R) a)  (open_tm_wrt_tm  B   a )
 | E_IApp : forall (G:context) (b B a A:tm),
     Typing G b (a_Pi Irrel A B) ->
     Typing G a A ->
     Typing G (a_App b (Rho Irrel) a_Bullet)  (open_tm_wrt_tm  B   a )
 | E_Conv : forall (G:context) (a B A:tm),
     Typing G a A ->
     DefEq G  (dom  G )  A B a_Star Rep ->
      ( Typing G B a_Star )  ->
     Typing G a B
 | E_CPi : forall (L:vars) (G:context) (phi:constraint) (B:tm),
      ( forall c , c \notin  L  -> Typing  (( c ~ Co  phi ) ++  G )   ( open_tm_wrt_co B (g_Var_f c) )  a_Star )  ->
      ( PropWff G phi )  ->
     Typing G (a_CPi phi B) a_Star
 | E_CAbs : forall (L:vars) (G:context) (a:tm) (phi:constraint) (B:tm),
      ( forall c , c \notin  L  -> Typing  (( c ~ Co  phi ) ++  G )   ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  )  ->
      ( PropWff G phi )  ->
     Typing G (a_UCAbs a) (a_CPi phi B)
 | E_CApp : forall (G:context) (a1 B1 a b A:tm) (R:role),
     Typing G a1 (a_CPi  ( (Eq a b A R) )  B1) ->
     DefEq G  (dom  G )  a b A R ->
     Typing G (a_CApp a1 g_Triv)  (open_tm_wrt_co  B1   g_Triv )
 | E_Const : forall (G:context) (F:const) (A:tm) (Rs:roles),
     Ctx G ->
      binds  F  ( (Cs A Rs) )   toplevel   ->
      ( Typing  nil  A a_Star )  ->
     Typing G (a_Fam F) A
 | E_Fam : forall (G:context) (F:const) (A p a:tm) (R1:role) (Rs:roles),
     Ctx G ->
      binds  F  ( (Ax p a A R1 Rs) )   toplevel   ->
      ( Typing  nil  A a_Star )  ->
     Typing G (a_Fam F) A
 | E_Case : forall (G:context) (a:tm) (F:const) (Apps5:Apps) (b1 b2 C A B A1:tm),
     Typing G a A ->
     Typing G b1 B ->
     Typing G b2 C ->
     BranchTyping G Apps5 Nom a A (a_Fam F)  nil  A1 B C ->
     Typing G (a_Fam F) A1 ->
     SatApp F Apps5 ->
     Typing G (a_Pattern Nom a F Apps5 b1 b2) C
with Iso : context -> available_props -> constraint -> constraint -> Prop :=    (* defn Iso *)
 | E_PropCong : forall (G:context) (D:available_props) (A1 B1 A:tm) (R:role) (A2 B2:tm),
     DefEq G D A1 A2 A R ->
     DefEq G D B1 B2 A R ->
     Iso G D (Eq A1 B1 A R) (Eq A2 B2 A R)
 | E_IsoConv : forall (G:context) (D:available_props) (A1 A2 A:tm) (R:role) (B:tm) (R0:role),
     DefEq G D A B a_Star R0 ->
     PropWff G (Eq A1 A2 A R) ->
     PropWff G (Eq A1 A2 B R) ->
     Iso G D (Eq A1 A2 A R) (Eq A1 A2 B R)
 | E_CPiFst : forall (G:context) (D:available_props) (a1 a2 A:tm) (R1:role) (b1 b2 B:tm) (R2:role) (B1 B2:tm) (R':role),
     DefEq G D (a_CPi  ( (Eq a1 a2 A R1) )  B1) (a_CPi  ( (Eq b1 b2 B R2) )  B2) a_Star R' ->
     Iso G D (Eq a1 a2 A R1) (Eq b1 b2 B R2)
with DefEq : context -> available_props -> tm -> tm -> tm -> role -> Prop :=    (* defn DefEq *)
 | E_Assn : forall (G:context) (D:available_props) (a b A:tm) (R:role) (c:covar),
     Ctx G ->
      binds  c  (Co   ( (Eq a b A R) )  )  G  ->
      AtomSetImpl.In  c   D  ->
     DefEq G D a b A R
 | E_Refl : forall (G:context) (D:available_props) (a A:tm) (R:role),
     Typing G a A ->
     DefEq G D a a A R
 | E_Sym : forall (G:context) (D:available_props) (a b A:tm) (R:role),
     DefEq G D b a A R ->
     DefEq G D a b A R
 | E_Trans : forall (G:context) (D:available_props) (a b A:tm) (R:role) (a1:tm),
     DefEq G D a a1 A R ->
     DefEq G D a1 b A R ->
     DefEq G D a b A R
 | E_Sub : forall (G:context) (D:available_props) (a b A:tm) (R2 R1:role),
     DefEq G D a b A R1 ->
     SubRole R1 R2 ->
     DefEq G D a b A R2
 | E_Beta : forall (G:context) (D:available_props) (a1 a2 B:tm) (R:role),
     Typing G a1 B ->
      ( Typing G a2 B )  ->
     Beta a1 a2 R ->
     DefEq G D a1 a2 B R
 | E_PiCong : forall (L:vars) (G:context) (D:available_props) (rho:relflag) (A1 B1 A2 B2:tm) (R':role),
     DefEq G D A1 A2 a_Star R' ->
      ( forall x , x \notin  L  -> DefEq  (( x ~ Tm  A1 ) ++  G )  D  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  a_Star R' )  ->
      ( Typing G A1 a_Star )  ->
      ( Typing G (a_Pi rho A1 B1) a_Star )  ->
      ( Typing G (a_Pi rho A2 B2) a_Star )  ->
     DefEq G D  ( (a_Pi rho A1 B1) )   ( (a_Pi rho A2 B2) )  a_Star R'
 | E_AbsCong : forall (L:vars) (G:context) (D:available_props) (rho:relflag) (b1 b2 A1 B:tm) (R':role),
      ( forall x , x \notin  L  -> DefEq  (( x ~ Tm  A1 ) ++  G )  D  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  R' )  ->
      ( Typing G A1 a_Star )  ->
      ( forall x , x \notin  L  -> RhoCheck rho x  ( open_tm_wrt_tm b1 (a_Var_f x) )  )  ->
      ( forall x , x \notin  L  -> RhoCheck rho x  ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     DefEq G D  ( (a_UAbs rho b1) )   ( (a_UAbs rho b2) )   ( (a_Pi rho A1 B) )  R'
 | E_AppCong : forall (G:context) (D:available_props) (a1 a2 b1 b2 B:tm) (R':role) (A:tm),
     DefEq G D a1 b1  ( (a_Pi Rel A B) )  R' ->
     DefEq G D a2 b2 A Nom ->
     DefEq G D (a_App a1 (Rho Rel) a2) (a_App b1 (Rho Rel) b2)  (  (open_tm_wrt_tm  B   a2 )  )  R'
 | E_TAppCong : forall (G:context) (D:available_props) (a1:tm) (R:role) (a2 b1 b2 B:tm) (R':role) (A:tm) (Rs:roles),
     DefEq G D a1 b1  ( (a_Pi Rel A B) )  R' ->
     DefEq G D a2 b2 A  (param R   R' )  ->
     RolePath a1  ( R :: Rs )  ->
     RolePath b1  ( R :: Rs )  ->
     Typing G (a_App b1 (Role R) b2)  (open_tm_wrt_tm  B   a2 )  ->
     DefEq G D (a_App a1 (Role R) a2) (a_App b1 (Role R) b2)  (  (open_tm_wrt_tm  B   a2 )  )  R'
 | E_IAppCong : forall (G:context) (D:available_props) (a1 b1 B a:tm) (R:role) (A:tm),
     DefEq G D a1 b1  ( (a_Pi Irrel A B) )  R ->
     Typing G a A ->
     DefEq G D (a_App a1 (Rho Irrel) a_Bullet) (a_App b1 (Rho Irrel) a_Bullet)  (  (open_tm_wrt_tm  B   a )  )  R
 | E_PiFst : forall (G:context) (D:available_props) (A1 A2:tm) (R':role) (rho:relflag) (B1 B2:tm),
     DefEq G D (a_Pi rho A1 B1) (a_Pi rho A2 B2) a_Star R' ->
     DefEq G D A1 A2 a_Star R'
 | E_PiSnd : forall (G:context) (D:available_props) (B1 a1 B2 a2:tm) (R:role) (rho:relflag) (A1 A2:tm),
     DefEq G D (a_Pi rho A1 B1) (a_Pi rho A2 B2) a_Star R ->
     DefEq G D a1 a2 A1 Nom ->
     DefEq G D  (open_tm_wrt_tm  B1   a1 )   (open_tm_wrt_tm  B2   a2 )  a_Star R
 | E_CPiCong : forall (L:vars) (G:context) (D:available_props) (a1 b1 A1:tm) (R:role) (A a2 b2 A2 B:tm) (R':role),
     Iso G D (Eq a1 b1 A1 R) (Eq a2 b2 A2 R) ->
      ( forall c , c \notin  L  -> DefEq  (( c ~ Co  (Eq a1 b1 A1 R) ) ++  G )  D  ( open_tm_wrt_co A (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  a_Star R' )  ->
      ( PropWff G (Eq a1 b1 A1 R) )  ->
      ( Typing G (a_CPi (Eq a1 b1 A1 R) A) a_Star )  ->
      ( Typing G (a_CPi (Eq a2 b2 A2 R) B) a_Star )  ->
     DefEq G D (a_CPi (Eq a1 b1 A1 R) A) (a_CPi (Eq a2 b2 A2 R) B) a_Star R'
 | E_CAbsCong : forall (L:vars) (G:context) (D:available_props) (a b:tm) (phi1:constraint) (B:tm) (R:role),
      ( forall c , c \notin  L  -> DefEq  (( c ~ Co  phi1 ) ++  G )  D  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co b (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  R )  ->
      ( PropWff G phi1 )  ->
     DefEq G D  ( (a_UCAbs a) )   ( (a_UCAbs b) )  (a_CPi phi1 B) R
 | E_CAppCong : forall (G:context) (D:available_props) (a1 b1 B:tm) (R':role) (a b A:tm) (R:role),
     DefEq G D a1 b1  ( (a_CPi  ( (Eq a b A R) )  B) )  R' ->
     DefEq G  (dom  G )  a b A R ->
     DefEq G D (a_CApp a1 g_Triv) (a_CApp b1 g_Triv)  (  (open_tm_wrt_co  B   g_Triv )  )  R'
 | E_CPiSnd : forall (G:context) (D:available_props) (B1 B2:tm) (R0:role) (a1 a2 A:tm) (R:role) (a1' a2' A':tm) (R':role),
     DefEq G D (a_CPi  ( (Eq a1 a2 A R) )  B1) (a_CPi  ( (Eq a1' a2' A' R') )  B2) a_Star R0 ->
     DefEq G  (dom  G )  a1 a2 A R ->
     DefEq G  (dom  G )  a1' a2' A' R' ->
     DefEq G D  (open_tm_wrt_co  B1   g_Triv )   (open_tm_wrt_co  B2   g_Triv )  a_Star R0
 | E_Cast : forall (G:context) (D:available_props) (a' b' A':tm) (R':role) (a b A:tm) (R:role),
     DefEq G D a b A R ->
     Iso G D (Eq a b A R) (Eq a' b' A' R') ->
     DefEq G D a' b' A' R'
 | E_EqConv : forall (G:context) (D:available_props) (a b B:tm) (R:role) (A:tm),
     DefEq G D a b A R ->
     DefEq G  (dom  G )  A B a_Star Rep ->
      ( Typing G B a_Star )  ->
     DefEq G D a b B R
 | E_IsoSnd : forall (G:context) (D:available_props) (A A' a b:tm) (R1:role) (a' b':tm),
     Iso G D (Eq a b A R1) (Eq a' b' A' R1) ->
     DefEq G D A A' a_Star Rep
 | E_PatCong : forall (G:context) (D:available_props) (a:tm) (F:const) (Apps5:Apps) (b1 b2 a' b1' b2' C:tm) (R0:role) (A B A1 B':tm),
     DefEq G D a a' A Nom ->
     DefEq G D b1 b1' B R0 ->
     DefEq G D b2 b2' C R0 ->
     BranchTyping G Apps5 Nom a A (a_Fam F)  nil  A1 B C ->
     BranchTyping G Apps5 Nom a' A (a_Fam F)  nil  A1 B' C ->
     DefEq G D B B' a_Star Rep ->
     SatApp F Apps5 ->
     Typing G (a_Fam F) A1 ->
     DefEq G D (a_Pattern Nom a F Apps5 b1 b2) (a_Pattern Nom a' F Apps5 b1' b2') C R0
 | E_LeftRel : forall (G:context) (D:available_props) (a a' A B:tm) (R' R1:role) (b:tm) (F:const) (b':tm),
     CasePath R'  ( (a_App a (Role R1) b) )  F ->
     CasePath R'  ( (a_App a' (Role R1) b') )  F ->
     Typing G a (a_Pi Rel A B) ->
     Typing G b A ->
     Typing G a' (a_Pi Rel A B) ->
     Typing G b' A ->
     DefEq G D (a_App a (Role R1) b) (a_App a' (Role R1) b')  (open_tm_wrt_tm  B   b )  R' ->
     DefEq G  (dom  G )   (open_tm_wrt_tm  B   b )   (open_tm_wrt_tm  B   b' )  a_Star Rep ->
     DefEq G D a a' (a_Pi Rel A B) R'
 | E_LeftIrrel : forall (G:context) (D:available_props) (a a' A B:tm) (R':role) (F:const) (b b':tm),
     CasePath R'  ( (a_App a (Rho Irrel) a_Bullet) )  F ->
     CasePath R'  ( (a_App a' (Rho Irrel) a_Bullet) )  F ->
     Typing G a (a_Pi Irrel A B) ->
     Typing G b A ->
     Typing G a' (a_Pi Irrel A B) ->
     Typing G b' A ->
     DefEq G D (a_App a (Rho Irrel) a_Bullet) (a_App a' (Rho Irrel) a_Bullet)  (open_tm_wrt_tm  B   b )  R' ->
     DefEq G  (dom  G )   (open_tm_wrt_tm  B   b )   (open_tm_wrt_tm  B   b' )  a_Star Rep ->
     DefEq G D a a' (a_Pi Irrel A B) R'
 | E_Right : forall (G:context) (D:available_props) (b b' A:tm) (R1 R2:role) (a:tm) (F:const) (a' B:tm),
     CasePath R2  ( (a_App a (Role R1) b) )  F ->
     CasePath R2  ( (a_App a' (Role R1) b') )  F ->
     Typing G a (a_Pi Rel A B) ->
     Typing G b A ->
     Typing G a' (a_Pi Rel A B) ->
     Typing G b' A ->
     DefEq G D (a_App a (Role R1) b) (a_App a' (Role R1) b')  (open_tm_wrt_tm  B   b )  R2 ->
     DefEq G  (dom  G )   (open_tm_wrt_tm  B   b )   (open_tm_wrt_tm  B   b' )  a_Star Rep ->
     DefEq G D b b' A  (param R1   R2 )
 | E_CLeft : forall (G:context) (D:available_props) (a a' a1 a2 A:tm) (R1:role) (B:tm) (R':role) (F:const),
     CasePath R'  ( (a_CApp a g_Triv) )  F ->
     CasePath R'  ( (a_CApp a' g_Triv) )  F ->
     Typing G a (a_CPi  ( (Eq a1 a2 A R1) )  B) ->
     Typing G a' (a_CPi  ( (Eq a1 a2 A R1) )  B) ->
     DefEq G  (dom  G )  a1 a2 A  (param R1   R' )  ->
     DefEq G D (a_CApp a g_Triv) (a_CApp a' g_Triv)  (open_tm_wrt_co  B   g_Triv )  R' ->
     DefEq G D a a' (a_CPi  ( (Eq a1 a2 A R1) )  B) R'
with Ctx : context -> Prop :=    (* defn Ctx *)
 | E_Empty :
     Ctx  nil
 | E_ConsTm : forall (G:context) (x:tmvar) (A:tm),
     Ctx G ->
     Typing G A a_Star ->
      ~ AtomSetImpl.In  x    (dom  G )   ->
     Ctx  (( x ~ Tm  A ) ++  G )
 | E_ConsCo : forall (G:context) (c:covar) (phi:constraint),
     Ctx G ->
     PropWff G phi ->
      ~ AtomSetImpl.In  c    (dom  G )   ->
     Ctx  (( c ~ Co  phi ) ++  G ) .

(* defns Jsig *)
