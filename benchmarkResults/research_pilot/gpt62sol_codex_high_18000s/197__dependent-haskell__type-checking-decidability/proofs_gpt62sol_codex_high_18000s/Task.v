Require Import Language.
From Stdlib Require Import Arith Lia Bool.

(** Raw syntax, structural size, and opening and closing. *)

Scheme fc_ind_tm := Induction for tm Sort Prop
with fc_ind_brs := Induction for brs Sort Prop
with fc_ind_co := Induction for co Sort Prop
with fc_ind_constraint := Induction for constraint Sort Prop.
Combined Scheme fc_syntax_ind from fc_ind_tm, fc_ind_brs, fc_ind_co, fc_ind_constraint.

Fixpoint fc_size_tm (e : tm) : nat :=
  match e with
  | a_Star => 1
  | a_Var_b i => 1
  | a_Var_f x0 => 1
  | a_Abs rho A b => 1 + fc_size_tm A + fc_size_tm b
  | a_UAbs rho b => 1 + fc_size_tm b
  | a_App a rho b => 1 + fc_size_tm a + fc_size_tm b
  | a_Fam F => 1
  | a_Const T => 1
  | a_Pi rho A B => 1 + fc_size_tm A + fc_size_tm B
  | a_Conv a g => 1 + fc_size_tm a + fc_size_co g
  | a_CPi phi B => 1 + fc_size_constraint phi + fc_size_tm B
  | a_CAbs phi b => 1 + fc_size_constraint phi + fc_size_tm b
  | a_UCAbs b => 1 + fc_size_tm b
  | a_CApp a g => 1 + fc_size_tm a + fc_size_co g
  | a_Bullet => 1
  | a_DataCon K => 1
  | a_Case a brs5 => 1 + fc_size_tm a + fc_size_brs brs5
  end
with fc_size_brs (e : brs) : nat :=
  match e with
  | br_None => 1
  | br_One K a brs5 => 1 + fc_size_tm a + fc_size_brs brs5
  end
with fc_size_co (e : co) : nat :=
  match e with
  | g_Triv => 1
  | g_Var_b i => 1
  | g_Var_f c => 1
  | g_Beta a b => 1 + fc_size_tm a + fc_size_tm b
  | g_Refl a => 1 + fc_size_tm a
  | g_Refl2 a b g => 1 + fc_size_tm a + fc_size_tm b + fc_size_co g
  | g_Sym g => 1 + fc_size_co g
  | g_Trans g1 g2 => 1 + fc_size_co g1 + fc_size_co g2
  | g_PiCong rho g1 g2 => 1 + fc_size_co g1 + fc_size_co g2
  | g_AbsCong rho g1 g2 => 1 + fc_size_co g1 + fc_size_co g2
  | g_AppCong g1 rho g2 => 1 + fc_size_co g1 + fc_size_co g2
  | g_PiFst g => 1 + fc_size_co g
  | g_CPiFst g => 1 + fc_size_co g
  | g_IsoSnd g => 1 + fc_size_co g
  | g_PiSnd g1 g2 => 1 + fc_size_co g1 + fc_size_co g2
  | g_CPiCong g1 g3 => 1 + fc_size_co g1 + fc_size_co g3
  | g_CAbsCong g1 g3 g4 => 1 + fc_size_co g1 + fc_size_co g3 + fc_size_co g4
  | g_CAppCong g g1 g2 => 1 + fc_size_co g + fc_size_co g1 + fc_size_co g2
  | g_CPiSnd g g1 g2 => 1 + fc_size_co g + fc_size_co g1 + fc_size_co g2
  | g_Cast g1 g2 => 1 + fc_size_co g1 + fc_size_co g2
  | g_EqCong g1 A g2 => 1 + fc_size_co g1 + fc_size_tm A + fc_size_co g2
  | g_IsoConv phi1 phi2 g => 1 + fc_size_constraint phi1 + fc_size_constraint phi2 + fc_size_co g
  | g_Eta a => 1 + fc_size_tm a
  | g_Left g g' => 1 + fc_size_co g + fc_size_co g'
  | g_Right g g' => 1 + fc_size_co g + fc_size_co g'
  end
with fc_size_constraint (e : constraint) : nat :=
  match e with
  | Eq a b A => 1 + fc_size_tm a + fc_size_tm b + fc_size_tm A
  end.

Fixpoint fc_fv_tm (e : tm) : atoms :=
  match e with
  | a_Star => {}
  | a_Var_b i => {}
  | a_Var_f x0 => {{x0}}
  | a_Abs rho A b => fc_fv_tm A \u fc_fv_tm b
  | a_UAbs rho b => fc_fv_tm b
  | a_App a rho b => fc_fv_tm a \u fc_fv_tm b
  | a_Fam F => {}
  | a_Const T => {}
  | a_Pi rho A B => fc_fv_tm A \u fc_fv_tm B
  | a_Conv a g => fc_fv_tm a \u fc_fv_co g
  | a_CPi phi B => fc_fv_constraint phi \u fc_fv_tm B
  | a_CAbs phi b => fc_fv_constraint phi \u fc_fv_tm b
  | a_UCAbs b => fc_fv_tm b
  | a_CApp a g => fc_fv_tm a \u fc_fv_co g
  | a_Bullet => {}
  | a_DataCon K => {}
  | a_Case a brs5 => fc_fv_tm a \u fc_fv_brs brs5
  end
with fc_fv_brs (e : brs) : atoms :=
  match e with
  | br_None => {}
  | br_One K a brs5 => fc_fv_tm a \u fc_fv_brs brs5
  end
with fc_fv_co (e : co) : atoms :=
  match e with
  | g_Triv => {}
  | g_Var_b i => {}
  | g_Var_f c => {{c}}
  | g_Beta a b => fc_fv_tm a \u fc_fv_tm b
  | g_Refl a => fc_fv_tm a
  | g_Refl2 a b g => fc_fv_tm a \u fc_fv_tm b \u fc_fv_co g
  | g_Sym g => fc_fv_co g
  | g_Trans g1 g2 => fc_fv_co g1 \u fc_fv_co g2
  | g_PiCong rho g1 g2 => fc_fv_co g1 \u fc_fv_co g2
  | g_AbsCong rho g1 g2 => fc_fv_co g1 \u fc_fv_co g2
  | g_AppCong g1 rho g2 => fc_fv_co g1 \u fc_fv_co g2
  | g_PiFst g => fc_fv_co g
  | g_CPiFst g => fc_fv_co g
  | g_IsoSnd g => fc_fv_co g
  | g_PiSnd g1 g2 => fc_fv_co g1 \u fc_fv_co g2
  | g_CPiCong g1 g3 => fc_fv_co g1 \u fc_fv_co g3
  | g_CAbsCong g1 g3 g4 => fc_fv_co g1 \u fc_fv_co g3 \u fc_fv_co g4
  | g_CAppCong g g1 g2 => fc_fv_co g \u fc_fv_co g1 \u fc_fv_co g2
  | g_CPiSnd g g1 g2 => fc_fv_co g \u fc_fv_co g1 \u fc_fv_co g2
  | g_Cast g1 g2 => fc_fv_co g1 \u fc_fv_co g2
  | g_EqCong g1 A g2 => fc_fv_co g1 \u fc_fv_tm A \u fc_fv_co g2
  | g_IsoConv phi1 phi2 g => fc_fv_constraint phi1 \u fc_fv_constraint phi2 \u fc_fv_co g
  | g_Eta a => fc_fv_tm a
  | g_Left g g' => fc_fv_co g \u fc_fv_co g'
  | g_Right g g' => fc_fv_co g \u fc_fv_co g'
  end
with fc_fv_constraint (e : constraint) : atoms :=
  match e with
  | Eq a b A => fc_fv_tm a \u fc_fv_tm b \u fc_fv_tm A
  end.

Fixpoint fc_degree_tm (p q : nat) (e : tm) : Prop :=
  match e with
  | a_Star => True
  | a_Var_b i => i < p
  | a_Var_f x0 => True
  | a_Abs rho A b => fc_degree_tm p q A /\ fc_degree_tm (S p) q b
  | a_UAbs rho b => fc_degree_tm (S p) q b
  | a_App a rho b => fc_degree_tm p q a /\ fc_degree_tm p q b
  | a_Fam F => True
  | a_Const T => True
  | a_Pi rho A B => fc_degree_tm p q A /\ fc_degree_tm (S p) q B
  | a_Conv a g => fc_degree_tm p q a /\ fc_degree_co p q g
  | a_CPi phi B => fc_degree_constraint p q phi /\ fc_degree_tm p (S q) B
  | a_CAbs phi b => fc_degree_constraint p q phi /\ fc_degree_tm p (S q) b
  | a_UCAbs b => fc_degree_tm p (S q) b
  | a_CApp a g => fc_degree_tm p q a /\ fc_degree_co p q g
  | a_Bullet => True
  | a_DataCon K => True
  | a_Case a brs5 => fc_degree_tm p q a /\ fc_degree_brs p q brs5
  end
with fc_degree_brs (p q : nat) (e : brs) : Prop :=
  match e with
  | br_None => True
  | br_One K a brs5 => fc_degree_tm p q a /\ fc_degree_brs p q brs5
  end
with fc_degree_co (p q : nat) (e : co) : Prop :=
  match e with
  | g_Triv => True
  | g_Var_b i => i < q
  | g_Var_f c => True
  | g_Beta a b => fc_degree_tm p q a /\ fc_degree_tm p q b
  | g_Refl a => fc_degree_tm p q a
  | g_Refl2 a b g => fc_degree_tm p q a /\ fc_degree_tm p q b /\ fc_degree_co p q g
  | g_Sym g => fc_degree_co p q g
  | g_Trans g1 g2 => fc_degree_co p q g1 /\ fc_degree_co p q g2
  | g_PiCong rho g1 g2 => fc_degree_co p q g1 /\ fc_degree_co (S p) q g2
  | g_AbsCong rho g1 g2 => fc_degree_co p q g1 /\ fc_degree_co (S p) q g2
  | g_AppCong g1 rho g2 => fc_degree_co p q g1 /\ fc_degree_co p q g2
  | g_PiFst g => fc_degree_co p q g
  | g_CPiFst g => fc_degree_co p q g
  | g_IsoSnd g => fc_degree_co p q g
  | g_PiSnd g1 g2 => fc_degree_co p q g1 /\ fc_degree_co p q g2
  | g_CPiCong g1 g3 => fc_degree_co p q g1 /\ fc_degree_co p (S q) g3
  | g_CAbsCong g1 g3 g4 => fc_degree_co p q g1 /\ fc_degree_co p (S q) g3 /\ fc_degree_co p q g4
  | g_CAppCong g g1 g2 => fc_degree_co p q g /\ fc_degree_co p q g1 /\ fc_degree_co p q g2
  | g_CPiSnd g g1 g2 => fc_degree_co p q g /\ fc_degree_co p q g1 /\ fc_degree_co p q g2
  | g_Cast g1 g2 => fc_degree_co p q g1 /\ fc_degree_co p q g2
  | g_EqCong g1 A g2 => fc_degree_co p q g1 /\ fc_degree_tm p q A /\ fc_degree_co p q g2
  | g_IsoConv phi1 phi2 g => fc_degree_constraint p q phi1 /\ fc_degree_constraint p q phi2 /\ fc_degree_co p q g
  | g_Eta a => fc_degree_tm p q a
  | g_Left g g' => fc_degree_co p q g /\ fc_degree_co p q g'
  | g_Right g g' => fc_degree_co p q g /\ fc_degree_co p q g'
  end
with fc_degree_constraint (p q : nat) (e : constraint) : Prop :=
  match e with
  | Eq a b A => fc_degree_tm p q a /\ fc_degree_tm p q b /\ fc_degree_tm p q A
  end.

Fixpoint fc_subst_tm (f : atom -> tm) (h : atom -> co) (e : tm) : tm :=
  match e with
  | a_Star => a_Star
  | a_Var_b i => a_Var_b i
  | a_Var_f x0 => f x0
  | a_Abs rho A b => a_Abs rho (fc_subst_tm f h A) (fc_subst_tm f h b)
  | a_UAbs rho b => a_UAbs rho (fc_subst_tm f h b)
  | a_App a rho b => a_App (fc_subst_tm f h a) rho (fc_subst_tm f h b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (fc_subst_tm f h A) (fc_subst_tm f h B)
  | a_Conv a g => a_Conv (fc_subst_tm f h a) (fc_subst_co f h g)
  | a_CPi phi B => a_CPi (fc_subst_constraint f h phi) (fc_subst_tm f h B)
  | a_CAbs phi b => a_CAbs (fc_subst_constraint f h phi) (fc_subst_tm f h b)
  | a_UCAbs b => a_UCAbs (fc_subst_tm f h b)
  | a_CApp a g => a_CApp (fc_subst_tm f h a) (fc_subst_co f h g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs5 => a_Case (fc_subst_tm f h a) (fc_subst_brs f h brs5)
  end
with fc_subst_brs (f : atom -> tm) (h : atom -> co) (e : brs) : brs :=
  match e with
  | br_None => br_None
  | br_One K a brs5 => br_One K (fc_subst_tm f h a) (fc_subst_brs f h brs5)
  end
with fc_subst_co (f : atom -> tm) (h : atom -> co) (e : co) : co :=
  match e with
  | g_Triv => g_Triv
  | g_Var_b i => g_Var_b i
  | g_Var_f c => h c
  | g_Beta a b => g_Beta (fc_subst_tm f h a) (fc_subst_tm f h b)
  | g_Refl a => g_Refl (fc_subst_tm f h a)
  | g_Refl2 a b g => g_Refl2 (fc_subst_tm f h a) (fc_subst_tm f h b) (fc_subst_co f h g)
  | g_Sym g => g_Sym (fc_subst_co f h g)
  | g_Trans g1 g2 => g_Trans (fc_subst_co f h g1) (fc_subst_co f h g2)
  | g_PiCong rho g1 g2 => g_PiCong rho (fc_subst_co f h g1) (fc_subst_co f h g2)
  | g_AbsCong rho g1 g2 => g_AbsCong rho (fc_subst_co f h g1) (fc_subst_co f h g2)
  | g_AppCong g1 rho g2 => g_AppCong (fc_subst_co f h g1) rho (fc_subst_co f h g2)
  | g_PiFst g => g_PiFst (fc_subst_co f h g)
  | g_CPiFst g => g_CPiFst (fc_subst_co f h g)
  | g_IsoSnd g => g_IsoSnd (fc_subst_co f h g)
  | g_PiSnd g1 g2 => g_PiSnd (fc_subst_co f h g1) (fc_subst_co f h g2)
  | g_CPiCong g1 g3 => g_CPiCong (fc_subst_co f h g1) (fc_subst_co f h g3)
  | g_CAbsCong g1 g3 g4 => g_CAbsCong (fc_subst_co f h g1) (fc_subst_co f h g3) (fc_subst_co f h g4)
  | g_CAppCong g g1 g2 => g_CAppCong (fc_subst_co f h g) (fc_subst_co f h g1) (fc_subst_co f h g2)
  | g_CPiSnd g g1 g2 => g_CPiSnd (fc_subst_co f h g) (fc_subst_co f h g1) (fc_subst_co f h g2)
  | g_Cast g1 g2 => g_Cast (fc_subst_co f h g1) (fc_subst_co f h g2)
  | g_EqCong g1 A g2 => g_EqCong (fc_subst_co f h g1) (fc_subst_tm f h A) (fc_subst_co f h g2)
  | g_IsoConv phi1 phi2 g => g_IsoConv (fc_subst_constraint f h phi1) (fc_subst_constraint f h phi2) (fc_subst_co f h g)
  | g_Eta a => g_Eta (fc_subst_tm f h a)
  | g_Left g g' => g_Left (fc_subst_co f h g) (fc_subst_co f h g')
  | g_Right g g' => g_Right (fc_subst_co f h g) (fc_subst_co f h g')
  end
with fc_subst_constraint (f : atom -> tm) (h : atom -> co) (e : constraint) : constraint :=
  match e with
  | Eq a b A => Eq (fc_subst_tm f h a) (fc_subst_tm f h b) (fc_subst_tm f h A)
  end.

Fixpoint fc_close_tm_tm (n : nat) (x : atom) (e : tm) : tm :=
  match e with
  | a_Star => a_Star
  | a_Var_b i => if lt_dec i n then a_Var_b i else a_Var_b (S i)
  | a_Var_f x0 => if x0 == x then a_Var_b n else a_Var_f x0
  | a_Abs rho A b => a_Abs rho (fc_close_tm_tm n x A) (fc_close_tm_tm (S n) x b)
  | a_UAbs rho b => a_UAbs rho (fc_close_tm_tm (S n) x b)
  | a_App a rho b => a_App (fc_close_tm_tm n x a) rho (fc_close_tm_tm n x b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (fc_close_tm_tm n x A) (fc_close_tm_tm (S n) x B)
  | a_Conv a g => a_Conv (fc_close_tm_tm n x a) (fc_close_tm_co n x g)
  | a_CPi phi B => a_CPi (fc_close_tm_constraint n x phi) (fc_close_tm_tm n x B)
  | a_CAbs phi b => a_CAbs (fc_close_tm_constraint n x phi) (fc_close_tm_tm n x b)
  | a_UCAbs b => a_UCAbs (fc_close_tm_tm n x b)
  | a_CApp a g => a_CApp (fc_close_tm_tm n x a) (fc_close_tm_co n x g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs5 => a_Case (fc_close_tm_tm n x a) (fc_close_tm_brs n x brs5)
  end
with fc_close_tm_brs (n : nat) (x : atom) (e : brs) : brs :=
  match e with
  | br_None => br_None
  | br_One K a brs5 => br_One K (fc_close_tm_tm n x a) (fc_close_tm_brs n x brs5)
  end
with fc_close_tm_co (n : nat) (x : atom) (e : co) : co :=
  match e with
  | g_Triv => g_Triv
  | g_Var_b i => g_Var_b i
  | g_Var_f c => g_Var_f c
  | g_Beta a b => g_Beta (fc_close_tm_tm n x a) (fc_close_tm_tm n x b)
  | g_Refl a => g_Refl (fc_close_tm_tm n x a)
  | g_Refl2 a b g => g_Refl2 (fc_close_tm_tm n x a) (fc_close_tm_tm n x b) (fc_close_tm_co n x g)
  | g_Sym g => g_Sym (fc_close_tm_co n x g)
  | g_Trans g1 g2 => g_Trans (fc_close_tm_co n x g1) (fc_close_tm_co n x g2)
  | g_PiCong rho g1 g2 => g_PiCong rho (fc_close_tm_co n x g1) (fc_close_tm_co (S n) x g2)
  | g_AbsCong rho g1 g2 => g_AbsCong rho (fc_close_tm_co n x g1) (fc_close_tm_co (S n) x g2)
  | g_AppCong g1 rho g2 => g_AppCong (fc_close_tm_co n x g1) rho (fc_close_tm_co n x g2)
  | g_PiFst g => g_PiFst (fc_close_tm_co n x g)
  | g_CPiFst g => g_CPiFst (fc_close_tm_co n x g)
  | g_IsoSnd g => g_IsoSnd (fc_close_tm_co n x g)
  | g_PiSnd g1 g2 => g_PiSnd (fc_close_tm_co n x g1) (fc_close_tm_co n x g2)
  | g_CPiCong g1 g3 => g_CPiCong (fc_close_tm_co n x g1) (fc_close_tm_co n x g3)
  | g_CAbsCong g1 g3 g4 => g_CAbsCong (fc_close_tm_co n x g1) (fc_close_tm_co n x g3) (fc_close_tm_co n x g4)
  | g_CAppCong g g1 g2 => g_CAppCong (fc_close_tm_co n x g) (fc_close_tm_co n x g1) (fc_close_tm_co n x g2)
  | g_CPiSnd g g1 g2 => g_CPiSnd (fc_close_tm_co n x g) (fc_close_tm_co n x g1) (fc_close_tm_co n x g2)
  | g_Cast g1 g2 => g_Cast (fc_close_tm_co n x g1) (fc_close_tm_co n x g2)
  | g_EqCong g1 A g2 => g_EqCong (fc_close_tm_co n x g1) (fc_close_tm_tm n x A) (fc_close_tm_co n x g2)
  | g_IsoConv phi1 phi2 g => g_IsoConv (fc_close_tm_constraint n x phi1) (fc_close_tm_constraint n x phi2) (fc_close_tm_co n x g)
  | g_Eta a => g_Eta (fc_close_tm_tm n x a)
  | g_Left g g' => g_Left (fc_close_tm_co n x g) (fc_close_tm_co n x g')
  | g_Right g g' => g_Right (fc_close_tm_co n x g) (fc_close_tm_co n x g')
  end
with fc_close_tm_constraint (n : nat) (x : atom) (e : constraint) : constraint :=
  match e with
  | Eq a b A => Eq (fc_close_tm_tm n x a) (fc_close_tm_tm n x b) (fc_close_tm_tm n x A)
  end.

Fixpoint fc_close_co_tm (n : nat) (x : atom) (e : tm) : tm :=
  match e with
  | a_Star => a_Star
  | a_Var_b i => a_Var_b i
  | a_Var_f x0 => a_Var_f x0
  | a_Abs rho A b => a_Abs rho (fc_close_co_tm n x A) (fc_close_co_tm n x b)
  | a_UAbs rho b => a_UAbs rho (fc_close_co_tm n x b)
  | a_App a rho b => a_App (fc_close_co_tm n x a) rho (fc_close_co_tm n x b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (fc_close_co_tm n x A) (fc_close_co_tm n x B)
  | a_Conv a g => a_Conv (fc_close_co_tm n x a) (fc_close_co_co n x g)
  | a_CPi phi B => a_CPi (fc_close_co_constraint n x phi) (fc_close_co_tm (S n) x B)
  | a_CAbs phi b => a_CAbs (fc_close_co_constraint n x phi) (fc_close_co_tm (S n) x b)
  | a_UCAbs b => a_UCAbs (fc_close_co_tm (S n) x b)
  | a_CApp a g => a_CApp (fc_close_co_tm n x a) (fc_close_co_co n x g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs5 => a_Case (fc_close_co_tm n x a) (fc_close_co_brs n x brs5)
  end
with fc_close_co_brs (n : nat) (x : atom) (e : brs) : brs :=
  match e with
  | br_None => br_None
  | br_One K a brs5 => br_One K (fc_close_co_tm n x a) (fc_close_co_brs n x brs5)
  end
with fc_close_co_co (n : nat) (x : atom) (e : co) : co :=
  match e with
  | g_Triv => g_Triv
  | g_Var_b i => if lt_dec i n then g_Var_b i else g_Var_b (S i)
  | g_Var_f c => if c == x then g_Var_b n else g_Var_f c
  | g_Beta a b => g_Beta (fc_close_co_tm n x a) (fc_close_co_tm n x b)
  | g_Refl a => g_Refl (fc_close_co_tm n x a)
  | g_Refl2 a b g => g_Refl2 (fc_close_co_tm n x a) (fc_close_co_tm n x b) (fc_close_co_co n x g)
  | g_Sym g => g_Sym (fc_close_co_co n x g)
  | g_Trans g1 g2 => g_Trans (fc_close_co_co n x g1) (fc_close_co_co n x g2)
  | g_PiCong rho g1 g2 => g_PiCong rho (fc_close_co_co n x g1) (fc_close_co_co n x g2)
  | g_AbsCong rho g1 g2 => g_AbsCong rho (fc_close_co_co n x g1) (fc_close_co_co n x g2)
  | g_AppCong g1 rho g2 => g_AppCong (fc_close_co_co n x g1) rho (fc_close_co_co n x g2)
  | g_PiFst g => g_PiFst (fc_close_co_co n x g)
  | g_CPiFst g => g_CPiFst (fc_close_co_co n x g)
  | g_IsoSnd g => g_IsoSnd (fc_close_co_co n x g)
  | g_PiSnd g1 g2 => g_PiSnd (fc_close_co_co n x g1) (fc_close_co_co n x g2)
  | g_CPiCong g1 g3 => g_CPiCong (fc_close_co_co n x g1) (fc_close_co_co (S n) x g3)
  | g_CAbsCong g1 g3 g4 => g_CAbsCong (fc_close_co_co n x g1) (fc_close_co_co (S n) x g3) (fc_close_co_co n x g4)
  | g_CAppCong g g1 g2 => g_CAppCong (fc_close_co_co n x g) (fc_close_co_co n x g1) (fc_close_co_co n x g2)
  | g_CPiSnd g g1 g2 => g_CPiSnd (fc_close_co_co n x g) (fc_close_co_co n x g1) (fc_close_co_co n x g2)
  | g_Cast g1 g2 => g_Cast (fc_close_co_co n x g1) (fc_close_co_co n x g2)
  | g_EqCong g1 A g2 => g_EqCong (fc_close_co_co n x g1) (fc_close_co_tm n x A) (fc_close_co_co n x g2)
  | g_IsoConv phi1 phi2 g => g_IsoConv (fc_close_co_constraint n x phi1) (fc_close_co_constraint n x phi2) (fc_close_co_co n x g)
  | g_Eta a => g_Eta (fc_close_co_tm n x a)
  | g_Left g g' => g_Left (fc_close_co_co n x g) (fc_close_co_co n x g')
  | g_Right g g' => g_Right (fc_close_co_co n x g) (fc_close_co_co n x g')
  end
with fc_close_co_constraint (n : nat) (x : atom) (e : constraint) : constraint :=
  match e with
  | Eq a b A => Eq (fc_close_co_tm n x a) (fc_close_co_tm n x b) (fc_close_co_tm n x A)
  end.

Fixpoint fc_eq_tm (a b : tm) {struct a} : {a = b} + {a <> b}
with fc_eq_brs (a b : brs) {struct a} : {a = b} + {a <> b}
with fc_eq_co (a b : co) {struct a} : {a = b} + {a <> b}
with fc_eq_constraint (a b : constraint) {struct a} : {a = b} + {a <> b}.
Proof.
  all: decide equality; try apply Atom.eq_dec; try decide equality.
Defined.

Lemma fc_open_size :
  (forall e n x, fc_size_tm (open_tm_wrt_tm_rec n (a_Var_f x) e) = fc_size_tm e) /\
  (forall e n x, fc_size_brs (open_brs_wrt_tm_rec n (a_Var_f x) e) = fc_size_brs e) /\
  (forall e n x, fc_size_co (open_co_wrt_tm_rec n (a_Var_f x) e) = fc_size_co e) /\
  (forall e n x, fc_size_constraint (open_constraint_wrt_tm_rec n (a_Var_f x) e) = fc_size_constraint e).
Proof.
  apply fc_syntax_ind; intros; cbn;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H end;
    repeat destruct lt_eq_lt_dec as [[]|]; reflexivity.
Qed.

Lemma fc_copen_size :
  (forall e n x, fc_size_tm (open_tm_wrt_co_rec n (g_Var_f x) e) = fc_size_tm e) /\
  (forall e n x, fc_size_brs (open_brs_wrt_co_rec n (g_Var_f x) e) = fc_size_brs e) /\
  (forall e n x, fc_size_co (open_co_wrt_co_rec n (g_Var_f x) e) = fc_size_co e) /\
  (forall e n x, fc_size_constraint (open_constraint_wrt_co_rec n (g_Var_f x) e) = fc_size_constraint e).
Proof.
  apply fc_syntax_ind; intros; cbn;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H end;
    repeat destruct lt_eq_lt_dec as [[]|]; reflexivity.
Qed.

Lemma fc_close_after_open :
  (forall e n x, x \notin fc_fv_tm e ->
    fc_close_tm_tm n x (open_tm_wrt_tm_rec n (a_Var_f x) e) = e) /\
  (forall e n x, x \notin fc_fv_brs e ->
    fc_close_tm_brs n x (open_brs_wrt_tm_rec n (a_Var_f x) e) = e) /\
  (forall e n x, x \notin fc_fv_co e ->
    fc_close_tm_co n x (open_co_wrt_tm_rec n (a_Var_f x) e) = e) /\
  (forall e n x, x \notin fc_fv_constraint e ->
    fc_close_tm_constraint n x (open_constraint_wrt_tm_rec n (a_Var_f x) e) = e).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H by fsetdec end;
    repeat destruct lt_eq_lt_dec as [[?|?]|?]; cbn;
    repeat destruct lt_dec; repeat destruct (_ == _); try subst; try fsetdec;
    try reflexivity; f_equal; lia.
Qed.

Lemma fc_cclose_after_open :
  (forall e n x, x \notin fc_fv_tm e ->
    fc_close_co_tm n x (open_tm_wrt_co_rec n (g_Var_f x) e) = e) /\
  (forall e n x, x \notin fc_fv_brs e ->
    fc_close_co_brs n x (open_brs_wrt_co_rec n (g_Var_f x) e) = e) /\
  (forall e n x, x \notin fc_fv_co e ->
    fc_close_co_co n x (open_co_wrt_co_rec n (g_Var_f x) e) = e) /\
  (forall e n x, x \notin fc_fv_constraint e ->
    fc_close_co_constraint n x (open_constraint_wrt_co_rec n (g_Var_f x) e) = e).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H by fsetdec end;
    repeat destruct lt_eq_lt_dec as [[?|?]|?]; cbn;
    repeat destruct lt_dec; repeat destruct (_ == _); try subst; try fsetdec;
    try reflexivity; f_equal; lia.
Qed.

Lemma fc_open_after_close :
  (forall e n x, open_tm_wrt_tm_rec n (a_Var_f x) (fc_close_tm_tm n x e) = e) /\
  (forall e n x, open_brs_wrt_tm_rec n (a_Var_f x) (fc_close_tm_brs n x e) = e) /\
  (forall e n x, open_co_wrt_tm_rec n (a_Var_f x) (fc_close_tm_co n x e) = e) /\
  (forall e n x, open_constraint_wrt_tm_rec n (a_Var_f x) (fc_close_tm_constraint n x e) = e).
Proof.
  apply fc_syntax_ind; intros; cbn;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H end;
    repeat destruct lt_dec; repeat destruct (_ == _); try subst; cbn -[lt_eq_lt_dec];
    repeat destruct lt_eq_lt_dec as [[?|?]|?]; try reflexivity; f_equal; lia.
Qed.

Lemma fc_copen_after_close :
  (forall e n x, open_tm_wrt_co_rec n (g_Var_f x) (fc_close_co_tm n x e) = e) /\
  (forall e n x, open_brs_wrt_co_rec n (g_Var_f x) (fc_close_co_brs n x e) = e) /\
  (forall e n x, open_co_wrt_co_rec n (g_Var_f x) (fc_close_co_co n x e) = e) /\
  (forall e n x, open_constraint_wrt_co_rec n (g_Var_f x) (fc_close_co_constraint n x e) = e).
Proof.
  apply fc_syntax_ind; intros; cbn;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H end;
    repeat destruct lt_dec; repeat destruct (_ == _); try subst; cbn -[lt_eq_lt_dec];
    repeat destruct lt_eq_lt_dec as [[?|?]|?]; try reflexivity; f_equal; lia.
Qed.

Lemma fc_degree_mono :
  (forall e p q p' q', p <= p' -> q <= q' -> fc_degree_tm p q e -> fc_degree_tm p' q' e) /\
  (forall e p q p' q', p <= p' -> q <= q' -> fc_degree_brs p q e -> fc_degree_brs p' q' e) /\
  (forall e p q p' q', p <= p' -> q <= q' -> fc_degree_co p q e -> fc_degree_co p' q' e) /\
  (forall e p q p' q', p <= p' -> q <= q' -> fc_degree_constraint p q e -> fc_degree_constraint p' q' e).
Proof.
  apply fc_syntax_ind; intros; cbn in *; try lia;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try (eapply H; [idtac|idtac|eassumption]; lia);
    try (eapply H0; [idtac|idtac|eassumption]; lia); try (eapply H1; [idtac|idtac|eassumption]; lia).
Qed.
Definition fc_degree_mono_tm := proj1 (fc_degree_mono).
Definition fc_degree_mono_co := proj1 (proj2 (proj2 (fc_degree_mono))).

Lemma fc_tmopen_degree :
  (forall e p q n u, n <= p -> fc_degree_tm 0 0 u ->
    fc_degree_tm (S p) q e -> fc_degree_tm p q (open_tm_wrt_tm_rec n u e)) /\
  (forall e p q n u, n <= p -> fc_degree_tm 0 0 u ->
    fc_degree_brs (S p) q e -> fc_degree_brs p q (open_brs_wrt_tm_rec n u e)) /\
  (forall e p q n u, n <= p -> fc_degree_tm 0 0 u ->
    fc_degree_co (S p) q e -> fc_degree_co p q (open_co_wrt_tm_rec n u e)) /\
  (forall e p q n u, n <= p -> fc_degree_tm 0 0 u ->
    fc_degree_constraint (S p) q e -> fc_degree_constraint p q (open_constraint_wrt_tm_rec n u e)).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try assumption; try (eapply H; [idtac|eassumption|eassumption]; lia);
    try (eapply H0; [idtac|eassumption|eassumption]; lia);
    try (eapply H1; [idtac|eassumption|eassumption]; lia);
    destruct lt_eq_lt_dec as [[?|?]|?]; cbn; try lia;
    eapply fc_degree_mono_tm; [idtac|idtac|eassumption]; lia.
Qed.
Definition fc_tmopen_degree_tm := proj1 (fc_tmopen_degree).
Definition fc_tmopen_degree_co := proj1 (proj2 (proj2 (fc_tmopen_degree))).

Lemma fc_tmopen_degree_inv :
  (forall e p q n u, n <= p ->
    fc_degree_tm p q (open_tm_wrt_tm_rec n u e) -> fc_degree_tm (S p) q e) /\
  (forall e p q n u, n <= p ->
    fc_degree_brs p q (open_brs_wrt_tm_rec n u e) -> fc_degree_brs (S p) q e) /\
  (forall e p q n u, n <= p ->
    fc_degree_co p q (open_co_wrt_tm_rec n u e) -> fc_degree_co (S p) q e) /\
  (forall e p q n u, n <= p ->
    fc_degree_constraint p q (open_constraint_wrt_tm_rec n u e) -> fc_degree_constraint (S p) q e).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try assumption; try (eapply H; [idtac|eassumption]; lia);
    try (eapply H0; [idtac|eassumption]; lia); try (eapply H1; [idtac|eassumption]; lia);
    destruct lt_eq_lt_dec as [[?|?]|?] in *; cbn in *; lia.
Qed.
Definition fc_tmopen_degree_inv_tm := proj1 (fc_tmopen_degree_inv).
Definition fc_tmopen_degree_inv_co := proj1 (proj2 (proj2 (fc_tmopen_degree_inv))).

Lemma fc_tmopen_id :
  (forall e p q u, fc_degree_tm p q e -> open_tm_wrt_tm_rec p u e = e) /\
  (forall e p q u, fc_degree_brs p q e -> open_brs_wrt_tm_rec p u e = e) /\
  (forall e p q u, fc_degree_co p q e -> open_co_wrt_tm_rec p u e = e) /\
  (forall e p q u, fc_degree_constraint p q e -> open_constraint_wrt_tm_rec p u e = e).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : forall _ _ _, _ |- _ => erewrite H by eassumption end;
    try reflexivity; destruct lt_eq_lt_dec as [[?|?]|?]; try reflexivity; lia.
Qed.
Definition fc_tmopen_id_tm := proj1 (fc_tmopen_id).
Definition fc_tmopen_id_co := proj1 (proj2 (proj2 (fc_tmopen_id))).

Lemma fc_subst_tmopen :
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_tm f h (open_tm_wrt_tm_rec n u e) = open_tm_wrt_tm_rec n (fc_subst_tm f h u) (fc_subst_tm f h e)) /\
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_brs f h (open_brs_wrt_tm_rec n u e) = open_brs_wrt_tm_rec n (fc_subst_tm f h u) (fc_subst_brs f h e)) /\
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_co f h (open_co_wrt_tm_rec n u e) = open_co_wrt_tm_rec n (fc_subst_tm f h u) (fc_subst_co f h e)) /\
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_constraint f h (open_constraint_wrt_tm_rec n u e) = open_constraint_wrt_tm_rec n (fc_subst_tm f h u) (fc_subst_constraint f h e)).
Proof.
  apply fc_syntax_ind; intros; cbn;
    repeat match goal with H : forall _ _ _ _, _ |- _ => rewrite H by assumption end;
    try reflexivity;
    try (destruct lt_eq_lt_dec as [[?|?]|?]; reflexivity);
    symmetry; first
      [ eapply fc_tmopen_id_tm with (q := 0); eapply fc_degree_mono_tm; [idtac|idtac|first [apply H | apply H0]]; lia
      | eapply fc_tmopen_id_co with (q := 0); eapply fc_degree_mono_co; [idtac|idtac|first [apply H | apply H0]]; lia ].
Qed.
Definition fc_subst_tmopen_tm := proj1 (fc_subst_tmopen).
Definition fc_subst_tmopen_co := proj1 (proj2 (proj2 (fc_subst_tmopen))).

Lemma fc_coopen_degree :
  (forall e p q n u, n <= q -> fc_degree_co 0 0 u ->
    fc_degree_tm p (S q) e -> fc_degree_tm p q (open_tm_wrt_co_rec n u e)) /\
  (forall e p q n u, n <= q -> fc_degree_co 0 0 u ->
    fc_degree_brs p (S q) e -> fc_degree_brs p q (open_brs_wrt_co_rec n u e)) /\
  (forall e p q n u, n <= q -> fc_degree_co 0 0 u ->
    fc_degree_co p (S q) e -> fc_degree_co p q (open_co_wrt_co_rec n u e)) /\
  (forall e p q n u, n <= q -> fc_degree_co 0 0 u ->
    fc_degree_constraint p (S q) e -> fc_degree_constraint p q (open_constraint_wrt_co_rec n u e)).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try assumption; try (eapply H; [idtac|eassumption|eassumption]; lia);
    try (eapply H0; [idtac|eassumption|eassumption]; lia);
    try (eapply H1; [idtac|eassumption|eassumption]; lia);
    destruct lt_eq_lt_dec as [[?|?]|?]; cbn; try lia;
    eapply fc_degree_mono_co; [idtac|idtac|eassumption]; lia.
Qed.
Definition fc_coopen_degree_tm := proj1 (fc_coopen_degree).
Definition fc_coopen_degree_co := proj1 (proj2 (proj2 (fc_coopen_degree))).

Lemma fc_coopen_degree_inv :
  (forall e p q n u, n <= q ->
    fc_degree_tm p q (open_tm_wrt_co_rec n u e) -> fc_degree_tm p (S q) e) /\
  (forall e p q n u, n <= q ->
    fc_degree_brs p q (open_brs_wrt_co_rec n u e) -> fc_degree_brs p (S q) e) /\
  (forall e p q n u, n <= q ->
    fc_degree_co p q (open_co_wrt_co_rec n u e) -> fc_degree_co p (S q) e) /\
  (forall e p q n u, n <= q ->
    fc_degree_constraint p q (open_constraint_wrt_co_rec n u e) -> fc_degree_constraint p (S q) e).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try assumption; try (eapply H; [idtac|eassumption]; lia);
    try (eapply H0; [idtac|eassumption]; lia); try (eapply H1; [idtac|eassumption]; lia);
    destruct lt_eq_lt_dec as [[?|?]|?] in *; cbn in *; lia.
Qed.
Definition fc_coopen_degree_inv_tm := proj1 (fc_coopen_degree_inv).
Definition fc_coopen_degree_inv_co := proj1 (proj2 (proj2 (fc_coopen_degree_inv))).

Lemma fc_coopen_id :
  (forall e p q u, fc_degree_tm p q e -> open_tm_wrt_co_rec q u e = e) /\
  (forall e p q u, fc_degree_brs p q e -> open_brs_wrt_co_rec q u e = e) /\
  (forall e p q u, fc_degree_co p q e -> open_co_wrt_co_rec q u e = e) /\
  (forall e p q u, fc_degree_constraint p q e -> open_constraint_wrt_co_rec q u e = e).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : forall _ _ _, _ |- _ => erewrite H by eassumption end;
    try reflexivity; destruct lt_eq_lt_dec as [[?|?]|?]; try reflexivity; lia.
Qed.
Definition fc_coopen_id_tm := proj1 (fc_coopen_id).
Definition fc_coopen_id_co := proj1 (proj2 (proj2 (fc_coopen_id))).

Lemma fc_subst_coopen :
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_tm f h (open_tm_wrt_co_rec n u e) = open_tm_wrt_co_rec n (fc_subst_co f h u) (fc_subst_tm f h e)) /\
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_brs f h (open_brs_wrt_co_rec n u e) = open_brs_wrt_co_rec n (fc_subst_co f h u) (fc_subst_brs f h e)) /\
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_co f h (open_co_wrt_co_rec n u e) = open_co_wrt_co_rec n (fc_subst_co f h u) (fc_subst_co f h e)) /\
  (forall e f h n u,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_subst_constraint f h (open_constraint_wrt_co_rec n u e) = open_constraint_wrt_co_rec n (fc_subst_co f h u) (fc_subst_constraint f h e)).
Proof.
  apply fc_syntax_ind; intros; cbn;
    repeat match goal with H : forall _ _ _ _, _ |- _ => rewrite H by assumption end;
    try reflexivity;
    try (destruct lt_eq_lt_dec as [[?|?]|?]; reflexivity);
    symmetry; first
      [ eapply fc_coopen_id_tm with (p := 0); eapply fc_degree_mono_tm; [idtac|idtac|first [apply H | apply H0]]; lia
      | eapply fc_coopen_id_co with (p := 0); eapply fc_degree_mono_co; [idtac|idtac|first [apply H | apply H0]]; lia ].
Qed.
Definition fc_subst_coopen_tm := proj1 (fc_subst_coopen).
Definition fc_subst_coopen_co := proj1 (proj2 (proj2 (fc_subst_coopen))).

Lemma fc_subst_ext :
  (forall e f h f' h',
    (forall x, AtomSetImpl.In x (fc_fv_tm e) -> f x = f' x) ->
    (forall x, AtomSetImpl.In x (fc_fv_tm e) -> h x = h' x) ->
    fc_subst_tm f h e = fc_subst_tm f' h' e) /\
  (forall e f h f' h',
    (forall x, AtomSetImpl.In x (fc_fv_brs e) -> f x = f' x) ->
    (forall x, AtomSetImpl.In x (fc_fv_brs e) -> h x = h' x) ->
    fc_subst_brs f h e = fc_subst_brs f' h' e) /\
  (forall e f h f' h',
    (forall x, AtomSetImpl.In x (fc_fv_co e) -> f x = f' x) ->
    (forall x, AtomSetImpl.In x (fc_fv_co e) -> h x = h' x) ->
    fc_subst_co f h e = fc_subst_co f' h' e) /\
  (forall e f h f' h',
    (forall x, AtomSetImpl.In x (fc_fv_constraint e) -> f x = f' x) ->
    (forall x, AtomSetImpl.In x (fc_fv_constraint e) -> h x = h' x) ->
    fc_subst_constraint f h e = fc_subst_constraint f' h' e).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    try (f_equal; ((apply H || apply H0 || apply H1); intros; auto using AtomSetImpl.union_2, AtomSetImpl.union_3));
    try (apply H; fsetdec); try (apply H0; fsetdec); reflexivity.
Qed.
Definition fc_subst_ext_tm := proj1 (fc_subst_ext).
Definition fc_subst_ext_co := proj1 (proj2 (proj2 (fc_subst_ext))).

Lemma fc_subst_id :
  (forall e, fc_subst_tm a_Var_f g_Var_f e = e) /\
  (forall e, fc_subst_brs a_Var_f g_Var_f e = e) /\
  (forall e, fc_subst_co a_Var_f g_Var_f e = e) /\
  (forall e, fc_subst_constraint a_Var_f g_Var_f e = e).
Proof.
  apply fc_syntax_ind; intros; cbn; congruence.
Qed.
Definition fc_subst_id_tm := proj1 (fc_subst_id).
Definition fc_subst_id_co := proj1 (proj2 (proj2 (fc_subst_id))).
Definition fc_subst_id_constraint := proj2 (proj2 (proj2 (fc_subst_id))).

Lemma fc_subst_degree :
  (forall e f h p q,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_degree_tm p q e -> fc_degree_tm p q (fc_subst_tm f h e)) /\
  (forall e f h p q,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_degree_brs p q e -> fc_degree_brs p q (fc_subst_brs f h e)) /\
  (forall e f h p q,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_degree_co p q e -> fc_degree_co p q (fc_subst_co f h e)) /\
  (forall e f h p q,
    (forall x, fc_degree_tm 0 0 (f x)) -> (forall x, fc_degree_co 0 0 (h x)) ->
    fc_degree_constraint p q e -> fc_degree_constraint p q (fc_subst_constraint f h e)).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try assumption; try (apply H; assumption);
    try (apply H0; assumption); try (apply H1; assumption);
    try (eapply fc_degree_mono_tm with (p := 0) (q := 0); [lia|lia|apply H]);
    try (eapply fc_degree_mono_co with (p := 0) (q := 0); [lia|lia|apply H0]).
Qed.
Definition fc_subst_degree_tm := proj1 (fc_subst_degree).
Definition fc_subst_degree_co := proj1 (proj2 (proj2 (fc_subst_degree))).

Lemma fc_erase_subst :
  (forall e f h, erase_tm (fc_subst_tm f h e) =
    fc_subst_tm (fun x => erase_tm (f x)) g_Var_f (erase_tm e)) /\
  (forall e f h, erase_brs (fc_subst_brs f h e) =
    fc_subst_brs (fun x => erase_tm (f x)) g_Var_f (erase_brs e)) /\
  (forall e : co, True) /\
  (forall e f h, erase_constraint (fc_subst_constraint f h e) =
    fc_subst_constraint (fun x => erase_tm (f x)) g_Var_f (erase_constraint e)).
Proof.
  apply fc_syntax_ind; intros; cbn; try destruct rho; cbn;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H end;
    auto.
Qed.

Lemma fc_erase_degree :
  (forall e p q, fc_degree_tm p q e -> fc_degree_tm p q (erase_tm e)) /\
  (forall e p q, fc_degree_brs p q e -> fc_degree_brs p q (erase_brs e)) /\
  (forall e : co, True) /\
  (forall e p q, fc_degree_constraint p q e -> fc_degree_constraint p q (erase_constraint e)).
Proof.
  apply fc_syntax_ind; intros; cbn in *; try destruct rho; cbn in *; intuition eauto.
Qed.

Lemma fc_erase_topen :
  (forall e n a, erase_tm (open_tm_wrt_tm_rec n a e) =
    open_tm_wrt_tm_rec n (erase_tm a) (erase_tm e)) /\
  (forall e n a, erase_brs (open_brs_wrt_tm_rec n a e) =
    open_brs_wrt_tm_rec n (erase_tm a) (erase_brs e)) /\
  (forall e : co, True) /\
  (forall e n a, erase_constraint (open_constraint_wrt_tm_rec n a e) =
    open_constraint_wrt_tm_rec n (erase_tm a) (erase_constraint e)).
Proof.
  apply fc_syntax_ind; intros; cbn; try destruct rho; cbn;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H end;
    try destruct lt_eq_lt_dec as [[]|]; auto.
Qed.

Lemma fc_fv_subst_relevant :
  (forall e f h x,
    (forall y, y <> x -> x \notin fv_tm_tm_tm (f y)) ->
    (forall y, x \notin fv_tm_tm_co (h y)) ->
    x \notin fv_tm_tm_tm e -> x \notin fv_tm_tm_tm (fc_subst_tm f h e)) /\
  (forall e f h x,
    (forall y, y <> x -> x \notin fv_tm_tm_tm (f y)) ->
    (forall y, x \notin fv_tm_tm_co (h y)) ->
    x \notin fv_tm_tm_brs e -> x \notin fv_tm_tm_brs (fc_subst_brs f h e)) /\
  (forall e f h x,
    (forall y, y <> x -> x \notin fv_tm_tm_tm (f y)) ->
    (forall y, x \notin fv_tm_tm_co (h y)) ->
    x \notin fv_tm_tm_co e -> x \notin fv_tm_tm_co (fc_subst_co f h e)) /\
  (forall e f h x,
    (forall y, y <> x -> x \notin fv_tm_tm_tm (f y)) ->
    (forall y, x \notin fv_tm_tm_co (h y)) ->
    x \notin fv_tm_tm_constraint e -> x \notin fv_tm_tm_constraint (fc_subst_constraint f h e)).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    try (apply H; assumption); try (apply H0; assumption);
    repeat match goal with
    | F : forall y : atom, y <> ?x -> ~ AtomSetImpl.In ?x (fv_tm_tm_tm (?f y)),
      C : forall y : atom, ~ AtomSetImpl.In ?x (fv_tm_tm_co (?h y)),
      IH : forall (u : atom -> tm) (v : atom -> co) (z : atom), _ |- _ =>
        specialize (IH f h x F C ltac:(fsetdec))
    end;
    try (apply H; fsetdec); fsetdec.
Qed.

(** Local closure, substitution, and erasure. *)

Definition fc_erase_subst_tm := proj1 fc_erase_subst.
Definition fc_erase_degree_tm := proj1 fc_erase_degree.
Definition fc_erase_topen_tm := proj1 fc_erase_topen.

Ltac fc_unpack :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Definition fc_sz_topen_tm := proj1 fc_open_size.
Definition fc_sz_topen_co := proj1 (proj2 (proj2 fc_open_size)).
Definition fc_sz_copen_tm := proj1 fc_copen_size.
Definition fc_sz_copen_co := proj1 (proj2 (proj2 fc_copen_size)).

Ltac fc_open_sizes :=
  unfold open_tm_wrt_tm, open_tm_wrt_co, open_co_wrt_tm, open_co_wrt_co in *;
  rewrite ?fc_sz_topen_tm, ?fc_sz_topen_co, ?fc_sz_copen_tm, ?fc_sz_copen_co in *.

Ltac fc_ind_small :=
  match goal with IH : forall m : nat, m < _ -> _ |- _ =>
    lazymatch goal with
    | |- lc_tm ?a => refine ((proj1 (IH (fc_size_tm a) _)) a eq_refl _)
    | |- lc_brs ?a => refine ((proj1 (proj2 (IH (fc_size_brs a) _))) a eq_refl _)
    | |- lc_co ?a => refine ((proj1 (proj2 (proj2 (IH (fc_size_co a) _)))) a eq_refl _)
    | |- lc_constraint ?a => refine ((proj2 (proj2 (proj2 (IH (fc_size_constraint a) _)))) a eq_refl _)
    end; [fc_open_sizes; cbn in *; lia | idtac]
  end.

Lemma fc_degree_lc_size : forall n,
  (forall e, fc_size_tm e = n -> fc_degree_tm 0 0 e -> lc_tm e) /\
  (forall e, fc_size_brs e = n -> fc_degree_brs 0 0 e -> lc_brs e) /\
  (forall e, fc_size_co e = n -> fc_degree_co 0 0 e -> lc_co e) /\
  (forall e, fc_size_constraint e = n -> fc_degree_constraint 0 0 e -> lc_constraint e).
Proof.
  induction n using lt_wf_ind.
  repeat split; intros e E C; destruct e; cbn in C; fc_unpack.
  all: try solve [exfalso; lia].
  all: constructor.
  all: intros; fc_ind_small.
  all: try assumption.
  all: lazymatch goal with
    | |- fc_degree_tm _ _ (open_tm_wrt_tm _ _) => eapply fc_tmopen_degree_tm
    | |- fc_degree_tm _ _ (open_tm_wrt_co _ _) => eapply fc_coopen_degree_tm
    | |- fc_degree_co _ _ (open_co_wrt_tm _ _) => eapply fc_tmopen_degree_co
    | |- fc_degree_co _ _ (open_co_wrt_co _ _) => eapply fc_coopen_degree_co
    end; [lia | exact I | assumption].
Qed.

Lemma fc_degree_lc_tm : forall e, fc_degree_tm 0 0 e -> lc_tm e.
Proof. intros e H; exact ((proj1 (fc_degree_lc_size (fc_size_tm e))) e eq_refl H). Qed.
Lemma fc_degree_lc_co : forall e, fc_degree_co 0 0 e -> lc_co e.
Proof. intros e H; exact ((proj1 (proj2 (proj2 (fc_degree_lc_size (fc_size_co e))))) e eq_refl H). Qed.

Scheme fc_ind_lcc := Induction for lc_constraint Sort Prop
with fc_ind_lcg := Induction for lc_co Sort Prop
with fc_ind_lcb := Induction for lc_brs Sort Prop
with fc_ind_lct := Induction for lc_tm Sort Prop.
Combined Scheme fc_lc_ind from fc_ind_lcc, fc_ind_lcg, fc_ind_lcb, fc_ind_lct.

Lemma fc_lc_degree :
  (forall e, lc_constraint e -> fc_degree_constraint 0 0 e) /\
  (forall e, lc_co e -> fc_degree_co 0 0 e) /\
  (forall e, lc_brs e -> fc_degree_brs 0 0 e) /\
  (forall e, lc_tm e -> fc_degree_tm 0 0 e).
Proof.
  apply fc_lc_ind; intros; cbn; repeat split; try assumption;
    match goal with
    | IH : forall x, fc_degree_tm 0 0 (open_tm_wrt_tm _ (a_Var_f x)) |- _ =>
        eapply fc_tmopen_degree_inv_tm with (n:=0) (u:=a_Var_f Fix); [lia | apply IH]
    | IH : forall x, fc_degree_co 0 0 (open_co_wrt_tm _ (a_Var_f x)) |- _ =>
        eapply fc_tmopen_degree_inv_co with (n:=0) (u:=a_Var_f Fix); [lia | apply IH]
    | IH : forall x, fc_degree_tm 0 0 (open_tm_wrt_co _ (g_Var_f x)) |- _ =>
        eapply fc_coopen_degree_inv_tm with (n:=0) (u:=g_Var_f Fix); [lia | apply IH]
    | IH : forall x, fc_degree_co 0 0 (open_co_wrt_co _ (g_Var_f x)) |- _ =>
        eapply fc_coopen_degree_inv_co with (n:=0) (u:=g_Var_f Fix); [lia | apply IH]
    end.
Qed.

Definition fc_lc_degree_tm := proj2 (proj2 (proj2 fc_lc_degree)).
Definition fc_lc_degree_co := proj1 (proj2 fc_lc_degree).

Record fc_map : Type := FcMap {
  fc_tmap : atom -> tm;
  fc_cmap : atom -> co;
  fc_changed : atoms;
  fc_tmap_degree : forall x, fc_degree_tm 0 0 (fc_tmap x);
  fc_cmap_degree : forall x, fc_degree_co 0 0 (fc_cmap x);
  fc_tmap_fresh : forall x, x \notin fc_changed -> fc_tmap x = a_Var_f x;
  fc_cmap_fresh : forall x, x \notin fc_changed -> fc_cmap x = g_Var_f x;
  fc_tmap_relevance : forall x y, x \notin fc_changed -> x <> y ->
      x \notin fv_tm_tm_tm (erase_tm (fc_tmap y))
}.

Definition fc_T f := fc_subst_tm (fc_tmap f) (fc_cmap f).
Definition fc_C f := fc_subst_co (fc_tmap f) (fc_cmap f).
Definition fc_P f := fc_subst_constraint (fc_tmap f) (fc_cmap f).

Lemma fc_T_open_t : forall f a u, fc_T f (open_tm_wrt_tm a u) =
  open_tm_wrt_tm (fc_T f a) (fc_T f u).
Proof. intros; apply fc_subst_tmopen_tm; [apply fc_tmap_degree | apply fc_cmap_degree]. Qed.
Lemma fc_C_open_t : forall f a u, fc_C f (open_co_wrt_tm a u) =
  open_co_wrt_tm (fc_C f a) (fc_T f u).
Proof. intros; apply fc_subst_tmopen_co; [apply fc_tmap_degree | apply fc_cmap_degree]. Qed.
Lemma fc_T_open_c : forall f a u, fc_T f (open_tm_wrt_co a u) =
  open_tm_wrt_co (fc_T f a) (fc_C f u).
Proof. intros; apply fc_subst_coopen_tm; [apply fc_tmap_degree | apply fc_cmap_degree]. Qed.
Lemma fc_C_open_c : forall f a u, fc_C f (open_co_wrt_co a u) =
  open_co_wrt_co (fc_C f a) (fc_C f u).
Proof. intros; apply fc_subst_coopen_co; [apply fc_tmap_degree | apply fc_cmap_degree]. Qed.
Lemma fc_T_lc : forall f a, lc_tm a -> lc_tm (fc_T f a).
Proof.
  intros; apply fc_degree_lc_tm, fc_subst_degree_tm;
    auto using fc_tmap_degree, fc_cmap_degree, fc_lc_degree_tm.
Qed.
Lemma fc_C_lc : forall f a, lc_co a -> lc_co (fc_C f a).
Proof.
  intros; apply fc_degree_lc_co, fc_subst_degree_co;
    auto using fc_tmap_degree, fc_cmap_degree, fc_lc_degree_co.
Qed.
Lemma fc_P_lc : forall f phi, lc_constraint phi -> lc_constraint (fc_P f phi).
Proof.
  intros f [] H. inversion H; subst; constructor; apply fc_T_lc; assumption.
Qed.

Lemma fc_T_fvar : forall f x, x \notin fc_changed f -> fc_T f (a_Var_f x) = a_Var_f x.
Proof. apply fc_tmap_fresh. Qed.
Lemma fc_C_fvar : forall f x, x \notin fc_changed f -> fc_C f (g_Var_f x) = g_Var_f x.
Proof. apply fc_cmap_fresh. Qed.

Scheme fc_ind_cv := Induction for CoercedValue Sort Prop
with fc_ind_v := Induction for Value Sort Prop.
Combined Scheme fc_values_ind from fc_ind_cv, fc_ind_v.

Lemma fc_map_values : forall f,
  (forall a, CoercedValue a -> CoercedValue (fc_T f a)) /\
  (forall a, Value a -> Value (fc_T f a)).
Proof.
  intro f.
  apply fc_values_ind; intros.
  all: try solve [apply CV; assumption].
  all: try solve [constructor;
    first [assumption |
      match goal with
      | H : lc_tm ?a |- _ => exact (fc_T_lc f a H)
      | H : lc_co ?g |- _ => exact (fc_C_lc f g H)
      | H : lc_constraint ?p |- _ => exact (fc_P_lc f p H)
      end]].
  - apply Value_UAbsIrrel with (L := L \u fc_changed f).
    intros x Hx. specialize (H x ltac:(fsetdec)).
    rewrite fc_T_open_t, fc_T_fvar in H by fsetdec. exact H.
  - apply Value_AbsIrrel with (L := L \u fc_changed f).
    + apply (fc_T_lc f); assumption.
    + intros x Hx. specialize (H x ltac:(fsetdec)).
      rewrite fc_T_open_t, fc_T_fvar in H by fsetdec. exact H.
Qed.

Definition fc_map_value f := proj2 (fc_map_values f).

Definition fc_erase_map (f : fc_map) : fc_map.
Proof.
  refine {| fc_tmap := fun x => erase_tm (fc_tmap f x);
            fc_cmap := g_Var_f; fc_changed := fc_changed f |}.
  - intro; apply fc_erase_degree_tm, fc_tmap_degree.
  - intro; exact I.
  - intros; rewrite fc_tmap_fresh by assumption; reflexivity.
  - reflexivity.
  - intros x y Hx Hxy. cbn.
    (* Erasure is idempotent. *)
    revert y Hxy. enough (forall a, erase_tm (erase_tm a) = erase_tm a) as E.
    + intros; rewrite E. auto using fc_tmap_relevance.
    + enough ((forall a, erase_tm (erase_tm a) = erase_tm a) /\
              (forall a, erase_brs (erase_brs a) = erase_brs a) /\
              (forall a : co, True) /\
              (forall a, erase_constraint (erase_constraint a) = erase_constraint a))
        by tauto.
      apply fc_syntax_ind; intros; cbn; try destruct rho; cbn; try exact I; congruence.
Defined.

Lemma fc_T_erase : forall f a, erase_tm (fc_T f a) = fc_T (fc_erase_map f) (erase_tm a).
Proof. intros; apply fc_erase_subst_tm. Qed.

Lemma fc_beta_map : forall f a b, Beta a b -> Beta (fc_T (fc_erase_map f) a) (fc_T (fc_erase_map f) b).
Proof.
  intros f a b H; destruct H.
  - rewrite fc_T_open_t. apply Beta_AppAbs; [exact (fc_T_lc (fc_erase_map f) _ H) | exact (fc_map_value (fc_erase_map f) _ H0)].
  - rewrite fc_T_open_c. apply Beta_CAppCAbs. exact (fc_T_lc (fc_erase_map f) _ H).
  - unfold toplevel, erase_sig, an_toplevel in H; cbn in H.
    destruct H as [H|H]; [injection H as <- <- <- | contradiction].
    change (Beta (a_Fam Fix) (erase_tm FixDef)).
    eapply Beta_Axiom. unfold toplevel, erase_sig, an_toplevel. cbn. auto.
Qed.

Lemma fc_rho_map : forall f r x a, x \notin fc_changed f ->
  RhoCheck r x (erase_tm a) -> RhoCheck r x (erase_tm (fc_T f a)).
Proof.
  intros f r x a Hx HR; rewrite fc_T_erase.
  inversion HR; subst; constructor; [exact I |].
  apply (proj1 fc_fv_subst_relevant); eauto.
  - intros; apply fc_tmap_relevance; auto.
Qed.

(** Transport of annotated derivations. *)

Scheme fc_ind_wff := Induction for AnnPropWff Sort Prop
with fc_ind_typ := Induction for AnnTyping Sort Prop
with fc_ind_iso := Induction for AnnIso Sort Prop
with fc_ind_eq := Induction for AnnDefEq Sort Prop
with fc_ind_ctx := Induction for AnnCtx Sort Prop
with fc_ind_sig := Induction for AnnSig Sort Prop.
Combined Scheme fc_ann_ind from fc_ind_wff, fc_ind_typ, fc_ind_iso, fc_ind_eq, fc_ind_ctx, fc_ind_sig.

Definition fc_S (f : fc_map) (s : sort) : sort :=
  match s with Tm a => Tm (fc_T f a) | Co p => Co (fc_P f p) end.

Definition fc_Dmap (R : atom -> atom -> Prop) (D E : atoms) : Prop :=
  forall x y, R x y -> x `in` D -> y `in` E.

Record fc_context_map (f : fc_map) (R : atom -> atom -> Prop) (G H : context) : Prop := {
  fc_map_dom : fc_Dmap R (dom G) (dom H);
  fc_map_id_atom : forall x, x \notin fc_changed f -> R x x;
  fc_map_only_atom : forall x y, x \notin fc_changed f -> R x y -> x = y;
  fc_map_var : forall P x A,
    AnnCtx (map (fc_S f) P ++ H) -> binds x (Tm A) G ->
    AnnTyping (map (fc_S f) P ++ H) (fc_tmap f x) (fc_T f A);
  fc_map_assn : forall P x a b A E,
    AnnCtx (map (fc_S f) P ++ H) -> binds x (Co (Eq a b A)) G ->
    (forall y, R x y -> y `in` E) ->
    AnnDefEq (map (fc_S f) P ++ H) E (fc_cmap f x) (fc_T f a) (fc_T f b)
}.

Lemma fc_binds_in_dom : forall {A : Type} (G : list (atom * A)) x a,
  binds x a G -> x `in` dom G.
Proof.
  induction G as [|[y b] G IH]; intros x a H; simpl in *; [contradiction|].
  destruct H as [H|H].
  - inversion H; subst; fsetdec.
  - specialize (IH _ _ H); fsetdec.
Qed.

Lemma fc_map_full : forall f R G H P,
  fc_context_map f R G H ->
  (forall x, x `in` dom P -> x \notin fc_changed f) ->
  fc_Dmap R (dom (P ++ G)) (dom (map (fc_S f) P ++ H)).
Proof.
  intros f R G H P M FP x y HR HI.
  rewrite !dom_app, dom_map in *.
  apply AtomSetImpl.union_1 in HI. destruct HI as [HI|HI].
  - rewrite <- (fc_map_only_atom f R G H M x y (FP x HI) HR); fsetdec.
  - pose proof (fc_map_dom f R G H M x y HR HI); fsetdec.
Qed.

Lemma fc_map_bound_tm : forall f R G H P x A,
  fc_context_map f R G H ->
  (forall y, y `in` dom P -> y \notin fc_changed f) ->
  AnnCtx (map (fc_S f) P ++ H) ->
  binds x (Tm A) (P ++ G) ->
  AnnTyping (map (fc_S f) P ++ H) (fc_tmap f x) (fc_T f A).
Proof.
  intros f R G H P x A M FP W B.
  apply binds_app_1 in B; destruct B as [B|B].
  - rewrite fc_tmap_fresh by (apply FP; eapply fc_binds_in_dom; exact B).
    apply An_Var; [assumption | apply binds_app_l; exact (binds_map _ _ (fc_S f) _ _ _ B)].
  - eapply fc_map_var; eauto.
Qed.

Lemma fc_map_bound_co : forall f R G H P D E x a b A,
  fc_context_map f R G H ->
  (forall y, y `in` dom P -> y \notin fc_changed f) ->
  AnnCtx (map (fc_S f) P ++ H) -> fc_Dmap R D E ->
  binds x (Co (Eq a b A)) (P ++ G) -> x `in` D ->
  AnnDefEq (map (fc_S f) P ++ H) E (fc_cmap f x) (fc_T f a) (fc_T f b).
Proof.
  intros f R G H P D E x a b A M FP W MDE B I.
  apply binds_app_1 in B; destruct B as [B|B].
  - assert (F : x \notin fc_changed f) by (apply FP; eapply fc_binds_in_dom; exact B).
    rewrite fc_cmap_fresh by exact F.
    eapply An_Assn.
    + exact W.
    + apply binds_app_l. exact (binds_map _ _ (fc_S f) _ _ _ B).
    + eapply MDE; [exact (fc_map_id_atom f R G H M x F) | exact I].
  - eapply fc_map_assn; eauto.
Qed.

Lemma fc_map_fresh_cons : forall f (P : context) x s,
  (forall y, y `in` dom P -> y \notin fc_changed f) ->
  x \notin fc_changed f ->
  forall y, y `in` dom ((x, s) :: P) -> y \notin fc_changed f.
Proof. intros f P x s FP Fx y Hy; rewrite dom_cons in Hy. apply AtomSetImpl.union_1 in Hy; destruct Hy as [Hy|Hy]; [assert (x = y) by fsetdec; now subst | auto]. Qed.

Ltac fc_equal_erasure :=
  rewrite !fc_T_erase; f_equal; assumption.

Ltac fc_judgment_premise :=
  first [
    assumption
  | reflexivity
  | fc_equal_erasure
  | solve [apply fc_beta_map; assumption]
  | solve [rewrite !fc_T_erase; apply fc_beta_map; assumption]
  | solve [eapply fc_map_full; eassumption]
  | solve [eapply fc_map_bound_tm; eassumption]
  | solve [eapply fc_map_bound_co; eassumption]
  | solve [eauto 2]
  ].

Lemma fc_T_castvar : forall f x g, x `notin` fc_changed f ->
  fc_T f (a_Conv (a_Var_f x) (g_Sym g)) = a_Conv (a_Var_f x) (g_Sym (fc_C f g)).
Proof.
  intros. change (a_Conv (fc_T f (a_Var_f x)) (g_Sym (fc_C f g)) = a_Conv (a_Var_f x) (g_Sym (fc_C f g))).
  now rewrite fc_T_fvar.
Qed.

Lemma fc_C_castvar : forall f x g, x `notin` fc_changed f ->
  fc_C f (g_Cast (g_Var_f x) (g_Sym g)) = g_Cast (g_Var_f x) (g_Sym (fc_C f g)).
Proof.
  intros. change (g_Cast (fc_C f (g_Var_f x)) (g_Sym (fc_C f g)) = g_Cast (g_Var_f x) (g_Sym (fc_C f g))).
  now rewrite fc_C_fvar.
Qed.

Ltac fc_binder_premise :=
  intros;
  first [
    match goal with
    | Hr : forall z : atom, _ -> RhoCheck _ z (erase_tm _),
      Hx : ?x `notin` _ |- RhoCheck _ ?x (erase_tm (open_tm_wrt_tm (fc_T ?F _) _)) =>
      let H := fresh "HR" in
      pose proof (Hr x ltac:(fsetdec)) as H;
      apply (fc_rho_map F) in H; [|fsetdec];
      rewrite ?fc_T_open_t, ?fc_T_fvar in H by fsetdec;
      exact H
    end
  | match goal with
    | He : forall z : atom, _ -> open_tm_wrt_tm _ _ = open_tm_wrt_tm _ _,
      Hx : ?x `notin` _ |- open_tm_wrt_tm (fc_T ?F _) _ = _ =>
      let H := fresh "HO" in
      pose proof (f_equal (fc_T F) (He x ltac:(fsetdec))) as H;
      rewrite !fc_T_open_t, ?fc_T_fvar, ?fc_T_castvar in H by fsetdec; exact H
    | He : forall z : atom, _ -> open_tm_wrt_co _ _ = open_tm_wrt_co _ _,
      Hx : ?x `notin` _ |- open_tm_wrt_co (fc_T ?F _) _ = _ =>
      let H := fresh "HO" in
      pose proof (f_equal (fc_T F) (He x ltac:(fsetdec))) as H;
      rewrite !fc_T_open_c, ?fc_C_fvar, ?fc_C_castvar in H by fsetdec; exact H
    end
  | match goal with
    | W : AnnCtx (map (fc_S ?F) ?P ++ ?Dst),
      Hx : ?x `notin` _, IH : forall (z : atom), _ |- _ =>
        let s' := lazymatch goal with
          | |- AnnTyping (x ~ Tm (fc_T F ?A) ++ _) _ _ => constr:(Tm A)
          | |- AnnTyping (x ~ Co (fc_P F ?phi) ++ _) _ _ => constr:(Co phi)
          | |- AnnDefEq (x ~ Tm (fc_T F ?A) ++ _) _ _ _ _ => constr:(Tm A)
          | |- AnnDefEq (x ~ Co (fc_P F ?phi) ++ _) _ _ _ _ => constr:(Co phi)
        end in
        let Wext := fresh "Wext" in
        assert (Wext : AnnCtx (map (fc_S F) ((x, s') :: P) ++ Dst)) by
          ((apply An_ConsTm || apply An_ConsCo);
           [assumption | eassumption | change (x `notin` dom (map (fc_S F) P ++ Dst)); fsetdec]);
        let Fext := constr:(fc_map_fresh_cons F P x s' ltac:(assumption) ltac:(fsetdec)) in
        let J := fresh "Jopen" in
        first [
          pose proof (IH x ltac:(fsetdec) ((x,s')::P) eq_refl Fext Wext) as J
        | let E := lazymatch goal with |- AnnDefEq _ ?E _ _ _ => E end in
          pose proof (IH x ltac:(fsetdec) ((x,s')::P) E eq_refl Fext Wext ltac:(assumption)) as J
        ];
        rewrite ?fc_T_open_t, ?fc_T_open_c, ?fc_C_open_t, ?fc_C_open_c,
          ?fc_T_fvar, ?fc_C_fvar in J by fsetdec;
        exact J
    end
  ].

Lemma fc_transport : forall f R G H, fc_context_map f R G H ->
  (forall K phi, AnnPropWff K phi -> forall P,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> AnnPropWff (map (fc_S f) P ++ H) (fc_P f phi)) /\
  (forall K a A, AnnTyping K a A -> forall P,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> AnnTyping (map (fc_S f) P ++ H) (fc_T f a) (fc_T f A)) /\
  (forall K D g phi psi, AnnIso K D g phi psi -> forall P E,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> fc_Dmap R D E ->
    AnnIso (map (fc_S f) P ++ H) E (fc_C f g) (fc_P f phi) (fc_P f psi)) /\
  (forall K D g a b, AnnDefEq K D g a b -> forall P E,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> fc_Dmap R D E ->
    AnnDefEq (map (fc_S f) P ++ H) E (fc_C f g) (fc_T f a) (fc_T f b)).
Proof.
  intros f R G H M.
  assert (S :
  (forall K phi, AnnPropWff K phi -> forall P,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> AnnPropWff (map (fc_S f) P ++ H) (fc_P f phi)) /\
  (forall K a A, AnnTyping K a A -> forall P,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> AnnTyping (map (fc_S f) P ++ H) (fc_T f a) (fc_T f A)) /\
  (forall K D g phi psi, AnnIso K D g phi psi -> forall P E,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> fc_Dmap R D E ->
    AnnIso (map (fc_S f) P ++ H) E (fc_C f g) (fc_P f phi) (fc_P f psi)) /\
  (forall K D g a b, AnnDefEq K D g a b -> forall P E,
    K = P ++ G -> (forall x, x `in` dom P -> x \notin fc_changed f) ->
    AnnCtx (map (fc_S f) P ++ H) -> fc_Dmap R D E ->
    AnnDefEq (map (fc_S f) P ++ H) E (fc_C f g) (fc_T f a) (fc_T f b)) /\
  (forall K, AnnCtx K -> True) /\ (forall S, AnnSig S -> True)).
  2: tauto.
  apply fc_ann_ind; intros; subst; try exact I.
  all: repeat match goal with
  | W : AnnCtx (map (fc_S ?F) ?P ++ ?Dst), IH : forall _, _ |- _ =>
    first [
      specialize (IH P eq_refl ltac:(assumption) W)
    | specialize (IH P (dom (map (fc_S F) P ++ Dst)) eq_refl ltac:(assumption) W
                   ltac:(eapply fc_map_full; eassumption))
    | match goal with MD : fc_Dmap _ _ ?E |- _ =>
        specialize (IH P E eq_refl ltac:(assumption) W MD)
      end
    ]
  end.
  all: try solve [eapply An_Wff; fc_judgment_premise].
  all: try solve [apply An_Star; assumption].
  all: try solve [change (AnnTyping _ (fc_tmap f _) _); fc_judgment_premise].
  all: try solve [change (AnnDefEq _ _ (fc_cmap f _) _ _); fc_judgment_premise].
  all: try solve [rewrite fc_T_open_t; eapply An_App; eassumption].
  all: try solve [eapply An_Conv; eassumption].
  all: try solve [rewrite fc_T_open_c; eapply An_CApp; eassumption].
  all: try solve [eapply An_PropCong; eassumption].
  all: try solve [eapply An_CPiFst; eassumption].
  all: try solve [eapply An_IsoSym; eassumption].
  all: try solve [eapply An_IsoConv; fc_judgment_premise].
  all: try solve [eapply An_Refl; eassumption].
  all: try solve [eapply An_EraseEq; fc_judgment_premise].
  all: try solve [eapply An_Sym; eassumption].
  all: try solve [eapply An_Trans; eassumption].
  all: try solve [eapply An_Beta; fc_judgment_premise].
  all: try solve [eapply An_AppCong; eassumption].
  all: try solve [eapply An_PiFst; eassumption].
  all: try solve [rewrite !fc_T_open_t; eapply An_PiSnd; eassumption].
  all: try solve [eapply An_CAppCong; eassumption].
  all: try solve [rewrite !fc_T_open_c; eapply An_CPiSnd; eassumption].
  all: try solve [eapply An_Cast; eassumption].
  all: try solve [eapply An_IsoSnd; eassumption].
  all: try solve [eapply (An_Wff _ _ _ _ (fc_T f B)); [eassumption|eassumption|fc_equal_erasure]].
  all: try solve [eapply (fc_map_bound_tm f R _ _); eassumption].
  all: try solve [eapply (fc_map_bound_co f R _ _); eassumption].
  all: try solve [
    match goal with
    | T : AnnTyping _ (fc_T ?f ?a) (fc_T ?f (a_CPi (Eq ?u ?v ?U) ?B)) |- _ =>
        rewrite fc_T_open_c;
        eapply (An_CApp _ (fc_T f a) _ (fc_T f B) (fc_T f u) (fc_T f v) (fc_T f U));
        eassumption
    end].
  all: try solve [
    match goal with
    | J : AnnDefEq _ _ (fc_C ?f ?g) (fc_T ?f (a_CPi (Eq ?a ?a' ?A) ?B1))
                                 (fc_T ?f (a_CPi (Eq ?b ?b' ?B) ?B2)) |- _ =>
      rewrite !fc_T_open_c;
      eapply (An_CPiSnd _ _ (fc_C f g) _ _ (fc_T f B1) (fc_T f B2)
              (fc_T f a) (fc_T f a') (fc_T f A) (fc_T f b) (fc_T f b') (fc_T f B));
      eassumption
    end].
  all: try solve [
    match goal with
    | J : AnnDefEq _ _ (fc_C ?f ?g) (fc_T ?f ?A) (fc_T ?f ?B) |-
        AnnIso _ _ (fc_C ?f (g_IsoConv (Eq ?a1 ?a2 ?A) (Eq ?b1 ?b2 ?B) ?g)) _ _ =>
      eapply (An_IsoConv _ _ (fc_T f a1) (fc_T f a2) (fc_T f A)
                            (fc_T f b1) (fc_T f b2) (fc_T f B) (fc_C f g));
      first [eassumption | fc_equal_erasure]
    end].
  all: try solve [
    match goal with
    | B : binds _ (Ax _ _) an_toplevel |- _ =>
        change (_ = _ \/ False) in B;
        destruct B as [B|B]; [inversion B; subst|contradiction];
        eapply An_Fam; eassumption
    end].
  - eapply (An_Wff _ (fc_T f a) (fc_T f b) (fc_T f A) (fc_T f B)); [exact H0|exact H1|].
    rewrite !fc_T_erase. now rewrite e.
  - eapply (An_Pi (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ rho (fc_T f A) (fc_T f B)).
    + fc_binder_premise.
    + assumption.
  - eapply (An_Abs (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ rho (fc_T f A) (fc_T f a) (fc_T f B)).
    + assumption.
    + fc_binder_premise.
    + fc_binder_premise.
  - eapply (An_CPi (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ (fc_P f phi) (fc_T f B)).
    + assumption.
    + fc_binder_premise.
  - eapply (An_CAbs (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ (fc_P f phi) (fc_T f a) (fc_T f B)).
    + assumption.
    + fc_binder_premise.
  - assert (F = Fix /\ a = FixDef /\ A = FixTy) as (-> & -> & ->).
    { simpl in b. destruct b as [B|B]; [inversion B; auto | contradiction]. }
    exact (An_Fam _ Fix FixTy FixDef H4 (or_introl eq_refl) a1).
  - eapply (An_PiCong (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ E rho
               (fc_C f g1) (fc_C f g2) (fc_T f A1) (fc_T f B1) (fc_T f A2) (fc_T f B3) (fc_T f B2)).
    + assumption.
    + assert (AnnTyping (map (fc_S f) P ++ H) (fc_T f A1) a_Star).
      { match goal with
        | J : AnnTyping _ (fc_T f (a_Pi rho A1 B1)) _ |- _ =>
          inversion J; assumption
        end. }
      fc_binder_premise.
    + fc_binder_premise.
    + assumption.
    + assumption.
    + assumption.
  - eapply (An_AbsCong (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ E rho
               (fc_C f g1) (fc_C f g2) (fc_T f A1) (fc_T f b1) (fc_T f A2) (fc_T f b3)
               (fc_T f b2) (fc_T f B));
      first [assumption | fc_binder_premise].
  - eapply (An_CPiCong (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ E
               (fc_C f g1) (fc_C f g3) (fc_P f phi1) (fc_T f B1) (fc_P f phi2)
               (fc_T f B3) (fc_T f B2)).
    + assumption.
    + assert (AnnPropWff (map (fc_S f) P ++ H) (fc_P f phi1)).
      { match goal with
        | J : AnnTyping _ (fc_T f (a_CPi phi1 B1)) _ |- _ =>
          inversion J; assumption
        end. }
      fc_binder_premise.
    + fc_binder_premise.
    + assumption.
    + assumption.
    + assumption.
  - eapply (An_CAbsCong (L \u fc_changed f \u dom (map (fc_S f) P ++ H)) _ E
               (fc_C f g1) (fc_C f g3) (fc_C f g4) (fc_P f phi1) (fc_T f a1) (fc_P f phi2)
               (fc_T f a3) (fc_T f a2) (fc_T f B1) (fc_T f B) (fc_T f B2)).
    + assumption.
    + assert (AnnPropWff (map (fc_S f) P ++ H) (fc_P f phi1)).
      { match goal with
        | J : AnnTyping _ (fc_T f (a_CAbs phi1 a1)) _ |- _ =>
          inversion J; assumption
        end. }
      fc_binder_premise.
    + fc_binder_premise.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
Qed.

(** Weakening and substitution in well-formed contexts. *)

Definition fc_typ_map f R G H M := proj1 (proj2 (fc_transport f R G H M)).
Definition fc_wff_map f R G H M := proj1 (fc_transport f R G H M).
Definition fc_iso_map f R G H M := proj1 (proj2 (proj2 (fc_transport f R G H M))).
Definition fc_eq_map f R G H M := proj2 (proj2 (proj2 (fc_transport f R G H M))).

Lemma fc_transport_base : forall f R G H, fc_context_map f R G H -> AnnCtx H ->
  (forall phi, AnnPropWff G phi -> AnnPropWff H (fc_P f phi)) /\
  (forall a A, AnnTyping G a A -> AnnTyping H (fc_T f a) (fc_T f A)) /\
  (forall D E g phi psi, fc_Dmap R D E -> AnnIso G D g phi psi ->
    AnnIso H E (fc_C f g) (fc_P f phi) (fc_P f psi)) /\
  (forall D E g a b, fc_Dmap R D E -> AnnDefEq G D g a b ->
    AnnDefEq H E (fc_C f g) (fc_T f a) (fc_T f b)).
Proof.
  intros f R G H M WH. repeat split; intros.
  - exact (fc_wff_map f R G H M _ _ H0 nil eq_refl ltac:(simpl; fsetdec) WH).
  - exact (fc_typ_map f R G H M _ _ _ H0 nil eq_refl ltac:(simpl; fsetdec) WH).
  - exact (fc_iso_map f R G H M _ _ _ _ _ H1 nil _ eq_refl ltac:(simpl; fsetdec) WH H0).
  - exact (fc_eq_map f R G H M _ _ _ _ _ H1 nil _ eq_refl ltac:(simpl; fsetdec) WH H0).
Qed.

Lemma fc_dom_binds : forall (A : Type) (G : list (atom * A)) x,
  x `in` dom G -> exists a, binds x a G.
Proof.
  induction G as [|[y a] G IH]; intros x J; [simpl in J; fsetdec|].
  rewrite dom_cons in J; apply AtomSetImpl.union_1 in J; destruct J as [J|J].
  - assert (x = y) by fsetdec; subst; exists a; simpl; auto.
  - destruct (IH x J) as [b B]. exists b. simpl; auto.
Qed.

Definition fc_identity : fc_map.
Proof.
  refine {| fc_tmap := a_Var_f; fc_cmap := g_Var_f; fc_changed := empty |};
    intros; cbn; try exact I; try reflexivity; fsetdec.
Defined.

Lemma fc_identity_context : forall G H,
  (forall x a, binds x a G -> binds x a H) ->
  fc_context_map fc_identity eq G H.
Proof.
  intros G H B; constructor; try (intros; congruence).
  - intros x y <- HX. apply fc_dom_binds in HX.
    destruct HX as [a Ha]. eapply fc_binds_in_dom; apply B; exact Ha.
  - intros; unfold fc_T; cbn -[fc_subst_tm]; rewrite fc_subst_id_tm.
    apply An_Var; [assumption | apply binds_app_r; auto].
  - intros; unfold fc_T; cbn -[fc_subst_tm]; rewrite !fc_subst_id_tm.
    eapply An_Assn; [eassumption | apply binds_app_r; eauto | auto].
Qed.

Lemma fc_weakening : forall G H,
  (forall x a, binds x a G -> binds x a H) -> AnnCtx H ->
  (forall phi, AnnPropWff G phi -> AnnPropWff H phi) /\
  (forall a A, AnnTyping G a A -> AnnTyping H a A) /\
  (forall D E g phi psi, D [<=] E -> AnnIso G D g phi psi -> AnnIso H E g phi psi) /\
  (forall D E g a b, D [<=] E -> AnnDefEq G D g a b -> AnnDefEq H E g a b).
Proof.
  intros G H B W.
  pose proof (fc_transport_base _ _ _ _ (fc_identity_context G H B) W) as J.
  unfold fc_T, fc_C, fc_P in J; cbn -[fc_subst_tm fc_subst_co fc_subst_constraint] in J.
  setoid_rewrite fc_subst_id_tm in J.
  setoid_rewrite fc_subst_id_co in J.
  setoid_rewrite fc_subst_id_constraint in J.
  fc_unpack; repeat split; intros; eauto 2; first [eapply H2 | eapply H3]; try eassumption.
  all: intros x y <- HI; auto.
Qed.

Lemma fc_weak_typ : forall G H a A, AnnTyping G a A ->
  (forall x s, binds x s G -> binds x s H) -> AnnCtx H -> AnnTyping H a A.
Proof. intros. exact (proj1 (proj2 (fc_weakening G H H1 H2)) a A H0). Qed.

Lemma fc_weak_eq : forall G H D E g a b, AnnDefEq G D g a b ->
  (forall x s, binds x s G -> binds x s H) -> AnnCtx H ->
  D [<=] E -> AnnDefEq H E g a b.
Proof. intros G H D E g a b J B W S. exact (proj2 (proj2 (proj2 (fc_weakening G H B W))) D E g a b S J). Qed.

Lemma fc_weak_iso : forall G H D E g a b, AnnIso G D g a b ->
  (forall x s, binds x s G -> binds x s H) -> AnnCtx H ->
  D [<=] E -> AnnIso H E g a b.
Proof. intros G H D E g a b J B W S. exact (proj1 (proj2 (proj2 (fc_weakening G H B W))) D E g a b S J). Qed.

Lemma fc_weak_wff : forall G H p, AnnPropWff G p ->
  (forall x s, binds x s G -> binds x s H) -> AnnCtx H -> AnnPropWff H p.
Proof. intros G H p J B W. exact (proj1 (fc_weakening G H B W) p J). Qed.

Lemma fc_ctx_uniq : forall G, AnnCtx G -> uniq G.
Proof. intros G H; induction H; constructor; assumption. Qed.

Definition fc_once {A : Type} (v : atom -> A) (x : atom) (a : A) :=
  fun y => if y == x then a else v y.

Lemma fc_once_here : forall A (v : atom -> A) x a, fc_once v x a x = a.
Proof. unfold fc_once; intros; destruct (_ == _); congruence. Qed.
Lemma fc_once_away : forall A (v : atom -> A) x y a, x <> y -> fc_once v x a y = v y.
Proof. unfold fc_once; intros; destruct (_ == _); congruence. Qed.

Definition fc_replace_tm (x : atom) (a : tm) (valid : fc_degree_tm 0 0 a) : fc_map.
Proof.
  refine {| fc_tmap := fc_once a_Var_f x a; fc_cmap := g_Var_f;
            fc_changed := singleton x \u fv_tm_tm_tm (erase_tm a) |}.
  - intro y; unfold fc_once. destruct (y == x); [exact valid | exact I].
  - intro; exact I.
  - intros; apply fc_once_away; fsetdec.
  - reflexivity.
  - intros y z Fy Fz; unfold fc_once; destruct (z == x); [fsetdec | cbn; fsetdec].
Defined.

Definition fc_replace_co (x : atom) (g : co) (valid : fc_degree_co 0 0 g) : fc_map.
Proof.
  refine {| fc_tmap := a_Var_f; fc_cmap := fc_once g_Var_f x g;
            fc_changed := singleton x |}.
  - intro; exact I.
  - intro y; unfold fc_once. destruct (y == x); [exact valid | exact I].
  - reflexivity.
  - intros; apply fc_once_away; fsetdec.
  - intros; cbn; fsetdec.
Defined.

Definition fc_id_off (f : fc_map) (x : atom) : Prop :=
  forall y, x <> y -> fc_tmap f y = a_Var_f y /\ fc_cmap f y = g_Var_f y.

Lemma fc_replace_tm_off : forall x a v, fc_id_off (fc_replace_tm x a v) x.
Proof.
  unfold fc_id_off; simpl; intros; split; [apply fc_once_away; assumption|reflexivity].
Qed.
Lemma fc_replace_co_off : forall x a v, fc_id_off (fc_replace_co x a v) x.
Proof.
  unfold fc_id_off; simpl; intros; split; [reflexivity|apply fc_once_away; assumption].
Qed.

Definition fc_fv_sort s :=
  match s with Tm a => fc_fv_tm a | Co p => fc_fv_constraint p end.

Fixpoint fc_fv_ctx (G : context) : atoms :=
  match G with nil => empty | (x,s)::G => singleton x \u fc_fv_sort s \u fc_fv_ctx G end.

Lemma fc_Gfv_binds : forall G x s, binds x s G -> AtomSetImpl.Subset (fc_fv_sort s) (fc_fv_ctx G).
Proof.
  induction G as [|[y v] G IH]; intros x s B z F; simpl in *; [contradiction|].
  destruct B as [B|B]; [inversion B; subst | pose proof (IH x s B z F)]; fsetdec.
Qed.
Lemma fc_Gfv_dom : forall G, AtomSetImpl.Subset (dom G) (fc_fv_ctx G).
Proof.
  induction G as [|[x s] G IH]; intros y Hy; [exact Hy|].
  rewrite dom_cons in Hy; apply AtomSetImpl.union_1 in Hy; destruct Hy as [Hy|Hy]; [|specialize (IH y Hy)]; simpl; fsetdec.
Qed.

Ltac fc_id_off_proof lemma :=
  intros F x e OFF Hx; unfold fc_T, fc_C, fc_P;
  etransitivity; [eapply lemma|];
  try first [apply fc_subst_id_tm | apply fc_subst_id_co | apply fc_subst_id_constraint];
  intros y Hy; assert (x <> y) by (intro E; subst; contradiction);
  destruct (OFF y ltac:(assumption)); assumption.

Lemma fc_T_off : forall f x a, fc_id_off f x -> x \notin fc_fv_tm a -> fc_T f a = a.
Proof. fc_id_off_proof fc_subst_ext_tm. Qed.
Lemma fc_C_off : forall f x a, fc_id_off f x -> x \notin fc_fv_co a -> fc_C f a = a.
Proof. fc_id_off_proof fc_subst_ext_co. Qed.

Lemma fc_open_subst_Tt : forall f x a, fc_id_off f x -> x \notin fc_fv_tm a ->
  fc_T f (open_tm_wrt_tm a (a_Var_f x)) = open_tm_wrt_tm a (fc_tmap f x).
Proof. intros. rewrite fc_T_open_t, (fc_T_off f x a) by assumption. reflexivity. Qed.
Lemma fc_open_subst_Tc : forall f x a, fc_id_off f x -> x \notin fc_fv_tm a ->
  fc_T f (open_tm_wrt_co a (g_Var_f x)) = open_tm_wrt_co a (fc_cmap f x).
Proof. intros. rewrite fc_T_open_c, (fc_T_off f x a) by assumption. reflexivity. Qed.
Lemma fc_open_subst_Ct : forall f x g, fc_id_off f x -> x \notin fc_fv_co g ->
  fc_C f (open_co_wrt_tm g (a_Var_f x)) = open_co_wrt_tm g (fc_tmap f x).
Proof. intros. rewrite fc_C_open_t, (fc_C_off f x g) by assumption. reflexivity. Qed.
Lemma fc_open_subst_Cc : forall f x g, fc_id_off f x -> x \notin fc_fv_co g ->
  fc_C f (open_co_wrt_co g (g_Var_f x)) = open_co_wrt_co g (fc_cmap f x).
Proof. intros. rewrite fc_C_open_c, (fc_C_off f x g) by assumption. reflexivity. Qed.

Definition fc_replace_rel (x : atom) (H : context) (u v : atom) :=
  (u <> x /\ u = v) \/ (u = x /\ v `in` dom H).

Lemma fc_context_replace : forall f x s G H,
  fc_id_off f x -> x `in` fc_changed f ->
  x \notin fc_fv_ctx G ->
  (forall y v, binds y v G -> binds y v H) ->
  (forall A, s = Tm A -> AnnTyping H (fc_tmap f x) (fc_T f A)) ->
  (forall a b A, s = Co (Eq a b A) -> AnnDefEq H (dom H) (fc_cmap f x) (fc_T f a) (fc_T f b)) ->
  fc_context_map f (fc_replace_rel x H) ((x,s)::G) H.
Proof.
  intros f x s G H OFF CH FR BI BT BC; constructor.
  - intros u v [[N ->]|[-> I]] J; [|exact I].
    rewrite dom_cons in J. apply AtomSetImpl.union_1 in J. destruct J as [J|J]; [fsetdec|].
    apply fc_dom_binds in J. destruct J as [s0 J]; eapply fc_binds_in_dom; eauto.
  - intros u Fu; left; split; [intro E; subst; contradiction | reflexivity].
  - intros u v Fu [[N E]|[E I]]; [assumption | subst; contradiction].
  - intros P y A W B; destruct B as [B|B].
    + inversion B; subst; eapply fc_weak_typ; [eapply BT; reflexivity| | exact W].
      intros; apply binds_app_r; assumption.
    + assert (N : x <> y) by
        (intro E; subst; apply FR, fc_Gfv_dom; eapply fc_binds_in_dom; exact B).
      rewrite (proj1 (OFF y N)), (fc_T_off f x A OFF).
      * apply An_Var; auto using binds_app_r.
      * intro I; apply FR; exact (fc_Gfv_binds _ _ _ B _ I).
  - intros P y a b A E W B Av; destruct B as [B|B].
    + inversion B; subst; eapply fc_weak_eq; [eapply BC; reflexivity| | exact W |].
      * intros; apply binds_app_r; assumption.
      * intros v I; apply Av; right; auto.
    + assert (N : x <> y) by
        (intro E'; subst; apply FR, fc_Gfv_dom; eapply fc_binds_in_dom; exact B).
      pose proof (fc_Gfv_binds _ _ _ B) as F; simpl in F.
      assert (Fa : x \notin fc_fv_tm a) by (intro I; apply FR, F; fsetdec).
      assert (Fb : x \notin fc_fv_tm b) by (intro I; apply FR, F; fsetdec).
      rewrite (proj2 (OFF y N)), (fc_T_off f x a OFF Fa), (fc_T_off f x b OFF Fb).
      eapply (An_Assn _ _ _ _ _ A); [exact W | apply binds_app_r; auto | apply Av; left; intuition].
Qed.

Lemma fc_tsubst_typ : forall L G H A a B u,
  AnnCtx H ->
  (forall x s, binds x s G -> binds x s H) ->
  AnnTyping H u A -> fc_degree_tm 0 0 u ->
  (forall x, x \notin L ->
     AnnTyping ((x,Tm A)::G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  AnnTyping H (open_tm_wrt_tm a u) (open_tm_wrt_tm B u).
Proof.
  intros L G H A a B u W Bi U Du J.
  destruct (atom_fresh (L \u fc_fv_ctx G \u fc_fv_tm A \u fc_fv_tm a \u fc_fv_tm B))
    as [x Fx].
  pose (f := fc_replace_tm x u Du).
  assert (O : fc_id_off f x) by apply fc_replace_tm_off.
  assert (M : fc_context_map f (fc_replace_rel x H) ((x,Tm A)::G) H).
  { apply fc_context_replace; try assumption; try solve [unfold f; simpl; fsetdec].
    - intros A' E; inversion E; subst.
      rewrite (fc_T_off f x A' O) by fsetdec.
      unfold f; cbn [fc_tmap fc_replace_tm]; now rewrite fc_once_here.
    - discriminate. }
  pose proof (proj1 (proj2 (fc_transport_base _ _ _ _ M W)) _ _
                (J x ltac:(fsetdec))) as Q.
  rewrite !fc_open_subst_Tt with (x:=x) in Q by (assumption || fsetdec).
  unfold f in Q; cbn [fc_tmap fc_replace_tm] in Q; now rewrite fc_once_here in Q.
Qed.

Lemma fc_csubst_typ : forall L G H phi a B g,
  AnnCtx H ->
  (forall x s, binds x s G -> binds x s H) ->
  (forall u v A, phi = Eq u v A -> AnnDefEq H (dom H) g u v) ->
  fc_degree_co 0 0 g ->
  (forall x, x \notin L ->
     AnnTyping ((x,Co phi)::G) (open_tm_wrt_co a (g_Var_f x)) (open_tm_wrt_co B (g_Var_f x))) ->
  AnnTyping H (open_tm_wrt_co a g) (open_tm_wrt_co B g).
Proof.
  intros L G H phi a B g W Bi U Dg J.
  destruct (atom_fresh (L \u fc_fv_ctx G \u fc_fv_constraint phi \u fc_fv_tm a \u fc_fv_tm B))
    as [x Fx].
  pose (f := fc_replace_co x g Dg).
  assert (O : fc_id_off f x) by apply fc_replace_co_off.
  assert (M : fc_context_map f (fc_replace_rel x H) ((x,Co phi)::G) H).
  { apply fc_context_replace; try assumption; try solve [unfold f; simpl; fsetdec].
    - discriminate.
    - intros u v A E. injection E as E. assert (P : x \notin fc_fv_constraint (Eq u v A)) by (rewrite <- E; fsetdec).
      cbn in P.
      rewrite (fc_T_off f x u O), (fc_T_off f x v O) by fsetdec.
      unfold f; cbn [fc_cmap fc_replace_co]; rewrite fc_once_here; exact (U u v A E). }
  pose proof (proj1 (proj2 (fc_transport_base _ _ _ _ M W)) _ _
                (J x ltac:(fsetdec))) as Q.
  rewrite !fc_open_subst_Tc with (x:=x) in Q by (assumption || fsetdec).
  unfold f in Q; cbn [fc_cmap fc_replace_co] in Q; now rewrite fc_once_here in Q.
Qed.

Lemma fc_tsubst_star : forall L G H A B u,
  AnnCtx H ->
  (forall x s, binds x s G -> binds x s H) ->
  AnnTyping H u A -> fc_degree_tm 0 0 u ->
  (forall x, x \notin L -> AnnTyping ((x,Tm A)::G) (open_tm_wrt_tm B (a_Var_f x)) a_Star) ->
  AnnTyping H (open_tm_wrt_tm B u) a_Star.
Proof.
  intros. change (AnnTyping H (open_tm_wrt_tm B u) (open_tm_wrt_tm a_Star u)).
  eapply fc_tsubst_typ; eauto.
Qed.

Lemma fc_csubst_star : forall L G H phi B g,
  AnnCtx H ->
  (forall x s, binds x s G -> binds x s H) ->
  (forall u v A, phi = Eq u v A -> AnnDefEq H (dom H) g u v) ->
  fc_degree_co 0 0 g ->
  (forall x, x \notin L -> AnnTyping ((x,Co phi)::G) (open_tm_wrt_co B (g_Var_f x)) a_Star) ->
  AnnTyping H (open_tm_wrt_co B g) a_Star.
Proof.
  intros. change (AnnTyping H (open_tm_wrt_co B g) (open_tm_wrt_co a_Star g)).
  eapply fc_csubst_typ; eauto.
Qed.

Lemma fc_extra_term_atom :
  (forall G p, AnnPropWff G p -> True) /\
  (forall G a A, AnnTyping G a A -> True) /\
  (forall G D g p q, AnnIso G D g p q ->
    forall E, (forall c phi, binds c (Co phi) G -> c `in` D -> c `in` E) -> AnnIso G E g p q) /\
  (forall G D g a b, AnnDefEq G D g a b ->
    forall E, (forall c phi, binds c (Co phi) G -> c `in` D -> c `in` E) -> AnnDefEq G E g a b) /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof.
  apply fc_ann_ind; intros; try exact I.
  all: try solve [
    (eapply An_PropCong || eapply An_CPiFst || eapply An_IsoSym || eapply An_IsoConv ||
     eapply An_Refl || eapply An_EraseEq || eapply An_Sym || eapply An_Trans ||
     eapply An_Beta || eapply An_AppCong || eapply An_PiFst || eapply An_PiSnd ||
     eapply An_CAppCong || eapply An_CPiSnd || eapply An_Cast || eapply An_IsoSnd);
    first [eassumption | solve [eauto 2]]].
  - eapply An_Assn; [exact a0|exact b0|eauto].
  - eapply (An_PiCong L); try eassumption; try solve [eauto 2].
    intros x Hx. eapply H0; [exact Hx|].
    intros c phi BC I. destruct BC as [BC|BC]; [discriminate BC|eauto].
  - eapply (An_AbsCong L); try eassumption; try solve [eauto 2].
    intros x Hx. eapply H0; [exact Hx|].
    intros c phi BC I. destruct BC as [BC|BC]; [discriminate BC|eauto].
  - eapply (An_CPiCong (L \u D)); try eassumption; try solve [eauto 2].
    + intros x Hx. eapply H0; [fsetdec|].
      intros c phi BC I. destruct BC as [BC|BC]; [inversion BC; subst; fsetdec|eauto].
  - eapply (An_CAbsCong (L \u D)); try eassumption; try solve [eauto 2].
    + intros x Hx. eapply H0; [fsetdec|].
      intros c phi BC I. destruct BC as [BC|BC]; [inversion BC; subst; fsetdec|eauto].
Qed.

Lemma fc_eq_all_term : forall G x A g a b,
  AnnDefEq ((x,Tm A)::G) (dom ((x,Tm A)::G)) g a b ->
  AnnDefEq ((x,Tm A)::G) (dom G) g a b.
Proof.
  intros G x A g a b J.
  eapply (proj1 (proj2 (proj2 (proj2 fc_extra_term_atom)))); [exact J|].
  intros c phi B _. destruct B as [B|B]; [discriminate B|].
  eapply fc_binds_in_dom; exact B.
Qed.

(** Free atoms under opening. *)

Lemma fc_fv_tmopen :
  (forall e d u x,
    (x `in` fc_fv_tm e -> x `in` fc_fv_tm (open_tm_wrt_tm_rec d u e)) /\
    (x `in` fc_fv_tm (open_tm_wrt_tm_rec d u e) -> x `in` fc_fv_tm e \/ x `in` fc_fv_tm u)) /\
  (forall e d u x,
    (x `in` fc_fv_brs e -> x `in` fc_fv_brs (open_brs_wrt_tm_rec d u e)) /\
    (x `in` fc_fv_brs (open_brs_wrt_tm_rec d u e) -> x `in` fc_fv_brs e \/ x `in` fc_fv_tm u)) /\
  (forall e d u x,
    (x `in` fc_fv_co e -> x `in` fc_fv_co (open_co_wrt_tm_rec d u e)) /\
    (x `in` fc_fv_co (open_co_wrt_tm_rec d u e) -> x `in` fc_fv_co e \/ x `in` fc_fv_tm u)) /\
  (forall e d u x,
    (x `in` fc_fv_constraint e -> x `in` fc_fv_constraint (open_constraint_wrt_tm_rec d u e)) /\
    (x `in` fc_fv_constraint (open_constraint_wrt_tm_rec d u e) -> x `in` fc_fv_constraint e \/ x `in` fc_fv_tm u)).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    try (split; fsetdec);
    try (destruct lt_eq_lt_dec as [[]|]; cbn; split; fsetdec);
    repeat match goal with IH : forall _ _ _, _ |- _ => first [pose proof (IH d u x); pose proof (IH (S d) u x); clear IH | fail 1] end;
    fc_unpack; split; fsetdec.
Qed.
Definition fc_fv_tmopen_tm := proj1 (fc_fv_tmopen).
Definition fc_fv_tmopen_co := proj1 (proj2 (proj2 (fc_fv_tmopen))).

Lemma fc_fv_coopen :
  (forall e d u x,
    (x `in` fc_fv_tm e -> x `in` fc_fv_tm (open_tm_wrt_co_rec d u e)) /\
    (x `in` fc_fv_tm (open_tm_wrt_co_rec d u e) -> x `in` fc_fv_tm e \/ x `in` fc_fv_co u)) /\
  (forall e d u x,
    (x `in` fc_fv_brs e -> x `in` fc_fv_brs (open_brs_wrt_co_rec d u e)) /\
    (x `in` fc_fv_brs (open_brs_wrt_co_rec d u e) -> x `in` fc_fv_brs e \/ x `in` fc_fv_co u)) /\
  (forall e d u x,
    (x `in` fc_fv_co e -> x `in` fc_fv_co (open_co_wrt_co_rec d u e)) /\
    (x `in` fc_fv_co (open_co_wrt_co_rec d u e) -> x `in` fc_fv_co e \/ x `in` fc_fv_co u)) /\
  (forall e d u x,
    (x `in` fc_fv_constraint e -> x `in` fc_fv_constraint (open_constraint_wrt_co_rec d u e)) /\
    (x `in` fc_fv_constraint (open_constraint_wrt_co_rec d u e) -> x `in` fc_fv_constraint e \/ x `in` fc_fv_co u)).
Proof.
  apply fc_syntax_ind; intros; cbn in *;
    try (split; fsetdec);
    try (destruct lt_eq_lt_dec as [[]|]; cbn; split; fsetdec);
    repeat match goal with IH : forall _ _ _, _ |- _ => first [pose proof (IH d u x); pose proof (IH (S d) u x); clear IH | fail 1] end;
    fc_unpack; split; fsetdec.
Qed.
Definition fc_fv_coopen_tm := proj1 (fc_fv_coopen).
Definition fc_fv_coopen_co := proj1 (proj2 (proj2 (fc_fv_coopen))).

(** Scoping of annotated judgments and the fixed signature. *)

Lemma fc_FixTyping : AnnTyping nil FixTy a_Star.
Proof.
  unfold FixTy.
  eapply (An_Pi empty).
  - intros x Fx.
    change (AnnTyping (x ~ Tm a_Star)
              (a_Pi Rel (a_Pi Rel (a_Var_f x) (a_Var_f x)) (a_Var_f x)) a_Star).
    assert (X : AnnCtx (x ~ Tm a_Star)).
    { apply An_ConsTm; [constructor|apply An_Star; constructor|simpl; fsetdec]. }
    assert (V : AnnTyping (x ~ Tm a_Star) (a_Var_f x) a_Star).
    { apply An_Var; [assumption|simpl; auto]. }
    assert (F : AnnTyping (x ~ Tm a_Star) (a_Pi Rel (a_Var_f x) (a_Var_f x)) a_Star).
    { eapply (An_Pi (singleton x)); [|exact V].
      intros y Fy. change (AnnTyping ((y,Tm (a_Var_f x)) :: x ~ Tm a_Star) (a_Var_f x) a_Star).
      apply An_Var.
      - apply An_ConsTm; [exact X|exact V|simpl; fsetdec].
      - simpl; auto. }
    eapply (An_Pi (singleton x)); [|exact F].
    intros y Fy. change (AnnTyping ((y,Tm (a_Pi Rel (a_Var_f x) (a_Var_f x))) :: x ~ Tm a_Star) (a_Var_f x) a_Star).
    apply An_Var.
    + apply An_ConsTm; [exact X|exact F|simpl; fsetdec].
    + simpl; auto.
  - apply An_Star; constructor.
Qed.

Lemma fc_family_binding : forall F a A, binds F (Ax a A) an_toplevel ->
  F = Fix /\ a = FixDef /\ A = FixTy.
Proof. intros F a A B; simpl in B; destruct B as [B|[]]; inversion B; auto. Qed.

Definition fc_degree_sort s :=
  match s with Tm a => fc_degree_tm 0 0 a | Co p => fc_degree_constraint 0 0 p end.

Ltac fc_unopen_degree :=
  repeat match goal with
  | J : fc_degree_tm 0 0 (open_tm_wrt_tm ?a ?u) |- _ =>
      apply (fc_tmopen_degree_inv_tm a 0 0 0 u (Nat.le_refl 0)) in J
  | J : fc_degree_co 0 0 (open_co_wrt_tm ?a ?u) |- _ =>
      apply (fc_tmopen_degree_inv_co a 0 0 0 u (Nat.le_refl 0)) in J
  | J : fc_degree_tm 0 0 (open_tm_wrt_co ?a ?u) |- _ =>
      apply (fc_coopen_degree_inv_tm a 0 0 0 u (Nat.le_refl 0)) in J
  | J : fc_degree_co 0 0 (open_co_wrt_co ?a ?u) |- _ =>
      apply (fc_coopen_degree_inv_co a 0 0 0 u (Nat.le_refl 0)) in J
  end.

Ltac fc_open_degree :=
  lazymatch goal with
  | |- fc_degree_tm 0 0 (open_tm_wrt_tm _ _) =>
      apply fc_tmopen_degree_tm; [apply Nat.le_refl | cbn; auto | assumption]
  | |- fc_degree_tm 0 0 (open_tm_wrt_co _ _) =>
      apply fc_coopen_degree_tm; [apply Nat.le_refl | cbn; auto | assumption]
  end.

Ltac fc_specialize_fresh :=
  match goal with
  | J : forall x : atom, x `notin` ?L -> _ |- _ =>
    let y := fresh "fresh_atom" in let F := fresh "fresh_proof" in
    destruct (atom_fresh L) as [y F];
    repeat match goal with K : forall x : atom, x `notin` L -> _ |- _ =>
      specialize (K y F)
    end
  end.

Lemma fc_judgment_degrees :
  (forall G p, AnnPropWff G p -> fc_degree_constraint 0 0 p) /\
  (forall G a A, AnnTyping G a A -> fc_degree_tm 0 0 a /\ fc_degree_tm 0 0 A) /\
  (forall G D g p q, AnnIso G D g p q ->
    fc_degree_co 0 0 g /\ fc_degree_constraint 0 0 p /\ fc_degree_constraint 0 0 q) /\
  (forall G D g a b, AnnDefEq G D g a b ->
    fc_degree_co 0 0 g /\ fc_degree_tm 0 0 a /\ fc_degree_tm 0 0 b) /\
  (forall G, AnnCtx G -> forall x s, binds x s G -> fc_degree_sort s) /\
  (forall S, AnnSig S -> True).
Proof.
  apply fc_ann_ind; intros; try exact I.
  all: try fc_specialize_fresh.
  all: fc_unpack; fc_unopen_degree.
  all: try match goal with B : binds _ (Ax _ _) an_toplevel |- _ =>
      destruct (fc_family_binding _ _ _ B) as (-> & -> & ->) end.
  all: cbn [fc_degree_tm fc_degree_co fc_degree_constraint] in *; fc_unpack.
  all: try solve [repeat split; first [assumption | fc_open_degree | eauto 2]].
  - split; [exact I | exact (H x (Tm A) b)].
  - compute; repeat split; lia.
  - pose proof (H c (Co (Eq a b A)) b0) as J.
    simpl in J. tauto.
  - assert (C : fc_degree_tm 1 0 b3).
    { match goal with J : open_tm_wrt_tm b3 (a_Var_f ?x) = _ |- _ =>
        apply (fc_tmopen_degree_inv_tm b3 0 0 0 (a_Var_f x) (Nat.le_refl 0));
        change (fc_degree_tm 0 0 (open_tm_wrt_tm b3 (a_Var_f x)));
        rewrite J; fc_open_degree
      end. }
    tauto.
  - contradiction.
  - match goal with J : binds _ _ _ |- _ => destruct J as [E|B] end; [inversion E; subst; assumption | eauto].
  - match goal with J : binds _ _ _ |- _ => destruct J as [E|B] end; [inversion E; subst; assumption | eauto].
Qed.

Definition fc_type_degrees := proj1 (proj2 fc_judgment_degrees).
Definition fc_co_degrees := proj1 (proj2 (proj2 (proj2 fc_judgment_degrees))).
Definition fc_iso_degrees := proj1 (proj2 (proj2 fc_judgment_degrees)).
Definition fc_typ_degree G a A H := proj1 (fc_type_degrees G a A H).
Definition fc_co_degree G D g a b H := proj1 (fc_co_degrees G D g a b H).
Definition fc_iso_degree G D g a b H := proj1 (fc_iso_degrees G D g a b H).

(** Free atoms in synthesized classifiers and endpoints. *)

Ltac fc_open_fv_away :=
  lazymatch goal with
  | |- ?z `notin` fc_fv_tm (open_tm_wrt_tm ?a ?u) =>
    let I := fresh "HI" in intro I; apply (proj2 (fc_fv_tmopen_tm a 0 u z)) in I; cbn in I; fsetdec
  | |- ?z `notin` fc_fv_tm (open_tm_wrt_co ?a ?u) =>
    let I := fresh "HI" in intro I; apply (proj2 (fc_fv_coopen_tm a 0 u z)) in I; cbn in I; fsetdec
  | |- ?z `notin` fc_fv_co (open_co_wrt_tm ?a ?u) =>
    let I := fresh "HI" in intro I; apply (proj2 (fc_fv_tmopen_co a 0 u z)) in I; cbn in I; fsetdec
  | |- ?z `notin` fc_fv_co (open_co_wrt_co ?a ?u) =>
    let I := fresh "HI" in intro I; apply (proj2 (fc_fv_coopen_co a 0 u z)) in I; cbn in I; fsetdec
  end.

Ltac fc_forget_open_fv :=
  repeat match goal with
  | J : ?z `notin` fc_fv_tm (open_tm_wrt_tm ?a ?u) |- _ =>
    let F := fresh "F" in let K := fresh "occurs" in assert (F : z `notin` fc_fv_tm a) by
      (intro K; exact (J (proj1 (fc_fv_tmopen_tm a 0 u z) K))); clear J
  | J : ?z `notin` fc_fv_tm (open_tm_wrt_co ?a ?u) |- _ =>
    let F := fresh "F" in let K := fresh "occurs" in assert (F : z `notin` fc_fv_tm a) by
      (intro K; exact (J (proj1 (fc_fv_coopen_tm a 0 u z) K))); clear J
  end.

Ltac fc_solve_fv :=
  first [
    assumption
  | fc_open_fv_away
  | lazymatch goal with
    | |- ?z `notin` fc_fv_ctx (?x ~ ?s ++ ?G) =>
      change (z `notin` fc_fv_ctx ((x,s)::G));
      cbn [fc_fv_ctx fc_fv_sort]; fsetdec
    end
  | solve [cbn [fc_fv_tm fc_fv_co fc_fv_constraint fc_fv_ctx fc_fv_sort] in *; fsetdec]
  ].

Ltac fc_fresh_for L z :=
  let y := fresh "fresh_atom" in let F := fresh "fresh_proof" in
  destruct (atom_fresh (L \u singleton z)) as [y F];
  let N := fresh "fresh_clause" in assert (N : y `notin` L) by fsetdec;
  repeat match goal with K : forall x : _, x `notin` ?S -> _ |- _ =>
    constr_eq L S; specialize (K y N)
  end.

Ltac fc_fv_spec z :=
  repeat match goal with J : forall x : atom, x `notin` fc_fv_ctx _ -> _ |- _ =>
    let K := fresh "available_fv" in
    pose proof (J z ltac:(fc_solve_fv) ltac:(fc_solve_fv)) as K; clear J;
    cbn [fc_fv_tm fc_fv_co fc_fv_constraint] in K; fc_unpack
  end.

Lemma fc_judgment_free :
  (forall G p, AnnPropWff G p -> True) /\
  (forall G a A, AnnTyping G a A -> forall z,
    z \notin fc_fv_ctx G -> z \notin fc_fv_tm a -> z \notin fc_fv_tm A) /\
  (forall G D g p q, AnnIso G D g p q -> forall z,
    z \notin fc_fv_ctx G -> z \notin fc_fv_co g ->
      z \notin fc_fv_constraint p /\ z \notin fc_fv_constraint q) /\
  (forall G D g a b, AnnDefEq G D g a b -> forall z,
    z \notin fc_fv_ctx G -> z \notin fc_fv_co g ->
      z \notin fc_fv_tm a /\ z \notin fc_fv_tm b) /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof.
  apply fc_ann_ind; intros; try exact I.
  all: try match goal with B : binds _ (Ax _ _) an_toplevel |- _ =>
      destruct (fc_family_binding _ _ _ B) as (-> & -> & ->) end.
  all: cbn [fc_fv_tm fc_fv_co fc_fv_constraint] in *.
  all: try fc_fv_spec z.
  all: repeat split; try fc_solve_fv.
  all: try match goal with
    | B : binds _ _ _ |- _ =>
      pose proof (fc_Gfv_binds _ _ _ B z) as F;
      simpl in F; fsetdec
    end.
  all: try (fc_fresh_for L z); try fc_fv_spec z; fc_forget_open_fv; try fc_solve_fv.
  all: try solve [unfold FixTy; cbn [fc_fv_tm]; fsetdec].
  all: try match goal with
  | J : open_tm_wrt_tm ?a (a_Var_f ?x) = ?t |- _ =>
    let F := fresh in assert (F : z `notin` fc_fv_tm (open_tm_wrt_tm a (a_Var_f x))) by
      (rewrite J; fc_open_fv_away)
  | J : open_tm_wrt_co ?a (g_Var_f ?x) = ?t |- _ =>
    let F := fresh in assert (F : z `notin` fc_fv_tm (open_tm_wrt_co a (g_Var_f x))) by
      (rewrite J; fc_open_fv_away)
  end; fc_forget_open_fv; fc_solve_fv.
Qed.

Definition fc_typ_free := proj1 (proj2 fc_judgment_free).
Definition fc_iso_free := proj1 (proj2 (proj2 fc_judgment_free)).
Definition fc_eq_free := proj1 (proj2 (proj2 (proj2 fc_judgment_free))).

(** Checking cofinite premises at one fresh atom. *)

Lemma fc_tmopen_close_subst :
  (forall e n x u,
    open_tm_wrt_tm_rec n u (fc_close_tm_tm n x e) = fc_subst_tm (fc_once a_Var_f x u) g_Var_f e) /\
  (forall e n x u,
    open_brs_wrt_tm_rec n u (fc_close_tm_brs n x e) = fc_subst_brs (fc_once a_Var_f x u) g_Var_f e) /\
  (forall e n x u,
    open_co_wrt_tm_rec n u (fc_close_tm_co n x e) = fc_subst_co (fc_once a_Var_f x u) g_Var_f e) /\
  (forall e n x u,
    open_constraint_wrt_tm_rec n u (fc_close_tm_constraint n x e) = fc_subst_constraint (fc_once a_Var_f x u) g_Var_f e).
Proof.
  apply fc_syntax_ind; intros; cbn -[lt_eq_lt_dec];
    repeat match goal with H : forall _ _ _, _ |- _ => rewrite H end;
    try reflexivity.
  all: unfold fc_once; repeat destruct lt_dec; repeat destruct (_ == _); try subst;
    cbn -[lt_eq_lt_dec]; repeat destruct lt_eq_lt_dec as [[?|?]|?];
    try reflexivity; f_equal; lia.
Qed.
Definition fc_tmopen_close_subst_tm := proj1 (fc_tmopen_close_subst).
Definition fc_tmopen_close_subst_co := proj1 (proj2 (proj2 (fc_tmopen_close_subst))).

Lemma fc_coopen_close_subst :
  (forall e n x u,
    open_tm_wrt_co_rec n u (fc_close_co_tm n x e) = fc_subst_tm a_Var_f (fc_once g_Var_f x u) e) /\
  (forall e n x u,
    open_brs_wrt_co_rec n u (fc_close_co_brs n x e) = fc_subst_brs a_Var_f (fc_once g_Var_f x u) e) /\
  (forall e n x u,
    open_co_wrt_co_rec n u (fc_close_co_co n x e) = fc_subst_co a_Var_f (fc_once g_Var_f x u) e) /\
  (forall e n x u,
    open_constraint_wrt_co_rec n u (fc_close_co_constraint n x e) = fc_subst_constraint a_Var_f (fc_once g_Var_f x u) e).
Proof.
  apply fc_syntax_ind; intros; cbn -[lt_eq_lt_dec];
    repeat match goal with H : forall _ _ _, _ |- _ => rewrite H end;
    try reflexivity.
  all: unfold fc_once; repeat destruct lt_dec; repeat destruct (_ == _); try subst;
    cbn -[lt_eq_lt_dec]; repeat destruct lt_eq_lt_dec as [[?|?]|?];
    try reflexivity; f_equal; lia.
Qed.
Definition fc_coopen_close_subst_tm := proj1 (fc_coopen_close_subst).
Definition fc_coopen_close_subst_co := proj1 (proj2 (proj2 (fc_coopen_close_subst))).

Definition fc_rename_t x y := fc_replace_tm x (a_Var_f y) I.
Definition fc_rename_c x y := fc_replace_co x (g_Var_f y) I.

Lemma fc_rename_t_context : forall G x y A,
  AnnCtx G -> AnnTyping G A a_Star -> x \notin fc_fv_ctx G ->
  x \notin fc_fv_tm A -> y \notin dom G ->
  fc_context_map (fc_rename_t x y) (fc_replace_rel x ((y,Tm A)::G))
    ((x,Tm A)::G) ((y,Tm A)::G).
Proof.
  intros G x y A W J Fx Fa Fy.
  assert (O : fc_id_off (fc_rename_t x y) x) by apply fc_replace_tm_off.
  apply fc_context_replace; try assumption.
  - unfold fc_rename_t; simpl; fsetdec.
  - intros; right; assumption.
  - intros A' E. injection E as <-. rewrite (fc_T_off (fc_rename_t x y) x A O Fa).
    change (AnnTyping ((y,Tm A)::G) (fc_once a_Var_f x (a_Var_f y) x) A).
    rewrite fc_once_here. apply An_Var; [apply An_ConsTm; assumption | simpl; auto].
  - discriminate.
Qed.

Lemma fc_rename_c_context : forall G x y phi,
  AnnCtx G -> AnnPropWff G phi -> x \notin fc_fv_ctx G ->
  x \notin fc_fv_constraint phi -> y \notin dom G ->
  fc_context_map (fc_rename_c x y) (fc_replace_rel x ((y,Co phi)::G))
    ((x,Co phi)::G) ((y,Co phi)::G).
Proof.
  intros G x y phi W J Fx Fa Fy.
  assert (O : fc_id_off (fc_rename_c x y) x) by apply fc_replace_co_off.
  apply fc_context_replace; try assumption.
  - unfold fc_rename_c; simpl; fsetdec.
  - intros; right; assumption.
  - discriminate.
  - intros u v A E; injection E as ->. simpl in Fa.
    rewrite (fc_T_off (fc_rename_c x y) x u O), (fc_T_off (fc_rename_c x y) x v O) by fsetdec.
    change (AnnDefEq ((y,Co (Eq u v A))::G) (dom ((y,Co (Eq u v A))::G)) (fc_once g_Var_f x (g_Var_f y) x) u v).
    rewrite fc_once_here; eapply (An_Assn _ _ _ _ _ A).
    + apply An_ConsCo; assumption.
    + simpl; auto.
    + rewrite dom_cons; fsetdec.
Qed.

Lemma fc_rename_t_typ : forall G x y A a B,
  AnnCtx G -> AnnTyping G A a_Star -> x \notin fc_fv_ctx G ->
  x \notin fc_fv_tm A -> y \notin dom G ->
  AnnTyping ((x,Tm A)::G) a B ->
  AnnTyping ((y,Tm A)::G) (fc_T (fc_rename_t x y) a) (fc_T (fc_rename_t x y) B).
Proof.
  intros G x y A a B W J Fx Fa Fy K.
  pose proof (fc_rename_t_context G x y A W J Fx Fa Fy) as M.
  exact (proj1 (proj2 (fc_transport_base _ _ _ _ M (An_ConsTm G y A W J Fy))) a B K).
Qed.

Lemma fc_rename_c_typ : forall G x y phi a B,
  AnnCtx G -> AnnPropWff G phi -> x \notin fc_fv_ctx G ->
  x \notin fc_fv_constraint phi -> y \notin dom G ->
  AnnTyping ((x,Co phi)::G) a B ->
  AnnTyping ((y,Co phi)::G) (fc_T (fc_rename_c x y) a) (fc_T (fc_rename_c x y) B).
Proof.
  intros G x y phi a B W J Fx Fa Fy K.
  pose proof (fc_rename_c_context G x y phi W J Fx Fa Fy) as M.
  exact (proj1 (proj2 (fc_transport_base _ _ _ _ M (An_ConsCo G y phi W J Fy))) a B K).
Qed.

Lemma fc_rename_avail : forall x H D, x \notin D -> fc_Dmap (fc_replace_rel x H) D D.
Proof. intros x H D N u v [[_ ->]|[-> _]] J; [exact J|contradiction]. Qed.

Lemma fc_rename_t_eq : forall G D x y A g a b,
  AnnCtx G -> AnnTyping G A a_Star -> x \notin fc_fv_ctx G ->
  x \notin fc_fv_tm A -> y \notin dom G -> x \notin D ->
  AnnDefEq ((x,Tm A)::G) D g a b ->
  AnnDefEq ((y,Tm A)::G) D (fc_C (fc_rename_t x y) g)
    (fc_T (fc_rename_t x y) a) (fc_T (fc_rename_t x y) b).
Proof.
  intros G D x y A g a b W J Fx Fa Fy N K.
  pose proof (fc_rename_t_context G x y A W J Fx Fa Fy) as M.
  exact (proj2 (proj2 (proj2 (fc_transport_base _ _ _ _ M (An_ConsTm G y A W J Fy)))) _ _ _ _ _
            (fc_rename_avail x _ D N) K).
Qed.

Lemma fc_rename_c_eq : forall G D x y phi g a b,
  AnnCtx G -> AnnPropWff G phi -> x \notin fc_fv_ctx G ->
  x \notin fc_fv_constraint phi -> y \notin dom G -> x \notin D ->
  AnnDefEq ((x,Co phi)::G) D g a b ->
  AnnDefEq ((y,Co phi)::G) D (fc_C (fc_rename_c x y) g)
    (fc_T (fc_rename_c x y) a) (fc_T (fc_rename_c x y) b).
Proof.
  intros G D x y phi g a b W J Fx Fa Fy N K.
  pose proof (fc_rename_c_context G x y phi W J Fx Fa Fy) as M.
  exact (proj2 (proj2 (proj2 (fc_transport_base _ _ _ _ M (An_ConsCo G y phi W J Fy)))) _ _ _ _ _
            (fc_rename_avail x _ D N) K).
Qed.

Lemma fc_rename_t_topen : forall x y a, x \notin fc_fv_tm a ->
  fc_T (fc_rename_t x y) (open_tm_wrt_tm a (a_Var_f x)) =
  open_tm_wrt_tm a (a_Var_f y).
Proof.
  intros. rewrite fc_open_subst_Tt with (x:=x); try assumption; [|apply fc_replace_tm_off].
  change (open_tm_wrt_tm a (fc_once a_Var_f x (a_Var_f y) x) = open_tm_wrt_tm a (a_Var_f y)).
  now rewrite fc_once_here.
Qed.
Lemma fc_rename_t_copen : forall x y g, x \notin fc_fv_co g ->
  fc_C (fc_rename_t x y) (open_co_wrt_tm g (a_Var_f x)) =
  open_co_wrt_tm g (a_Var_f y).
Proof.
  intros. rewrite fc_open_subst_Ct with (x:=x); try assumption; [|apply fc_replace_tm_off].
  change (open_co_wrt_tm g (fc_once a_Var_f x (a_Var_f y) x) = open_co_wrt_tm g (a_Var_f y)).
  now rewrite fc_once_here.
Qed.
Lemma fc_rename_c_topen : forall x y a, x \notin fc_fv_tm a ->
  fc_T (fc_rename_c x y) (open_tm_wrt_co a (g_Var_f x)) =
  open_tm_wrt_co a (g_Var_f y).
Proof.
  intros. rewrite fc_open_subst_Tc with (x:=x); try assumption; [|apply fc_replace_co_off].
  change (open_tm_wrt_co a (fc_once g_Var_f x (g_Var_f y) x) = open_tm_wrt_co a (g_Var_f y)).
  now rewrite fc_once_here.
Qed.
Lemma fc_rename_c_copen : forall x y g, x \notin fc_fv_co g ->
  fc_C (fc_rename_c x y) (open_co_wrt_co g (g_Var_f x)) =
  open_co_wrt_co g (g_Var_f y).
Proof.
  intros. rewrite fc_open_subst_Cc with (x:=x); try assumption; [|apply fc_replace_co_off].
  change (open_co_wrt_co g (fc_once g_Var_f x (g_Var_f y) x) = open_co_wrt_co g (g_Var_f y)).
  now rewrite fc_once_here.
Qed.

Lemma fc_close_rename_t : forall x y a,
  open_tm_wrt_tm (fc_close_tm_tm 0 x a) (a_Var_f y) = fc_T (fc_rename_t x y) a.
Proof. intros; apply fc_tmopen_close_subst_tm. Qed.
Lemma fc_close_rename_c : forall x y a,
  open_tm_wrt_co (fc_close_co_tm 0 x a) (g_Var_f y) = fc_T (fc_rename_c x y) a.
Proof. intros; apply fc_coopen_close_subst_tm. Qed.
Lemma fc_close_rename_ct : forall x y g,
  open_co_wrt_tm (fc_close_tm_co 0 x g) (a_Var_f y) = fc_C (fc_rename_t x y) g.
Proof. intros; apply fc_tmopen_close_subst_co. Qed.
Lemma fc_close_rename_cc : forall x y g,
  open_co_wrt_co (fc_close_co_co 0 x g) (g_Var_f y) = fc_C (fc_rename_c x y) g.
Proof. intros; apply fc_coopen_close_subst_co. Qed.

Lemma fc_tabstract_typ : forall G A x a B, AnnCtx G -> AnnTyping G A a_Star ->
  x \notin fc_fv_ctx G -> x \notin fc_fv_tm A ->
  AnnTyping ((x,Tm A)::G) a B ->
  forall y, y \notin dom G -> AnnTyping ((y,Tm A)::G)
    (open_tm_wrt_tm (fc_close_tm_tm 0 x a) (a_Var_f y))
    (open_tm_wrt_tm (fc_close_tm_tm 0 x B) (a_Var_f y)).
Proof.
  intros. rewrite !fc_close_rename_t. apply fc_rename_t_typ; assumption.
Qed.

Lemma fc_cabstract_typ : forall G phi x a B, AnnCtx G -> AnnPropWff G phi ->
  x \notin fc_fv_ctx G -> x \notin fc_fv_constraint phi ->
  AnnTyping ((x,Co phi)::G) a B ->
  forall y, y \notin dom G -> AnnTyping ((y,Co phi)::G)
    (open_tm_wrt_co (fc_close_co_tm 0 x a) (g_Var_f y))
    (open_tm_wrt_co (fc_close_co_tm 0 x B) (g_Var_f y)).
Proof.
  intros. rewrite !fc_close_rename_c. apply fc_rename_c_typ; assumption.
Qed.

Lemma fc_tabstract_eq : forall G D A x g a b, AnnCtx G -> AnnTyping G A a_Star ->
  x \notin fc_fv_ctx G -> x \notin fc_fv_tm A -> x \notin D ->
  AnnDefEq ((x,Tm A)::G) D g a b ->
  forall y, y \notin dom G -> AnnDefEq ((y,Tm A)::G) D
    (open_co_wrt_tm (fc_close_tm_co 0 x g) (a_Var_f y))
    (open_tm_wrt_tm (fc_close_tm_tm 0 x a) (a_Var_f y))
    (open_tm_wrt_tm (fc_close_tm_tm 0 x b) (a_Var_f y)).
Proof.
  intros; rewrite fc_close_rename_ct, !fc_close_rename_t; apply fc_rename_t_eq; assumption.
Qed.

Lemma fc_cabstract_eq : forall G D phi x g a b, AnnCtx G -> AnnPropWff G phi ->
  x \notin fc_fv_ctx G -> x \notin fc_fv_constraint phi -> x \notin D ->
  AnnDefEq ((x,Co phi)::G) D g a b ->
  forall y, y \notin dom G -> AnnDefEq ((y,Co phi)::G) D
    (open_co_wrt_co (fc_close_co_co 0 x g) (g_Var_f y))
    (open_tm_wrt_co (fc_close_co_tm 0 x a) (g_Var_f y))
    (open_tm_wrt_co (fc_close_co_tm 0 x b) (g_Var_f y)).
Proof.
  intros; rewrite fc_close_rename_cc, !fc_close_rename_c; apply fc_rename_c_eq; assumption.
Qed.

Lemma fc_fresh_t_typ : forall L G A a B x, AnnCtx G -> AnnTyping G A a_Star ->
  x \notin dom G ->
  (forall y, y \notin L -> AnnTyping ((y,Tm A)::G)
      (open_tm_wrt_tm a (a_Var_f y)) (open_tm_wrt_tm B (a_Var_f y))) ->
  AnnTyping ((x,Tm A)::G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)).
Proof.
  intros L G A a B x W K Fx J.
  destruct (atom_fresh (L \u fc_fv_ctx G \u fc_fv_tm A \u fc_fv_tm a \u fc_fv_tm B))
    as [y Fy].
  pose proof (fc_rename_t_typ G y x A _ _ W K ltac:(fsetdec) ltac:(fsetdec) Fx (J y ltac:(fsetdec))) as Q.
  now rewrite !fc_rename_t_topen in Q by fsetdec.
Qed.

Lemma fc_fresh_c_typ : forall L G phi a B x, AnnCtx G -> AnnPropWff G phi ->
  x \notin dom G ->
  (forall y, y \notin L -> AnnTyping ((y,Co phi)::G)
      (open_tm_wrt_co a (g_Var_f y)) (open_tm_wrt_co B (g_Var_f y))) ->
  AnnTyping ((x,Co phi)::G) (open_tm_wrt_co a (g_Var_f x)) (open_tm_wrt_co B (g_Var_f x)).
Proof.
  intros L G phi a B x W K Fx J.
  destruct (atom_fresh (L \u fc_fv_ctx G \u fc_fv_constraint phi \u fc_fv_tm a \u fc_fv_tm B))
    as [y Fy].
  pose proof (fc_rename_c_typ G y x phi _ _ W K ltac:(fsetdec) ltac:(fsetdec) Fx (J y ltac:(fsetdec))) as Q.
  now rewrite !fc_rename_c_topen in Q by fsetdec.
Qed.

Lemma fc_fresh_t_eq : forall L G D A g a b x, AnnCtx G -> AnnTyping G A a_Star ->
  x \notin dom G ->
  (forall y, y \notin L -> AnnDefEq ((y,Tm A)::G) D
      (open_co_wrt_tm g (a_Var_f y)) (open_tm_wrt_tm a (a_Var_f y)) (open_tm_wrt_tm b (a_Var_f y))) ->
  AnnDefEq ((x,Tm A)::G) D
    (open_co_wrt_tm g (a_Var_f x)) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x)).
Proof.
  intros L G D A g a b x W K Fx J.
  destruct (atom_fresh (L \u D \u fc_fv_ctx G \u fc_fv_tm A \u fc_fv_co g \u fc_fv_tm a \u fc_fv_tm b)) as [y Fy].
  pose proof (fc_rename_t_eq G D y x A _ _ _ W K ltac:(fsetdec) ltac:(fsetdec)
                Fx ltac:(fsetdec) (J y ltac:(fsetdec))) as Q.
  now rewrite fc_rename_t_copen, !fc_rename_t_topen in Q by fsetdec.
Qed.

Lemma fc_fresh_c_eq : forall L G D phi g a b x, AnnCtx G -> AnnPropWff G phi ->
  x \notin dom G ->
  (forall y, y \notin L -> AnnDefEq ((y,Co phi)::G) D
      (open_co_wrt_co g (g_Var_f y)) (open_tm_wrt_co a (g_Var_f y)) (open_tm_wrt_co b (g_Var_f y))) ->
  AnnDefEq ((x,Co phi)::G) D
    (open_co_wrt_co g (g_Var_f x)) (open_tm_wrt_co a (g_Var_f x)) (open_tm_wrt_co b (g_Var_f x)).
Proof.
  intros L G D phi g a b x W K Fx J.
  destruct (atom_fresh (L \u D \u fc_fv_ctx G \u fc_fv_constraint phi \u fc_fv_co g \u fc_fv_tm a \u fc_fv_tm b)) as [y Fy].
  pose proof (fc_rename_c_eq G D y x phi _ _ _ W K ltac:(fsetdec) ltac:(fsetdec)
                Fx ltac:(fsetdec) (J y ltac:(fsetdec))) as Q.
  now rewrite fc_rename_c_copen, !fc_rename_c_topen in Q by fsetdec.
Qed.

(** Transport of a binder body across its domain equality. *)

Fixpoint fc_tmcast_tm (d : nat) (witness : co) (e : tm) : tm :=
  match e with
  | a_Star => a_Star
  | a_Var_b i => if Nat.eq_dec i d then a_Conv (a_Var_b i) (g_Sym witness) else a_Var_b i
  | a_Var_f x0 => a_Var_f x0
  | a_Abs rho A b => a_Abs rho (fc_tmcast_tm d witness A) (fc_tmcast_tm (S d) witness b)
  | a_UAbs rho b => a_UAbs rho (fc_tmcast_tm (S d) witness b)
  | a_App a rho b => a_App (fc_tmcast_tm d witness a) rho (fc_tmcast_tm d witness b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (fc_tmcast_tm d witness A) (fc_tmcast_tm (S d) witness B)
  | a_Conv a g => a_Conv (fc_tmcast_tm d witness a) (fc_tmcast_co d witness g)
  | a_CPi phi B => a_CPi (fc_tmcast_constraint d witness phi) (fc_tmcast_tm d witness B)
  | a_CAbs phi b => a_CAbs (fc_tmcast_constraint d witness phi) (fc_tmcast_tm d witness b)
  | a_UCAbs b => a_UCAbs (fc_tmcast_tm d witness b)
  | a_CApp a g => a_CApp (fc_tmcast_tm d witness a) (fc_tmcast_co d witness g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs5 => a_Case (fc_tmcast_tm d witness a) (fc_tmcast_brs d witness brs5)
  end
with fc_tmcast_brs (d : nat) (witness : co) (e : brs) : brs :=
  match e with
  | br_None => br_None
  | br_One K a brs5 => br_One K (fc_tmcast_tm d witness a) (fc_tmcast_brs d witness brs5)
  end
with fc_tmcast_co (d : nat) (witness : co) (e : co) : co :=
  match e with
  | g_Triv => g_Triv
  | g_Var_b i => g_Var_b i
  | g_Var_f c => g_Var_f c
  | g_Beta a b => g_Beta (fc_tmcast_tm d witness a) (fc_tmcast_tm d witness b)
  | g_Refl a => g_Refl (fc_tmcast_tm d witness a)
  | g_Refl2 a b g => g_Refl2 (fc_tmcast_tm d witness a) (fc_tmcast_tm d witness b) (fc_tmcast_co d witness g)
  | g_Sym g => g_Sym (fc_tmcast_co d witness g)
  | g_Trans g1 g2 => g_Trans (fc_tmcast_co d witness g1) (fc_tmcast_co d witness g2)
  | g_PiCong rho g1 g2 => g_PiCong rho (fc_tmcast_co d witness g1) (fc_tmcast_co (S d) witness g2)
  | g_AbsCong rho g1 g2 => g_AbsCong rho (fc_tmcast_co d witness g1) (fc_tmcast_co (S d) witness g2)
  | g_AppCong g1 rho g2 => g_AppCong (fc_tmcast_co d witness g1) rho (fc_tmcast_co d witness g2)
  | g_PiFst g => g_PiFst (fc_tmcast_co d witness g)
  | g_CPiFst g => g_CPiFst (fc_tmcast_co d witness g)
  | g_IsoSnd g => g_IsoSnd (fc_tmcast_co d witness g)
  | g_PiSnd g1 g2 => g_PiSnd (fc_tmcast_co d witness g1) (fc_tmcast_co d witness g2)
  | g_CPiCong g1 g3 => g_CPiCong (fc_tmcast_co d witness g1) (fc_tmcast_co d witness g3)
  | g_CAbsCong g1 g3 g4 => g_CAbsCong (fc_tmcast_co d witness g1) (fc_tmcast_co d witness g3) (fc_tmcast_co d witness g4)
  | g_CAppCong g g1 g2 => g_CAppCong (fc_tmcast_co d witness g) (fc_tmcast_co d witness g1) (fc_tmcast_co d witness g2)
  | g_CPiSnd g g1 g2 => g_CPiSnd (fc_tmcast_co d witness g) (fc_tmcast_co d witness g1) (fc_tmcast_co d witness g2)
  | g_Cast g1 g2 => g_Cast (fc_tmcast_co d witness g1) (fc_tmcast_co d witness g2)
  | g_EqCong g1 A g2 => g_EqCong (fc_tmcast_co d witness g1) (fc_tmcast_tm d witness A) (fc_tmcast_co d witness g2)
  | g_IsoConv phi1 phi2 g => g_IsoConv (fc_tmcast_constraint d witness phi1) (fc_tmcast_constraint d witness phi2) (fc_tmcast_co d witness g)
  | g_Eta a => g_Eta (fc_tmcast_tm d witness a)
  | g_Left g g' => g_Left (fc_tmcast_co d witness g) (fc_tmcast_co d witness g')
  | g_Right g g' => g_Right (fc_tmcast_co d witness g) (fc_tmcast_co d witness g')
  end
with fc_tmcast_constraint (d : nat) (witness : co) (e : constraint) : constraint :=
  match e with
  | Eq a b A => Eq (fc_tmcast_tm d witness a) (fc_tmcast_tm d witness b) (fc_tmcast_tm d witness A)
  end.

Lemma fc_tmcast_open :
  (forall e d g x, fc_degree_co 0 0 g ->
    open_tm_wrt_tm_rec d (a_Var_f x) (fc_tmcast_tm d g e) =
    open_tm_wrt_tm_rec d (a_Conv (a_Var_f x) (g_Sym g)) e) /\
  (forall e d g x, fc_degree_co 0 0 g ->
    open_brs_wrt_tm_rec d (a_Var_f x) (fc_tmcast_brs d g e) =
    open_brs_wrt_tm_rec d (a_Conv (a_Var_f x) (g_Sym g)) e) /\
  (forall e d g x, fc_degree_co 0 0 g ->
    open_co_wrt_tm_rec d (a_Var_f x) (fc_tmcast_co d g e) =
    open_co_wrt_tm_rec d (a_Conv (a_Var_f x) (g_Sym g)) e) /\
  (forall e d g x, fc_degree_co 0 0 g ->
    open_constraint_wrt_tm_rec d (a_Var_f x) (fc_tmcast_constraint d g e) =
    open_constraint_wrt_tm_rec d (a_Conv (a_Var_f x) (g_Sym g)) e).
Proof.
  apply fc_syntax_ind; intros; cbn -[lt_eq_lt_dec];
    repeat match goal with H : forall _ _ _, _ |- _ => rewrite H by assumption end;
    try reflexivity.
  destruct (Nat.eq_dec n d) as [->|N]; cbn -[lt_eq_lt_dec].
  - destruct lt_eq_lt_dec as [[?|?]|?]; try lia.
    erewrite fc_tmopen_id_co.
    + reflexivity.
    + eapply fc_degree_mono_co with (p:=0) (q:=0); [lia|exact (Nat.le_refl 0)|assumption].
  - destruct lt_eq_lt_dec as [[?|?]|?]; try reflexivity; contradiction.
Qed.
Definition fc_tmcast_open_tm := proj1 (fc_tmcast_open).
Fixpoint fc_cocast_tm (d : nat) (witness : co) (e : tm) : tm :=
  match e with
  | a_Star => a_Star
  | a_Var_b i => a_Var_b i
  | a_Var_f x0 => a_Var_f x0
  | a_Abs rho A b => a_Abs rho (fc_cocast_tm d witness A) (fc_cocast_tm d witness b)
  | a_UAbs rho b => a_UAbs rho (fc_cocast_tm d witness b)
  | a_App a rho b => a_App (fc_cocast_tm d witness a) rho (fc_cocast_tm d witness b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (fc_cocast_tm d witness A) (fc_cocast_tm d witness B)
  | a_Conv a g => a_Conv (fc_cocast_tm d witness a) (fc_cocast_co d witness g)
  | a_CPi phi B => a_CPi (fc_cocast_constraint d witness phi) (fc_cocast_tm (S d) witness B)
  | a_CAbs phi b => a_CAbs (fc_cocast_constraint d witness phi) (fc_cocast_tm (S d) witness b)
  | a_UCAbs b => a_UCAbs (fc_cocast_tm (S d) witness b)
  | a_CApp a g => a_CApp (fc_cocast_tm d witness a) (fc_cocast_co d witness g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs5 => a_Case (fc_cocast_tm d witness a) (fc_cocast_brs d witness brs5)
  end
with fc_cocast_brs (d : nat) (witness : co) (e : brs) : brs :=
  match e with
  | br_None => br_None
  | br_One K a brs5 => br_One K (fc_cocast_tm d witness a) (fc_cocast_brs d witness brs5)
  end
with fc_cocast_co (d : nat) (witness : co) (e : co) : co :=
  match e with
  | g_Triv => g_Triv
  | g_Var_b i => if Nat.eq_dec i d then g_Cast (g_Var_b i) (g_Sym witness) else g_Var_b i
  | g_Var_f c => g_Var_f c
  | g_Beta a b => g_Beta (fc_cocast_tm d witness a) (fc_cocast_tm d witness b)
  | g_Refl a => g_Refl (fc_cocast_tm d witness a)
  | g_Refl2 a b g => g_Refl2 (fc_cocast_tm d witness a) (fc_cocast_tm d witness b) (fc_cocast_co d witness g)
  | g_Sym g => g_Sym (fc_cocast_co d witness g)
  | g_Trans g1 g2 => g_Trans (fc_cocast_co d witness g1) (fc_cocast_co d witness g2)
  | g_PiCong rho g1 g2 => g_PiCong rho (fc_cocast_co d witness g1) (fc_cocast_co d witness g2)
  | g_AbsCong rho g1 g2 => g_AbsCong rho (fc_cocast_co d witness g1) (fc_cocast_co d witness g2)
  | g_AppCong g1 rho g2 => g_AppCong (fc_cocast_co d witness g1) rho (fc_cocast_co d witness g2)
  | g_PiFst g => g_PiFst (fc_cocast_co d witness g)
  | g_CPiFst g => g_CPiFst (fc_cocast_co d witness g)
  | g_IsoSnd g => g_IsoSnd (fc_cocast_co d witness g)
  | g_PiSnd g1 g2 => g_PiSnd (fc_cocast_co d witness g1) (fc_cocast_co d witness g2)
  | g_CPiCong g1 g3 => g_CPiCong (fc_cocast_co d witness g1) (fc_cocast_co (S d) witness g3)
  | g_CAbsCong g1 g3 g4 => g_CAbsCong (fc_cocast_co d witness g1) (fc_cocast_co (S d) witness g3) (fc_cocast_co d witness g4)
  | g_CAppCong g g1 g2 => g_CAppCong (fc_cocast_co d witness g) (fc_cocast_co d witness g1) (fc_cocast_co d witness g2)
  | g_CPiSnd g g1 g2 => g_CPiSnd (fc_cocast_co d witness g) (fc_cocast_co d witness g1) (fc_cocast_co d witness g2)
  | g_Cast g1 g2 => g_Cast (fc_cocast_co d witness g1) (fc_cocast_co d witness g2)
  | g_EqCong g1 A g2 => g_EqCong (fc_cocast_co d witness g1) (fc_cocast_tm d witness A) (fc_cocast_co d witness g2)
  | g_IsoConv phi1 phi2 g => g_IsoConv (fc_cocast_constraint d witness phi1) (fc_cocast_constraint d witness phi2) (fc_cocast_co d witness g)
  | g_Eta a => g_Eta (fc_cocast_tm d witness a)
  | g_Left g g' => g_Left (fc_cocast_co d witness g) (fc_cocast_co d witness g')
  | g_Right g g' => g_Right (fc_cocast_co d witness g) (fc_cocast_co d witness g')
  end
with fc_cocast_constraint (d : nat) (witness : co) (e : constraint) : constraint :=
  match e with
  | Eq a b A => Eq (fc_cocast_tm d witness a) (fc_cocast_tm d witness b) (fc_cocast_tm d witness A)
  end.

Lemma fc_cocast_open :
  (forall e d g x, fc_degree_co 0 0 g ->
    open_tm_wrt_co_rec d (g_Var_f x) (fc_cocast_tm d g e) =
    open_tm_wrt_co_rec d (g_Cast (g_Var_f x) (g_Sym g)) e) /\
  (forall e d g x, fc_degree_co 0 0 g ->
    open_brs_wrt_co_rec d (g_Var_f x) (fc_cocast_brs d g e) =
    open_brs_wrt_co_rec d (g_Cast (g_Var_f x) (g_Sym g)) e) /\
  (forall e d g x, fc_degree_co 0 0 g ->
    open_co_wrt_co_rec d (g_Var_f x) (fc_cocast_co d g e) =
    open_co_wrt_co_rec d (g_Cast (g_Var_f x) (g_Sym g)) e) /\
  (forall e d g x, fc_degree_co 0 0 g ->
    open_constraint_wrt_co_rec d (g_Var_f x) (fc_cocast_constraint d g e) =
    open_constraint_wrt_co_rec d (g_Cast (g_Var_f x) (g_Sym g)) e).
Proof.
  apply fc_syntax_ind; intros; cbn -[lt_eq_lt_dec];
    repeat match goal with H : forall _ _ _, _ |- _ => rewrite H by assumption end;
    try reflexivity.
  destruct (Nat.eq_dec n d) as [->|N]; cbn -[lt_eq_lt_dec].
  - destruct lt_eq_lt_dec as [[?|?]|?]; try lia.
    erewrite fc_coopen_id_co.
    + reflexivity.
    + eapply fc_degree_mono_co with (p:=0) (q:=0); [exact (Nat.le_refl 0)|lia|assumption].
  - destruct lt_eq_lt_dec as [[?|?]|?]; try reflexivity; contradiction.
Qed.
Definition fc_cocast_open_tm := proj1 (fc_cocast_open).

(** Uniqueness of classifiers and coercion endpoints. *)

Lemma fc_close_t_open_t : forall a x, x `notin` fc_fv_tm a ->
  fc_close_tm_tm 0 x (open_tm_wrt_tm a (a_Var_f x)) = a.
Proof. exact (fun a x => proj1 fc_close_after_open a 0 x). Qed.
Lemma fc_close_c_open_c : forall a x, x `notin` fc_fv_tm a ->
  fc_close_co_tm 0 x (open_tm_wrt_co a (g_Var_f x)) = a.
Proof. exact (fun a x => proj1 fc_cclose_after_open a 0 x). Qed.

Ltac fc_all_names :=
  let S := gather_atoms_with (fun x : atoms => x) in
  let T := gather_atoms_with fc_fv_tm in
  let C := gather_atoms_with fc_fv_co in
  let P := gather_atoms_with fc_fv_constraint in
  let G := gather_atoms_with fc_fv_ctx in
  constr:(S \u T \u C \u P \u G).

Ltac fc_open_inject :=
  repeat match goal with
  | E : open_tm_wrt_tm ?a (a_Var_f ?x) = open_tm_wrt_tm ?b (a_Var_f ?x) |- _ =>
    let J := fresh in pose proof (f_equal (fc_close_tm_tm 0 x) E) as J;
    cbn beta in J; rewrite !fc_close_t_open_t in J by fsetdec; clear E
  | E : open_tm_wrt_co ?a (g_Var_f ?x) = open_tm_wrt_co ?b (g_Var_f ?x) |- _ =>
    let J := fresh in pose proof (f_equal (fc_close_co_tm 0 x) E) as J;
    cbn beta in J; rewrite !fc_close_c_open_c in J by fsetdec; clear E
  end.

Ltac fc_use_unique :=
  repeat match goal with
  | IH : forall B, AnnTyping ?G ?a B -> ?A = B,
    J : AnnTyping ?G ?a ?B |- _ =>
    let E := fresh in
    first [constr_eq A B; fail 1 | pose proof (IH B J) as E; clear IH; try (injection E as E); subst]
  | IH : forall a b, AnnDefEq ?G ?D ?g a b -> ?A = a /\ ?B = b,
    J : AnnDefEq ?G ?D ?g ?A' ?B' |- _ =>
    let E1 := fresh in let E2 := fresh in
    first [constr_eq (A,B) (A',B'); fail 1 |
           destruct (IH A' B' J) as [E1 E2]; clear IH;
           try (injection E1 as E1); try (injection E2 as E2); subst]
  | IH : forall a b, AnnIso ?G ?D ?g a b -> ?A = a /\ ?B = b,
    J : AnnIso ?G ?D ?g ?A' ?B' |- _ =>
    let E1 := fresh in let E2 := fresh in
    first [constr_eq (A,B) (A',B'); fail 1 |
           destruct (IH A' B' J) as [E1 E2]; clear IH;
           try (injection E1 as E1); try (injection E2 as E2); subst]
  end.

Lemma fc_unique :
  (forall G p, AnnPropWff G p -> True) /\
  (forall G a A, AnnTyping G a A -> forall B, AnnTyping G a B -> A = B) /\
  (forall G D g p q, AnnIso G D g p q -> forall p' q', AnnIso G D g p' q' -> p = p' /\ q = q') /\
  (forall G D g a b, AnnDefEq G D g a b -> forall a' b', AnnDefEq G D g a' b' -> a = a' /\ b = b') /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof.
  apply fc_ann_ind; intros; try exact I.
  all: match goal with
  | J : AnnTyping _ _ ?B |- _ = ?B => inversion J; subst; clear J
  | J : AnnIso _ _ _ ?p ?q |- _ = ?p /\ _ = ?q => inversion J; subst; clear J
  | J : AnnDefEq _ _ _ ?a ?b |- _ = ?a /\ _ = ?b => inversion J; subst; clear J
  end.
  all: fc_use_unique; try solve [split; reflexivity | reflexivity].
  all: try solve [
    match goal with B1 : binds ?x ?a ?G, B2 : binds ?x ?b ?G, W : AnnCtx ?G |- _ =>
      let E := fresh in
      pose proof (binds_unique _ x a b G B1 B2 (fc_ctx_uniq G W)) as E;
      inversion E; auto
    end].
  all: try solve [
    repeat match goal with B : binds _ (Ax _ _) an_toplevel |- _ =>
      destruct (fc_family_binding _ _ _ B) as (? & ? & ?); clear B; subst end;
    reflexivity].
  all: let S := fc_all_names in destruct (atom_fresh S) as [x Fx].
  all: repeat match goal with
    | J : forall c : covar, c `notin` _ -> _ |- _ => specialize (J x ltac:(fsetdec))
    | J : forall c : atom, c `notin` _ -> _ |- _ => specialize (J x ltac:(fsetdec))
    end.
  all: fc_use_unique; fc_open_inject; subst; try solve [split; reflexivity | reflexivity].
  all: try match goal with
      | E1 : open_tm_wrt_tm ?a (a_Var_f ?x) = ?v,
        E2 : open_tm_wrt_tm ?b (a_Var_f ?x) = ?v |- _ =>
        let H := fresh in assert (H : open_tm_wrt_tm a (a_Var_f x) = open_tm_wrt_tm b (a_Var_f x)) by congruence
      | E1 : open_tm_wrt_co ?a (g_Var_f ?x) = ?v,
        E2 : open_tm_wrt_co ?b (g_Var_f ?x) = ?v |- _ =>
        let H := fresh in assert (H : open_tm_wrt_co a (g_Var_f x) = open_tm_wrt_co b (g_Var_f x)) by congruence
      end.
  all: fc_open_inject; subst; try (split; reflexivity).
Qed.

Definition fc_typ_unique := proj1 (proj2 fc_unique).
Definition fc_iso_unique := proj1 (proj2 (proj2 fc_unique)).
Definition fc_eq_unique := proj1 (proj2 (proj2 (proj2 fc_unique))).

(** Well-formed classifiers and implicit equality witnesses. *)

Lemma fc_typ_pi_domain : forall G r A B T, AnnTyping G (a_Pi r A B) T -> AnnTyping G A a_Star.
Proof. intros; inversion H; assumption. Qed.
Lemma fc_typ_cpi_domain : forall G phi B T, AnnTyping G (a_CPi phi B) T -> AnnPropWff G phi.
Proof. intros; inversion H; assumption. Qed.

Lemma fc_pi_range : forall G r A B T u, AnnCtx G ->
  AnnTyping G (a_Pi r A B) T -> AnnTyping G u A ->
  AnnTyping G (open_tm_wrt_tm B u) a_Star.
Proof.
  intros G r A B T u W K U. inversion K; subst.
  eapply (fc_tsubst_star L G G A B u); try assumption.
  - auto.
  - exact (fc_typ_degree G u A U).
Qed.

Lemma fc_cpi_range : forall G phi B T g, AnnCtx G ->
  AnnTyping G (a_CPi phi B) T ->
  (forall u v A, phi = Eq u v A -> AnnDefEq G (dom G) g u v) ->
  fc_degree_co 0 0 g ->
  AnnTyping G (open_tm_wrt_co B g) a_Star.
Proof.
  intros G phi B T g W K J DG. inversion K; subst.
  eapply (fc_csubst_star L G G phi B g); eauto.
Qed.

Lemma fc_ctx_lookup : forall G s x, AnnCtx G -> binds x s G ->
  match s with Tm A => AnnTyping G A a_Star | Co p => AnnPropWff G p end.
Proof.
  intros G s x W; induction W; intro B; [contradiction| |].
  - destruct B as [B|B].
    + inversion B; subst. eapply fc_weak_typ; [eassumption| |].
      * auto using binds_app_r.
      * eapply An_ConsTm; eassumption.
    + specialize (IHW B). destruct s.
      * eapply fc_weak_typ; [exact IHW | auto using binds_app_r | eapply An_ConsTm; eassumption].
      * eapply fc_weak_wff; [exact IHW | auto using binds_app_r | eapply An_ConsTm; eassumption].
  - destruct B as [B|B].
    + inversion B; subst. eapply fc_weak_wff; [eassumption| |].
      * auto using binds_app_r.
      * eapply An_ConsCo; eassumption.
    + specialize (IHW B). destruct s.
      * eapply fc_weak_typ; [exact IHW | auto using binds_app_r | eapply An_ConsCo; eassumption].
      * eapply fc_weak_wff; [exact IHW | auto using binds_app_r | eapply An_ConsCo; eassumption].
Qed.

Lemma fc_type_valid : forall G a A, AnnTyping G a A -> AnnCtx G -> AnnTyping G A a_Star.
Proof.
  apply (fc_ind_typ (fun G p _ => True)
                    (fun G a A _ => AnnCtx G -> AnnTyping G A a_Star)
                    (fun G D g p q _ => True)
                    (fun G D g a b _ => True)
                    (fun G _ => True)
                    (fun S _ => True)); intros; try exact I.
  all: try solve [apply An_Star; assumption].
  all: try solve [assumption].
  - exact (fc_ctx_lookup _ _ _ a b).
  - eapply (An_Pi (L \u dom G)); [|eassumption].
    intros x Fx. apply H0; [fsetdec|].
    apply An_ConsTm; [assumption|assumption|fsetdec].
  - eapply fc_pi_range; [assumption|apply H; assumption|assumption].
  - eapply (An_CPi (L \u dom G)); [eassumption|].
    intros x Fx. apply H0; [fsetdec|].
    apply An_ConsCo; [assumption|assumption|fsetdec].
  - eapply fc_cpi_range; [assumption|apply H; assumption| |].
    + intros u v U E; inversion E; subst; assumption.
    + eapply fc_co_degree; eassumption.
  - destruct (fc_family_binding _ _ _ b) as (? & ? & ->).
    eapply fc_weak_typ; [exact a1 | contradiction | assumption].
Qed.

Lemma fc_full_eq : forall G D g a b, AnnDefEq G D g a b -> AnnDefEq G (dom G) g a b.
Proof.
  intros G D g a b J.
  eapply (proj1 (proj2 (proj2 (proj2 fc_extra_term_atom)))); [exact J|].
  intros; eapply fc_binds_in_dom; eassumption.
Qed.

Lemma fc_full_iso : forall G D g a b, AnnIso G D g a b -> AnnIso G (dom G) g a b.
Proof.
  intros G D g a b J.
  eapply (proj1 (proj2 (proj2 fc_extra_term_atom))); [exact J|].
  intros; eapply fc_binds_in_dom; eassumption.
Qed.

Lemma fc_star_refl : forall G D, AnnCtx G -> AnnDefEq G D (g_Refl a_Star) a_Star a_Star.
Proof. intros; apply (An_Refl _ _ _ a_Star), An_Star; assumption. Qed.

Lemma fc_kind_sym : forall G D g A B, AnnCtx G ->
  AnnDefEq G D g A B -> AnnTyping G A a_Star -> AnnTyping G B a_Star ->
  AnnDefEq G D (g_Sym g) B A.
Proof. intros; eapply An_Sym; eauto using fc_star_refl. Qed.

Lemma fc_kind_trans : forall G D g h A B C, AnnCtx G ->
  AnnDefEq G D g A B -> AnnDefEq G D h B C ->
  AnnTyping G A a_Star -> AnnTyping G B a_Star ->
  AnnDefEq G D (g_Trans g h) A C.
Proof. intros; eapply An_Trans; eauto using fc_star_refl. Qed.

Lemma fc_kind_erasure : forall G D A B, AnnCtx G ->
  AnnTyping G A a_Star -> AnnTyping G B a_Star -> erase_tm A = erase_tm B ->
  AnnDefEq G D (g_Refl2 A B (g_Refl a_Star)) A B.
Proof. intros; eapply An_EraseEq; eauto using fc_star_refl. Qed.

Lemma fc_var_cast : forall G D g A B x, AnnCtx G -> x \notin dom G ->
  AnnTyping G A a_Star -> AnnTyping G B a_Star -> AnnDefEq G D g A B ->
  AnnTyping ((x,Tm B)::G) (a_Conv (a_Var_f x) (g_Sym g)) A.
Proof.
  intros G D g A B x W Fx KA KB J.
  assert (W' : AnnCtx ((x,Tm B)::G)) by (apply An_ConsTm; assumption).
  assert (Bi : forall y s, binds y s G -> binds y s ((x,Tm B)::G)).
  { intros y s H; simpl; auto. }
  eapply (An_Conv _ _ _ _ B).
  - eapply An_Var; [exact W'|simpl; auto].
  - eapply fc_weak_eq.
    + exact (fc_full_eq G D _ _ _ (fc_kind_sym G D g A B W J KA KB)).
    + exact Bi.
    + exact W'.
    + intros z Hz; rewrite dom_cons; fsetdec.
  - eapply fc_weak_typ; eassumption.
Qed.

Lemma fc_assn_cast : forall G D g phi psi x, AnnCtx G -> x \notin dom G ->
  AnnPropWff G psi -> AnnIso G D g phi psi ->
  forall u v A, phi = Eq u v A ->
  AnnDefEq ((x,Co psi)::G) (dom ((x,Co psi)::G)) (g_Cast (g_Var_f x) (g_Sym g)) u v.
Proof.
  intros G D g phi [b b' B] x W Fx KB J u v A ->.
  assert (W' : AnnCtx ((x,Co (Eq b b' B))::G)).
  { apply An_ConsCo; assumption. }
  eapply (An_Cast _ _ _ _ _ _ b b' B A).
  - eapply (An_Assn _ _ _ _ _ B); [exact W'|simpl; auto|].
    rewrite dom_cons; fsetdec.
  - apply An_IsoSym.
    eapply fc_weak_iso.
    + exact (fc_full_iso G D g (Eq u v A) (Eq b b' B) J).
    + intros; right; assumption.
    + exact W'.
    + intros z Hz; rewrite dom_cons; fsetdec.
Qed.

Definition fc_equal_classifiers G a b :=
  exists A B h, AnnTyping G a A /\ AnnTyping G b B /\ AnnDefEq G (dom G) h A B.

Lemma fc_wff_classifiers : forall G a b A, AnnCtx G -> AnnPropWff G (Eq a b A) ->
  fc_equal_classifiers G a b.
Proof.
  intros G a b A W J. inversion J; subst.
  exists A, B, (g_Refl2 A B (g_Refl a_Star)).
  repeat split; try assumption.
  apply fc_kind_erasure; eauto using fc_type_valid.
Qed.

Lemma fc_eq_star_classifiers : forall G a b, AnnCtx G ->
  AnnTyping G a a_Star -> AnnTyping G b a_Star -> fc_equal_classifiers G a b.
Proof.
  intros. exists a_Star, a_Star, (g_Refl a_Star); auto using fc_star_refl.
Qed.

Lemma fc_eq_abs_classifiers : forall L G D r g k A1 A2 b1 b2 b3,
  AnnCtx G -> AnnDefEq G D g A1 A2 ->
  AnnTyping G A1 a_Star -> AnnTyping G A2 a_Star ->
  (forall x, x \notin L -> AnnDefEq ((x,Tm A1)::G) D
      (open_co_wrt_tm k (a_Var_f x))
      (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))) ->
  (forall x, x \notin L -> AnnCtx ((x,Tm A1)::G) -> fc_equal_classifiers ((x,Tm A1)::G)
      (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))) ->
  (forall x, x \notin L -> open_tm_wrt_tm b3 (a_Var_f x) =
     open_tm_wrt_tm b2 (a_Conv (a_Var_f x) (g_Sym g))) ->
  (forall x, x \notin L -> RhoCheck r x (erase_tm (open_tm_wrt_tm b1 (a_Var_f x)))) ->
  (forall x, x \notin L -> RhoCheck r x (erase_tm (open_tm_wrt_tm b3 (a_Var_f x)))) ->
  fc_equal_classifiers G (a_Abs r A1 b1) (a_Abs r A2 b3).
Proof.
  intros L G D r g k A1 A2 b1 b2 b3 W E K1 K2 J I Cast R1 R3.
  destruct (atom_fresh (L \u fc_fv_ctx G \u fc_fv_tm A1 \u fc_fv_tm b1 \u fc_fv_tm b2 \u dom G))
    as [x Fx].
  assert (X : AnnCtx ((x,Tm A1)::G)) by (apply An_ConsTm; [assumption|assumption|fsetdec]).
  destruct (I x ltac:(fsetdec) X) as (B1 & B2 & h & T1 & T2 & H).
  pose (C1 := fc_close_tm_tm 0 x B1).
  pose (C2 := fc_close_tm_tm 0 x B2).
  pose (C3 := fc_tmcast_tm 0 g C2).
  assert (DG : fc_degree_co 0 0 g) by (eapply fc_co_degree; exact E).
  assert (B1open : forall y, y \notin dom G -> AnnTyping ((y,Tm A1)::G)
      (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm C1 (a_Var_f y))).
  { intros y Fy. pose proof (fc_tabstract_typ G A1 x _ B1 W K1 ltac:(fsetdec) ltac:(fsetdec) T1 y Fy) as Q.
    now rewrite fc_close_t_open_t in Q by fsetdec. }
  assert (B2open : forall y, y \notin dom G -> AnnTyping ((y,Tm A1)::G)
      (open_tm_wrt_tm b2 (a_Var_f y)) (open_tm_wrt_tm C2 (a_Var_f y))).
  { intros y Fy. pose proof (fc_tabstract_typ G A1 x _ B2 W K1 ltac:(fsetdec) ltac:(fsetdec) T2 y Fy) as Q.
    now rewrite fc_close_t_open_t in Q by fsetdec. }
  assert (B3open : forall y, y \notin L \u dom G -> AnnTyping ((y,Tm A2)::G)
      (open_tm_wrt_tm b3 (a_Var_f y)) (open_tm_wrt_tm C3 (a_Var_f y))).
  { intros y Fy.
    rewrite Cast by fsetdec.
    unfold C3, open_tm_wrt_tm at 2. rewrite fc_tmcast_open_tm by assumption.
    apply (fc_tsubst_typ (dom G) G ((y,Tm A2)::G) A1).
    - apply An_ConsTm; [assumption|assumption|fsetdec].
    - intros; right; assumption.
    - apply (fc_var_cast G D); try assumption; fsetdec.
    - simpl; tauto.
    - exact B2open. }
  assert (U1 : AnnTyping G (a_Abs r A1 b1) (a_Pi r A1 C1)).
  { apply (An_Abs (L \u dom G)); [assumption|intros; apply B1open; fsetdec|intros; apply R1; fsetdec]. }
  assert (U3 : AnnTyping G (a_Abs r A2 b3) (a_Pi r A2 C3)).
  { apply (An_Abs (L \u dom G)); [assumption|exact B3open|intros; apply R3; fsetdec]. }
  exists (a_Pi r A1 C1), (a_Pi r A2 C3), (g_PiCong r g (fc_close_tm_co 0 x h)).
  repeat split; try assumption.
  eapply (An_PiCong (dom G) _ _ _ _ _ _ _ _ _ C2).
  - apply (fc_full_eq G D); exact E.
  - apply fc_tabstract_eq; try assumption; try fsetdec.
    apply fc_eq_all_term; exact H.
  - intros; apply fc_tmcast_open_tm; assumption.
  - eapply fc_type_valid; eassumption.
  - apply (An_Pi (dom G)); [|exact K1].
    intros y Fy. eapply fc_type_valid; [apply B2open; exact Fy|].
    apply An_ConsTm; assumption.
  - eapply fc_type_valid; eassumption.
Qed.

Lemma fc_reg_app : forall G D r g a1 a2 b1 b2 A B,
  AnnCtx G -> AnnDefEq G D g a2 b2 ->
  fc_equal_classifiers G a1 b1 ->
  AnnTyping G (a_App a1 r a2) A -> AnnTyping G (a_App b1 r b2) B ->
  exists k, AnnDefEq G (dom G) k A B.
Proof.
  intros G D r g a1 a2 b1 b2 A B W E (A1 & A2 & h & T1 & T2 & H) U1 U2.
  inversion U1; subst.
  inversion U2; subst.
  repeat match goal with
  | T : AnnTyping ?G ?a ?A0, U : AnnTyping ?G ?a (a_Pi _ _ _) |- _ =>
    is_var A0; let EQ := fresh in
    pose proof (fc_typ_unique G a A0 T _ U) as EQ; subst A0
  end.
  exists (g_PiSnd h g). eapply An_PiSnd; eauto using fc_full_eq.
Qed.

Lemma fc_reg_capp : forall G g1 g2 a b a1 a2 b1 b2 A B,
  AnnDefEq G (dom G) g1 a1 a2 -> AnnDefEq G (dom G) g2 b1 b2 ->
  fc_equal_classifiers G a b ->
  AnnTyping G (a_CApp a g1) A -> AnnTyping G (a_CApp b g2) B ->
  exists k, AnnDefEq G (dom G) k A B.
Proof.
  intros G g1 g2 a b a1 a2 b1 b2 A B E1 E2 (A1 & A2 & h & T1 & T2 & H) U1 U2.
  inversion U1; subst.
  inversion U2; subst.
  repeat match goal with
  | T : AnnTyping ?G ?a ?A0, U : AnnTyping ?G ?a (a_CPi _ _) |- _ =>
    is_var A0; let EQ := fresh in
    pose proof (fc_typ_unique G a A0 T _ U) as EQ; subst A0
  end.
  exists (g_CPiSnd h g1 g2). eapply An_CPiSnd; eassumption.
Qed.

Lemma fc_coercion_regular :
  (forall G p, AnnPropWff G p -> True) /\
  (forall G a A, AnnTyping G a A -> True) /\
  (forall G D g p q, AnnIso G D g p q -> AnnCtx G -> AnnPropWff G p /\ AnnPropWff G q) /\
  (forall G D g a b, AnnDefEq G D g a b -> AnnCtx G -> fc_equal_classifiers G a b) /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof.
  apply fc_ann_ind; intros; try exact I.
  all: repeat match goal with J : AnnCtx ?G -> _, W : AnnCtx ?G |- _ => specialize (J W) end.
  all: try solve [split; assumption].
  all: try solve [apply fc_eq_star_classifiers; assumption].
  all: try solve [
    match goal with
    | J : fc_equal_classifiers ?G (a_CPi ?p _) (a_CPi ?q _) |- _ =>
      destruct J as (A & B & h & T1 & T2 & H);
      split; eapply fc_typ_cpi_domain; eassumption
    end].
  all: try solve [
    match goal with
    | J : fc_equal_classifiers ?G (a_Pi _ _ _) (a_Pi _ _ _) |- _ =>
      destruct J as (A & B & h & T1 & T2 & H);
      apply fc_eq_star_classifiers; [assumption|eapply fc_typ_pi_domain; eassumption|eapply fc_typ_pi_domain; eassumption]
    end].
  all: try solve [apply fc_wff_classifiers; [assumption|eapply fc_ctx_lookup; eassumption]].
  all: try solve [
    match goal with
    | J : AnnTyping ?G ?a ?A |- fc_equal_classifiers ?G ?a ?a =>
      exists A, A, (g_Refl A);
      repeat split; try exact J; eapply An_Refl; eapply fc_type_valid; eassumption
    end].
  all: try solve [unfold fc_equal_classifiers; eauto 9].
  - tauto.
  - apply (fc_wff_classifiers G a b A); [assumption|exact (fc_ctx_lookup G (Co (Eq a b A)) c a0 b0)].
  - exists A, B, (g_Sym g1). repeat split; try assumption.
    eapply fc_kind_sym; eauto using fc_type_valid.
  - match goal with
    | J : fc_equal_classifiers G a1 b |- _ =>
      destruct J as (C & B & k & TM & TB & EK);
      assert (A1 = C) by (eapply fc_typ_unique; eassumption); subst C;
      exists A, B, (g_Trans g3 k); repeat split; try assumption;
      eapply fc_kind_trans; eauto using fc_type_valid
    end.
  - exists B0, B1, (g_Refl2 B0 B1 (g_Refl a_Star)).
    repeat split; try assumption. eapply fc_kind_erasure; eauto using fc_type_valid.
  - eapply (fc_eq_abs_classifiers L); eassumption.
  - match goal with
    | J : fc_equal_classifiers G (a_Pi _ _ _) (a_Pi _ _ _) |- _ =>
      destruct J as (T1 & T2 & h & U1 & U2 & H)
    end.
    apply fc_eq_star_classifiers; [assumption | eapply fc_pi_range; eassumption | eapply fc_pi_range; eassumption].
  - match goal with
    | J : fc_equal_classifiers G (a_CPi _ _) (a_CPi _ _) |- _ =>
      destruct J as (T1 & T2 & h & U1 & U2 & H)
    end.
    apply fc_eq_star_classifiers; [assumption | |].
    + eapply fc_cpi_range; [eassumption|exact U1| |eapply fc_co_degree; eassumption].
      intros; match goal with E : Eq _ _ _ = Eq _ _ _ |- _ => inversion E; subst; assumption end.
    + eapply fc_cpi_range; [eassumption|exact U2| |eapply fc_co_degree; eassumption].
      intros; match goal with E : Eq _ _ _ = Eq _ _ _ |- _ => inversion E; subst; assumption end.
  - apply (fc_wff_classifiers G b b' B); tauto.
  - fc_unpack. apply fc_eq_star_classifiers; [assumption| |].
    + match goal with J : AnnPropWff G (Eq _ _ A) |- _ => inversion J; subst; eapply fc_type_valid; eassumption end.
    + match goal with J : AnnPropWff G (Eq _ _ B) |- _ => inversion J; subst; eapply fc_type_valid; eassumption end.
Qed.

Definition fc_defeq_reg := proj1 (proj2 (proj2 (proj2 fc_coercion_regular))).
Definition fc_iso_reg := proj1 (proj2 (proj2 fc_coercion_regular)).

(** Classifier reconstruction for terms already known to type-check. *)

Fixpoint fc_lookup (G : context) (x : atom) : option sort :=
  match G with
  | nil => None
  | (y,s)::G => if x == y then Some s else fc_lookup G x
  end.

Lemma fc_lookup_binds : forall G x s, fc_lookup G x = Some s -> binds x s G.
Proof.
  induction G as [|[y v] G IH]; simpl; intros x s E; [discriminate|].
  destruct (x == y) as [->|N]; [inversion E; subst; left; reflexivity|right; eapply IH; exact E].
Qed.

Lemma fc_lookup_complete : forall G x s, uniq G -> binds x s G -> fc_lookup G x = Some s.
Proof.
  intros G x s U; induction U; intros B; [contradiction|].
  simpl. destruct B as [B|B].
  - inversion B; subst; destruct (_ == _); congruence.
  - destruct (x == x0) as [->|N]; auto.
    exfalso; match goal with H : x0 `notin` dom _ |- _ => apply H end.
    eapply fc_binds_in_dom; exact B.
Qed.

Definition fc_pick (G : context) (S : atoms) := proj1_sig (atom_fresh (fc_fv_ctx G \u S)).
Lemma fc_pick_spec : forall G S, fc_pick G S \notin fc_fv_ctx G \u S.
Proof. intros; exact (proj2_sig (atom_fresh (fc_fv_ctx G \u S))). Qed.
Lemma fc_pick_dom : forall G S, fc_pick G S \notin dom G.
Proof. intros G S I; pose proof (fc_pick_spec G S); apply fc_Gfv_dom in I; fsetdec. Qed.

Local Notation "'let?' x := p 'in' q" :=
  (match p with Some x => q | None => None end)
  (at level 200, x pattern, p at level 100, q at level 200).

Fixpoint fc_guess_eq (n : nat) (G : context) (g : co) : option (tm * tm) :=
  match n with
  | 0 => None
  | S n =>
    match g with
    | g_Var_f c =>
        match fc_lookup G c with Some (Co (Eq a b _)) => Some (a,b) | _ => None end
    | g_Refl a => Some (a,a)
    | g_Refl2 a b _ | g_Beta a b => Some (a,b)
    | g_Sym g => let? (a,b) := fc_guess_eq n G g in Some (b,a)
    | g_Trans g h =>
        let? (a,_) := fc_guess_eq n G g in
        let? (_,b) := fc_guess_eq n G h in Some (a,b)
    | g_PiCong r g h =>
        let? (A1,A2) := fc_guess_eq n G g in
        let x := fc_pick G (fc_fv_co g \u fc_fv_co h) in
        let? (b1,b2) := fc_guess_eq n ((x,Tm A1)::G) (open_co_wrt_tm h (a_Var_f x)) in
        let a := fc_close_tm_tm 0 x b1 in
        let b := fc_tmcast_tm 0 g (fc_close_tm_tm 0 x b2) in
        Some (a_Pi r A1 a, a_Pi r A2 b)
    | g_AbsCong r g h =>
        let? (A1,A2) := fc_guess_eq n G g in
        let x := fc_pick G (fc_fv_co g \u fc_fv_co h) in
        let? (b1,b2) := fc_guess_eq n ((x,Tm A1)::G) (open_co_wrt_tm h (a_Var_f x)) in
        let a := fc_close_tm_tm 0 x b1 in
        let b := fc_tmcast_tm 0 g (fc_close_tm_tm 0 x b2) in
        Some (a_Abs r A1 a, a_Abs r A2 b)
    | g_AppCong g r h =>
        let? (a,b) := fc_guess_eq n G g in
        let? (u,v) := fc_guess_eq n G h in Some (a_App a r u, a_App b r v)
    | g_PiFst g =>
        match fc_guess_eq n G g with
        | Some (a_Pi _ A _, a_Pi _ B _) => Some (A,B)
        | _ => None
        end
    | g_IsoSnd g =>
        let? (Eq _ _ A, Eq _ _ B) := fc_guess_iso n G g in Some (A,B)
    | g_PiSnd g h =>
        match fc_guess_eq n G g with
        | Some (a_Pi _ _ A, a_Pi _ _ B) =>
            let? (a,b) := fc_guess_eq n G h in
            Some (open_tm_wrt_tm A a, open_tm_wrt_tm B b)
        | _ => None
        end
    | g_CPiCong g h =>
        let? (phi,psi) := fc_guess_iso n G g in
        let x := fc_pick G (fc_fv_co g \u fc_fv_co h) in
        let? (b1,b2) := fc_guess_eq n ((x,Co phi)::G) (open_co_wrt_co h (g_Var_f x)) in
        Some (a_CPi phi (fc_close_co_tm 0 x b1), a_CPi psi (fc_cocast_tm 0 g (fc_close_co_tm 0 x b2)))
    | g_CAbsCong g h _ =>
        let? (phi,psi) := fc_guess_iso n G g in
        let x := fc_pick G (fc_fv_co g \u fc_fv_co h) in
        let? (b1,b2) := fc_guess_eq n ((x,Co phi)::G) (open_co_wrt_co h (g_Var_f x)) in
        Some (a_CAbs phi (fc_close_co_tm 0 x b1), a_CAbs psi (fc_cocast_tm 0 g (fc_close_co_tm 0 x b2)))
    | g_CAppCong g h k =>
        let? (a,b) := fc_guess_eq n G g in Some (a_CApp a h, a_CApp b k)
    | g_CPiSnd g h k =>
        match fc_guess_eq n G g with
        | Some (a_CPi _ A, a_CPi _ B) => Some (open_tm_wrt_co A h, open_tm_wrt_co B k)
        | _ => None
        end
    | g_Cast _ h =>
        let? (_, Eq b b' _) := fc_guess_iso n G h in Some (b,b')
    | _ => None
    end
  end
with fc_guess_iso (n : nat) (G : context) (g : co) : option (constraint * constraint) :=
  match n with
  | 0 => None
  | S n =>
    match g with
    | g_EqCong g A h =>
        let? (a,b) := fc_guess_eq n G g in
        let? (u,v) := fc_guess_eq n G h in Some (Eq a u A, Eq b v A)
    | g_CPiFst g =>
        match fc_guess_eq n G g with
        | Some (a_CPi phi _, a_CPi psi _) => Some (phi,psi)
        | _ => None
        end
    | g_Sym g => let? (phi,psi) := fc_guess_iso n G g in Some (psi,phi)
    | g_IsoConv phi psi _ => Some (phi,psi)
    | _ => None
    end
  end.

Fixpoint fc_guess_tm (n : nat) (G : context) (a : tm) : option tm :=
  match n with
  | 0 => None
  | S n =>
    match a with
    | a_Star | a_Pi _ _ _ | a_CPi _ _ => Some a_Star
    | a_Var_f x => match fc_lookup G x with Some (Tm A) => Some A | _ => None end
    | a_Abs r A b =>
        let x := fc_pick G (fc_fv_tm A \u fc_fv_tm b) in
        let? B := fc_guess_tm n ((x,Tm A)::G) (open_tm_wrt_tm b (a_Var_f x)) in
        Some (a_Pi r A (fc_close_tm_tm 0 x B))
    | a_App a _ b =>
        match fc_guess_tm n G a with
        | Some (a_Pi _ _ B) => Some (open_tm_wrt_tm B b)
        | _ => None
        end
    | a_Fam _ => Some FixTy
    | a_Conv _ g =>
        let? (_, B) := fc_guess_eq n G g in Some B
    | a_CAbs phi b =>
        let x := fc_pick G (fc_fv_constraint phi \u fc_fv_tm b) in
        let? B := fc_guess_tm n ((x,Co phi)::G) (open_tm_wrt_co b (g_Var_f x)) in
        Some (a_CPi phi (fc_close_co_tm 0 x B))
    | a_CApp a g =>
        match fc_guess_tm n G a with
        | Some (a_CPi _ B) => Some (open_tm_wrt_co B g)
        | _ => None
        end
    | _ => None
    end
  end.

Lemma fc_tcast_cofinite : forall L b3 b2 g, fc_degree_co 0 0 g ->
  (forall x, x \notin L -> open_tm_wrt_tm b3 (a_Var_f x) =
       open_tm_wrt_tm b2 (a_Conv (a_Var_f x) (g_Sym g))) ->
  fc_tmcast_tm 0 g b2 = b3.
Proof.
  intros L b3 b2 g D J.
  destruct (atom_fresh (L \u fc_fv_tm b3 \u fc_fv_tm (fc_tmcast_tm 0 g b2))) as [x Fx].
  specialize (J x ltac:(fsetdec)).
  unfold open_tm_wrt_tm in J.
  rewrite <- (fc_tmcast_open_tm b2 0 g x D) in J.
  apply (f_equal (fc_close_tm_tm 0 x)) in J.
  change (fc_close_tm_tm 0 x (open_tm_wrt_tm b3 (a_Var_f x)) =
          fc_close_tm_tm 0 x (open_tm_wrt_tm (fc_tmcast_tm 0 g b2) (a_Var_f x))) in J.
  rewrite !fc_close_t_open_t in J by fsetdec; symmetry; assumption.
Qed.

Lemma fc_ccast_cofinite : forall L b3 b2 g, fc_degree_co 0 0 g ->
  (forall x, x \notin L -> open_tm_wrt_co b3 (g_Var_f x) =
       open_tm_wrt_co b2 (g_Cast (g_Var_f x) (g_Sym g))) ->
  fc_cocast_tm 0 g b2 = b3.
Proof.
  intros L b3 b2 g D J.
  destruct (atom_fresh (L \u fc_fv_tm b3 \u fc_fv_tm (fc_cocast_tm 0 g b2))) as [x Fx].
  specialize (J x ltac:(fsetdec)).
  unfold open_tm_wrt_co in J.
  rewrite <- (fc_cocast_open_tm b2 0 g x D) in J.
  apply (f_equal (fc_close_co_tm 0 x)) in J.
  change (fc_close_co_tm 0 x (open_tm_wrt_co b3 (g_Var_f x)) =
          fc_close_co_tm 0 x (open_tm_wrt_co (fc_cocast_tm 0 g b2) (g_Var_f x))) in J.
  rewrite !fc_close_c_open_c in J by fsetdec; symmetry; assumption.
Qed.

Lemma fc_eq_binder_free_t : forall G A g D a b x,
  x \notin fc_fv_ctx G -> x \notin fc_fv_tm A -> x \notin fc_fv_co g ->
  (exists L, forall y, y \notin L ->
    AnnDefEq ((y,Tm A)::G) D (open_co_wrt_tm g (a_Var_f y))
      (open_tm_wrt_tm a (a_Var_f y)) (open_tm_wrt_tm b (a_Var_f y))) ->
  x \notin fc_fv_tm a /\ x \notin fc_fv_tm b.
Proof.
  intros G A g D a b x FG FA Fg [L J].
  destruct (atom_fresh (L \u singleton x)) as [y Fy].
  pose proof (fc_eq_free _ _ _ _ _ (J y ltac:(fsetdec)) x
                ltac:(cbn [fc_fv_ctx fc_fv_sort]; fsetdec) ltac:(fc_open_fv_away)) as K.
  fc_unpack; fc_forget_open_fv; auto.
Qed.

Lemma fc_eq_binder_free_c : forall G phi g D a b x,
  x \notin fc_fv_ctx G -> x \notin fc_fv_constraint phi -> x \notin fc_fv_co g ->
  (exists L, forall y, y \notin L ->
    AnnDefEq ((y,Co phi)::G) D (open_co_wrt_co g (g_Var_f y))
      (open_tm_wrt_co a (g_Var_f y)) (open_tm_wrt_co b (g_Var_f y))) ->
  x \notin fc_fv_tm a /\ x \notin fc_fv_tm b.
Proof.
  intros G phi g D a b x FG FA Fg [L J].
  destruct (atom_fresh (L \u singleton x)) as [y Fy].
  pose proof (fc_eq_free _ _ _ _ _ (J y ltac:(fsetdec)) x
                ltac:(cbn [fc_fv_ctx fc_fv_sort]; fsetdec) ltac:(fc_open_fv_away)) as K.
  fc_unpack; fc_forget_open_fv; auto.
Qed.

Ltac fc_size_bound :=
  rewrite ?fc_sz_topen_tm, ?fc_sz_copen_tm, ?fc_sz_topen_co, ?fc_sz_copen_co;
  unfold open_tm_wrt_tm, open_tm_wrt_co, open_co_wrt_tm, open_co_wrt_co;
  rewrite ?fc_sz_topen_tm, ?fc_sz_copen_tm, ?fc_sz_topen_co, ?fc_sz_copen_co;
  cbn [fc_size_tm fc_size_co fc_size_constraint] in *; lia.

Ltac fc_guess_rewrite :=
  repeat match goal with
  | H : forall G a A, AnnCtx G -> fc_size_tm a < ?n -> AnnTyping G a A -> _,
    J : AnnTyping ?G ?a ?A |- context [fc_guess_tm ?n ?G ?a] =>
      rewrite (H G a A ltac:(assumption) ltac:(fc_size_bound) J)
  | H : forall G D g a b, AnnCtx G -> fc_size_co g < ?n -> AnnDefEq G D g a b -> _,
    J : AnnDefEq ?G ?D ?g ?a ?b |- context [fc_guess_eq ?n ?G ?g] =>
      rewrite (H G D g a b ltac:(assumption) ltac:(fc_size_bound) J)
  | H : forall G D g a b, AnnCtx G -> fc_size_co g < ?n -> AnnIso G D g a b -> _,
    J : AnnIso ?G ?D ?g ?a ?b |- context [fc_guess_iso ?n ?G ?g] =>
      rewrite (H G D g a b ltac:(assumption) ltac:(fc_size_bound) J)
  end; cbn beta iota zeta.

Lemma fc_guess_complete : forall n,
  (forall G a A, AnnCtx G -> fc_size_tm a < n -> AnnTyping G a A -> fc_guess_tm n G a = Some A) /\
  (forall G D g a b, AnnCtx G -> fc_size_co g < n -> AnnDefEq G D g a b -> fc_guess_eq n G g = Some (a,b)) /\
  (forall G D g a b, AnnCtx G -> fc_size_co g < n -> AnnIso G D g a b -> fc_guess_iso n G g = Some (a,b)).
Proof.
  induction n as [|n IH].
  - repeat split; intros; lia.
  - destruct IH as [IT [IE II]].
    repeat split; intros G; intros; inversion H1; subst;
      cbn [fc_guess_tm fc_guess_eq fc_guess_iso]; try reflexivity.
    all: fc_guess_rewrite; try reflexivity.
    all: try solve [
      match goal with B : binds _ _ _ |- _ =>
        rewrite (fc_lookup_complete _ _ _ (fc_ctx_uniq G H) B); reflexivity
      end].
    all: try solve [
      match goal with B : binds _ (Ax _ _) an_toplevel |- _ =>
        destruct (fc_family_binding _ _ _ B) as (? & ? & ?); subst; reflexivity
      end].
    all: match goal with |- context [fc_pick ?G ?S] =>
      let F := fresh "Fpick" in pose proof (fc_pick_spec G S) as F;
      let D := fresh "Dpick" in pose proof (fc_pick_dom G S) as D;
      set (x := fc_pick G S) in *
    end.
    + assert (Q : AnnTyping ((x,Tm A0)::G)
          (open_tm_wrt_tm a0 (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))).
      { apply (fc_fresh_t_typ L); assumption. }
      assert (W : AnnCtx ((x,Tm A0)::G)) by (apply An_ConsTm; assumption).
      fc_guess_rewrite.
      rewrite fc_close_t_open_t; [reflexivity|].
      pose proof (fc_typ_free _ _ _ H1 x ltac:(fsetdec) ltac:(simpl; fsetdec)); simpl in *; fsetdec.
    + assert (Q : AnnTyping ((x,Co phi)::G)
          (open_tm_wrt_co a0 (g_Var_f x)) (open_tm_wrt_co B (g_Var_f x))).
      { apply (fc_fresh_c_typ L); assumption. }
      assert (W : AnnCtx ((x,Co phi)::G)) by (apply An_ConsCo; assumption).
      fc_guess_rewrite.
      rewrite fc_close_c_open_c; [reflexivity|].
      pose proof (fc_typ_free _ _ _ H1 x ltac:(fsetdec) ltac:(simpl; fsetdec)); simpl in *; fsetdec.
    + assert (KA : AnnTyping G A1 a_Star) by (eapply fc_typ_pi_domain; exact H5).
      assert (W : AnnCtx ((x,Tm A1)::G)) by (apply An_ConsTm; assumption).
      pose proof (fc_fresh_t_eq L G D A1 g2 B1 B2 x H KA Dpick H3) as Q.
      destruct (fc_eq_free _ _ _ _ _ H2 x ltac:(fsetdec) ltac:(fsetdec)) as [F1 F2].
      destruct (fc_eq_binder_free_t G A1 g2 D B1 B2 x ltac:(fsetdec) F1 ltac:(fsetdec) (ex_intro _ L H3)).
      fc_guess_rewrite; rewrite !fc_close_t_open_t by assumption.
      rewrite (fc_tcast_cofinite L B3 B2 g1 (fc_co_degree _ _ _ _ _ H2) H4); reflexivity.
    + assert (KA : AnnTyping G A1 a_Star) by assumption.
      assert (W : AnnCtx ((x,Tm A1)::G)) by (apply An_ConsTm; assumption).
      pose proof (fc_fresh_t_eq L G D A1 g2 b1 b2 x H KA Dpick H3) as Q.
      destruct (fc_eq_free _ _ _ _ _ H2 x ltac:(fsetdec) ltac:(fsetdec)) as [F1 F2].
      destruct (fc_eq_binder_free_t G A1 g2 D b1 b2 x ltac:(fsetdec) F1 ltac:(fsetdec) (ex_intro _ L H3)).
      fc_guess_rewrite; rewrite !fc_close_t_open_t by assumption.
      rewrite (fc_tcast_cofinite L b3 b2 g1 (fc_co_degree _ _ _ _ _ H2) H4); reflexivity.
    + assert (KA : AnnPropWff G phi1) by (eapply fc_typ_cpi_domain; exact H5).
      assert (W : AnnCtx ((x,Co phi1)::G)) by (apply An_ConsCo; assumption).
      pose proof (fc_fresh_c_eq L G D phi1 g3 B1 B2 x H KA Dpick H3) as Q.
      destruct (fc_iso_free _ _ _ _ _ H2 x ltac:(fsetdec) ltac:(fsetdec)) as [F1 F2].
      destruct (fc_eq_binder_free_c G phi1 g3 D B1 B2 x ltac:(fsetdec) F1 ltac:(fsetdec) (ex_intro _ L H3)).
      fc_guess_rewrite; rewrite !fc_close_c_open_c by assumption.
      rewrite (fc_ccast_cofinite L B3 B2 g1 (fc_iso_degree _ _ _ _ _ H2) H4); reflexivity.
    + assert (KA : AnnPropWff G phi1).
      { match goal with J : AnnTyping ?G (a_CAbs ?phi1 _) _ |- _ => inversion J; assumption end. }
      assert (W : AnnCtx ((x,Co phi1)::G)) by (apply An_ConsCo; assumption).
      pose proof (fc_fresh_c_eq L G D phi1 g3 a1 a2 x H KA Dpick H3) as Q.
      destruct (fc_iso_free _ _ _ _ _ H2 x ltac:(fsetdec) ltac:(fsetdec)) as [F1 F2].
      destruct (fc_eq_binder_free_c G phi1 g3 D a1 a2 x ltac:(fsetdec) F1 ltac:(fsetdec) (ex_intro _ L H3)).
      fc_guess_rewrite; rewrite !fc_close_c_open_c by assumption.
      rewrite (fc_ccast_cofinite L a3 a2 g1 (fc_iso_degree _ _ _ _ _ H2) H4); reflexivity.
Qed.

(** Deciding the side conditions for the annotated rules. *)

Fixpoint fc_scopedb_tm (p q : nat) (e : tm) : bool :=
  match e with
  | a_Star => true
  | a_Var_b i => Nat.ltb i p
  | a_Var_f x0 => true
  | a_Abs rho A b => fc_scopedb_tm p q A && fc_scopedb_tm (S p) q b
  | a_UAbs rho b => fc_scopedb_tm (S p) q b
  | a_App a rho b => fc_scopedb_tm p q a && fc_scopedb_tm p q b
  | a_Fam F => true
  | a_Const T => true
  | a_Pi rho A B => fc_scopedb_tm p q A && fc_scopedb_tm (S p) q B
  | a_Conv a g => fc_scopedb_tm p q a && fc_scopedb_co p q g
  | a_CPi phi B => fc_scopedb_constraint p q phi && fc_scopedb_tm p (S q) B
  | a_CAbs phi b => fc_scopedb_constraint p q phi && fc_scopedb_tm p (S q) b
  | a_UCAbs b => fc_scopedb_tm p (S q) b
  | a_CApp a g => fc_scopedb_tm p q a && fc_scopedb_co p q g
  | a_Bullet => true
  | a_DataCon K => true
  | a_Case a brs5 => fc_scopedb_tm p q a && fc_scopedb_brs p q brs5
  end
with fc_scopedb_brs (p q : nat) (e : brs) : bool :=
  match e with
  | br_None => true
  | br_One K a brs5 => fc_scopedb_tm p q a && fc_scopedb_brs p q brs5
  end
with fc_scopedb_co (p q : nat) (e : co) : bool :=
  match e with
  | g_Triv => true
  | g_Var_b i => Nat.ltb i q
  | g_Var_f c => true
  | g_Beta a b => fc_scopedb_tm p q a && fc_scopedb_tm p q b
  | g_Refl a => fc_scopedb_tm p q a
  | g_Refl2 a b g => fc_scopedb_tm p q a && fc_scopedb_tm p q b && fc_scopedb_co p q g
  | g_Sym g => fc_scopedb_co p q g
  | g_Trans g1 g2 => fc_scopedb_co p q g1 && fc_scopedb_co p q g2
  | g_PiCong rho g1 g2 => fc_scopedb_co p q g1 && fc_scopedb_co (S p) q g2
  | g_AbsCong rho g1 g2 => fc_scopedb_co p q g1 && fc_scopedb_co (S p) q g2
  | g_AppCong g1 rho g2 => fc_scopedb_co p q g1 && fc_scopedb_co p q g2
  | g_PiFst g => fc_scopedb_co p q g
  | g_CPiFst g => fc_scopedb_co p q g
  | g_IsoSnd g => fc_scopedb_co p q g
  | g_PiSnd g1 g2 => fc_scopedb_co p q g1 && fc_scopedb_co p q g2
  | g_CPiCong g1 g3 => fc_scopedb_co p q g1 && fc_scopedb_co p (S q) g3
  | g_CAbsCong g1 g3 g4 => fc_scopedb_co p q g1 && fc_scopedb_co p (S q) g3 && fc_scopedb_co p q g4
  | g_CAppCong g g1 g2 => fc_scopedb_co p q g && fc_scopedb_co p q g1 && fc_scopedb_co p q g2
  | g_CPiSnd g g1 g2 => fc_scopedb_co p q g && fc_scopedb_co p q g1 && fc_scopedb_co p q g2
  | g_Cast g1 g2 => fc_scopedb_co p q g1 && fc_scopedb_co p q g2
  | g_EqCong g1 A g2 => fc_scopedb_co p q g1 && fc_scopedb_tm p q A && fc_scopedb_co p q g2
  | g_IsoConv phi1 phi2 g => fc_scopedb_constraint p q phi1 && fc_scopedb_constraint p q phi2 && fc_scopedb_co p q g
  | g_Eta a => fc_scopedb_tm p q a
  | g_Left g g' => fc_scopedb_co p q g && fc_scopedb_co p q g'
  | g_Right g g' => fc_scopedb_co p q g && fc_scopedb_co p q g'
  end
with fc_scopedb_constraint (p q : nat) (e : constraint) : bool :=
  match e with
  | Eq a b A => fc_scopedb_tm p q a && fc_scopedb_tm p q b && fc_scopedb_tm p q A
  end.

Lemma fc_scopedb_spec :
  (forall e p q, fc_scopedb_tm p q e = true <-> fc_degree_tm p q e) /\
  (forall e p q, fc_scopedb_brs p q e = true <-> fc_degree_brs p q e) /\
  (forall e p q, fc_scopedb_co p q e = true <-> fc_degree_co p q e) /\
  (forall e p q, fc_scopedb_constraint p q e = true <-> fc_degree_constraint p q e).
Proof.
  apply fc_syntax_ind; intros; cbn -[Nat.ltb];
    rewrite ?Nat.ltb_lt; repeat rewrite andb_true_iff;
    repeat match goal with H : forall _ _, _ |- _ => rewrite H end; intuition auto.
Qed.
Definition fc_scopedb_spec_tm := proj1 (fc_scopedb_spec).
Definition fc_scopedb_spec_co := proj1 (proj2 (proj2 (fc_scopedb_spec))).

Lemma fc_notin_union_iff : forall x s t, x `notin` (s \u t) <-> x `notin` s /\ x `notin` t.
Proof. intros; fsetdec. Qed.

Lemma fc_same_rho :
  (forall e n x y, x `notin` fv_tm_tm_tm e -> y `notin` fv_tm_tm_tm e ->
   (x `notin` fv_tm_tm_tm (open_tm_wrt_tm_rec n (a_Var_f x) e) <->
    y `notin` fv_tm_tm_tm (open_tm_wrt_tm_rec n (a_Var_f y) e))) /\
  (forall e n x y, x `notin` fv_tm_tm_brs e -> y `notin` fv_tm_tm_brs e ->
   (x `notin` fv_tm_tm_brs (open_brs_wrt_tm_rec n (a_Var_f x) e) <->
    y `notin` fv_tm_tm_brs (open_brs_wrt_tm_rec n (a_Var_f y) e))) /\
  (forall e n x y, x `notin` fv_tm_tm_co e -> y `notin` fv_tm_tm_co e ->
   (x `notin` fv_tm_tm_co (open_co_wrt_tm_rec n (a_Var_f x) e) <->
    y `notin` fv_tm_tm_co (open_co_wrt_tm_rec n (a_Var_f y) e))) /\
  (forall e n x y, x `notin` fv_tm_tm_constraint e -> y `notin` fv_tm_tm_constraint e ->
   (x `notin` fv_tm_tm_constraint (open_constraint_wrt_tm_rec n (a_Var_f x) e) <->
    y `notin` fv_tm_tm_constraint (open_constraint_wrt_tm_rec n (a_Var_f y) e))).
Proof.
  apply fc_syntax_ind; intros; cbn -[lt_eq_lt_dec] in *;
    try solve [split; fsetdec].
  all: try solve [destruct lt_eq_lt_dec as [[]|]; cbn; split; fsetdec].
  all: repeat rewrite fc_notin_union_iff in *.
  all: fc_unpack;
    repeat match goal with IH : forall _ _ _, _ |- _ => first [rewrite (IH n x y) by assumption | rewrite (IH (S n) x y) by assumption] end; tauto.
Qed.
Definition fc_same_rho_tm := proj1 (fc_same_rho).

Definition fc_degree_dec_tm (a : tm) : {fc_degree_tm 0 0 a} + {~ fc_degree_tm 0 0 a}.
Proof. destruct (fc_scopedb_tm 0 0 a) eqn:B; [left|right]; rewrite <- fc_scopedb_spec_tm; congruence. Defined.
Definition fc_degree_dec_co (a : co) : {fc_degree_co 0 0 a} + {~ fc_degree_co 0 0 a}.
Proof. destruct (fc_scopedb_co 0 0 a) eqn:B; [left|right]; rewrite <- fc_scopedb_spec_co; congruence. Defined.

Definition fc_lc_dec_tm (a : tm) : {lc_tm a} + {~ lc_tm a}.
Proof.
  destruct (fc_degree_dec_tm a); [left; auto using fc_degree_lc_tm | right; auto using fc_lc_degree_tm].
Defined.
Definition fc_lc_dec_co (a : co) : {lc_co a} + {~ lc_co a}.
Proof.
  destruct (fc_degree_dec_co a); [left; auto using fc_degree_lc_co | right; auto using fc_lc_degree_co].
Defined.

Definition fc_lc_dec_phi (p : constraint) : {lc_constraint p} + {~ lc_constraint p}.
Proof.
  destruct p as [a b A].
  destruct (fc_lc_dec_tm a), (fc_lc_dec_tm b), (fc_lc_dec_tm A);
  try solve [left; constructor; assumption];
  right; intro H; inversion H; contradiction.
Defined.

Lemma fc_erase_free : forall e x, x \notin fc_fv_tm e -> x \notin fv_tm_tm_tm (erase_tm e).
Proof.
  enough ((forall e x, x \notin fc_fv_tm e -> x \notin fv_tm_tm_tm (erase_tm e)) /\
          (forall e x, x \notin fc_fv_brs e -> x \notin fv_tm_tm_brs (erase_brs e)) /\
          (forall e : co, True) /\
          (forall e x, x \notin fc_fv_constraint e -> x \notin fv_tm_tm_constraint (erase_constraint e)))
    by tauto.
  apply fc_syntax_ind; intros; cbn in *; try destruct rho; cbn in *;
    try exact I;
    repeat match goal with IH : forall _, _, N : ?x `notin` _ |- _ =>
      let H := fresh in pose proof (IH x ltac:(fsetdec)) as H; clear IH
    end; fsetdec.
Qed.

Lemma fc_rho_rename : forall r a x y, x \notin fc_fv_tm a -> y \notin fc_fv_tm a ->
  RhoCheck r x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) ->
  RhoCheck r y (erase_tm (open_tm_wrt_tm a (a_Var_f y))).
Proof.
  intros r a x y Fx Fy R. destruct r; [constructor; exact I|].
  inversion R; subst.
  constructor. unfold open_tm_wrt_tm in *.
  rewrite fc_erase_topen_tm in *. cbn [erase_tm] in *.
  apply (proj1 (fc_same_rho_tm (erase_tm a) 0 x y (fc_erase_free _ _ Fx) (fc_erase_free _ _ Fy))); assumption.
Qed.

Definition fc_rho_dec (r : relflag) (x : atom) (a : tm) : {RhoCheck r x a} + {~ RhoCheck r x a}.
Proof.
  destruct r; [left; constructor; exact I|].
  destruct (AtomSetProperties.In_dec x (fv_tm_tm_tm a)).
  - right; intro H; inversion H; contradiction.
  - left; constructor; assumption.
Defined.

Definition fc_rel_dec (r s : relflag) : {r = s} + {r <> s}.
Proof. decide equality. Defined.

Lemma fc_value_rename : forall a x y, x \notin fc_fv_tm a ->
  Value (open_tm_wrt_tm a (a_Var_f x)) -> Value (open_tm_wrt_tm a (a_Var_f y)).
Proof.
  intros a x y Fx V.
  apply (fc_map_value (fc_rename_t x y)) in V.
  now rewrite fc_rename_t_topen in V.
Qed.
Lemma fc_cvalue_rename : forall a x y, x \notin fc_fv_tm a ->
  CoercedValue (open_tm_wrt_tm a (a_Var_f x)) -> CoercedValue (open_tm_wrt_tm a (a_Var_f y)).
Proof.
  intros a x y Fx V.
  apply (proj1 (fc_map_values (fc_rename_t x y))) in V.
  now rewrite fc_rename_t_topen in V.
Qed.

Definition fc_value_dec_size : forall n,
  (forall a, fc_size_tm a < n -> {Value a} + {~ Value a}) *
  (forall a, fc_size_tm a < n -> {CoercedValue a} + {~ CoercedValue a}).
Proof.
  induction n as [|n [V C]].
  - split; intros; exfalso; lia.
  - assert (U : forall a, fc_size_tm a < S n -> {Value a} + {~ Value a}).
    { intros a Sza. destruct a; try solve [right; intro H; inversion H].
      - left; constructor.
      - destruct rho.
        + destruct (fc_lc_dec_tm a1), (fc_lc_dec_tm (a_Abs Rel a1 a2));
          try solve [left; constructor; assumption];
          right; intro H; inversion H; contradiction.
        + destruct (fc_lc_dec_tm a1) as [K|K]; [|right; intro H; inversion H; contradiction].
          destruct (atom_fresh (fc_fv_tm a2)) as [x Fx].
          destruct (C (open_tm_wrt_tm a2 (a_Var_f x))) as [J|J].
          * unfold open_tm_wrt_tm; rewrite fc_sz_topen_tm; cbn in Sza; lia.
          * left. eapply (Value_AbsIrrel (fc_fv_tm a2)); [assumption|].
            intros y Fy; exact (fc_cvalue_rename a2 x y Fx J).
          * right; intro H; inversion H; subst.
            apply J.
            destruct (atom_fresh (L \u fc_fv_tm a2)) as [y Fy].
            eapply (fc_cvalue_rename a2 y x); [fsetdec|apply H3; fsetdec].
      - destruct rho.
        + destruct (fc_lc_dec_tm (a_UAbs Rel a)); [left; constructor; assumption | right; intro H; inversion H; contradiction].
        + destruct (atom_fresh (fc_fv_tm a)) as [x Fx].
          destruct (V (open_tm_wrt_tm a (a_Var_f x))) as [J|J].
          * unfold open_tm_wrt_tm; rewrite fc_sz_topen_tm; cbn in Sza; lia.
          * left. eapply (Value_UAbsIrrel (fc_fv_tm a)).
            intros y Fy; exact (fc_value_rename a x y Fx J).
          * right; intro H; inversion H; subst.
            apply J.
            destruct (atom_fresh (L \u fc_fv_tm a)) as [y Fy].
            eapply (fc_value_rename a y x); [fsetdec|eauto].
      - destruct (fc_lc_dec_tm a1), (fc_lc_dec_tm (a_Pi rho a1 a2));
        try solve [left; constructor; assumption];
        right; intro H; inversion H; contradiction.
      - destruct (fc_lc_dec_phi phi), (fc_lc_dec_tm (a_CPi phi a));
        try solve [left; constructor; assumption];
        right; intro H; inversion H; contradiction.
      - destruct (fc_lc_dec_phi phi), (fc_lc_dec_tm (a_CAbs phi a));
        try solve [left; constructor; assumption];
        right; intro H; inversion H; contradiction.
      - destruct (fc_lc_dec_tm (a_UCAbs a)); [left; constructor; assumption | right; intro H; inversion H; contradiction]. }
    split; [exact U|].
    intros a Sza. destruct (U a Sza) as [J|J];
      [left; now apply CV |].
    destruct a; try solve [right; let H := fresh in intro H; inversion H; contradiction].
    destruct (V a ltac:(cbn in Sza; lia)), (fc_lc_dec_co g);
      try solve [left; apply CC; assumption];
      right; intro H; inversion H; contradiction.
Defined.

Definition fc_value_dec a := fst (fc_value_dec_size (S (fc_size_tm a))) a (Nat.lt_succ_diag_r _).

Lemma fc_beta_signature : forall F a A, binds F (Ax a A) toplevel -> F = Fix /\ a = erase_tm FixDef.
Proof. intros F a A J; simpl in J; destruct J as [J|[]]; inversion J; auto. Qed.

Definition fc_beta_dec (a b : tm) : {Beta a b} + {~ Beta a b}.
Proof.
  destruct a; try solve [right; intro J; inversion J].
  - destruct a1; try solve [right; intro J; inversion J].
    destruct (fc_rel_dec rho0 rho) as [->|N]; [|right; intro J; inversion J; subst; try contradiction; congruence].
    destruct (fc_lc_dec_tm a2), (fc_value_dec (a_UAbs rho a1)),
       (fc_eq_tm b (open_tm_wrt_tm a1 a2));
       try solve [left; subst; apply Beta_AppAbs; assumption];
       right; intro J; inversion J; subst; try contradiction; congruence.
  - destruct (F == Fix) as [->|N], (fc_eq_tm b (erase_tm FixDef)) as [->|M].
    + left; eapply Beta_Axiom; simpl; left; reflexivity.
    + right; intro J; inversion J; subst.
      match goal with K : binds _ (Ax _ _) toplevel |- _ =>
        destruct (fc_beta_signature _ _ _ K); contradiction end.
    + right; intro J; inversion J; subst.
      match goal with K : binds _ (Ax _ _) toplevel |- _ =>
        destruct (fc_beta_signature _ _ _ K); contradiction end.
    + right; intro J; inversion J; subst.
      match goal with K : binds _ (Ax _ _) toplevel |- _ =>
        destruct (fc_beta_signature _ _ _ K); contradiction end.
  - destruct a; try solve [right; intro J; inversion J].
    destruct g; try solve [right; intro J; inversion J].
    destruct (fc_lc_dec_tm (a_UCAbs a)), (fc_eq_tm b (open_tm_wrt_co a g_Triv));
      try solve [left; subst; apply Beta_CAppCAbs; assumption];
      right; intro J; inversion J; subst; try contradiction; congruence.
Defined.

(** Syntax-directed decisions and the closed-term checker. *)

Definition fc_term_answer G a :=
  { A : tm | AnnTyping G a A } + { forall A, ~ AnnTyping G a A }.
Definition fc_co_answer G D g :=
  { p : tm * tm | AnnDefEq G D g (fst p) (snd p) } +
  { forall a b, ~ AnnDefEq G D g a b }.
Definition fc_iso_answer G D g :=
  { p : constraint * constraint | AnnIso G D g (fst p) (snd p) } +
  { forall a b, ~ AnnIso G D g a b }.

Record fc_checks n : Type := {
  fc_check_t : forall G a, AnnCtx G -> fc_size_tm a < n -> fc_term_answer G a;
  fc_check_p : forall G phi, AnnCtx G -> fc_size_constraint phi < n ->
                              {AnnPropWff G phi} + {~ AnnPropWff G phi};
  fc_check_e : forall G D g, AnnCtx G -> D [<=] dom G -> fc_size_co g < n -> fc_co_answer G D g;
  fc_check_i : forall G D g, AnnCtx G -> D [<=] dom G -> fc_size_co g < n -> fc_iso_answer G D g
}.

Definition fc_known_type G a (W : AnnCtx G) (P : exists A, AnnTyping G a A) :
  {A | AnnTyping G a A}.
Proof.
  destruct (fc_guess_tm (S (fc_size_tm a)) G a) as [A|] eqn:E.
  - exists A. destruct P as [B J].
    rewrite (proj1 (fc_guess_complete _) G a B W (Nat.lt_succ_diag_r _) J) in E.
    congruence.
  - exfalso. destruct P as [B J].
    rewrite (proj1 (fc_guess_complete _) G a B W (Nat.lt_succ_diag_r _) J) in E.
    discriminate.
Defined.

Definition fc_eq_types G D g a b (W : AnnCtx G) (J : AnnDefEq G D g a b) :
  {p : tm * tm | AnnTyping G a (fst p) /\ AnnTyping G b (snd p)}.
Proof.
  pose proof (fc_defeq_reg G D g a b J W) as R.
  assert (P : exists A, AnnTyping G a A) by (unfold fc_equal_classifiers in R; firstorder).
  assert (Q : exists B, AnnTyping G b B) by (unfold fc_equal_classifiers in R; firstorder).
  destruct (fc_known_type G a W P) as [A T], (fc_known_type G b W Q) as [B U].
  exists (A,B); simpl; auto.
Defined.

Ltac fc_align :=
  repeat match reverse goal with
  | J : AnnTyping ?G ?a ?A, K : AnnTyping ?G ?a ?B |- _ =>
    first [constr_eq A B; fail 1 |
      let E := fresh in pose proof (fc_typ_unique G a A J B K) as E;
      first [discriminate E | is_var A; subst A | is_var B; subst B |
             progress (injection E as E; subst)] ]
  | J : AnnDefEq ?G ?D ?g ?a ?b, K : AnnDefEq ?G ?D ?g ?u ?v |- _ =>
    first [constr_eq (a,b) (u,v); fail 1 |
      let E := fresh in let F := fresh in destruct (fc_eq_unique G D g a b J u v K) as [E F];
      first [discriminate E | discriminate F |
             progress (try (is_var a; subst a); try (is_var b; subst b)) |
             progress (try (injection E as E); try (injection F as F); subst)] ]
  | J : AnnIso ?G ?D ?g ?a ?b, K : AnnIso ?G ?D ?g ?u ?v |- _ =>
    first [constr_eq (a,b) (u,v); fail 1 |
      let E := fresh in let F := fresh in destruct (fc_iso_unique G D g a b J u v K) as [E F];
      first [discriminate E | discriminate F |
             progress (try (is_var a; subst a); try (is_var b; subst b)) |
             progress (try (injection E as E); try (injection F as F); subst)] ]
  end.

Ltac fc_impossible :=
  first [congruence | contradiction |
    match goal with N : forall _, _ |- False => solve [eapply N; eassumption] end |
    solve [eauto 4] ].

Ltac fc_no_term :=
  right; let A := fresh "candidate" in let J := fresh "derivation" in
  intros A J; inversion J; subst; clear J; fc_align; try fc_impossible.

Ltac fc_no_co :=
  right; let a := fresh "candidate_left" in let b := fresh "candidate_right" in
  let J := fresh "derivation" in intros a b J; inversion J; subst; clear J;
  fc_align; try fc_impossible.

Ltac fc_no_wff :=
  right; let J := fresh "derivation" in intros J; inversion J; subst; clear J;
  fc_align; try fc_impossible.

Ltac fc_sub_t n sub G a W A J :=
  destruct (fc_check_t n sub G a W ltac:(fc_size_bound)) as [[A J]|J];
  [idtac|solve [fc_no_term | fc_no_co | fc_no_wff]].
Ltac fc_sub_e n sub G D g W a b J :=
  destruct (fc_check_e n sub G D g W ltac:(first [assumption | solve [intros z Hz; exact Hz]]) ltac:(fc_size_bound)) as [[[a b] J]|J];
  [cbn in J|solve [fc_no_term | fc_no_co]].
Ltac fc_sub_i n sub G D g W a b J :=
  destruct (fc_check_i n sub G D g W ltac:(first [assumption | solve [intros z Hz; exact Hz]]) ltac:(fc_size_bound)) as [[[a b] J]|J];
  [cbn in J|solve [fc_no_co]].

Definition fc_wff_from_typed G a b A X Y
    (J : AnnTyping G a X) (K : AnnTyping G b Y) :
  {AnnPropWff G (Eq a b A)} + {~ AnnPropWff G (Eq a b A)}.
Proof.
  destruct (fc_eq_tm X A) as [->|N]; [|fc_no_wff].
  destruct (fc_eq_tm (erase_tm A) (erase_tm Y)) as [E|N]; [|fc_no_wff].
  left; eapply An_Wff; eassumption.
Defined.

Definition fc_wff_step n (sub : fc_checks n) G phi (W : AnnCtx G)
  (Sphi : fc_size_constraint phi < S n) :
    {AnnPropWff G phi} + {~ AnnPropWff G phi}.
Proof.
  destruct phi as [a b A].
  fc_sub_t n sub G a W T HT.
  fc_sub_t n sub G b W U HU.
  exact (fc_wff_from_typed G a b A T U HT HU).
Defined.

Definition fc_app_check G a rho b A B
  (J : AnnTyping G a A) (K : AnnTyping G b B) : fc_term_answer G (a_App a rho b).
Proof.
  destruct A; try solve [fc_no_term].
  destruct (fc_rel_dec rho0 rho) as [->|N]; [|fc_no_term].
  destruct (fc_eq_tm A1 B) as [->|N]; [|fc_no_term].
  left; exists (open_tm_wrt_tm A2 b); eapply An_App; eassumption.
Defined.

Definition fc_capp_check G a g A a1 a2
  (J : AnnTyping G a A) (K : AnnDefEq G (dom G) g a1 a2) :
  fc_term_answer G (a_CApp a g).
Proof.
  destruct A; try solve [fc_no_term].
  destruct phi as [x y T].
  destruct (fc_eq_tm a1 x) as [->|N]; [|fc_no_term].
  destruct (fc_eq_tm a2 y) as [->|N]; [|fc_no_term].
  left; exists (open_tm_wrt_co A g); eapply An_CApp; eassumption.
Defined.

Lemma fc_rho_fresh : forall L r a x, x \notin fc_fv_tm a ->
  (forall y, y \notin L -> RhoCheck r y (erase_tm (open_tm_wrt_tm a (a_Var_f y)))) ->
  RhoCheck r x (erase_tm (open_tm_wrt_tm a (a_Var_f x))).
Proof.
  intros L r a x Fx J.
  destruct (atom_fresh (L \u fc_fv_tm a)) as [y Fy].
  apply (fc_rho_rename r a y x); [fsetdec|exact Fx|apply J; fsetdec].
Qed.

Ltac fc_force_typ_domain A J :=
  let K := fresh "domain_kind" in
  destruct (fc_eq_tm A a_Star) as [K|K];
  [subst A | solve [fc_no_term | fc_no_co]].

Definition fc_term_step n (sub : fc_checks n) G a (W : AnnCtx G)
  (Sa : fc_size_tm a < S n) : fc_term_answer G a.
Proof.
  destruct a; try solve [fc_no_term].
  - left; exists a_Star; constructor; assumption.
  - destruct (fc_lookup G x) as [[A|phi]|] eqn:E.
    + left; exists A; apply An_Var; [assumption|eapply fc_lookup_binds; exact E].
    + fc_no_term.
      match goal with B : binds _ _ _ |- _ =>
        rewrite (fc_lookup_complete _ _ _ (fc_ctx_uniq G W) B) in E; discriminate end.
    + fc_no_term.
      match goal with B : binds _ _ _ |- _ =>
        rewrite (fc_lookup_complete _ _ _ (fc_ctx_uniq G W) B) in E; discriminate end.
  - fc_sub_t n sub G a1 W A J.
    fc_force_typ_domain A J.
    pose (x := fc_pick G (fc_fv_tm a1 \u fc_fv_tm a2)).
    pose proof (fc_pick_spec G (fc_fv_tm a1 \u fc_fv_tm a2)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_tm a1 \u fc_fv_tm a2)) as Dx; fold x in Dx.
    pose proof (An_ConsTm G x a1 W J Dx) as W'.
    destruct (fc_rho_dec rho x (erase_tm (open_tm_wrt_tm a2 (a_Var_f x)))) as [R|R].
    2: { fc_no_term. apply R; eapply fc_rho_fresh; [fsetdec|eassumption]. }
    destruct (fc_check_t n sub ((x,Tm a1)::G) (open_tm_wrt_tm a2 (a_Var_f x)) W'
              ltac:(fc_size_bound)) as [[B K]|N].
    + left; exists (a_Pi rho a1 (fc_close_tm_tm 0 x B)).
      apply (An_Abs (dom G \u fc_fv_tm a2)); [exact J| |].
      * intros y Fy.
        pose proof (fc_tabstract_typ G a1 x _ B W J ltac:(fsetdec) ltac:(fsetdec) K y ltac:(fsetdec)) as Q.
        now rewrite fc_close_t_open_t in Q by fsetdec.
      * intros y Fy; apply (fc_rho_rename rho a2 x y); [fsetdec|fsetdec|assumption].
    + fc_no_term.
      eapply N; eapply (fc_fresh_t_typ L); eassumption.
  - fc_sub_t n sub G a1 W A J.
    fc_sub_t n sub G a2 W B K.
    exact (fc_app_check G a1 rho a2 A B J K).
  - destruct (F == Fix) as [->|N].
    + left; exists FixTy; exact (An_Fam G Fix FixTy FixDef W (or_introl eq_refl) fc_FixTyping).
    + fc_no_term.
      match goal with B : binds _ (Ax _ _) an_toplevel |- _ =>
        destruct (fc_family_binding _ _ _ B) as (? & ? & ?); contradiction end.
  - fc_sub_t n sub G a1 W A J.
    fc_force_typ_domain A J.
    pose (x := fc_pick G (fc_fv_tm a1 \u fc_fv_tm a2)).
    pose proof (fc_pick_spec G (fc_fv_tm a1 \u fc_fv_tm a2)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_tm a1 \u fc_fv_tm a2)) as Dx; fold x in Dx.
    pose proof (An_ConsTm G x a1 W J Dx) as W'.
    destruct (fc_check_t n sub ((x,Tm a1)::G) (open_tm_wrt_tm a2 (a_Var_f x)) W'
              ltac:(fc_size_bound)) as [[B K]|N].
    + destruct (fc_eq_tm B a_Star) as [->|M].
      * left; exists a_Star; apply (An_Pi (dom G)); [|exact J].
        intros y Fy. pose proof (fc_tabstract_typ G a1 x _ a_Star W J
          ltac:(fsetdec) ltac:(fsetdec) K y Fy) as Q.
        now rewrite fc_close_t_open_t in Q by fsetdec.
      * fc_no_term.
        assert (P : AnnTyping ((x,Tm a1)::G) (open_tm_wrt_tm a2 (a_Var_f x)) a_Star) by
          (eapply (fc_fresh_t_typ L G a1 a2 a_Star); eassumption).
        fc_align; contradiction.
    + fc_no_term. apply (N a_Star).
      eapply (fc_fresh_t_typ L G a1 a2 a_Star); eassumption.
  - fc_sub_t n sub G a W A J.
    fc_sub_e n sub G (dom G) g W X Y E.
    destruct (fc_eq_tm A X) as [->|N]; [|fc_no_term].
    destruct (fc_eq_types G (dom G) g X Y W E) as [[AX AY] [TX TY]]; simpl in *.
    destruct (fc_eq_tm AY a_Star) as [->|N]; [|fc_no_term].
    left; exists Y; eapply An_Conv; eassumption.
  - destruct (fc_check_p n sub G phi W ltac:(fc_size_bound)) as [J|J]; [|fc_no_term].
    pose (x := fc_pick G (fc_fv_constraint phi \u fc_fv_tm a)).
    pose proof (fc_pick_spec G (fc_fv_constraint phi \u fc_fv_tm a)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_constraint phi \u fc_fv_tm a)) as Dx; fold x in Dx.
    pose proof (An_ConsCo G x phi W J Dx) as W'.
    destruct (fc_check_t n sub ((x,Co phi)::G) (open_tm_wrt_co a (g_Var_f x)) W'
              ltac:(fc_size_bound)) as [[B K]|N].
    + destruct (fc_eq_tm B a_Star) as [->|M].
      * left; exists a_Star; apply (An_CPi (dom G)); [exact J|].
        intros y Fy. pose proof (fc_cabstract_typ G phi x _ a_Star W J
          ltac:(fsetdec) ltac:(fsetdec) K y Fy) as Q.
        now rewrite fc_close_c_open_c in Q by fsetdec.
      * fc_no_term.
        assert (P : AnnTyping ((x,Co phi)::G) (open_tm_wrt_co a (g_Var_f x)) a_Star) by
          (eapply (fc_fresh_c_typ L G phi a a_Star); eassumption).
        fc_align; contradiction.
    + fc_no_term. apply (N a_Star).
      eapply (fc_fresh_c_typ L G phi a a_Star); eassumption.
  - destruct (fc_check_p n sub G phi W ltac:(fc_size_bound)) as [J|J]; [|fc_no_term].
    pose (x := fc_pick G (fc_fv_constraint phi \u fc_fv_tm a)).
    pose proof (fc_pick_spec G (fc_fv_constraint phi \u fc_fv_tm a)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_constraint phi \u fc_fv_tm a)) as Dx; fold x in Dx.
    pose proof (An_ConsCo G x phi W J Dx) as W'.
    destruct (fc_check_t n sub ((x,Co phi)::G) (open_tm_wrt_co a (g_Var_f x)) W'
              ltac:(fc_size_bound)) as [[B K]|N].
    + left; exists (a_CPi phi (fc_close_co_tm 0 x B)).
      apply (An_CAbs (dom G)); [exact J|].
      intros y Fy. pose proof (fc_cabstract_typ G phi x _ B W J
        ltac:(fsetdec) ltac:(fsetdec) K y Fy) as Q.
      now rewrite fc_close_c_open_c in Q by fsetdec.
    + fc_no_term. eapply N.
      eapply (fc_fresh_c_typ L); eassumption.
  - fc_sub_t n sub G a W A J.
    fc_sub_e n sub G (dom G) g W X Y E.
    exact (fc_capp_check G a g A X Y J E).
Defined.

Lemma fc_subset_extend : forall D (G : context) x s, D [<=] dom G -> D [<=] dom ((x,s)::G).
Proof. intros D G x s S c I. rewrite dom_cons. apply AtomSetImpl.union_3, S, I. Qed.

Definition fc_iso_step n (sub : fc_checks n) G D g (W : AnnCtx G) (AD : D [<=] dom G)
  (Sg : fc_size_co g < S n) : fc_iso_answer G D g.
Proof.
  destruct g; try solve [fc_no_co].
  - fc_sub_i n sub G D g W phi psi J.
    left; exists (psi,phi); simpl; eapply An_IsoSym; exact J.
  - fc_sub_e n sub G D g W X Y J.
    destruct X; try solve [fc_no_co].
    destruct Y; try solve [fc_no_co].
    left; eexists (_, _); eapply An_CPiFst; eassumption.
  - fc_sub_e n sub G D g1 W a b J.
    fc_sub_e n sub G D g2 W u v K.
    destruct (fc_eq_types G D g1 a b W J) as [[AT BT] [TA TB]].
    destruct (fc_eq_types G D g2 u v W K) as [[UT VT] [TU TV]].
    cbn in *.
    destruct (fc_wff_from_typed G a u A AT UT TA TU) as [L1|L1]; [|fc_no_co].
    destruct (fc_wff_from_typed G b v A BT VT TB TV) as [L2|L2]; [|fc_no_co].
    left; exists (Eq a u A, Eq b v A); eapply An_PropCong; eassumption.
  - destruct (fc_check_p n sub G phi1 W ltac:(fc_size_bound)) as [W1|W1]; [|fc_no_co].
    destruct (fc_check_p n sub G phi2 W ltac:(fc_size_bound)) as [W2|W2]; [|fc_no_co].
    fc_sub_e n sub G D g W a b J.
    destruct phi1 as [u v A], phi2 as [u' v' B].
    destruct (fc_eq_tm a A) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm b B) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm (erase_tm u) (erase_tm u')) as [E|N]; [|fc_no_co].
    destruct (fc_eq_tm (erase_tm v) (erase_tm v')) as [F|N]; [|fc_no_co].
    left; eexists (_, _); eapply An_IsoConv; eassumption.
Defined.

Ltac fc_co_success a b rule :=
  left; exists (a,b); cbn; eapply rule; eassumption.

Lemma fc_co_close_t : forall g x, x \notin fc_fv_co g ->
  fc_close_tm_co 0 x (open_co_wrt_tm g (a_Var_f x)) = g.
Proof. exact (fun g x => proj1 (proj2 (proj2 fc_close_after_open)) g 0 x). Qed.
Lemma fc_co_close_c : forall g x, x \notin fc_fv_co g ->
  fc_close_co_co 0 x (open_co_wrt_co g (g_Var_f x)) = g.
Proof. exact (fun g x => proj1 (proj2 (proj2 fc_cclose_after_open)) g 0 x). Qed.

Lemma fc_term_body_unique : forall L G D A g x a b p q,
  AnnCtx G -> AnnTyping G A a_Star -> x \notin dom G ->
  x \notin fc_fv_ctx G -> x \notin fc_fv_tm A -> x \notin fc_fv_co g ->
  AnnDefEq ((x,Tm A)::G) D (open_co_wrt_tm g (a_Var_f x)) p q ->
  (forall y, y \notin L -> AnnDefEq ((y,Tm A)::G) D (open_co_wrt_tm g (a_Var_f y))
    (open_tm_wrt_tm a (a_Var_f y)) (open_tm_wrt_tm b (a_Var_f y))) ->
  fc_close_tm_tm 0 x p = a /\ fc_close_tm_tm 0 x q = b.
Proof.
  intros L G D A g x a b p q W K Dx Fx FA Fg J H.
  pose proof (fc_fresh_t_eq L G D A g a b x W K Dx H) as E.
  destruct (fc_eq_unique _ _ _ _ _ J _ _ E) as [-> ->].
  destruct (fc_eq_binder_free_t G A g D a b x Fx FA Fg (ex_intro _ L H)).
  split; apply fc_close_t_open_t; assumption.
Qed.

Lemma fc_co_body_unique : forall L G D phi g x a b p q,
  AnnCtx G -> AnnPropWff G phi -> x \notin dom G ->
  x \notin fc_fv_ctx G -> x \notin fc_fv_constraint phi -> x \notin fc_fv_co g ->
  AnnDefEq ((x,Co phi)::G) D (open_co_wrt_co g (g_Var_f x)) p q ->
  (forall y, y \notin L -> AnnDefEq ((y,Co phi)::G) D (open_co_wrt_co g (g_Var_f y))
    (open_tm_wrt_co a (g_Var_f y)) (open_tm_wrt_co b (g_Var_f y))) ->
  fc_close_co_tm 0 x p = a /\ fc_close_co_tm 0 x q = b.
Proof.
  intros L G D phi g x a b p q W K Dx Fx FA Fg J H.
  pose proof (fc_fresh_c_eq L G D phi g a b x W K Dx H) as E.
  destruct (fc_eq_unique _ _ _ _ _ J _ _ E) as [-> ->].
  destruct (fc_eq_binder_free_c G phi g D a b x Fx FA Fg (ex_intro _ L H)).
  split; apply fc_close_c_open_c; assumption.
Qed.

Lemma fc_tcast_typ : forall G D g A1 A2 b B,
  AnnCtx G -> AnnDefEq G D g A1 A2 -> AnnTyping G A1 a_Star -> AnnTyping G A2 a_Star ->
  (forall y, y \notin dom G -> AnnTyping ((y,Tm A1)::G)
           (open_tm_wrt_tm b (a_Var_f y)) (open_tm_wrt_tm B (a_Var_f y))) ->
  forall y, y \notin dom G -> AnnTyping ((y,Tm A2)::G)
           (open_tm_wrt_tm (fc_tmcast_tm 0 g b) (a_Var_f y))
           (open_tm_wrt_tm (fc_tmcast_tm 0 g B) (a_Var_f y)).
Proof.
  intros G D g A1 A2 b B W J T U K y Fy.
  pose proof (fc_co_degree _ _ _ _ _ J) as DG.
  unfold open_tm_wrt_tm at 1 2. rewrite !fc_tmcast_open_tm by exact DG.
  apply (fc_tsubst_typ (dom G) G ((y,Tm A2)::G) A1).
  - constructor; assumption.
  - intros; right; assumption.
  - apply (fc_var_cast G D); assumption.
  - simpl; auto.
  - exact K.
Qed.

Lemma fc_ccast_typ : forall G D g phi psi b B,
  AnnCtx G -> AnnIso G D g phi psi -> AnnPropWff G psi ->
  (forall y, y \notin dom G -> AnnTyping ((y,Co phi)::G)
           (open_tm_wrt_co b (g_Var_f y)) (open_tm_wrt_co B (g_Var_f y))) ->
  forall y, y \notin dom G -> AnnTyping ((y,Co psi)::G)
           (open_tm_wrt_co (fc_cocast_tm 0 g b) (g_Var_f y))
           (open_tm_wrt_co (fc_cocast_tm 0 g B) (g_Var_f y)).
Proof.
  intros G D g phi psi b B W J Q K y Fy.
  pose proof (fc_iso_degree _ _ _ _ _ J) as DG.
  unfold open_tm_wrt_co at 1 2. rewrite !fc_cocast_open_tm by exact DG.
  apply (fc_csubst_typ (dom G) G ((y,Co psi)::G) phi).
  - constructor; assumption.
  - intros; right; assumption.
  - apply (fc_assn_cast G D _ _ _ _ W Fy Q J).
  - simpl; auto.
  - exact K.
Qed.

Definition fc_rho_binder r b :
  {forall y, y \notin fc_fv_tm b -> RhoCheck r y (erase_tm (open_tm_wrt_tm b (a_Var_f y)))} +
  {forall L, ~ (forall y, y \notin L -> RhoCheck r y (erase_tm (open_tm_wrt_tm b (a_Var_f y))))}.
Proof.
  destruct (atom_fresh (fc_fv_tm b)) as [x Fx].
  destruct (fc_rho_dec r x (erase_tm (open_tm_wrt_tm b (a_Var_f x)))) as [R|R].
  - left; intros; apply (fc_rho_rename r b x); assumption.
  - right; intros L J. apply R. apply (fc_rho_fresh L); assumption.
Defined.

Lemma fc_pi_at : forall G x r A b T, AnnCtx G -> x `notin` dom G ->
  AnnTyping G (a_Pi r A b) T ->
  AnnTyping ((x,Tm A)::G) (open_tm_wrt_tm b (a_Var_f x)) a_Star.
Proof.
  intros G x r A b T W Dx J; inversion J; subst.
  eapply (fc_fresh_t_typ L G A b a_Star); eassumption.
Qed.

Lemma fc_cpi_at : forall G x phi b T, AnnCtx G -> x `notin` dom G ->
  AnnTyping G (a_CPi phi b) T ->
  AnnTyping ((x,Co phi)::G) (open_tm_wrt_co b (g_Var_f x)) a_Star.
Proof.
  intros G x phi b T W Dx J; inversion J; subst.
  eapply (fc_fresh_c_typ L G phi b a_Star); eassumption.
Qed.

Lemma fc_abs_rho_inv : forall G r A b T, AnnTyping G (a_Abs r A b) T ->
  exists L, forall y, y `notin` L -> RhoCheck r y (erase_tm (open_tm_wrt_tm b (a_Var_f y))).
Proof. intros; inversion H; eauto. Qed.

Ltac fc_body_align_t :=
  match goal with
  | J : AnnDefEq ((?x,Tm ?A)::?G) ?D (open_co_wrt_tm ?k (a_Var_f ?x)) ?p ?q,
    H : forall y : _, y `notin` ?L -> AnnDefEq _ ?D _
        (open_tm_wrt_tm ?b1 _) (open_tm_wrt_tm ?b2 _) |- _ =>
      let U := fresh in let V := fresh in
      destruct (fc_term_body_unique L G D A k x b1 b2 p q
        ltac:(assumption) ltac:(assumption) ltac:(assumption)
        ltac:(fsetdec) ltac:(fsetdec) ltac:(fsetdec) J H) as [U V];
      subst b1 b2
  end.

Ltac fc_body_align_c :=
  match goal with
  | J : AnnDefEq ((?x,Co ?A)::?G) ?D (open_co_wrt_co ?k (g_Var_f ?x)) ?p ?q,
    H : forall y : _, y `notin` ?L -> AnnDefEq _ ?D _
        (open_tm_wrt_co ?b1 _) (open_tm_wrt_co ?b2 _) |- _ =>
      let U := fresh in let V := fresh in
      destruct (fc_co_body_unique L G D A k x b1 b2 p q
        ltac:(assumption) ltac:(assumption) ltac:(assumption)
        ltac:(fsetdec) ltac:(fsetdec) ltac:(fsetdec) J H) as [U V];
      subst b1 b2
  end.
Definition fc_co_step n (sub : fc_checks n) G D g (W : AnnCtx G) (AD : D [<=] dom G)
  (Sg : fc_size_co g < S n) : fc_co_answer G D g.
Proof.
  destruct g; try solve [fc_no_co].
  - destruct (fc_lookup G c) as [[A|[a b A]]|] eqn:E.
    + fc_no_co. match goal with B : binds _ _ _ |- _ =>
        rewrite (fc_lookup_complete _ _ _ (fc_ctx_uniq G W) B) in E; discriminate end.
    + destruct (AtomSetProperties.In_dec c D) as [I|I]; [|fc_no_co].
      left; exists (a,b); cbn; eapply (An_Assn _ _ _ _ _ A);
        [assumption|eapply fc_lookup_binds; exact E|assumption].
    + fc_no_co. match goal with B : binds _ _ _ |- _ =>
        rewrite (fc_lookup_complete _ _ _ (fc_ctx_uniq G W) B) in E; discriminate end.
  - fc_sub_t n sub G a W A J.
    fc_sub_t n sub G b W B K.
    destruct (fc_eq_tm (erase_tm A) (erase_tm B)) as [E|N]; [|fc_no_co].
    destruct (fc_beta_dec (erase_tm a) (erase_tm b)) as [Q|N]; [|fc_no_co].
    fc_co_success a b An_Beta.
  - fc_sub_t n sub G a W A J.
    fc_co_success a a An_Refl.
  - fc_sub_t n sub G a W A J.
    fc_sub_t n sub G b W B K.
    fc_sub_e n sub G (dom G) g W X Y E.
    destruct (fc_eq_tm (erase_tm a) (erase_tm b)) as [Q|N]; [|fc_no_co].
    destruct (fc_eq_tm A X) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm B Y) as [->|N]; [|fc_no_co].
    fc_co_success a b An_EraseEq.
  - fc_sub_e n sub G D g W a b J.
    left; exists (b,a); cbn.
    destruct (fc_defeq_reg G D g a b J W) as (A & B & h & TA & TB & E).
    eapply An_Sym; eassumption.
  - fc_sub_e n sub G D g1 W a m J.
    fc_sub_e n sub G D g2 W m' b K.
    destruct (fc_eq_tm m m') as [->|N]; [|fc_no_co].
    left; exists (a,b); cbn.
    destruct (fc_defeq_reg G D g1 a m' J W) as (A & B & h & TA & TB & E).
    eapply An_Trans; eassumption.
  - fc_sub_e n sub G D g1 W A1 A2 J.
    destruct (fc_eq_types G D g1 A1 A2 W J) as [[S1 S2] [K1 K2]]; cbn in *.
    destruct (fc_eq_tm S1 a_Star) as [->|N]; [|fc_no_co
      ; apply N; eapply fc_typ_unique; [exact K1|eapply fc_typ_pi_domain; eassumption]].
    destruct (fc_eq_tm S2 a_Star) as [->|N]; [|fc_no_co
      ; apply N; eapply fc_typ_unique; [exact K2|eapply fc_typ_pi_domain; eassumption]].
    pose (x := fc_pick G (fc_fv_co g1 \u fc_fv_co g2)).
    pose proof (fc_pick_spec G (fc_fv_co g1 \u fc_fv_co g2)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_co g1 \u fc_fv_co g2)) as Dx; fold x in Dx.
    assert (Nd : x `notin` D) by (intro I; apply Dx, AD, I).
    destruct (fc_eq_free _ _ _ _ _ J x ltac:(fsetdec) ltac:(fsetdec)) as [FA1 FA2].
    pose proof (An_ConsTm G x A1 W K1 Dx) as W'.
    pose proof (fc_subset_extend D G x (Tm A1) AD) as AD'.
    destruct (fc_check_e n sub ((x,Tm A1)::G) D (open_co_wrt_tm g2 (a_Var_f x)) W' AD'
          ltac:(fc_size_bound)) as [[[p q] K]|N].
    2: { fc_no_co. eapply N. eapply (fc_fresh_t_eq L); eassumption. }
    cbn in K.
    pose (b1 := fc_close_tm_tm 0 x p).
    pose (b2 := fc_close_tm_tm 0 x q).
    pose (b3 := fc_tmcast_tm 0 g1 b2).
    assert (Body : forall y, y \notin dom G -> AnnDefEq ((y,Tm A1)::G) D
        (open_co_wrt_tm g2 (a_Var_f y))
        (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y))).
    { pose proof (fc_tabstract_eq G D A1 x _ p q W K1 ltac:(fsetdec) FA1 Nd K) as Q.
      now rewrite fc_co_close_t in Q by fsetdec. }
    destruct (fc_eq_types ((x,Tm A1)::G) D _ p q W' K) as [[T1 T2] [U1 U2]]; cbn in *.
    destruct (fc_eq_tm T1 a_Star) as [->|N].
    2: { fc_no_co. fc_body_align_t.
         assert (P : AnnTyping ((x,Tm A1)::G) p a_Star).
         { rewrite <- (proj1 fc_open_after_close p 0 x).
           change (AnnTyping ((x,Tm A1)::G) (open_tm_wrt_tm b1 (a_Var_f x)) a_Star).
           unfold b1, b2; eapply fc_pi_at; eassumption. }
         fc_align; contradiction. }
    destruct (fc_eq_tm T2 a_Star) as [->|N].
    2: { fc_no_co. fc_body_align_t.
         assert (P : AnnTyping ((x,Tm A1)::G) q a_Star).
         { rewrite <- (proj1 fc_open_after_close q 0 x).
           change (AnnTyping ((x,Tm A1)::G) (open_tm_wrt_tm b2 (a_Var_f x)) a_Star).
           unfold b1, b2; eapply fc_pi_at; eassumption. }
         fc_align; contradiction. }
    pose proof (fc_tabstract_typ G A1 x p a_Star W K1 ltac:(fsetdec) FA1 U1) as T1o.
    pose proof (fc_tabstract_typ G A1 x q a_Star W K1 ltac:(fsetdec) FA1 U2) as T2o.
    left; exists (a_Pi rho A1 b1, a_Pi rho A2 b3); cbn.
    eapply (An_PiCong (dom G) _ _ _ _ _ _ _ _ _ b2).
    + exact J.
    + exact Body.
    + intros y Fy; apply fc_tmcast_open_tm; eapply fc_co_degree; exact J.
    + apply (An_Pi (dom G)); assumption.
    + apply (An_Pi (dom G)); assumption.
    + apply (An_Pi (dom G)); [|exact K2].
      intros y Fy. eapply (fc_tcast_typ G D _ A1 A2 b2 a_Star); eassumption.
  - fc_sub_e n sub G D g1 W A1 A2 J.
    destruct (fc_eq_types G D g1 A1 A2 W J) as [[S1 S2] [K1 K2]]; cbn in *.
    destruct (fc_eq_tm S1 a_Star) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm S2 a_Star) as [->|N]; [|fc_no_co].
    pose (x := fc_pick G (fc_fv_co g1 \u fc_fv_co g2)).
    pose proof (fc_pick_spec G (fc_fv_co g1 \u fc_fv_co g2)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_co g1 \u fc_fv_co g2)) as Dx; fold x in Dx.
    assert (Nd : x `notin` D) by (intro I; apply Dx, AD, I).
    destruct (fc_eq_free _ _ _ _ _ J x ltac:(fsetdec) ltac:(fsetdec)) as [FA1 FA2].
    pose proof (An_ConsTm G x A1 W K1 Dx) as W'.
    pose proof (fc_subset_extend D G x (Tm A1) AD) as AD'.
    destruct (fc_check_e n sub ((x,Tm A1)::G) D (open_co_wrt_tm g2 (a_Var_f x)) W' AD'
          ltac:(fc_size_bound)) as [[[p q] K]|N].
    2: { fc_no_co. eapply N. eapply (fc_fresh_t_eq L); eassumption. }
    cbn in K.
    pose (b1 := fc_close_tm_tm 0 x p).
    pose (b2 := fc_close_tm_tm 0 x q).
    pose (b3 := fc_tmcast_tm 0 g1 b2).
    assert (Body : forall y, y \notin dom G -> AnnDefEq ((y,Tm A1)::G) D
        (open_co_wrt_tm g2 (a_Var_f y))
        (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y))).
    { pose proof (fc_tabstract_eq G D A1 x _ p q W K1 ltac:(fsetdec) FA1 Nd K) as Q.
      now rewrite fc_co_close_t in Q by fsetdec. }
    destruct (fc_eq_types ((x,Tm A1)::G) D _ p q W' K) as [[T1 T2] [U1 U2]]; cbn in *.
    destruct (fc_rho_binder rho b1) as [R1|N1].
    2: { fc_no_co. fc_body_align_t. eapply N1; eassumption. }
    destruct (fc_rho_binder rho b2) as [R2|N2].
    2: { fc_no_co. fc_body_align_t.
         assert (S : exists L, forall y, y `notin` L ->
           RhoCheck rho y (erase_tm (open_tm_wrt_tm b2 (a_Var_f y)))).
         { unfold b2; eapply fc_abs_rho_inv; eassumption. }
         destruct S as [F RF]; exact (N2 F RF). }
    destruct (fc_rho_binder rho b3) as [R3|N3].
    2: { fc_no_co. fc_body_align_t.
         unfold b3, b2 in N3.
         match goal with E : forall y : _, _ -> open_tm_wrt_tm _ _ =
            open_tm_wrt_tm _ (a_Conv _ _) |- _ =>
           rewrite (fc_tcast_cofinite _ _ _ _ (fc_co_degree _ _ _ _ _ J) E) in N3
         end.
         eapply N3; eassumption. }
    left; exists (a_Abs rho A1 b1, a_Abs rho A2 b3); cbn.
    eapply (An_AbsCong (dom G \u fc_fv_tm b1 \u fc_fv_tm b3)
      _ _ _ _ _ _ _ _ _ b2 (a_Pi rho A1 (fc_close_tm_tm 0 x T2))).
    + exact J.
    + intros; apply Body; fsetdec.
    + intros y Fy; apply fc_tmcast_open_tm; eapply fc_co_degree; exact J.
    + exact K1.
    + exact K2.
    + intros; apply R1; fsetdec.
    + intros; apply R3; fsetdec.
    + apply (An_Abs (dom G \u fc_fv_tm b2)).
      * exact K1.
      * intros y Fy. apply (fc_tabstract_typ G A1 x q T2 W K1 ltac:(fsetdec) FA1 U2 y); fsetdec.
      * intros; apply R2; fsetdec.
  - fc_sub_e n sub G D g1 W a b J.
    fc_sub_e n sub G D g2 W u v K.
    destruct (fc_eq_types G D g1 a b W J) as [[A B] [TA TB]].
    destruct (fc_eq_types G D g2 u v W K) as [[U V] [TU TV]].
    cbn in *.
    destruct (fc_app_check G a rho u A U TA TU) as [[AT T1]|N]; [|fc_no_co].
    destruct (fc_app_check G b rho v B V TB TV) as [[BT T2]|N]; [|fc_no_co].
    left; exists (a_App a rho u, a_App b rho v); cbn.
    destruct (fc_reg_app G D rho g2 a u b v AT BT W K
      (fc_defeq_reg G D g1 a b J W) T1 T2) as [h H].
    eapply An_AppCong; eassumption.
  - fc_sub_e n sub G D g W X Y J.
    destruct X; try solve [fc_no_co].
    destruct Y; try solve [fc_no_co].
    destruct (fc_rel_dec rho rho0) as [->|N]; [|fc_no_co].
    fc_co_success X1 Y1 An_PiFst.
  - fc_sub_i n sub G D g W phi psi J.
    destruct phi as [a b A], psi as [u v B].
    fc_co_success A B An_IsoSnd.
  - fc_sub_e n sub G D g1 W X Y J.
    destruct X; try solve [fc_no_co].
    destruct Y; try solve [fc_no_co].
    destruct (fc_rel_dec rho rho0) as [->|N]; [|fc_no_co].
    fc_sub_e n sub G D g2 W a b K.
    destruct (fc_eq_types G D g2 a b W K) as [[A B] [TA TB]]; cbn in *.
    destruct (fc_eq_tm A X1) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm B Y1) as [->|N]; [|fc_no_co].
    fc_co_success (open_tm_wrt_tm X2 a) (open_tm_wrt_tm Y2 b) An_PiSnd.
  - fc_sub_i n sub G D g1 W phi psi J.
    destruct (fc_iso_reg G D g1 phi psi J W) as [K1 K2].
    pose (x := fc_pick G (fc_fv_co g1 \u fc_fv_co g2)).
    pose proof (fc_pick_spec G (fc_fv_co g1 \u fc_fv_co g2)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_co g1 \u fc_fv_co g2)) as Dx; fold x in Dx.
    assert (Nd : x `notin` D) by (intro I; apply Dx, AD, I).
    destruct (fc_iso_free _ _ _ _ _ J x ltac:(fsetdec) ltac:(fsetdec)) as [FA1 FA2].
    pose proof (An_ConsCo G x phi W K1 Dx) as W'.
    pose proof (fc_subset_extend D G x (Co phi) AD) as AD'.
    destruct (fc_check_e n sub ((x,Co phi)::G) D (open_co_wrt_co g2 (g_Var_f x)) W' AD'
          ltac:(fc_size_bound)) as [[[p q] K]|N].
    2: { fc_no_co. eapply N. eapply (fc_fresh_c_eq L); eassumption. }
    cbn in K.
    pose (b1 := fc_close_co_tm 0 x p).
    pose (b2 := fc_close_co_tm 0 x q).
    pose (b3 := fc_cocast_tm 0 g1 b2).
    assert (Body : forall y, y \notin dom G -> AnnDefEq ((y,Co phi)::G) D
        (open_co_wrt_co g2 (g_Var_f y))
        (open_tm_wrt_co b1 (g_Var_f y)) (open_tm_wrt_co b2 (g_Var_f y))).
    { pose proof (fc_cabstract_eq G D phi x _ p q W K1 ltac:(fsetdec) FA1 Nd K) as Q.
      now rewrite fc_co_close_c in Q by fsetdec. }
    destruct (fc_eq_types ((x,Co phi)::G) D _ p q W' K) as [[T1 T2] [U1 U2]]; cbn in *.
    destruct (fc_eq_tm T1 a_Star) as [->|N].
    2: { fc_no_co. fc_body_align_c.
         assert (P : AnnTyping ((x,Co phi)::G) p a_Star).
         { rewrite <- (proj1 fc_copen_after_close p 0 x).
           change (AnnTyping ((x,Co phi)::G) (open_tm_wrt_co b1 (g_Var_f x)) a_Star).
           unfold b1, b2; eapply fc_cpi_at; eassumption. }
         fc_align; contradiction. }
    destruct (fc_eq_tm T2 a_Star) as [->|N].
    2: { fc_no_co. fc_body_align_c.
         assert (P : AnnTyping ((x,Co phi)::G) q a_Star).
         { rewrite <- (proj1 fc_copen_after_close q 0 x).
           change (AnnTyping ((x,Co phi)::G) (open_tm_wrt_co b2 (g_Var_f x)) a_Star).
           unfold b1, b2; eapply fc_cpi_at; eassumption. }
         fc_align; contradiction. }
    pose proof (fc_cabstract_typ G phi x p a_Star W K1 ltac:(fsetdec) FA1 U1) as T1o.
    pose proof (fc_cabstract_typ G phi x q a_Star W K1 ltac:(fsetdec) FA1 U2) as T2o.
    left; exists (a_CPi phi b1, a_CPi psi b3); cbn.
    eapply (An_CPiCong (dom G) _ _ _ _ _ _ _ _ b2).
    + exact J.
    + exact Body.
    + intros y Fy; apply fc_cocast_open_tm; eapply fc_iso_degree; exact J.
    + apply (An_CPi (dom G)); assumption.
    + apply (An_CPi (dom G)); [exact K2|].
      intros y Fy. eapply (fc_ccast_typ G D _ phi psi b2 a_Star); eassumption.
    + apply (An_CPi (dom G)); assumption.
  - fc_sub_i n sub G D g1 W phi psi J.
    destruct (fc_iso_reg G D g1 phi psi J W) as [K1 K2].
    pose (x := fc_pick G (fc_fv_co g1 \u fc_fv_co g2)).
    pose proof (fc_pick_spec G (fc_fv_co g1 \u fc_fv_co g2)) as Fx; fold x in Fx.
    pose proof (fc_pick_dom G (fc_fv_co g1 \u fc_fv_co g2)) as Dx; fold x in Dx.
    assert (Nd : x `notin` D) by (intro I; apply Dx, AD, I).
    destruct (fc_iso_free _ _ _ _ _ J x ltac:(fsetdec) ltac:(fsetdec)) as [FA1 FA2].
    pose proof (An_ConsCo G x phi W K1 Dx) as W'.
    pose proof (fc_subset_extend D G x (Co phi) AD) as AD'.
    destruct (fc_check_e n sub ((x,Co phi)::G) D (open_co_wrt_co g2 (g_Var_f x)) W' AD'
          ltac:(fc_size_bound)) as [[[p q] K]|N].
    2: { fc_no_co. eapply N. eapply (fc_fresh_c_eq L); eassumption. }
    cbn in K.
    pose (b1 := fc_close_co_tm 0 x p).
    pose (b2 := fc_close_co_tm 0 x q).
    pose (b3 := fc_cocast_tm 0 g1 b2).
    assert (Body : forall y, y \notin dom G -> AnnDefEq ((y,Co phi)::G) D
        (open_co_wrt_co g2 (g_Var_f y))
        (open_tm_wrt_co b1 (g_Var_f y)) (open_tm_wrt_co b2 (g_Var_f y))).
    { pose proof (fc_cabstract_eq G D phi x _ p q W K1 ltac:(fsetdec) FA1 Nd K) as Q.
      now rewrite fc_co_close_c in Q by fsetdec. }
    destruct (fc_eq_types ((x,Co phi)::G) D _ p q W' K) as [[T1 T2] [U1 U2]]; cbn in *.
    pose (C1 := fc_close_co_tm 0 x T1).
    pose (C2 := fc_close_co_tm 0 x T2).
    pose (C3 := fc_cocast_tm 0 g1 C2).
    assert (Q1 : AnnTyping G (a_CAbs phi b1) (a_CPi phi C1)).
    { apply (An_CAbs (dom G)); [exact K1|].
      eapply (fc_cabstract_typ G phi x); try eassumption; fsetdec. }
    assert (Q2 : AnnTyping G (a_CAbs phi b2) (a_CPi phi C2)).
    { apply (An_CAbs (dom G)); [exact K1|].
      eapply (fc_cabstract_typ G phi x); try eassumption; fsetdec. }
    assert (Q3 : AnnTyping G (a_CAbs psi b3) (a_CPi psi C3)).
    { apply (An_CAbs (dom G)); [exact K2|].
      eapply (fc_ccast_typ G D); try eassumption.
      eapply (fc_cabstract_typ G phi x); try eassumption; fsetdec. }
    fc_sub_e n sub G (dom G) g3 W A B E.
    destruct (fc_eq_tm A (a_CPi phi C1)) as [->|N].
    2: { fc_no_co. fc_body_align_c. unfold b1 in Q1; fc_align; contradiction. }
    destruct (fc_eq_tm B (a_CPi psi C3)) as [->|N].
    2: { fc_no_co. fc_body_align_c.
         unfold b3, b2 in Q3.
         match goal with S : forall y : _, _ -> open_tm_wrt_co _ _ =
            open_tm_wrt_co _ (g_Cast _ _) |- _ =>
           rewrite (fc_ccast_cofinite _ _ _ _ (fc_iso_degree _ _ _ _ _ J) S) in Q3
         end.
         fc_align; contradiction. }
    left; exists (a_CAbs phi b1, a_CAbs psi b3); cbn.
    eapply (An_CAbsCong (dom G) _ _ _ _ _ _ _ _ _ b2 _ _ _).
    + exact J.
    + exact Body.
    + intros y Fy; apply fc_cocast_open_tm; eapply fc_iso_degree; exact J.
    + exact Q1.
    + exact Q2.
    + exact Q3.
    + exact E.
  - fc_sub_e n sub G D g1 W a b J.
    fc_sub_e n sub G (dom G) g2 W x y E1.
    fc_sub_e n sub G (dom G) g3 W u v E2.
    destruct (fc_eq_types G D g1 a b W J) as [[A B] [TA TB]]; cbn in *.
    destruct (fc_capp_check G a g2 A x y TA E1) as [[AT T1]|N]; [|fc_no_co].
    destruct (fc_capp_check G b g3 B u v TB E2) as [[BT T2]|N]; [|fc_no_co].
    left; exists (a_CApp a g2, a_CApp b g3); cbn.
    destruct (fc_reg_capp G g2 g3 a b x y u v AT BT E1 E2
        (fc_defeq_reg G D g1 a b J W) T1 T2) as [h H].
    eapply An_CAppCong; eassumption.
  - fc_sub_e n sub G D g1 W X Y J.
    destruct X; try solve [fc_no_co].
    destruct Y; try solve [fc_no_co].
    destruct phi as [a b A], phi0 as [u v B].
    fc_sub_e n sub G (dom G) g2 W x y E1.
    fc_sub_e n sub G (dom G) g3 W p q E2.
    destruct (fc_eq_tm x a) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm y b) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm p u) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm q v) as [->|N]; [|fc_no_co].
    fc_co_success (open_tm_wrt_co X g2) (open_tm_wrt_co Y g3) An_CPiSnd.
  - fc_sub_e n sub G D g1 W a b J.
    fc_sub_i n sub G D g2 W phi psi K.
    destruct phi as [u v A], psi as [p q B].
    destruct (fc_eq_tm a u) as [->|N]; [|fc_no_co].
    destruct (fc_eq_tm b v) as [->|N]; [|fc_no_co].
    fc_co_success p q An_Cast.
Defined.

Definition fc_all_checks : forall n, fc_checks n.
Proof.
  induction n as [|n rec].
  - constructor; intros; exfalso; lia.
  - exact {| fc_check_t := fc_term_step n rec;
             fc_check_p := fc_wff_step n rec;
             fc_check_e := fc_co_step n rec;
             fc_check_i := fc_iso_step n rec |}.
Defined.

Theorem FC_typechecker : forall t : tm,
  { T : tm | AnnTyping nil t T } + { forall T, ~ AnnTyping nil t T }.
Proof.
  intro t.
  exact (fc_check_t _ (fc_all_checks (S (fc_size_tm t))) nil t An_Empty
           (Nat.lt_succ_diag_r _)).
Defined.
