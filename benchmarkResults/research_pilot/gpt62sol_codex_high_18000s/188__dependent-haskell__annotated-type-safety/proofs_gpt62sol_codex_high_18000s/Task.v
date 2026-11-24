Require Import Language.

Inductive erased_sort : sort -> Prop :=
| erased_Tm : forall a, erased_tm a -> erased_sort (Tm a)
| erased_Co : forall a b A, erased_tm a -> erased_tm b -> erased_tm A -> erased_sort (Co (Eq a b A)).

Definition erased_context : context -> Prop :=
  Forall (fun p => match p with (a,s) => erased_sort s end).

Definition Good (G : context) (D : available_props):=
  erased_context G /\
  forall c1 A B1 T1,
    binds c1 (Co (Eq A B1 T1)) G
    -> c1 `in` D
    -> exists C, Par G D A C /\ Par G D B1 C.

Definition AnnGood G D := Good (erase_context G) D.

Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm_tm_tm (erase_tm a)) /\ AnnGood G D.

From Stdlib Require Import Lia.

(* Mutual induction principles. *)
Scheme tm_ind' := Induction for tm Sort Prop
with brs_ind' := Induction for brs Sort Prop
with co_ind' := Induction for co Sort Prop
with constraint_ind' := Induction for constraint Sort Prop.
Combined Scheme syntax_ind from tm_ind', brs_ind', co_ind', constraint_ind'.

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop
with lc_brs_ind' := Induction for lc_brs Sort Prop
with lc_co_ind' := Induction for lc_co Sort Prop
with lc_constraint_ind' := Induction for lc_constraint Sort Prop.
Combined Scheme lc_syntax_ind from lc_tm_ind', lc_brs_ind', lc_co_ind', lc_constraint_ind'.

Scheme typing_ind' := Induction for AnnTyping Sort Prop
with prop_ind' := Induction for AnnPropWff Sort Prop
with iso_ind' := Induction for AnnIso Sort Prop
with eq_ind' := Induction for AnnDefEq Sort Prop
with ctx_ind' := Induction for AnnCtx Sort Prop.
Combined Scheme ann_ind from typing_ind', prop_ind', iso_ind', eq_ind', ctx_ind'.

#[local] Hint Constructors lc_tm lc_constraint lc_co lc_brs : lc.
#[local] Hint Constructors AnnTyping AnnPropWff AnnIso AnnDefEq AnnCtx : ann.

(* Weakening in an annotated context. *)
Lemma binds_dom_subset (G E : context) :
  (forall x s, binds x s G -> binds x s E) -> dom G [<=] dom E.
Proof.
  intros H x Hx. apply binds_In_inv in Hx as [s Hs].
  eapply binds_In; eauto.
Qed.

Lemma ann_weakening_mut :
  (forall G a A, AnnTyping G a A -> forall E, AnnCtx E ->
    (forall x s, binds x s G -> binds x s E) -> AnnTyping E a A) /\
  (forall G p, AnnPropWff G p -> forall E, AnnCtx E ->
    (forall x s, binds x s G -> binds x s E) -> AnnPropWff E p) /\
  (forall G D g p q, AnnIso G D g p q -> forall E D', AnnCtx E ->
    (forall x s, binds x s G -> binds x s E) -> D [<=] D' -> AnnIso E D' g p q) /\
  (forall G D g a b, AnnDefEq G D g a b -> forall E D', AnnCtx E ->
    (forall x s, binds x s G -> binds x s E) -> D [<=] D' -> AnnDefEq E D' g a b) /\
  (forall G, AnnCtx G -> True).
Proof.
  apply ann_ind; intros.
  all: try solve [eauto 5 using binds_dom_subset with ann].
  all: try match goal with
  | |- AnnTyping _ (a_Conv _ _) _ => eapply An_Conv
  | |- AnnIso _ _ (g_EqCong _ _ _) _ _ => eapply An_PropCong
  | |- AnnDefEq _ _ (g_Refl2 _ _ _) _ _ => eapply An_EraseEq
  | |- AnnDefEq _ _ (g_Sym _) _ _ => eapply An_Sym
  | |- AnnDefEq _ _ (g_Trans _ _) _ _ => eapply An_Trans
  | |- AnnDefEq _ _ (g_AppCong _ _ _) _ _ => eapply An_AppCong
  | |- AnnDefEq _ _ (g_PiSnd _ _) _ _ => eapply An_PiSnd
  | |- AnnDefEq _ _ (g_CAppCong _ _ _) _ _ => eapply An_CAppCong
  | |- AnnDefEq _ _ (g_CPiSnd _ _ _) _ _ => eapply An_CPiSnd
  end.
  all: try solve [eauto 6 using binds_dom_subset].
  all: try match goal with
  | |- AnnTyping ?E (a_Pi _ _ _) _ => eapply An_Pi with (L := L \u dom E)
  | |- AnnTyping ?E (a_Abs _ _ _) _ => eapply An_Abs with (L := L \u dom E)
  | |- AnnTyping ?E (a_CPi _ _) _ => eapply An_CPi with (L := L \u dom E)
  | |- AnnTyping ?E (a_CAbs _ _) _ => eapply An_CAbs with (L := L \u dom E)
  | |- AnnDefEq ?E _ (g_PiCong _ _ _) _ _ => eapply An_PiCong with (L := L \u dom E)
  | |- AnnDefEq ?E _ (g_AbsCong _ _ _) _ _ => eapply An_AbsCong with (L := L \u dom E)
  | |- AnnDefEq ?E _ (g_CPiCong _ _) _ _ => eapply An_CPiCong with (L := L \u dom E)
  | |- AnnDefEq ?E _ (g_CAbsCong _ _ _) _ _ => eapply An_CAbsCong with (L := L \u dom E)
  end.
  all: try solve [eauto 5 using binds_dom_subset with ann].
  all: try (intros x Hx; solve [eauto | eapply H; fsetdec]).
  all: try match goal with
  | [ |- forall _, _ ] =>
      intros x Hx;
      match goal with
      | [ IH : forall y, y \notin ?L -> forall E : context, _ |- _ ] =>
          eapply (IH x ltac:(fsetdec))
      end
  end.
  all: try solve [intros y s Hb; apply binds_app_iff in Hb as [Hb|Hb];
                  apply binds_app_iff; eauto].
  all: try solve [assumption].
  all: try match goal with
  | |- AnnCtx ((?x ~ Tm ?A) ++ ?E) =>
      apply An_ConsTm; [assumption | | fsetdec];
      first [solve [eauto] |
        match goal with
        | IH : forall E, AnnCtx E -> _ -> AnnTyping E (a_Pi _ A _) _ |- _ =>
            let H := fresh in
            pose proof (IH E ltac:(assumption) ltac:(assumption)) as H;
            inversion H; assumption
        end]
  | |- AnnCtx ((?x ~ Co ?p) ++ ?E) =>
      apply An_ConsCo; [assumption | | fsetdec];
      first [solve [eauto] |
        match goal with
        | IH : forall E, AnnCtx E -> _ -> AnnTyping E (a_CPi p _) _ |- _ =>
            let H := fresh in
            pose proof (IH E ltac:(assumption) ltac:(assumption)) as H;
            inversion H; assumption
        | IH : forall E, AnnCtx E -> _ -> AnnTyping E (a_CAbs p _) _ |- _ =>
            let H := fresh in
            pose proof (IH E ltac:(assumption) ltac:(assumption)) as H;
            inversion H; assumption
        end]
  end.
Qed.
(* Opening, free substitution, and local closure. *)
Fixpoint scoped_tm (nt nc : nat) (e : tm) {struct e} : Prop :=
  match e with
  | a_Star => True
  | (a_Var_b nat) => nat < nt
  | (a_Var_f x) => True
  | (a_Abs rho A b) => scoped_tm nt nc A /\ scoped_tm (S nt) nc b
  | (a_UAbs rho b) => scoped_tm (S nt) nc b
  | (a_App a rho b) => scoped_tm nt nc a /\ scoped_tm nt nc b
  | (a_Fam F) => True
  | (a_Const T) => True
  | (a_Pi rho A B) => scoped_tm nt nc A /\ scoped_tm (S nt) nc B
  | (a_Conv a g) => scoped_tm nt nc a /\ scoped_co nt nc g
  | (a_CPi phi B) => scoped_constraint nt nc phi /\ scoped_tm nt (S nc) B
  | (a_CAbs phi b) => scoped_constraint nt nc phi /\ scoped_tm nt (S nc) b
  | (a_UCAbs b) => scoped_tm nt (S nc) b
  | (a_CApp a g) => scoped_tm nt nc a /\ scoped_co nt nc g
  | a_Bullet => True
  | (a_DataCon K) => True
  | (a_Case a brs5) => scoped_tm nt nc a /\ scoped_brs nt nc brs5
  end
with scoped_brs (nt nc : nat) (e : brs) {struct e} : Prop :=
  match e with
  | br_None => True
  | (br_One K a brs5) => scoped_tm nt nc a /\ scoped_brs nt nc brs5
  end
with scoped_co (nt nc : nat) (e : co) {struct e} : Prop :=
  match e with
  | g_Triv => True
  | (g_Var_b nat) => nat < nc
  | (g_Var_f c) => True
  | (g_Beta a b) => scoped_tm nt nc a /\ scoped_tm nt nc b
  | (g_Refl a) => scoped_tm nt nc a
  | (g_Refl2 a b g) => scoped_tm nt nc a /\ scoped_tm nt nc b /\ scoped_co nt nc g
  | (g_Sym g) => scoped_co nt nc g
  | (g_Trans g1 g2) => scoped_co nt nc g1 /\ scoped_co nt nc g2
  | (g_PiCong rho g1 g2) => scoped_co nt nc g1 /\ scoped_co (S nt) nc g2
  | (g_AbsCong rho g1 g2) => scoped_co nt nc g1 /\ scoped_co (S nt) nc g2
  | (g_AppCong g1 rho g2) => scoped_co nt nc g1 /\ scoped_co nt nc g2
  | (g_PiFst g) => scoped_co nt nc g
  | (g_CPiFst g) => scoped_co nt nc g
  | (g_IsoSnd g) => scoped_co nt nc g
  | (g_PiSnd g1 g2) => scoped_co nt nc g1 /\ scoped_co nt nc g2
  | (g_CPiCong g1 g3) => scoped_co nt nc g1 /\ scoped_co nt (S nc) g3
  | (g_CAbsCong g1 g3 g4) => scoped_co nt nc g1 /\ scoped_co nt (S nc) g3 /\ scoped_co nt nc g4
  | (g_CAppCong g g1 g2) => scoped_co nt nc g /\ scoped_co nt nc g1 /\ scoped_co nt nc g2
  | (g_CPiSnd g g1 g2) => scoped_co nt nc g /\ scoped_co nt nc g1 /\ scoped_co nt nc g2
  | (g_Cast g1 g2) => scoped_co nt nc g1 /\ scoped_co nt nc g2
  | (g_EqCong g1 A g2) => scoped_co nt nc g1 /\ scoped_tm nt nc A /\ scoped_co nt nc g2
  | (g_IsoConv phi1 phi2 g) => scoped_constraint nt nc phi1 /\ scoped_constraint nt nc phi2 /\ scoped_co nt nc g
  | (g_Eta a) => scoped_tm nt nc a
  | (g_Left g g') => scoped_co nt nc g /\ scoped_co nt nc g'
  | (g_Right g g') => scoped_co nt nc g /\ scoped_co nt nc g'
  end
with scoped_constraint (nt nc : nat) (e : constraint) {struct e} : Prop :=
  match e with
  | (Eq a b A) => scoped_tm nt nc a /\ scoped_tm nt nc b /\ scoped_tm nt nc A
  end.

Fixpoint syntax_size_tm  (e : tm) {struct e} : nat :=
  match e with
  | a_Star => 1
  | (a_Var_b nat) => 1
  | (a_Var_f x) => 1
  | (a_Abs rho A b) => S (syntax_size_tm A + syntax_size_tm b)
  | (a_UAbs rho b) => S (syntax_size_tm b)
  | (a_App a rho b) => S (syntax_size_tm a + syntax_size_tm b)
  | (a_Fam F) => 1
  | (a_Const T) => 1
  | (a_Pi rho A B) => S (syntax_size_tm A + syntax_size_tm B)
  | (a_Conv a g) => S (syntax_size_tm a + syntax_size_co g)
  | (a_CPi phi B) => S (syntax_size_constraint phi + syntax_size_tm B)
  | (a_CAbs phi b) => S (syntax_size_constraint phi + syntax_size_tm b)
  | (a_UCAbs b) => S (syntax_size_tm b)
  | (a_CApp a g) => S (syntax_size_tm a + syntax_size_co g)
  | a_Bullet => 1
  | (a_DataCon K) => 1
  | (a_Case a brs5) => S (syntax_size_tm a + syntax_size_brs brs5)
  end
with syntax_size_brs  (e : brs) {struct e} : nat :=
  match e with
  | br_None => 1
  | (br_One K a brs5) => S (syntax_size_tm a + syntax_size_brs brs5)
  end
with syntax_size_co  (e : co) {struct e} : nat :=
  match e with
  | g_Triv => 1
  | (g_Var_b nat) => 1
  | (g_Var_f c) => 1
  | (g_Beta a b) => S (syntax_size_tm a + syntax_size_tm b)
  | (g_Refl a) => S (syntax_size_tm a)
  | (g_Refl2 a b g) => S (syntax_size_tm a + syntax_size_tm b + syntax_size_co g)
  | (g_Sym g) => S (syntax_size_co g)
  | (g_Trans g1 g2) => S (syntax_size_co g1 + syntax_size_co g2)
  | (g_PiCong rho g1 g2) => S (syntax_size_co g1 + syntax_size_co g2)
  | (g_AbsCong rho g1 g2) => S (syntax_size_co g1 + syntax_size_co g2)
  | (g_AppCong g1 rho g2) => S (syntax_size_co g1 + syntax_size_co g2)
  | (g_PiFst g) => S (syntax_size_co g)
  | (g_CPiFst g) => S (syntax_size_co g)
  | (g_IsoSnd g) => S (syntax_size_co g)
  | (g_PiSnd g1 g2) => S (syntax_size_co g1 + syntax_size_co g2)
  | (g_CPiCong g1 g3) => S (syntax_size_co g1 + syntax_size_co g3)
  | (g_CAbsCong g1 g3 g4) => S (syntax_size_co g1 + syntax_size_co g3 + syntax_size_co g4)
  | (g_CAppCong g g1 g2) => S (syntax_size_co g + syntax_size_co g1 + syntax_size_co g2)
  | (g_CPiSnd g g1 g2) => S (syntax_size_co g + syntax_size_co g1 + syntax_size_co g2)
  | (g_Cast g1 g2) => S (syntax_size_co g1 + syntax_size_co g2)
  | (g_EqCong g1 A g2) => S (syntax_size_co g1 + syntax_size_tm A + syntax_size_co g2)
  | (g_IsoConv phi1 phi2 g) => S (syntax_size_constraint phi1 + syntax_size_constraint phi2 + syntax_size_co g)
  | (g_Eta a) => S (syntax_size_tm a)
  | (g_Left g g') => S (syntax_size_co g + syntax_size_co g')
  | (g_Right g g') => S (syntax_size_co g + syntax_size_co g')
  end
with syntax_size_constraint  (e : constraint) {struct e} : nat :=
  match e with
  | (Eq a b A) => S (syntax_size_tm a + syntax_size_tm b + syntax_size_tm A)
  end.

Fixpoint support_tm  (e : tm) {struct e} : atoms :=
  match e with
  | a_Star => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_Abs rho A b) => support_tm A \u support_tm b
  | (a_UAbs rho b) => support_tm b
  | (a_App a rho b) => support_tm a \u support_tm b
  | (a_Fam F) => {}
  | (a_Const T) => {}
  | (a_Pi rho A B) => support_tm A \u support_tm B
  | (a_Conv a g) => support_tm a \u support_co g
  | (a_CPi phi B) => support_constraint phi \u support_tm B
  | (a_CAbs phi b) => support_constraint phi \u support_tm b
  | (a_UCAbs b) => support_tm b
  | (a_CApp a g) => support_tm a \u support_co g
  | a_Bullet => {}
  | (a_DataCon K) => {}
  | (a_Case a brs5) => support_tm a \u support_brs brs5
  end
with support_brs  (e : brs) {struct e} : atoms :=
  match e with
  | br_None => {}
  | (br_One K a brs5) => support_tm a \u support_brs brs5
  end
with support_co  (e : co) {struct e} : atoms :=
  match e with
  | g_Triv => {}
  | (g_Var_b nat) => {}
  | (g_Var_f c) => {{c}}
  | (g_Beta a b) => support_tm a \u support_tm b
  | (g_Refl a) => support_tm a
  | (g_Refl2 a b g) => support_tm a \u support_tm b \u support_co g
  | (g_Sym g) => support_co g
  | (g_Trans g1 g2) => support_co g1 \u support_co g2
  | (g_PiCong rho g1 g2) => support_co g1 \u support_co g2
  | (g_AbsCong rho g1 g2) => support_co g1 \u support_co g2
  | (g_AppCong g1 rho g2) => support_co g1 \u support_co g2
  | (g_PiFst g) => support_co g
  | (g_CPiFst g) => support_co g
  | (g_IsoSnd g) => support_co g
  | (g_PiSnd g1 g2) => support_co g1 \u support_co g2
  | (g_CPiCong g1 g3) => support_co g1 \u support_co g3
  | (g_CAbsCong g1 g3 g4) => support_co g1 \u support_co g3 \u support_co g4
  | (g_CAppCong g g1 g2) => support_co g \u support_co g1 \u support_co g2
  | (g_CPiSnd g g1 g2) => support_co g \u support_co g1 \u support_co g2
  | (g_Cast g1 g2) => support_co g1 \u support_co g2
  | (g_EqCong g1 A g2) => support_co g1 \u support_tm A \u support_co g2
  | (g_IsoConv phi1 phi2 g) => support_constraint phi1 \u support_constraint phi2 \u support_co g
  | (g_Eta a) => support_tm a
  | (g_Left g g') => support_co g \u support_co g'
  | (g_Right g g') => support_co g \u support_co g'
  end
with support_constraint  (e : constraint) {struct e} : atoms :=
  match e with
  | (Eq a b A) => support_tm a \u support_tm b \u support_tm A
  end.

Fixpoint subst_free_tm (ft : atom -> tm) (fc : atom -> co) (e : tm) {struct e} : tm :=
  match e with
  | a_Star => a_Star
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => ft x
  | (a_Abs rho A b) => a_Abs rho (subst_free_tm ft fc A) (subst_free_tm ft fc b)
  | (a_UAbs rho b) => a_UAbs rho (subst_free_tm ft fc b)
  | (a_App a rho b) => a_App (subst_free_tm ft fc a) rho (subst_free_tm ft fc b)
  | (a_Fam F) => a_Fam F
  | (a_Const T) => a_Const T
  | (a_Pi rho A B) => a_Pi rho (subst_free_tm ft fc A) (subst_free_tm ft fc B)
  | (a_Conv a g) => a_Conv (subst_free_tm ft fc a) (subst_free_co ft fc g)
  | (a_CPi phi B) => a_CPi (subst_free_constraint ft fc phi) (subst_free_tm ft fc B)
  | (a_CAbs phi b) => a_CAbs (subst_free_constraint ft fc phi) (subst_free_tm ft fc b)
  | (a_UCAbs b) => a_UCAbs (subst_free_tm ft fc b)
  | (a_CApp a g) => a_CApp (subst_free_tm ft fc a) (subst_free_co ft fc g)
  | a_Bullet => a_Bullet
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (subst_free_tm ft fc a) (subst_free_brs ft fc brs5)
  end
with subst_free_brs (ft : atom -> tm) (fc : atom -> co) (e : brs) {struct e} : brs :=
  match e with
  | br_None => br_None
  | (br_One K a brs5) => br_One K (subst_free_tm ft fc a) (subst_free_brs ft fc brs5)
  end
with subst_free_co (ft : atom -> tm) (fc : atom -> co) (e : co) {struct e} : co :=
  match e with
  | g_Triv => g_Triv
  | (g_Var_b nat) => g_Var_b nat
  | (g_Var_f c) => fc c
  | (g_Beta a b) => g_Beta (subst_free_tm ft fc a) (subst_free_tm ft fc b)
  | (g_Refl a) => g_Refl (subst_free_tm ft fc a)
  | (g_Refl2 a b g) => g_Refl2 (subst_free_tm ft fc a) (subst_free_tm ft fc b) (subst_free_co ft fc g)
  | (g_Sym g) => g_Sym (subst_free_co ft fc g)
  | (g_Trans g1 g2) => g_Trans (subst_free_co ft fc g1) (subst_free_co ft fc g2)
  | (g_PiCong rho g1 g2) => g_PiCong rho (subst_free_co ft fc g1) (subst_free_co ft fc g2)
  | (g_AbsCong rho g1 g2) => g_AbsCong rho (subst_free_co ft fc g1) (subst_free_co ft fc g2)
  | (g_AppCong g1 rho g2) => g_AppCong (subst_free_co ft fc g1) rho (subst_free_co ft fc g2)
  | (g_PiFst g) => g_PiFst (subst_free_co ft fc g)
  | (g_CPiFst g) => g_CPiFst (subst_free_co ft fc g)
  | (g_IsoSnd g) => g_IsoSnd (subst_free_co ft fc g)
  | (g_PiSnd g1 g2) => g_PiSnd (subst_free_co ft fc g1) (subst_free_co ft fc g2)
  | (g_CPiCong g1 g3) => g_CPiCong (subst_free_co ft fc g1) (subst_free_co ft fc g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (subst_free_co ft fc g1) (subst_free_co ft fc g3) (subst_free_co ft fc g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (subst_free_co ft fc g) (subst_free_co ft fc g1) (subst_free_co ft fc g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (subst_free_co ft fc g) (subst_free_co ft fc g1) (subst_free_co ft fc g2)
  | (g_Cast g1 g2) => g_Cast (subst_free_co ft fc g1) (subst_free_co ft fc g2)
  | (g_EqCong g1 A g2) => g_EqCong (subst_free_co ft fc g1) (subst_free_tm ft fc A) (subst_free_co ft fc g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (subst_free_constraint ft fc phi1) (subst_free_constraint ft fc phi2) (subst_free_co ft fc g)
  | (g_Eta a) => g_Eta (subst_free_tm ft fc a)
  | (g_Left g g') => g_Left (subst_free_co ft fc g) (subst_free_co ft fc g')
  | (g_Right g g') => g_Right (subst_free_co ft fc g) (subst_free_co ft fc g')
  end
with subst_free_constraint (ft : atom -> tm) (fc : atom -> co) (e : constraint) {struct e} : constraint :=
  match e with
  | (Eq a b A) => Eq (subst_free_tm ft fc a) (subst_free_tm ft fc b) (subst_free_tm ft fc A)
  end.

Fixpoint close_term_tm (k : nat) (y : atom) (e : tm) {struct e} : tm :=
  match e with
  | a_Star => a_Star
  | (a_Var_b nat) => if le_lt_dec k nat then a_Var_b (S nat) else a_Var_b nat
  | (a_Var_f x) => if y == x then a_Var_b k else a_Var_f x
  | (a_Abs rho A b) => a_Abs rho (close_term_tm k y A) (close_term_tm (S k) y b)
  | (a_UAbs rho b) => a_UAbs rho (close_term_tm (S k) y b)
  | (a_App a rho b) => a_App (close_term_tm k y a) rho (close_term_tm k y b)
  | (a_Fam F) => a_Fam F
  | (a_Const T) => a_Const T
  | (a_Pi rho A B) => a_Pi rho (close_term_tm k y A) (close_term_tm (S k) y B)
  | (a_Conv a g) => a_Conv (close_term_tm k y a) (close_term_co k y g)
  | (a_CPi phi B) => a_CPi (close_term_constraint k y phi) (close_term_tm k y B)
  | (a_CAbs phi b) => a_CAbs (close_term_constraint k y phi) (close_term_tm k y b)
  | (a_UCAbs b) => a_UCAbs (close_term_tm k y b)
  | (a_CApp a g) => a_CApp (close_term_tm k y a) (close_term_co k y g)
  | a_Bullet => a_Bullet
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (close_term_tm k y a) (close_term_brs k y brs5)
  end
with close_term_brs (k : nat) (y : atom) (e : brs) {struct e} : brs :=
  match e with
  | br_None => br_None
  | (br_One K a brs5) => br_One K (close_term_tm k y a) (close_term_brs k y brs5)
  end
with close_term_co (k : nat) (y : atom) (e : co) {struct e} : co :=
  match e with
  | g_Triv => g_Triv
  | (g_Var_b nat) => g_Var_b nat
  | (g_Var_f c) => g_Var_f c
  | (g_Beta a b) => g_Beta (close_term_tm k y a) (close_term_tm k y b)
  | (g_Refl a) => g_Refl (close_term_tm k y a)
  | (g_Refl2 a b g) => g_Refl2 (close_term_tm k y a) (close_term_tm k y b) (close_term_co k y g)
  | (g_Sym g) => g_Sym (close_term_co k y g)
  | (g_Trans g1 g2) => g_Trans (close_term_co k y g1) (close_term_co k y g2)
  | (g_PiCong rho g1 g2) => g_PiCong rho (close_term_co k y g1) (close_term_co (S k) y g2)
  | (g_AbsCong rho g1 g2) => g_AbsCong rho (close_term_co k y g1) (close_term_co (S k) y g2)
  | (g_AppCong g1 rho g2) => g_AppCong (close_term_co k y g1) rho (close_term_co k y g2)
  | (g_PiFst g) => g_PiFst (close_term_co k y g)
  | (g_CPiFst g) => g_CPiFst (close_term_co k y g)
  | (g_IsoSnd g) => g_IsoSnd (close_term_co k y g)
  | (g_PiSnd g1 g2) => g_PiSnd (close_term_co k y g1) (close_term_co k y g2)
  | (g_CPiCong g1 g3) => g_CPiCong (close_term_co k y g1) (close_term_co k y g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (close_term_co k y g1) (close_term_co k y g3) (close_term_co k y g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (close_term_co k y g) (close_term_co k y g1) (close_term_co k y g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (close_term_co k y g) (close_term_co k y g1) (close_term_co k y g2)
  | (g_Cast g1 g2) => g_Cast (close_term_co k y g1) (close_term_co k y g2)
  | (g_EqCong g1 A g2) => g_EqCong (close_term_co k y g1) (close_term_tm k y A) (close_term_co k y g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (close_term_constraint k y phi1) (close_term_constraint k y phi2) (close_term_co k y g)
  | (g_Eta a) => g_Eta (close_term_tm k y a)
  | (g_Left g g') => g_Left (close_term_co k y g) (close_term_co k y g')
  | (g_Right g g') => g_Right (close_term_co k y g) (close_term_co k y g')
  end
with close_term_constraint (k : nat) (y : atom) (e : constraint) {struct e} : constraint :=
  match e with
  | (Eq a b A) => Eq (close_term_tm k y a) (close_term_tm k y b) (close_term_tm k y A)
  end.

Lemma scoped_mono :
  (forall e : tm, forall nt nc nt' nc', nt <= nt' -> nc <= nc' -> scoped_tm nt nc e -> scoped_tm nt' nc' e) /\
  (forall e : brs, forall nt nc nt' nc', nt <= nt' -> nc <= nc' -> scoped_brs nt nc e -> scoped_brs nt' nc' e) /\
  (forall e : co, forall nt nc nt' nc', nt <= nt' -> nc <= nc' -> scoped_co nt nc e -> scoped_co nt' nc' e) /\
  (forall e : constraint, forall nt nc nt' nc', nt <= nt' -> nc <= nc' -> scoped_constraint nt nc e -> scoped_constraint nt' nc' e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try lia.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: repeat split; try assumption; try exact I.
  all: match goal with
  | IH : forall nt nc nt' nc', _ -> _ -> ?P nt nc ?e -> ?P nt' nc' ?e,
    H : ?P ?n ?m ?e |- ?P ?n' ?m' ?e =>
      exact (IH n m n' m' ltac:(lia) ltac:(lia) H)
  end.
Qed.
Definition scoped_mono_tm := proj1 (scoped_mono).
Definition scoped_mono_co := proj1 (proj2 (proj2 (scoped_mono))).

Lemma scoped_open_tm :
  (forall e : tm, forall k (u : tm) nt nc, k <= nt -> scoped_tm nt nc u ->
   (scoped_tm nt nc (open_tm_wrt_tm_rec k u e) <-> scoped_tm (S nt) nc e)) /\
  (forall e : brs, forall k (u : tm) nt nc, k <= nt -> scoped_tm nt nc u ->
   (scoped_brs nt nc (open_brs_wrt_tm_rec k u e) <-> scoped_brs (S nt) nc e)) /\
  (forall e : co, forall k (u : tm) nt nc, k <= nt -> scoped_tm nt nc u ->
   (scoped_co nt nc (open_co_wrt_tm_rec k u e) <-> scoped_co (S nt) nc e)) /\
  (forall e : constraint, forall k (u : tm) nt nc, k <= nt -> scoped_tm nt nc u ->
   (scoped_constraint nt nc (open_constraint_wrt_tm_rec k u e) <-> scoped_constraint (S nt) nc e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try match goal with
  | |- context [lt_eq_lt_dec ?i ?k] =>
      destruct (lt_eq_lt_dec i k) as [[?|?]|?]; simpl; split; intro; first [assumption | lia]
  end.
  all: try reflexivity.
  all: repeat match goal with
  | IH : forall k u nt nc, _ -> _ -> _ <-> _, H : scoped_tm ?a ?b ?u |- _ =>
      first [rewrite (IH k u nt nc) by (first [lia | assumption])
            |rewrite (IH (S k) u (S nt) nc) by (first [lia | eapply scoped_mono_tm; [| |exact H]; lia])
            |rewrite (IH k u (S nt) nc) by (first [lia | eapply scoped_mono_tm; [| |exact H]; lia])
            |rewrite (IH (S k) u nt (S nc)) by (first [lia | eapply scoped_mono_tm; [| |exact H]; lia])
            |rewrite (IH k u nt (S nc)) by (first [lia | eapply scoped_mono_tm; [| |exact H]; lia])]
  end; reflexivity.
Qed.
Definition scoped_open_tm_tm := proj1 (scoped_open_tm).
Definition scoped_open_tm_co := proj1 (proj2 (proj2 (scoped_open_tm))).

Lemma open_scoped_identity_tm :
  (forall e : tm, forall nt nc (u : tm) k, scoped_tm nt nc e -> nt <= k -> open_tm_wrt_tm_rec k u e = e) /\
  (forall e : brs, forall nt nc (u : tm) k, scoped_brs nt nc e -> nt <= k -> open_brs_wrt_tm_rec k u e = e) /\
  (forall e : co, forall nt nc (u : tm) k, scoped_co nt nc e -> nt <= k -> open_co_wrt_tm_rec k u e = e) /\
  (forall e : constraint, forall nt nc (u : tm) k, scoped_constraint nt nc e -> nt <= k -> open_constraint_wrt_tm_rec k u e = e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try reflexivity.
  all: try match goal with
  | |- context [lt_eq_lt_dec ?i ?k] =>
      destruct (lt_eq_lt_dec i k) as [[?|?]|?]; [reflexivity|lia|lia]
  end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: f_equal;
      match goal with
      | IH : forall nt nc u k, ?P nt nc ?e -> _ -> _,
        H : ?P ?n ?m ?e |- _ =>
          rewrite (IH n m u) by (first [exact H | lia]); reflexivity
      end.
Qed.
Definition open_scoped_identity_tm_tm := proj1 (open_scoped_identity_tm).
Definition open_scoped_identity_tm_co := proj1 (proj2 (proj2 (open_scoped_identity_tm))).

Lemma size_open_tm :
  (forall e : tm, forall k x, syntax_size_tm (open_tm_wrt_tm_rec k (a_Var_f x) e) = syntax_size_tm e) /\
  (forall e : brs, forall k x, syntax_size_brs (open_brs_wrt_tm_rec k (a_Var_f x) e) = syntax_size_brs e) /\
  (forall e : co, forall k x, syntax_size_co (open_co_wrt_tm_rec k (a_Var_f x) e) = syntax_size_co e) /\
  (forall e : constraint, forall k x, syntax_size_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) e) = syntax_size_constraint e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try match goal with
  | |- context [lt_eq_lt_dec ?i ?k] =>
      destruct (lt_eq_lt_dec i k) as [[?|?]|?]; reflexivity
  end.
  all: repeat first [progress rewrite H | progress rewrite H0 | progress rewrite H1]; reflexivity.
Qed.
Definition size_open_tm_tm := proj1 (size_open_tm).
Definition size_open_tm_co := proj1 (proj2 (proj2 (size_open_tm))).

Lemma scoped_open_co :
  (forall e : tm, forall k (u : co) nt nc, k <= nc -> scoped_co nt nc u ->
   (scoped_tm nt nc (open_tm_wrt_co_rec k u e) <-> scoped_tm nt (S nc) e)) /\
  (forall e : brs, forall k (u : co) nt nc, k <= nc -> scoped_co nt nc u ->
   (scoped_brs nt nc (open_brs_wrt_co_rec k u e) <-> scoped_brs nt (S nc) e)) /\
  (forall e : co, forall k (u : co) nt nc, k <= nc -> scoped_co nt nc u ->
   (scoped_co nt nc (open_co_wrt_co_rec k u e) <-> scoped_co nt (S nc) e)) /\
  (forall e : constraint, forall k (u : co) nt nc, k <= nc -> scoped_co nt nc u ->
   (scoped_constraint nt nc (open_constraint_wrt_co_rec k u e) <-> scoped_constraint nt (S nc) e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try match goal with
  | |- context [lt_eq_lt_dec ?i ?k] =>
      destruct (lt_eq_lt_dec i k) as [[?|?]|?]; simpl; split; intro; first [assumption | lia]
  end.
  all: try reflexivity.
  all: repeat match goal with
  | IH : forall k u nt nc, _ -> _ -> _ <-> _, H : scoped_co ?a ?b ?u |- _ =>
      first [rewrite (IH k u nt nc) by (first [lia | assumption])
            |rewrite (IH (S k) u (S nt) nc) by (first [lia | eapply scoped_mono_co; [| |exact H]; lia])
            |rewrite (IH k u (S nt) nc) by (first [lia | eapply scoped_mono_co; [| |exact H]; lia])
            |rewrite (IH (S k) u nt (S nc)) by (first [lia | eapply scoped_mono_co; [| |exact H]; lia])
            |rewrite (IH k u nt (S nc)) by (first [lia | eapply scoped_mono_co; [| |exact H]; lia])]
  end; reflexivity.
Qed.
Definition scoped_open_co_tm := proj1 (scoped_open_co).
Definition scoped_open_co_co := proj1 (proj2 (proj2 (scoped_open_co))).

Lemma open_scoped_identity_co :
  (forall e : tm, forall nt nc (u : co) k, scoped_tm nt nc e -> nc <= k -> open_tm_wrt_co_rec k u e = e) /\
  (forall e : brs, forall nt nc (u : co) k, scoped_brs nt nc e -> nc <= k -> open_brs_wrt_co_rec k u e = e) /\
  (forall e : co, forall nt nc (u : co) k, scoped_co nt nc e -> nc <= k -> open_co_wrt_co_rec k u e = e) /\
  (forall e : constraint, forall nt nc (u : co) k, scoped_constraint nt nc e -> nc <= k -> open_constraint_wrt_co_rec k u e = e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try reflexivity.
  all: try match goal with
  | |- context [lt_eq_lt_dec ?i ?k] =>
      destruct (lt_eq_lt_dec i k) as [[?|?]|?]; [reflexivity|lia|lia]
  end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: f_equal;
      match goal with
      | IH : forall nt nc u k, ?P nt nc ?e -> _ -> _,
        H : ?P ?n ?m ?e |- _ =>
          rewrite (IH n m u) by (first [exact H | lia]); reflexivity
      end.
Qed.
Definition open_scoped_identity_co_tm := proj1 (open_scoped_identity_co).
Definition open_scoped_identity_co_co := proj1 (proj2 (proj2 (open_scoped_identity_co))).

Lemma size_open_co :
  (forall e : tm, forall k x, syntax_size_tm (open_tm_wrt_co_rec k (g_Var_f x) e) = syntax_size_tm e) /\
  (forall e : brs, forall k x, syntax_size_brs (open_brs_wrt_co_rec k (g_Var_f x) e) = syntax_size_brs e) /\
  (forall e : co, forall k x, syntax_size_co (open_co_wrt_co_rec k (g_Var_f x) e) = syntax_size_co e) /\
  (forall e : constraint, forall k x, syntax_size_constraint (open_constraint_wrt_co_rec k (g_Var_f x) e) = syntax_size_constraint e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try match goal with
  | |- context [lt_eq_lt_dec ?i ?k] =>
      destruct (lt_eq_lt_dec i k) as [[?|?]|?]; reflexivity
  end.
  all: repeat first [progress rewrite H | progress rewrite H0 | progress rewrite H1]; reflexivity.
Qed.
Definition size_open_co_tm := proj1 (size_open_co).
Definition size_open_co_co := proj1 (proj2 (proj2 (size_open_co))).

Ltac closed_from_open :=
  match goal with
  | IH : forall z, scoped_tm 0 0 (open_tm_wrt_tm ?a (a_Var_f z)) |- scoped_tm 1 0 ?a =>
      exact (proj1 (scoped_open_tm_tm a 0 (a_Var_f Fix) 0 0 ltac:(lia) I) (IH Fix))
  | IH : forall z, scoped_co 0 0 (open_co_wrt_tm ?a (a_Var_f z)) |- scoped_co 1 0 ?a =>
      exact (proj1 (scoped_open_tm_co a 0 (a_Var_f Fix) 0 0 ltac:(lia) I) (IH Fix))
  | IH : forall z, scoped_tm 0 0 (open_tm_wrt_co ?a (g_Var_f z)) |- scoped_tm 0 1 ?a =>
      exact (proj1 (scoped_open_co_tm a 0 (g_Var_f Fix) 0 0 ltac:(lia) I) (IH Fix))
  | IH : forall z, scoped_co 0 0 (open_co_wrt_co ?a (g_Var_f z)) |- scoped_co 0 1 ?a =>
      exact (proj1 (scoped_open_co_co a 0 (g_Var_f Fix) 0 0 ltac:(lia) I) (IH Fix))
  end.

Lemma lc_scoped :
  (forall a, lc_tm a -> scoped_tm 0 0 a) /\
  (forall bs, lc_brs bs -> scoped_brs 0 0 bs) /\
  (forall g, lc_co g -> scoped_co 0 0 g) /\
  (forall p, lc_constraint p -> scoped_constraint 0 0 p).
Proof.
  apply lc_syntax_ind; simpl; intros; repeat split; try assumption; closed_from_open.
Qed.

Lemma scoped_lc_size : forall n,
  (forall a, syntax_size_tm a < n -> scoped_tm 0 0 a -> lc_tm a) /\
  (forall bs, syntax_size_brs bs < n -> scoped_brs 0 0 bs -> lc_brs bs) /\
  (forall g, syntax_size_co g < n -> scoped_co 0 0 g -> lc_co g) /\
  (forall p, syntax_size_constraint p < n -> scoped_constraint 0 0 p -> lc_constraint p).
Proof.
  induction n as [|n [It [Ib [Ig Ip]]]].
  - repeat split; intros; lia.
  - repeat split; intros e Hsize Hsc; destruct e; simpl in Hsize, Hsc;
      try lia; constructor;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try (solve [apply It; [lia|assumption] | apply Ib; [lia|assumption] |
                  apply Ig; [lia|assumption] | apply Ip; [lia|assumption]]);
      intros x;
      unfold open_tm_wrt_tm, open_tm_wrt_co, open_co_wrt_tm, open_co_wrt_co;
      first [apply It | apply Ig];
      first [rewrite size_open_tm_tm; lia | rewrite size_open_co_tm; lia |
             rewrite size_open_tm_co; lia | rewrite size_open_co_co; lia |
             apply scoped_open_tm_tm; [lia|exact I|assumption] |
             apply scoped_open_co_tm; [lia|exact I|assumption] |
             apply scoped_open_tm_co; [lia|exact I|assumption] |
             apply scoped_open_co_co; [lia|exact I|assumption]].
Qed.

Lemma scoped_lc_tm a : scoped_tm 0 0 a -> lc_tm a.
Proof. apply (proj1 (scoped_lc_size (S (syntax_size_tm a)))); lia. Qed.
Lemma scoped_lc_co g : scoped_co 0 0 g -> lc_co g.
Proof. apply (proj1 (proj2 (proj2 (scoped_lc_size (S (syntax_size_co g)))))); lia. Qed.
Lemma scoped_lc_constraint p : scoped_constraint 0 0 p -> lc_constraint p.
Proof. apply (proj2 (proj2 (proj2 (scoped_lc_size (S (syntax_size_constraint p)))))); lia. Qed.
Definition scoped_maps (ft : atom -> tm) (fc : atom -> co) :=
  (forall x, scoped_tm 0 0 (ft x)) /\ (forall x, scoped_co 0 0 (fc x)).

Lemma subst_open_tm :
  (forall e : tm, forall k (u : tm) ft fc, scoped_maps ft fc ->
   subst_free_tm ft fc (open_tm_wrt_tm_rec k u e) =
   open_tm_wrt_tm_rec k (subst_free_tm ft fc u) (subst_free_tm ft fc e)) /\
  (forall e : brs, forall k (u : tm) ft fc, scoped_maps ft fc ->
   subst_free_brs ft fc (open_brs_wrt_tm_rec k u e) =
   open_brs_wrt_tm_rec k (subst_free_tm ft fc u) (subst_free_brs ft fc e)) /\
  (forall e : co, forall k (u : tm) ft fc, scoped_maps ft fc ->
   subst_free_co ft fc (open_co_wrt_tm_rec k u e) =
   open_co_wrt_tm_rec k (subst_free_tm ft fc u) (subst_free_co ft fc e)) /\
  (forall e : constraint, forall k (u : tm) ft fc, scoped_maps ft fc ->
   subst_free_constraint ft fc (open_constraint_wrt_tm_rec k u e) =
   open_constraint_wrt_tm_rec k (subst_free_tm ft fc u) (subst_free_constraint ft fc e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try reflexivity.
  all: try solve [destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity].
  all: try solve [destruct H as [Ht Hc]; symmetry;
                  first [apply (open_scoped_identity_tm_tm _ 0 0); [apply Ht|lia]
                        |apply (open_scoped_identity_tm_co _ 0 0); [apply Hc|lia]]].
  all: f_equal; auto.
Qed.
Definition subst_open_tm_tm := proj1 (subst_open_tm).
Definition subst_open_tm_co := proj1 (proj2 (proj2 (subst_open_tm))).

Lemma support_open_tm :
  (forall e : tm, forall k (u : tm), support_tm e [<=] support_tm (open_tm_wrt_tm_rec k u e) /\
   support_tm (open_tm_wrt_tm_rec k u e) [<=] (support_tm e \u support_tm u)) /\
  (forall e : brs, forall k (u : tm), support_brs e [<=] support_brs (open_brs_wrt_tm_rec k u e) /\
   support_brs (open_brs_wrt_tm_rec k u e) [<=] (support_brs e \u support_tm u)) /\
  (forall e : co, forall k (u : tm), support_co e [<=] support_co (open_co_wrt_tm_rec k u e) /\
   support_co (open_co_wrt_tm_rec k u e) [<=] (support_co e \u support_tm u)) /\
  (forall e : constraint, forall k (u : tm), support_constraint e [<=] support_constraint (open_constraint_wrt_tm_rec k u e) /\
   support_constraint (open_constraint_wrt_tm_rec k u e) [<=] (support_constraint e \u support_tm u)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; split; fsetdec).
  all: try solve [split; fsetdec].
  all: repeat match goal with
       | H : forall k u, _ /\ _ |- _ =>
           let Hb := fresh in
           let Hc := fresh in
           let Hd := fresh in
           pose proof (H k u) as [Hb Hc];
           pose proof (H (S k) u) as Hd; destruct Hd; clear H
       end;
       split; fsetdec.
Qed.
Definition support_open_tm_tm := proj1 (support_open_tm).
Definition support_open_tm_co := proj1 (proj2 (proj2 (support_open_tm))).

Lemma subst_open_co :
  (forall e : tm, forall k (u : co) ft fc, scoped_maps ft fc ->
   subst_free_tm ft fc (open_tm_wrt_co_rec k u e) =
   open_tm_wrt_co_rec k (subst_free_co ft fc u) (subst_free_tm ft fc e)) /\
  (forall e : brs, forall k (u : co) ft fc, scoped_maps ft fc ->
   subst_free_brs ft fc (open_brs_wrt_co_rec k u e) =
   open_brs_wrt_co_rec k (subst_free_co ft fc u) (subst_free_brs ft fc e)) /\
  (forall e : co, forall k (u : co) ft fc, scoped_maps ft fc ->
   subst_free_co ft fc (open_co_wrt_co_rec k u e) =
   open_co_wrt_co_rec k (subst_free_co ft fc u) (subst_free_co ft fc e)) /\
  (forall e : constraint, forall k (u : co) ft fc, scoped_maps ft fc ->
   subst_free_constraint ft fc (open_constraint_wrt_co_rec k u e) =
   open_constraint_wrt_co_rec k (subst_free_co ft fc u) (subst_free_constraint ft fc e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try reflexivity.
  all: try solve [destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity].
  all: try solve [destruct H as [Ht Hc]; symmetry;
                  first [apply (open_scoped_identity_co_tm _ 0 0); [apply Ht|lia]
                        |apply (open_scoped_identity_co_co _ 0 0); [apply Hc|lia]]].
  all: f_equal; auto.
Qed.
Definition subst_open_co_tm := proj1 (subst_open_co).
Definition subst_open_co_co := proj1 (proj2 (proj2 (subst_open_co))).

Lemma support_open_co :
  (forall e : tm, forall k (u : co), support_tm e [<=] support_tm (open_tm_wrt_co_rec k u e) /\
   support_tm (open_tm_wrt_co_rec k u e) [<=] (support_tm e \u support_co u)) /\
  (forall e : brs, forall k (u : co), support_brs e [<=] support_brs (open_brs_wrt_co_rec k u e) /\
   support_brs (open_brs_wrt_co_rec k u e) [<=] (support_brs e \u support_co u)) /\
  (forall e : co, forall k (u : co), support_co e [<=] support_co (open_co_wrt_co_rec k u e) /\
   support_co (open_co_wrt_co_rec k u e) [<=] (support_co e \u support_co u)) /\
  (forall e : constraint, forall k (u : co), support_constraint e [<=] support_constraint (open_constraint_wrt_co_rec k u e) /\
   support_constraint (open_constraint_wrt_co_rec k u e) [<=] (support_constraint e \u support_co u)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; split; fsetdec).
  all: try solve [split; fsetdec].
  all: repeat match goal with
       | H : forall k u, _ /\ _ |- _ =>
           let Hb := fresh in
           let Hc := fresh in
           let Hd := fresh in
           pose proof (H k u) as [Hb Hc];
           pose proof (H (S k) u) as Hd; destruct Hd; clear H
       end;
       split; fsetdec.
Qed.
Definition support_open_co_tm := proj1 (support_open_co).
Definition support_open_co_co := proj1 (proj2 (proj2 (support_open_co))).

Lemma subst_agree :
  (forall e : tm, forall ft fc ft' fc', (forall x, x `in` support_tm e -> ft x = ft' x) ->
   (forall x, x `in` support_tm e -> fc x = fc' x) ->
   subst_free_tm ft fc e = subst_free_tm ft' fc' e) /\
  (forall e : brs, forall ft fc ft' fc', (forall x, x `in` support_brs e -> ft x = ft' x) ->
   (forall x, x `in` support_brs e -> fc x = fc' x) ->
   subst_free_brs ft fc e = subst_free_brs ft' fc' e) /\
  (forall e : co, forall ft fc ft' fc', (forall x, x `in` support_co e -> ft x = ft' x) ->
   (forall x, x `in` support_co e -> fc x = fc' x) ->
   subst_free_co ft fc e = subst_free_co ft' fc' e) /\
  (forall e : constraint, forall ft fc ft' fc', (forall x, x `in` support_constraint e -> ft x = ft' x) ->
   (forall x, x `in` support_constraint e -> fc x = fc' x) ->
   subst_free_constraint ft fc e = subst_free_constraint ft' fc' e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity | apply H; fsetdec | apply H0; fsetdec].
  all: f_equal;
      match goal with
      | IH : forall ft fc ft' fc', _ -> _ -> ?F ft fc ?e = _ |- ?F _ _ ?e = _ =>
          apply IH; intros; first [apply H; fsetdec | apply H0; fsetdec | apply H1; fsetdec | apply H2; fsetdec | apply H3; fsetdec]
      end.
Qed.
Definition subst_agree_tm := proj1 (subst_agree).
Definition subst_agree_constraint := proj2 (proj2 (proj2 (subst_agree))).

Lemma subst_identity :
  (forall e : tm, subst_free_tm a_Var_f g_Var_f e = e) /\
  (forall e : brs, subst_free_brs a_Var_f g_Var_f e = e) /\
  (forall e : co, subst_free_co a_Var_f g_Var_f e = e) /\
  (forall e : constraint, subst_free_constraint a_Var_f g_Var_f e = e).
Proof.
  apply syntax_ind; simpl; intros.
  all: f_equal; auto.
Qed.
Definition subst_identity_tm := proj1 (subst_identity).
Definition subst_identity_constraint := proj2 (proj2 (proj2 (subst_identity))).

Lemma open_close_tm :
  (forall e : tm, forall k x, open_tm_wrt_tm_rec k (a_Var_f x) (close_term_tm k x e) = e) /\
  (forall e : brs, forall k x, open_brs_wrt_tm_rec k (a_Var_f x) (close_term_brs k x e) = e) /\
  (forall e : co, forall k x, open_co_wrt_tm_rec k (a_Var_f x) (close_term_co k x e) = e) /\
  (forall e : constraint, forall k x, open_constraint_wrt_tm_rec k (a_Var_f x) (close_term_constraint k x e) = e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [f_equal; auto].
  - destruct (le_lt_dec k n).
    + change ((match lt_eq_lt_dec (S n) k with
               | inleft (left _) => a_Var_b (S n)
               | inleft (right _) => a_Var_f x
               | inright _ => a_Var_b (S n - 1) end) = a_Var_b n).
      destruct (lt_eq_lt_dec (S n) k) as [[?|?]|?]; try lia; f_equal; lia.
    + change ((match lt_eq_lt_dec n k with
               | inleft (left _) => a_Var_b n
               | inleft (right _) => a_Var_f x
               | inright _ => a_Var_b (n - 1) end) = a_Var_b n).
      destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try lia; reflexivity.
  - destruct (@eq_dec Atom.atom EqDec_eq_of_X x0 x) as [Heq|Hneq].
    + change ((match lt_eq_lt_dec k k with
               | inleft (left _) => a_Var_b k
               | inleft (right _) => a_Var_f x0
               | inright _ => a_Var_b (k - 1) end) = a_Var_f x).
      destruct (lt_eq_lt_dec k k) as [[?|?]|?]; try lia. now subst.
    + reflexivity.
Qed.
Definition open_close_tm_tm := proj1 (open_close_tm).
Fixpoint close_co_tm (k : nat) (y : atom) (e : tm) {struct e} : tm :=
  match e with
  | a_Star => a_Star
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Abs rho A b) => a_Abs rho (close_co_tm k y A) (close_co_tm k y b)
  | (a_UAbs rho b) => a_UAbs rho (close_co_tm k y b)
  | (a_App a rho b) => a_App (close_co_tm k y a) rho (close_co_tm k y b)
  | (a_Fam F) => a_Fam F
  | (a_Const T) => a_Const T
  | (a_Pi rho A B) => a_Pi rho (close_co_tm k y A) (close_co_tm k y B)
  | (a_Conv a g) => a_Conv (close_co_tm k y a) (close_co_co k y g)
  | (a_CPi phi B) => a_CPi (close_co_constraint k y phi) (close_co_tm (S k) y B)
  | (a_CAbs phi b) => a_CAbs (close_co_constraint k y phi) (close_co_tm (S k) y b)
  | (a_UCAbs b) => a_UCAbs (close_co_tm (S k) y b)
  | (a_CApp a g) => a_CApp (close_co_tm k y a) (close_co_co k y g)
  | a_Bullet => a_Bullet
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (close_co_tm k y a) (close_co_brs k y brs5)
  end
with close_co_brs (k : nat) (y : atom) (e : brs) {struct e} : brs :=
  match e with
  | br_None => br_None
  | (br_One K a brs5) => br_One K (close_co_tm k y a) (close_co_brs k y brs5)
  end
with close_co_co (k : nat) (y : atom) (e : co) {struct e} : co :=
  match e with
  | g_Triv => g_Triv
  | (g_Var_b nat) => if le_lt_dec k nat then g_Var_b (S nat) else g_Var_b nat
  | (g_Var_f c) => if y == c then g_Var_b k else g_Var_f c
  | (g_Beta a b) => g_Beta (close_co_tm k y a) (close_co_tm k y b)
  | (g_Refl a) => g_Refl (close_co_tm k y a)
  | (g_Refl2 a b g) => g_Refl2 (close_co_tm k y a) (close_co_tm k y b) (close_co_co k y g)
  | (g_Sym g) => g_Sym (close_co_co k y g)
  | (g_Trans g1 g2) => g_Trans (close_co_co k y g1) (close_co_co k y g2)
  | (g_PiCong rho g1 g2) => g_PiCong rho (close_co_co k y g1) (close_co_co k y g2)
  | (g_AbsCong rho g1 g2) => g_AbsCong rho (close_co_co k y g1) (close_co_co k y g2)
  | (g_AppCong g1 rho g2) => g_AppCong (close_co_co k y g1) rho (close_co_co k y g2)
  | (g_PiFst g) => g_PiFst (close_co_co k y g)
  | (g_CPiFst g) => g_CPiFst (close_co_co k y g)
  | (g_IsoSnd g) => g_IsoSnd (close_co_co k y g)
  | (g_PiSnd g1 g2) => g_PiSnd (close_co_co k y g1) (close_co_co k y g2)
  | (g_CPiCong g1 g3) => g_CPiCong (close_co_co k y g1) (close_co_co (S k) y g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (close_co_co k y g1) (close_co_co (S k) y g3) (close_co_co k y g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (close_co_co k y g) (close_co_co k y g1) (close_co_co k y g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (close_co_co k y g) (close_co_co k y g1) (close_co_co k y g2)
  | (g_Cast g1 g2) => g_Cast (close_co_co k y g1) (close_co_co k y g2)
  | (g_EqCong g1 A g2) => g_EqCong (close_co_co k y g1) (close_co_tm k y A) (close_co_co k y g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (close_co_constraint k y phi1) (close_co_constraint k y phi2) (close_co_co k y g)
  | (g_Eta a) => g_Eta (close_co_tm k y a)
  | (g_Left g g') => g_Left (close_co_co k y g) (close_co_co k y g')
  | (g_Right g g') => g_Right (close_co_co k y g) (close_co_co k y g')
  end
with close_co_constraint (k : nat) (y : atom) (e : constraint) {struct e} : constraint :=
  match e with
  | (Eq a b A) => Eq (close_co_tm k y a) (close_co_tm k y b) (close_co_tm k y A)
  end.

Lemma close_open_tm :
  (forall e : tm, forall k x, x \notin support_tm e -> close_term_tm k x (open_tm_wrt_tm_rec k (a_Var_f x) e) = e) /\
  (forall e : brs, forall k x, x \notin support_brs e -> close_term_brs k x (open_brs_wrt_tm_rec k (a_Var_f x) e) = e) /\
  (forall e : co, forall k x, x \notin support_co e -> close_term_co k x (open_co_wrt_tm_rec k (a_Var_f x) e) = e) /\
  (forall e : constraint, forall k x, x \notin support_constraint e -> close_term_constraint k x (open_constraint_wrt_tm_rec k (a_Var_f x) e) = e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity].
  all: try solve [
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; subst; simpl;
    repeat match goal with
    | |- context [le_lt_dec ?k ?i] => destruct (le_lt_dec k i)
    | |- context [@eq_dec ?T ?E ?x ?y] => destruct (@eq_dec T E x y)
    end; try contradiction; try lia; f_equal; lia].
  all: try solve [match goal with |- context [@eq_dec ?T ?E ?x ?y] => destruct (@eq_dec T E x y) end;
    subst; [exfalso; fsetdec|reflexivity]].
  all: f_equal; match goal with
  | IH : forall k x, _ -> ?C k x (?O k (_ x) ?e) = ?e |- ?C _ _ (?O _ _ ?e) = ?e =>
      apply IH; fsetdec
  end.
Qed.
Definition close_open_tm_tm := proj1 (close_open_tm).

Lemma close_open_co :
  (forall e : tm, forall k x, x \notin support_tm e -> close_co_tm k x (open_tm_wrt_co_rec k (g_Var_f x) e) = e) /\
  (forall e : brs, forall k x, x \notin support_brs e -> close_co_brs k x (open_brs_wrt_co_rec k (g_Var_f x) e) = e) /\
  (forall e : co, forall k x, x \notin support_co e -> close_co_co k x (open_co_wrt_co_rec k (g_Var_f x) e) = e) /\
  (forall e : constraint, forall k x, x \notin support_constraint e -> close_co_constraint k x (open_constraint_wrt_co_rec k (g_Var_f x) e) = e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity].
  all: try solve [
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; subst; simpl;
    repeat match goal with
    | |- context [le_lt_dec ?k ?i] => destruct (le_lt_dec k i)
    | |- context [@eq_dec ?T ?E ?x ?y] => destruct (@eq_dec T E x y)
    end; try contradiction; try lia; f_equal; lia].
  all: try solve [match goal with |- context [@eq_dec ?T ?E ?x ?y] => destruct (@eq_dec T E x y) end;
    subst; [exfalso; fsetdec|reflexivity]].
  all: f_equal; match goal with
  | IH : forall k x, _ -> ?C k x (?O k (_ x) ?e) = ?e |- ?C _ _ (?O _ _ ?e) = ?e =>
      apply IH; fsetdec
  end.
Qed.
Definition close_open_co_tm := proj1 (close_open_co).

Lemma scoped_subst :
  (forall e : tm, forall nt nc ft fc, scoped_maps ft fc -> scoped_tm nt nc e -> scoped_tm nt nc (subst_free_tm ft fc e)) /\
  (forall e : brs, forall nt nc ft fc, scoped_maps ft fc -> scoped_brs nt nc e -> scoped_brs nt nc (subst_free_brs ft fc e)) /\
  (forall e : co, forall nt nc ft fc, scoped_maps ft fc -> scoped_co nt nc e -> scoped_co nt nc (subst_free_co ft fc e)) /\
  (forall e : constraint, forall nt nc ft fc, scoped_maps ft fc -> scoped_constraint nt nc e -> scoped_constraint nt nc (subst_free_constraint ft fc e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [assumption | exact I].
  all: try solve [destruct H as [Ht Hc];
     first [eapply scoped_mono_tm; [| |apply Ht]; lia
           |eapply scoped_mono_co; [| |apply Hc]; lia]].
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: repeat split; auto.
Qed.
Definition scoped_subst_tm := proj1 (scoped_subst).
Definition scoped_subst_co := proj1 (proj2 (proj2 (scoped_subst))).
Definition scoped_subst_constraint := proj2 (proj2 (proj2 (scoped_subst))).

Lemma erase_open_tm :
  (forall e : tm, forall k u, erase_tm (open_tm_wrt_tm_rec k u e) = open_tm_wrt_tm_rec k (erase_tm u) (erase_tm e)) /\
  (forall e : brs, True) /\
  (forall e : co, True) /\
  (forall e : constraint, forall k u, erase_constraint (open_constraint_wrt_tm_rec k u e) = open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity | exact I].
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity).
  all: try destruct rho; simpl; try solve [auto]; f_equal; auto.
Qed.
Definition erase_open_tm_tm := proj1 (erase_open_tm).

Lemma erase_open_co :
  (forall e : tm, forall k u, erase_tm (open_tm_wrt_co_rec k u e) = erase_tm e) /\
  (forall e : brs, True) /\
  (forall e : co, True) /\
  (forall e : constraint, forall k u, erase_constraint (open_constraint_wrt_co_rec k u e) = erase_constraint e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity | exact I].
  all: try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity).
  all: try destruct rho; simpl; try solve [auto]; f_equal; auto.
Qed.
Definition erase_open_co_tm := proj1 (erase_open_co).

Lemma open_erase_co :
  (forall e : tm, forall k u, open_tm_wrt_co_rec k u (erase_tm e) = erase_tm e) /\
  (forall e : brs, True) /\
  (forall e : co, True) /\
  (forall e : constraint, forall k u, open_constraint_wrt_co_rec k u (erase_constraint e) = erase_constraint e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity | exact I].
  all: try destruct rho; simpl; try solve [auto]; f_equal; auto.
Qed.

Lemma erase_subst :
  (forall e : tm, forall ft fc, erase_tm (subst_free_tm ft fc e) = subst_free_tm (fun x => erase_tm (ft x)) g_Var_f (erase_tm e)) /\
  (forall e : brs, True) /\
  (forall e : co, True) /\
  (forall e : constraint, forall ft fc, erase_constraint (subst_free_constraint ft fc e) = subst_free_constraint (fun x => erase_tm (ft x)) g_Var_f (erase_constraint e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity | exact I].
  all: try destruct rho; simpl; try solve [auto]; f_equal; auto.
Qed.
Definition erase_subst_tm := proj1 (erase_subst).

Lemma scoped_erase :
  (forall e : tm, forall nt nc, scoped_tm nt nc e -> scoped_tm nt nc (erase_tm e)) /\
  (forall e : brs, True) /\
  (forall e : co, True) /\
  (forall e : constraint, forall nt nc, scoped_constraint nt nc e -> scoped_constraint nt nc (erase_constraint e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try destruct rho; simpl.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: repeat split; auto.
Qed.
Definition scoped_erase_tm := proj1 (scoped_erase).

Lemma support_erase :
  (forall e : tm, support_tm (erase_tm e) = fv_tm_tm_tm (erase_tm e)) /\
  (forall e : brs, True) /\
  (forall e : co, True) /\
  (forall e : constraint, support_constraint (erase_constraint e) = fv_tm_tm_constraint (erase_constraint e)).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [reflexivity | exact I].
  all: try destruct rho; simpl; try solve [auto]; congruence.
Qed.
Definition support_erase_tm := proj1 (support_erase).

Lemma erase_support_subset :
  (forall e : tm, support_tm (erase_tm e) [<=] support_tm e) /\
  (forall e : brs, True) /\
  (forall e : co, True) /\
  (forall e : constraint, support_constraint (erase_constraint e) [<=] support_constraint e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [exact I].
  all: try destruct rho; simpl; fsetdec.
Qed.
Definition erase_support_subset_tm := proj1 (erase_support_subset).

Lemma support_subst :
  (forall e : tm, forall W ft fc, (forall x, support_tm (ft x) [<=] ({{x}} \u W)) ->
   (forall x, support_co (fc x) [<=] ({{x}} \u W)) ->
   support_tm (subst_free_tm ft fc e) [<=] (support_tm e \u W)) /\
  (forall e : brs, forall W ft fc, (forall x, support_tm (ft x) [<=] ({{x}} \u W)) ->
   (forall x, support_co (fc x) [<=] ({{x}} \u W)) ->
   support_brs (subst_free_brs ft fc e) [<=] (support_brs e \u W)) /\
  (forall e : co, forall W ft fc, (forall x, support_tm (ft x) [<=] ({{x}} \u W)) ->
   (forall x, support_co (fc x) [<=] ({{x}} \u W)) ->
   support_co (subst_free_co ft fc e) [<=] (support_co e \u W)) /\
  (forall e : constraint, forall W ft fc, (forall x, support_tm (ft x) [<=] ({{x}} \u W)) ->
   (forall x, support_co (fc x) [<=] ({{x}} \u W)) ->
   support_constraint (subst_free_constraint ft fc e) [<=] (support_constraint e \u W)).
Proof.
  apply syntax_ind; simpl; intros.
  all: repeat match goal with
  | IH : forall W ft fc, _ -> _ -> _ [<=] _ |- _ =>
      let HH := fresh in pose proof (IH W ft fc ltac:(assumption) ltac:(assumption)) as HH; clear IH
  end.
  all: try (solve [auto | fsetdec]).
Qed.
Definition support_subst_tm := proj1 (support_subst).

(* Regularity of annotated judgments. *)
Definition typing_weaken := proj1 ann_weakening_mut.
Definition eq_weaken := proj1 (proj2 (proj2 (proj2 ann_weakening_mut))).

Lemma fix_binding F a A :
  binds F (Ax a A) an_toplevel -> F = Fix /\ a = FixDef /\ A = FixTy.
Proof.
  intro H. change ((Fix, Ax FixDef FixTy) = (F, Ax a A) \/ False) in H.
  destruct H as [H|[]]. inversion H; auto.
Qed.

Lemma fix_erased_binding F a A :
  binds F (Ax a A) toplevel ->
  F = Fix /\ a = erase_tm FixDef /\ A = erase_tm FixTy.
Proof.
  intro H.
  change ((Fix, Ax (erase_tm FixDef) (erase_tm FixTy)) = (F, Ax a A) \/ False) in H.
  destruct H as [H|[]]. inversion H; auto.
Qed.

Lemma ann_ctx_uniq G : AnnCtx G -> uniq G.
Proof. induction 1; auto. Qed.

Lemma ann_ctx_mut :
  (forall G a A, AnnTyping G a A -> AnnCtx G) /\
  (forall G p, AnnPropWff G p -> AnnCtx G) /\
  (forall G D g p q, AnnIso G D g p q -> AnnCtx G) /\
  (forall G D g a b, AnnDefEq G D g a b -> AnnCtx G) /\
  (forall G, AnnCtx G -> True).
Proof. apply ann_ind; auto. Qed.
Definition typing_ctx := proj1 ann_ctx_mut.

Lemma fix_type_typing G : AnnCtx G -> AnnTyping G FixTy a_Star.
Proof.
  intros HG. unfold FixTy.
  eapply An_Pi with (L := dom G); [|now constructor].
  intros x Hx.
  change (AnnTyping (x ~ Tm a_Star ++ G)
      (a_Pi Rel (a_Pi Rel (a_Var_f x) (a_Var_f x)) (a_Var_f x)) a_Star).
  assert (HGx : AnnCtx (x ~ Tm a_Star ++ G)) by (constructor; auto with ann).
  assert (Tx : AnnTyping (x ~ Tm a_Star ++ G) (a_Var_f x) a_Star)
    by (constructor; [assumption | simpl; auto]).
  assert (Tfun : AnnTyping (x ~ Tm a_Star ++ G)
                           (a_Pi Rel (a_Var_f x) (a_Var_f x)) a_Star).
  { eapply An_Pi with (L := dom (x ~ Tm a_Star ++ G)); [|exact Tx].
    intros y Hy. simpl. eapply typing_weaken; [exact Tx| |].
    - now constructor.
    - intros z s Hb. simpl; right; exact Hb. }
  eapply An_Pi with (L := dom (x ~ Tm a_Star ++ G)); [|exact Tfun].
  intros y Hy. simpl. eapply typing_weaken; [exact Tx| |].
  - now constructor.
  - intros z s Hb. simpl; right; exact Hb.
Qed.

Lemma fix_def_typing G : AnnCtx G -> AnnTyping G FixDef FixTy.
Proof.
  intros HG. unfold FixDef, FixTy.
  eapply An_Abs with (L := dom G); [now constructor | |].
  - intros x Hx.
    change (AnnTyping (x ~ Tm a_Star ++ G)
       (a_Abs Rel (a_Pi Rel (a_Var_f x) (a_Var_f x))
          (a_App (a_Var_b 0) Rel (a_App (a_App (a_Fam Fix) Irrel (a_Var_f x)) Rel (a_Var_b 0))))
       (a_Pi Rel (a_Pi Rel (a_Var_f x) (a_Var_f x)) (a_Var_f x))).
    set (E := x ~ Tm a_Star ++ G).
    set (T := a_Pi Rel (a_Var_f x) (a_Var_f x)).
    assert (HE : AnnCtx E) by (unfold E; constructor; auto with ann).
    assert (Tx : AnnTyping E (a_Var_f x) a_Star)
      by (constructor; [assumption | unfold E; simpl; auto]).
    assert (TT : AnnTyping E T a_Star).
    { unfold T. eapply An_Pi with (L := dom E); [|exact Tx].
      intros y Hy. simpl. eapply typing_weaken; [exact Tx| |].
      - now constructor.
      - intros z s Hb. simpl; right; exact Hb. }
    eapply An_Abs with (L := dom E); [exact TT| |].
    + intros y Hy. simpl.
      assert (HEy : AnnCtx (y ~ Tm T ++ E)) by (now constructor).
      assert (Ty : AnnTyping (y ~ Tm T ++ E) (a_Var_f y) T)
        by (constructor; [assumption | simpl; auto]).
      assert (Tx' : AnnTyping (y ~ Tm T ++ E) (a_Var_f x) a_Star).
      { eapply typing_weaken; [exact Tx|assumption|].
        intros z s Hb. simpl; right; exact Hb. }
      change (AnnTyping (y ~ Tm T ++ E)
         (a_App (a_Var_f y) Rel (a_App (a_App (a_Fam Fix) Irrel (a_Var_f x)) Rel (a_Var_f y)))
         (open_tm_wrt_tm (a_Var_f x) (a_App (a_App (a_Fam Fix) Irrel (a_Var_f x)) Rel (a_Var_f y)))).
      eapply An_App with (A := a_Var_f x) (B := a_Var_f x); [exact Ty|].
      change (AnnTyping (y ~ Tm T ++ E)
         (a_App (a_App (a_Fam Fix) Irrel (a_Var_f x)) Rel (a_Var_f y))
         (open_tm_wrt_tm (a_Var_f x) (a_Var_f y))).
      eapply An_App with (A := T) (B := a_Var_f x); [|exact Ty].
      change (AnnTyping (y ~ Tm T ++ E) (a_App (a_Fam Fix) Irrel (a_Var_f x)) (open_tm_wrt_tm
         (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1)) (a_Var_b 1)) (a_Var_f x))).
      eapply An_App; [|exact Tx'].
      eapply An_Fam with (a := FixDef) (A := FixTy).
      * exact HEy.
      * unfold an_toplevel; simpl; auto.
      * apply fix_type_typing. constructor.
    + intros. constructor. exact I.
  - intros x Hx. constructor. simpl. fsetdec.
Qed.

Definition scoped_sort s :=
  match s with
  | Tm a => scoped_tm 0 0 a
  | Co p => scoped_constraint 0 0 p
  end.

Ltac destruct_ands :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac use_fresh_open :=
  repeat match goal with
  | H : forall x, x \notin ?L -> _ |- _ =>
    let Hx := fresh in
    pose proof (proj2_sig (atom_fresh L)) as Hx;
    specialize (H (proj1_sig (atom_fresh L)) Hx)
  end.

Ltac discharge_scoped_open :=
  first [apply scoped_open_tm_tm; [lia|simpl; auto|assumption]
        |apply scoped_open_co_tm; [lia|simpl; auto|assumption]
        |apply scoped_open_tm_co; [lia|simpl; auto|assumption]
        |apply scoped_open_co_co; [lia|simpl; auto|assumption]
        |match goal with
         | H : scoped_tm 0 0 (open_tm_wrt_tm ?a (a_Var_f ?x)) |- scoped_tm 1 0 ?a =>
           exact (proj1 (scoped_open_tm_tm a 0 (a_Var_f x) 0 0 ltac:(lia) I) H)
         | H : scoped_tm 0 0 (open_tm_wrt_co ?a (g_Var_f ?x)) |- scoped_tm 0 1 ?a =>
           exact (proj1 (scoped_open_co_tm a 0 (g_Var_f x) 0 0 ltac:(lia) I) H)
         | H : scoped_co 0 0 (open_co_wrt_tm ?a (a_Var_f ?x)) |- scoped_co 1 0 ?a =>
           exact (proj1 (scoped_open_tm_co a 0 (a_Var_f x) 0 0 ltac:(lia) I) H)
         | H : scoped_co 0 0 (open_co_wrt_co ?a (g_Var_f ?x)) |- scoped_co 0 1 ?a =>
           exact (proj1 (scoped_open_co_co a 0 (g_Var_f x) 0 0 ltac:(lia) I) H)
         end].

Lemma scoped_ann :
  (forall G a A, AnnTyping G a A -> scoped_tm 0 0 a /\ scoped_tm 0 0 A) /\
  (forall G p, AnnPropWff G p -> scoped_constraint 0 0 p) /\
  (forall G D g p q, AnnIso G D g p q ->
    scoped_co 0 0 g /\ scoped_constraint 0 0 p /\ scoped_constraint 0 0 q) /\
  (forall G D g a b, AnnDefEq G D g a b ->
    scoped_co 0 0 g /\ scoped_tm 0 0 a /\ scoped_tm 0 0 b) /\
  (forall G, AnnCtx G -> forall x s, binds x s G -> scoped_sort s).
Proof.
  apply ann_ind; intros; simpl in *.
  all: use_fresh_open; destruct_ands; repeat split; try assumption; try exact I.
  all: try (solve [discharge_scoped_open]).
  all: try match goal with
  | Hb : binds ?x ?s ?G, H : forall x s, binds x s ?G -> scoped_sort s |- _ =>
      let HH := fresh in pose proof (H x s Hb) as HH;
      simpl in HH; destruct_ands; try assumption
  end.
  all: try match goal with
  | Hb : binds _ _ nil |- _ => inversion Hb
  | Hb : binds _ _ (_ :: _) |- _ =>
      destruct Hb as [Heq|Hb]; [inversion Heq; subst; assumption|eauto]
  end.
  all: try match goal with
  | H : open_tm_wrt_tm ?a (a_Var_f ?x) = open_tm_wrt_tm ?b ?u
    |- scoped_tm 1 0 ?a =>
      apply (proj1 (scoped_open_tm_tm a 0 (a_Var_f x) 0 0 ltac:(lia) I));
      change (scoped_tm 0 0 (open_tm_wrt_tm a (a_Var_f x)));
      rewrite H;
      apply (proj2 (scoped_open_tm_tm b 0 u 0 0 ltac:(lia) ltac:(simpl; auto)));
      assumption
  end.
Qed.

Definition typing_scoped := proj1 scoped_ann.
Definition prop_scoped := proj1 (proj2 scoped_ann).
Definition eq_scoped := proj1 (proj2 (proj2 (proj2 scoped_ann))).

Lemma typing_lc G a A : AnnTyping G a A -> lc_tm a.
Proof. intro H. apply scoped_lc_tm. exact (proj1 (typing_scoped _ _ _ H)). Qed.
Lemma prop_lc G p : AnnPropWff G p -> lc_constraint p.
Proof. intro H. apply scoped_lc_constraint. exact (prop_scoped _ _ H). Qed.
Lemma eq_lc G D g a b : AnnDefEq G D g a b -> lc_co g.
Proof. intro H. apply scoped_lc_co. exact (proj1 (eq_scoped _ _ _ _ _ H)). Qed.

Definition support_sort s :=
  match s with
  | Tm a => support_tm a
  | Co p => support_constraint p
  end.

Ltac take_fresh L x Hx :=
  destruct (atom_fresh L) as [x Hx].

Ltac support_open_bound :=
  repeat match goal with
  | H : support_tm (open_tm_wrt_tm ?a ?u) [<=] ?S |- _ =>
    let H1 := fresh in
    pose proof (proj1 (support_open_tm_tm a 0 u)) as H1;
    change (support_tm a [<=] support_tm (open_tm_wrt_tm a u)) in H1;
    let H2 := fresh in
    assert (H2 : support_tm a [<=] S) by (intros ? ?; auto); clear H H1
  | H : support_tm (open_tm_wrt_co ?a ?u) [<=] ?S |- _ =>
    let H1 := fresh in
    pose proof (proj1 (support_open_co_tm a 0 u)) as H1;
    change (support_tm a [<=] support_tm (open_tm_wrt_co a u)) in H1;
    let H2 := fresh in
    assert (H2 : support_tm a [<=] S) by (intros ? ?; auto); clear H H1
  | H : support_co (open_co_wrt_tm ?a ?u) [<=] ?S |- _ =>
    let H1 := fresh in
    pose proof (proj1 (support_open_tm_co a 0 u)) as H1;
    change (support_co a [<=] support_co (open_co_wrt_tm a u)) in H1;
    let H2 := fresh in
    assert (H2 : support_co a [<=] S) by (intros ? ?; auto); clear H H1
  | H : support_co (open_co_wrt_co ?a ?u) [<=] ?S |- _ =>
    let H1 := fresh in
    pose proof (proj1 (support_open_co_co a 0 u)) as H1;
    change (support_co a [<=] support_co (open_co_wrt_co a u)) in H1;
    let H2 := fresh in
    assert (H2 : support_co a [<=] S) by (intros ? ?; auto); clear H H1
  end.

Lemma support_ann :
  (forall G a A, AnnTyping G a A -> support_tm a [<=] dom G /\ support_tm A [<=] dom G) /\
  (forall G p, AnnPropWff G p -> support_constraint p [<=] dom G) /\
  (forall G D g p q, AnnIso G D g p q ->
    support_co g [<=] dom G /\ support_constraint p [<=] dom G /\ support_constraint q [<=] dom G) /\
  (forall G D g a b, AnnDefEq G D g a b ->
    support_co g [<=] dom G /\ support_tm a [<=] dom G /\ support_tm b [<=] dom G) /\
  (forall G, AnnCtx G -> forall x s, binds x s G -> support_sort s [<=] dom G).
Proof.
  apply ann_ind; intros; simpl in *.
  all: try match goal with
  | Hb : binds _ _ nil |- _ => inversion Hb
  | Hb : binds _ _ (_ :: _) |- _ =>
      destruct Hb as [Heq|Hb]; [inversion Heq; subst; simpl |]
  end.
  all: try match goal with
  | Hb : binds ?x ?s ?G |- _ =>
      let HH := fresh in pose proof (binds_In _ _ _ _ Hb) as HH;
      match goal with
      | H : forall z s, binds z s ?G -> support_sort s [<=] dom ?G |- _ =>
        let HH := fresh in pose proof (H x s Hb) as HH; simpl in HH
      | _ => idtac
      end
  end.
  all: destruct_ands.
  all: repeat split; try assumption;
    try (match goal with
    | |- _ [<=] _ => intros z Hz
    end).
  all: try solve [fsetdec].
  all: try match goal with
  | H : forall x, x \notin ?L -> _ |- ?z `in` _ =>
      let x := fresh "x" in let Hx := fresh "Hx" in
      take_fresh (L \u {{z}}) x Hx;
      repeat match goal with
      | K : forall y, y \notin L -> _ |- _ => specialize (K x ltac:(fsetdec))
      end
  end.
  all: destruct_ands; simpl in *; support_open_bound.
  all: try solve [fsetdec].
  all: try match goal with
  | Hz : ?z `in` support_tm (open_tm_wrt_tm ?a ?u) |- _ =>
      apply (proj2 (support_open_tm_tm a 0 u)) in Hz; simpl in Hz
  | Hz : ?z `in` support_tm (open_tm_wrt_co ?a ?u) |- _ =>
      apply (proj2 (support_open_co_tm a 0 u)) in Hz; simpl in Hz
  end.
  all: try solve [fsetdec].
  - destruct (AtomSetImpl.union_1 Hz) as [Ha|Hz']; [fsetdec|].
    pose proof (proj1 (support_open_tm_tm b3 0 (a_Var_f x0)) z Hz') as Hopen.
    change (z `in` support_tm (open_tm_wrt_tm b3 (a_Var_f x0))) in Hopen.
    rewrite e in Hopen.
    pose proof (proj2 (support_open_tm_tm b2 0 (a_Conv (a_Var_f x0) (g_Sym g1))) z Hopen) as Hs.
    simpl in Hs; fsetdec.
  - pose proof (H x0 s H1) as HS; fsetdec.
  - pose proof (H x s H1) as HS; fsetdec.
Qed.

Definition typing_support := proj1 support_ann.
Definition ctx_support := proj2 (proj2 (proj2 (proj2 support_ann))).

(* Substitution of terms and coercions. *)
Record CleanMaps (W : atoms) (ft : atom -> tm) (fc : atom -> co) : Prop := {
  maps_scoped : scoped_maps ft fc;
  map_term_id : forall x, x \notin W -> ft x = a_Var_f x;
  map_co_id : forall x, x \notin W -> fc x = g_Var_f x;
  map_term_support : forall x, support_tm (ft x) [<=] ({{x}} \u W);
  map_co_support : forall x, support_co (fc x) [<=] ({{x}} \u W)
}.

Lemma erase_clean_maps W ft fc :
  CleanMaps W ft fc -> CleanMaps W (fun x => erase_tm (ft x)) g_Var_f.
Proof.
  intros [Hs Ht Hc Hst Hsc]. constructor.
  - destruct Hs as [H1 H2]. split; [intro x; now apply scoped_erase_tm | exact (fun _ => I)].
  - intros x Hx. now rewrite Ht.
  - reflexivity.
  - intros x z Hz. apply Hst. exact (erase_support_subset_tm _ _ Hz).
  - simpl; fsetdec.
Qed.

Lemma clean_rho W ft fc r x a :
  CleanMaps W ft fc -> x \notin W -> RhoCheck r x (erase_tm a) ->
  RhoCheck r x (erase_tm (subst_free_tm ft fc a)).
Proof.
  intros Hm Hx Hr. destruct r; inversion Hr; subst; constructor; [exact I|].
  rewrite <- support_erase_tm, erase_subst_tm.
  pose proof (erase_clean_maps _ _ _ Hm) as Hm'.
  pose proof (support_subst_tm (erase_tm a) _ _ _
    (map_term_support _ _ _ Hm') (map_co_support _ _ _ Hm')) as HS.
  rewrite support_erase_tm in HS. fsetdec.
Qed.

Lemma lc_subst_tm W ft fc a :
  CleanMaps W ft fc -> lc_tm a -> lc_tm (subst_free_tm ft fc a).
Proof.
  intros Hm Ha. apply scoped_lc_tm.
  apply scoped_subst_tm; [exact (maps_scoped _ _ _ Hm) | exact (proj1 lc_scoped _ Ha)].
Qed.
Lemma lc_subst_co W ft fc g :
  CleanMaps W ft fc -> lc_co g -> lc_co (subst_free_co ft fc g).
Proof.
  intros Hm Hg. apply scoped_lc_co.
  apply scoped_subst_co; [exact (maps_scoped _ _ _ Hm) | exact (proj1 (proj2 (proj2 lc_scoped)) _ Hg)].
Qed.
Lemma lc_subst_constraint W ft fc p :
  CleanMaps W ft fc -> lc_constraint p -> lc_constraint (subst_free_constraint ft fc p).
Proof.
  intros Hm Hp. apply scoped_lc_constraint.
  apply scoped_subst_constraint; [exact (maps_scoped _ _ _ Hm) | exact (proj2 (proj2 (proj2 lc_scoped)) _ Hp)].
Qed.

Scheme cv_ind' := Induction for CoercedValue Sort Prop
with val_ind' := Induction for Value Sort Prop.
Combined Scheme value_ind from cv_ind', val_ind'.
#[local] Hint Constructors CoercedValue Value value_type : values.
#[local] Hint Resolve lc_subst_tm lc_subst_co lc_subst_constraint : values.

Lemma subst_open_tm_tm_0 e (u : tm) ft fc :
  scoped_maps ft fc ->
  subst_free_tm ft fc (open_tm_wrt_tm e u) =
  open_tm_wrt_tm (subst_free_tm ft fc e) (subst_free_tm ft fc u).
Proof. apply subst_open_tm_tm. Qed.

Lemma subst_open_tm_co_0 e (u : tm) ft fc :
  scoped_maps ft fc ->
  subst_free_co ft fc (open_co_wrt_tm e u) =
  open_co_wrt_tm (subst_free_co ft fc e) (subst_free_tm ft fc u).
Proof. apply subst_open_tm_co. Qed.

Lemma subst_open_co_tm_0 e (u : co) ft fc :
  scoped_maps ft fc ->
  subst_free_tm ft fc (open_tm_wrt_co e u) =
  open_tm_wrt_co (subst_free_tm ft fc e) (subst_free_co ft fc u).
Proof. apply subst_open_co_tm. Qed.

Lemma subst_open_co_co_0 e (u : co) ft fc :
  scoped_maps ft fc ->
  subst_free_co ft fc (open_co_wrt_co e u) =
  open_co_wrt_co (subst_free_co ft fc e) (subst_free_co ft fc u).
Proof. apply subst_open_co_co. Qed.

Ltac commute_subst_open :=
  match goal with
  | Hm : CleanMaps ?W ?ft ?fc |- _ =>
    let HS := constr:(maps_scoped _ _ _ Hm) in
    repeat first [rewrite (subst_open_tm_tm_0 _ _ _ _ HS) in *
                 |rewrite (subst_open_tm_co_0 _ _ _ _ HS) in *
                 |rewrite (subst_open_co_tm_0 _ _ _ _ HS) in *
                 |rewrite (subst_open_co_co_0 _ _ _ _ HS) in *]
  end.

Lemma values_subst :
  (forall a, CoercedValue a -> forall W ft fc, CleanMaps W ft fc ->
    CoercedValue (subst_free_tm ft fc a)) /\
  (forall a, Value a -> forall W ft fc, CleanMaps W ft fc ->
    Value (subst_free_tm ft fc a)).
Proof.
  apply value_ind; intros; simpl; try exact I.
  all: repeat match goal with
  | H : lc_tm ?a, Hm : CleanMaps ?W ?ft ?fc |- _ =>
      let HH := fresh in pose proof (lc_subst_tm W ft fc a Hm H) as HH;
      cbn [subst_free_tm subst_free_constraint] in HH; clear H; revert HH
  | H : lc_constraint ?p, Hm : CleanMaps ?W ?ft ?fc |- _ =>
      let HH := fresh in pose proof (lc_subst_constraint W ft fc p Hm H) as HH;
      cbn [subst_free_tm subst_free_constraint] in HH; clear H; revert HH
  end.
  all: intros.
  all: try solve [eauto 5 using lc_subst_tm, lc_subst_co, lc_subst_constraint with values].
  all: first [apply Value_UAbsIrrel with (L := L \u W)
             |apply Value_AbsIrrel with (L := L \u W)].
  all: try solve [eauto using lc_subst_tm].
  all: intros x Hx;
    match goal with
    | IH : forall x, x \notin ?L -> forall W ft fc, CleanMaps W ft fc -> _,
      Hm : CleanMaps ?W ?ft ?fc |- _ =>
        let H := fresh in pose proof (IH x ltac:(fsetdec) W ft fc Hm) as H;
        clear IH; commute_subst_open;
        change (subst_free_tm ft fc (a_Var_f x)) with (ft x) in H;
        rewrite (map_term_id _ _ _ Hm x ltac:(fsetdec)) in H; exact H
    end.
Qed.

Lemma beta_subst a b W ft fc :
  Beta a b -> CleanMaps W ft fc ->
  Beta (subst_free_tm ft fc a) (subst_free_tm ft fc b).
Proof.
  intros H Hm. destruct H; simpl.
  - commute_subst_open. apply Beta_AppAbs.
    + eauto using lc_subst_tm.
    + exact (proj2 values_subst _ H0 _ _ _ Hm).
  - commute_subst_open. apply Beta_CAppCAbs.
    exact (lc_subst_tm _ _ _ _ Hm H).
  - apply fix_erased_binding in H as [-> [-> ->]].
    change (Beta (a_Fam Fix) (erase_tm FixDef)). eapply Beta_Axiom with (A := erase_tm FixTy). unfold toplevel, an_toplevel; simpl; auto.
Qed.

Definition term_map (G E : context) ft fc :=
  forall x A, binds x (Tm A) G ->
    AnnTyping E (ft x) (subst_free_tm ft fc A).

Definition co_map (G E : context) (D D' : available_props) ft fc :=
  forall x a b A, binds x (Co (Eq a b A)) G -> x `in` D ->
    AnnDefEq E D' (fc x) (subst_free_tm ft fc a) (subst_free_tm ft fc b).

Record CtxMap G E ft fc : Prop := {
  ctx_map_tm : term_map G E ft fc;
  ctx_map_co : co_map G E (dom G) (dom E) ft fc
}.

Lemma cons_binds (G : context) x s :
  forall y t, binds y t G -> binds y t (x ~ s ++ G).
Proof. intros; now apply binds_app_3. Qed.

Lemma extend_tm_ctx_map G E ft fc x A :
  AnnCtx ((x ~ Tm (subst_free_tm ft fc A)) ++ E) ->
  CtxMap G E ft fc -> ft x = a_Var_f x ->
  CtxMap ((x ~ Tm A) ++ G) ((x ~ Tm (subst_free_tm ft fc A)) ++ E) ft fc.
Proof.
  intros HE [HT HC] Hx. constructor.
  - intros y T Hb. destruct Hb as [Heq|Hb].
    + inversion Heq; subst. rewrite Hx. constructor; [assumption|simpl; auto].
    + eapply typing_weaken; [apply HT; exact Hb|exact HE|apply cons_binds].
  - intros y a b T Hb Hy. destruct Hb as [Heq|Hb]; [discriminate|].
    eapply eq_weaken; [eapply HC; [exact Hb|eapply binds_In; eauto]
                      |exact HE|apply cons_binds|simpl; fsetdec].
Qed.

Lemma extend_co_ctx_map G E ft fc x p :
  AnnCtx ((x ~ Co (subst_free_constraint ft fc p)) ++ E) ->
  CtxMap G E ft fc -> fc x = g_Var_f x ->
  CtxMap ((x ~ Co p) ++ G) ((x ~ Co (subst_free_constraint ft fc p)) ++ E) ft fc.
Proof.
  intros HE [HT HC] Hx. constructor.
  - intros y T Hb. destruct Hb as [Heq|Hb]; [discriminate|].
    eapply typing_weaken; [apply HT; exact Hb|exact HE|apply cons_binds].
  - intros y a b T Hb Hy. destruct Hb as [Heq|Hb].
    + inversion Heq; subst. rewrite Hx. eapply An_Assn; [exact HE| |simpl; fsetdec].
      simpl; left; reflexivity.
    + eapply eq_weaken; [eapply HC; [exact Hb|eapply binds_In; eauto]
                        |exact HE|apply cons_binds|simpl; fsetdec].
Qed.

Lemma extend_tm_co_map G E D D' ft fc x A :
  AnnCtx ((x ~ Tm (subst_free_tm ft fc A)) ++ E) ->
  co_map G E D D' ft fc ->
  co_map ((x ~ Tm A) ++ G) ((x ~ Tm (subst_free_tm ft fc A)) ++ E) D D' ft fc.
Proof.
  intros HE HC y a b T Hb Hy. destruct Hb as [Heq|Hb]; [discriminate|].
  eapply eq_weaken; [eapply HC; eauto|exact HE|apply cons_binds|fsetdec].
Qed.

Lemma extend_co_co_map G E D D' ft fc x p :
  AnnCtx ((x ~ Co (subst_free_constraint ft fc p)) ++ E) ->
  co_map G E D D' ft fc -> x \notin D ->
  co_map ((x ~ Co p) ++ G) ((x ~ Co (subst_free_constraint ft fc p)) ++ E) D D' ft fc.
Proof.
  intros HE HC Hx y a b T Hb Hy. destruct Hb as [Heq|Hb].
  - inversion Heq; subst; contradiction.
  - eapply eq_weaken; [eapply HC; eauto|exact HE|apply cons_binds|fsetdec].
Qed.

Definition typed_subst G E W ft fc :=
  CleanMaps W ft fc /\ AnnCtx E /\ CtxMap G E ft fc.

Ltac typed_subst_maps :=
  match goal with
  | H : typed_subst _ _ ?W ?ft ?fc |- _ =>
    let Hm := fresh "Hm" in let HE := fresh "HE" in let Hmap := fresh "Hmap" in
    destruct H as [Hm [HE Hmap]]
  end.

Ltac subst_open_fresh x :=
  commute_subst_open;
  match goal with
  | Hm : CleanMaps ?W ?ft ?fc |- _ =>
    change (subst_free_tm ft fc (a_Var_f x)) with (ft x) in *;
    change (subst_free_co ft fc (g_Var_f x)) with (fc x) in *;
    cbn [subst_free_tm subst_free_co subst_free_constraint] in *;
    rewrite ?(map_term_id _ _ _ Hm x ltac:(fsetdec)),
            ?(map_co_id _ _ _ Hm x ltac:(fsetdec)) in *
  end.

Ltac use_substed_premises W ft fc E :=
  repeat match goal with
  | IH : forall (W : atoms) ft fc E, typed_subst _ E W ft fc -> _ |- _ =>
    let H := fresh in assert (H : typed_subst _ E W ft fc) by (unfold typed_subst; eauto);
    specialize (IH W ft fc E H); clear H
  | IH : forall (W : atoms) ft fc E D', typed_subst _ E W ft fc -> co_map _ E ?D D' ft fc -> _ |- _ =>
    let H := fresh in assert (H : typed_subst _ E W ft fc) by (unfold typed_subst; eauto);
    first [let D' := constr:(dom E) in
           let HM := match goal with KM : CtxMap _ E ft fc |- _ => KM end in
           specialize (IH W ft fc E D' H (ctx_map_co _ _ _ _ HM)); clear H
          |let D' := match goal with HX : co_map _ E D ?D' ft fc |- _ => D' end in
           specialize (IH W ft fc E D' H ltac:(assumption)); clear H]
  end.

Lemma ann_subst :
  (forall G a A, AnnTyping G a A -> forall W ft fc E, typed_subst G E W ft fc ->
    AnnTyping E (subst_free_tm ft fc a) (subst_free_tm ft fc A)) /\
  (forall G p, AnnPropWff G p -> forall W ft fc E, typed_subst G E W ft fc ->
    AnnPropWff E (subst_free_constraint ft fc p)) /\
  (forall G D g p q, AnnIso G D g p q -> forall W ft fc E D',
    typed_subst G E W ft fc -> co_map G E D D' ft fc ->
    AnnIso E D' (subst_free_co ft fc g) (subst_free_constraint ft fc p) (subst_free_constraint ft fc q)) /\
  (forall G D g a b, AnnDefEq G D g a b -> forall W ft fc E D',
    typed_subst G E W ft fc -> co_map G E D D' ft fc ->
    AnnDefEq E D' (subst_free_co ft fc g) (subst_free_tm ft fc a) (subst_free_tm ft fc b)) /\
  (forall G, AnnCtx G -> True).
Proof.
  apply ann_ind; intros; simpl; try exact I.
  all: typed_subst_maps.
  all: use_substed_premises W ft fc E.
  all: try (solve [eapply ctx_map_tm; eauto | eapply H0; eauto | constructor; assumption]).
  all: try match goal with
  | Hb : binds ?F (Ax ?a ?A) an_toplevel |- AnnTyping _ (a_Fam ?F) _ =>
    apply fix_binding in Hb as [-> [-> ->]];
    change (AnnTyping E (a_Fam Fix) FixTy);
    eapply An_Fam with (a := FixDef) (A := FixTy); [assumption | unfold an_toplevel; simpl; auto | apply fix_type_typing; constructor]
  end.
  all: commute_subst_open.
  all: cbn [subst_free_tm subst_free_co subst_free_constraint] in *.
  all: try match goal with
  | H : erase_tm ?a = erase_tm ?b |- _ =>
      let HH := fresh in
      assert (HH : erase_tm (subst_free_tm ft fc a) = erase_tm (subst_free_tm ft fc b))
        by (rewrite !erase_subst_tm, H; reflexivity)
  end.
  all: try match goal with
  | H : Beta (erase_tm ?a) (erase_tm ?b) |- _ =>
      let HH := fresh in assert (HH : Beta (erase_tm (subst_free_tm ft fc a)) (erase_tm (subst_free_tm ft fc b)))
       by (rewrite !erase_subst_tm; eapply beta_subst; [exact H|eapply erase_clean_maps; eauto])
  end.
  all: try solve [eassumption | eauto 4 with ann].
  all: try match goal with
  | |- AnnTyping ?E (a_Pi _ _ _) _ => eapply An_Pi with (L := L \u W \u dom E)
  | |- AnnTyping ?E (a_Abs _ _ _) _ => eapply An_Abs with (L := L \u W \u dom E)
  | |- AnnTyping ?E (a_CPi _ _) _ => eapply An_CPi with (L := L \u W \u dom E)
  | |- AnnTyping ?E (a_CAbs _ _) _ => eapply An_CAbs with (L := L \u W \u dom E)
  | |- AnnDefEq ?E _ (g_PiCong _ _ _) _ _ => eapply An_PiCong with (L := L \u W \u dom E)
  | |- AnnDefEq ?E _ (g_AbsCong _ _ _) _ _ => eapply An_AbsCong with (L := L \u W \u dom E)
  | |- AnnDefEq ?E _ (g_CPiCong _ _) _ _ => eapply An_CPiCong with (L := L \u W \u dom E \u D)
  | |- AnnDefEq ?E _ (g_CAbsCong _ _ _) _ _ => eapply An_CAbsCong with (L := L \u W \u dom E \u D)
  | |- AnnTyping _ (a_CApp _ _) _ => eapply An_CApp
  | |- AnnTyping _ (a_Conv _ _) _ => eapply An_Conv
  | |- AnnIso _ _ (g_IsoConv _ _ _) _ _ => eapply An_IsoConv
  | |- AnnIso _ _ (g_EqCong _ _ _) _ _ => eapply An_PropCong
  | |- AnnDefEq _ _ (g_Refl2 _ _ _) _ _ => eapply An_EraseEq
  | |- AnnDefEq _ _ (g_Sym _) _ _ => eapply An_Sym
  | |- AnnDefEq _ _ (g_Trans _ _) _ _ => eapply An_Trans
  | |- AnnDefEq _ _ (g_AppCong _ _ _) _ _ => eapply An_AppCong
  | |- AnnDefEq _ _ (g_PiSnd _ _) _ _ => eapply An_PiSnd
  | |- AnnDefEq _ _ (g_CAppCong _ _ _) _ _ => eapply An_CAppCong
  | |- AnnDefEq _ _ (g_CPiSnd _ _ _) _ _ => eapply An_CPiSnd
  end.
  all: try solve [eauto 4].
  all: try solve [rewrite !erase_subst_tm; f_equal; assumption].
  all: try match goal with
  | |- forall _ : atom, _ => intros x Hx
  end.
  all: try match goal with
  | |- RhoCheck _ ?x _ =>
      match goal with
      | H : forall x, x \notin ?L -> RhoCheck _ x _ |- _ =>
        let HH := fresh in
        pose proof (clean_rho _ _ _ _ x _ Hm ltac:(fsetdec) (H x ltac:(fsetdec))) as HH;
        subst_open_fresh x; exact HH
      end
  | |- open_tm_wrt_tm _ (a_Var_f ?x) = _ =>
      match goal with
      | H : forall x, x \notin ?L -> open_tm_wrt_tm _ _ = _ |- _ =>
        let HH := fresh in
        pose proof (f_equal (subst_free_tm ft fc) (H x ltac:(fsetdec))) as HH;
        subst_open_fresh x; cbn [subst_free_tm subst_free_co] in HH;
        subst_open_fresh x; exact HH
      end
  | |- open_tm_wrt_co _ (g_Var_f ?x) = _ =>
      match goal with
      | H : forall x, x \notin ?L -> open_tm_wrt_co _ _ = _ |- _ =>
        let HH := fresh in
        pose proof (f_equal (subst_free_tm ft fc) (H x ltac:(fsetdec))) as HH;
        subst_open_fresh x; cbn [subst_free_tm subst_free_co] in HH;
        subst_open_fresh x; exact HH
      end
  end.
  all: try match goal with
  | IH : forall z, z \notin ?L -> forall W ft fc E, typed_subst ((z ~ ?s) ++ ?G0) E W ft fc -> _ |- _ =>
      let s' := lazymatch s with
                | Tm ?A => constr:(Tm (subst_free_tm ft fc A))
                | Co ?p => constr:(Co (subst_free_constraint ft fc p)) end in
      let E' := constr:((x ~ s') ++ E) in
      let Hx' := fresh in
      assert (Hx' : typed_subst ((x ~ s) ++ G0) E' W ft fc);
      [|let HH := fresh in
        pose proof (IH x ltac:(fsetdec) W ft fc E' Hx') as HH;
        subst_open_fresh x; exact HH]
  | IH : forall z, z \notin ?L -> forall W ft fc E D', typed_subst ((z ~ ?s) ++ ?G0) E W ft fc ->
      co_map _ E ?D D' ft fc -> _ |- _ =>
      let s' := lazymatch s with
                | Tm ?A => constr:(Tm (subst_free_tm ft fc A))
                | Co ?p => constr:(Co (subst_free_constraint ft fc p)) end in
      let E' := constr:((x ~ s') ++ E) in
      let Hx' := fresh in let Hc := fresh in
      assert (Hx' : typed_subst ((x ~ s) ++ G0) E' W ft fc);
      [|assert (Hc : co_map ((x ~ s) ++ G0) E' D D' ft fc);
       [|let HH := fresh in
         pose proof (IH x ltac:(fsetdec) W ft fc E' D' Hx' Hc) as HH;
         subst_open_fresh x; exact HH]]
  end.
  all: try match goal with
  | |- typed_subst _ _ _ _ _ =>
      split; [exact Hm|]; split;
      [|first [apply extend_tm_ctx_map; [|exact Hmap|eapply map_term_id; [exact Hm|fsetdec]]
              |apply extend_co_ctx_map; [|exact Hmap|eapply map_co_id; [exact Hm|fsetdec]]]]
  | HH : typed_subst _ ?E' _ _ _ |- co_map _ ?E' _ _ _ _ =>
      first [apply extend_tm_co_map; [exact (proj1 (proj2 HH))|assumption]
            |apply extend_co_co_map; [exact (proj1 (proj2 HH))|assumption|fsetdec]]
  end.
  all: try match goal with
  | |- AnnCtx ((?x ~ Tm ?A) ++ ?E) =>
      apply An_ConsTm; [assumption| |fsetdec];
      first [assumption |match goal with
      | H : AnnTyping ?E (a_Pi _ ?A _) _ |- _ => inversion H; assumption
      end]
  | |- AnnCtx ((?x ~ Co ?p) ++ ?E) =>
      apply An_ConsCo; [assumption| |fsetdec];
      first [assumption |match goal with
      | H : AnnTyping ?E (a_CPi ?p _) _ |- _ => inversion H; assumption
      | H : AnnTyping ?E (a_CAbs ?p _) _ |- _ => inversion H; assumption
      end]
  end.
Qed.

Definition replace_term x a (y : atom) := if x == y then a else a_Var_f y.
Definition replace_co x g (y : atom) := if x == y then g else g_Var_f y.

Lemma replace_term_eq x a : replace_term x a x = a.
Proof. unfold replace_term. destruct (x == x); congruence. Qed.
Lemma replace_term_neq x a y : x <> y -> replace_term x a y = a_Var_f y.
Proof. unfold replace_term. destruct (x == y); congruence. Qed.
Lemma replace_co_eq x g : replace_co x g x = g.
Proof. unfold replace_co. destruct (x == x); congruence. Qed.
Lemma replace_co_neq x g y : x <> y -> replace_co x g y = g_Var_f y.
Proof. unfold replace_co. destruct (x == y); congruence. Qed.

Lemma replace_term_maps x a :
  scoped_tm 0 0 a -> CleanMaps ({{x}} \u support_tm a) (replace_term x a) g_Var_f.
Proof.
  intro H. constructor.
  - split; [intros y; unfold replace_term; destruct (x == y); simpl; auto | exact (fun _ => I)].
  - intros y Hy. apply replace_term_neq; fsetdec.
  - reflexivity.
  - intros y; unfold replace_term; destruct (x == y); simpl; fsetdec.
  - simpl; fsetdec.
Qed.

Lemma replace_co_maps x g :
  scoped_co 0 0 g -> CleanMaps ({{x}} \u support_co g) a_Var_f (replace_co x g).
Proof.
  intro H. constructor.
  - split; [exact (fun _ => I) | intros y; unfold replace_co; destruct (x == y); simpl; auto].
  - reflexivity.
  - intros y Hy. apply replace_co_neq; fsetdec.
  - simpl; fsetdec.
  - intros y; unfold replace_co; destruct (x == y); simpl; fsetdec.
Qed.

Ltac fix_subst_fresh :=
  first [
    etransitivity; [apply subst_agree_tm with (ft' := a_Var_f) (fc' := g_Var_f) | apply subst_identity_tm]
  | etransitivity; [apply subst_agree_constraint with (ft' := a_Var_f) (fc' := g_Var_f) | apply subst_identity_constraint]];
  let z := fresh "z" in let Hz := fresh "Hz" in
  intros z Hz; first [reflexivity | apply replace_term_neq; fsetdec | apply replace_co_neq; fsetdec].

Lemma open_intro_term a b x :
  x \notin support_tm a -> scoped_tm 0 0 b ->
  subst_free_tm (replace_term x b) g_Var_f (open_tm_wrt_tm a (a_Var_f x)) = open_tm_wrt_tm a b.
Proof.
  intros Hx Hb. unfold open_tm_wrt_tm.
  rewrite subst_open_tm_tm by exact (maps_scoped _ _ _ (replace_term_maps _ _ Hb)).
  change (subst_free_tm (replace_term x b) g_Var_f (a_Var_f x)) with (replace_term x b x).
  rewrite replace_term_eq. f_equal. fix_subst_fresh.
Qed.

Lemma open_intro_co a g x :
  x \notin support_tm a -> scoped_co 0 0 g ->
  subst_free_tm a_Var_f (replace_co x g) (open_tm_wrt_co a (g_Var_f x)) = open_tm_wrt_co a g.
Proof.
  intros Hx Hg. unfold open_tm_wrt_co.
  rewrite subst_open_co_tm by exact (maps_scoped _ _ _ (replace_co_maps _ _ Hg)).
  change (subst_free_co a_Var_f (replace_co x g) (g_Var_f x)) with (replace_co x g x).
  rewrite replace_co_eq. f_equal. fix_subst_fresh.
Qed.

Lemma subst_remove_tm G x a A :
  x \notin dom G -> AnnTyping G a A ->
  typed_subst ((x ~ Tm A) ++ G) G ({{x}} \u support_tm a) (replace_term x a) g_Var_f.
Proof.
  intros Hx Ha.
  pose proof (typing_ctx _ _ _ Ha) as HG.
  split; [apply replace_term_maps; exact (proj1 (typing_scoped _ _ _ Ha)) |split; [exact HG|]].
  constructor.
  - intros y T Hb. destruct Hb as [Heq|Hb].
    + inversion Heq; subst. rewrite replace_term_eq.
      replace (subst_free_tm (replace_term y a) g_Var_f T) with T; [exact Ha|].
      symmetry. pose proof (proj2 (typing_support _ _ _ Ha)). fix_subst_fresh.
    + pose proof (binds_In _ _ _ _ Hb) as HD.
      rewrite replace_term_neq by fsetdec.
      replace (subst_free_tm (replace_term x a) g_Var_f T) with T.
      * now constructor.
      * symmetry. pose proof (ctx_support _ HG _ _ Hb) as HH; simpl in HH. fix_subst_fresh.
  - intros y b c T Hb Hy. destruct Hb as [Heq|Hb]; [discriminate|].
    pose proof (ctx_support _ HG _ _ Hb) as HH; simpl in HH.
    replace (subst_free_tm (replace_term x a) g_Var_f b) with b by (symmetry; fix_subst_fresh).
    replace (subst_free_tm (replace_term x a) g_Var_f c) with c by (symmetry; fix_subst_fresh).
    eapply An_Assn; eauto using binds_In.
Qed.

Lemma subst_remove_co G x a b A g :
  x \notin dom G -> AnnPropWff G (Eq a b A) -> AnnDefEq G (dom G) g a b ->
  typed_subst ((x ~ Co (Eq a b A)) ++ G) G ({{x}} \u support_co g) a_Var_f (replace_co x g).
Proof.
  intros Hx Hp Hg.
  pose proof (proj1 (proj2 ann_ctx_mut) _ _ Hp) as HG.
  split; [apply replace_co_maps; exact (proj1 (eq_scoped _ _ _ _ _ Hg)) |split; [exact HG|]].
  constructor.
  - intros y T Hb. destruct Hb as [Heq|Hb]; [discriminate|].
    pose proof (ctx_support _ HG _ _ Hb) as HH; simpl in HH.
    replace (subst_free_tm a_Var_f (replace_co x g) T) with T by (symmetry; fix_subst_fresh).
    now constructor.
  - intros y b0 c T Hb Hy. destruct Hb as [Heq|Hb].
    + inversion Heq; subst. rewrite replace_co_eq.
      pose proof (proj1 (proj2 support_ann) _ _ Hp) as HH; simpl in HH.
      replace (subst_free_tm a_Var_f (replace_co y g) b0) with b0 by (symmetry; fix_subst_fresh).
      replace (subst_free_tm a_Var_f (replace_co y g) c) with c by (symmetry; fix_subst_fresh).
      exact Hg.
    + pose proof (binds_In _ _ _ _ Hb) as HD.
      pose proof (ctx_support _ HG _ _ Hb) as HH; simpl in HH.
      rewrite replace_co_neq by fsetdec.
      replace (subst_free_tm a_Var_f (replace_co x g) b0) with b0 by (symmetry; fix_subst_fresh).
      replace (subst_free_tm a_Var_f (replace_co x g) c) with c by (symmetry; fix_subst_fresh).
      eapply An_Assn; eauto.
Qed.

Lemma typing_beta_term G L A a B b :
  (forall x, x \notin L -> AnnTyping (x ~ Tm A ++ G)
    (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  AnnTyping G b A -> AnnTyping G (open_tm_wrt_tm a b) (open_tm_wrt_tm B b).
Proof.
  intros Hbody Hb.
  take_fresh (L \u dom G \u support_tm a \u support_tm B) x Hx.
  pose proof (proj1 ann_subst _ _ _ (Hbody x ltac:(fsetdec)) _ _ _ _ (subst_remove_tm G x b A ltac:(fsetdec) Hb)) as H.
  pose proof (proj1 (typing_scoped _ _ _ Hb)) as HS.
  now rewrite !open_intro_term in H by (first [exact HS | fsetdec]).
Qed.

Lemma typing_beta_co G L a b A w B g :
  (forall x, x \notin L -> AnnTyping (x ~ Co (Eq a b A) ++ G)
    (open_tm_wrt_co w (g_Var_f x)) (open_tm_wrt_co B (g_Var_f x))) ->
  AnnPropWff G (Eq a b A) -> AnnDefEq G (dom G) g a b ->
  AnnTyping G (open_tm_wrt_co w g) (open_tm_wrt_co B g).
Proof.
  intros Hbody Hp Hg.
  take_fresh (L \u dom G \u support_tm w \u support_tm B) x Hx.
  pose proof (proj1 ann_subst _ _ _ (Hbody x ltac:(fsetdec)) _ _ _ _
    (subst_remove_co G x a b A g ltac:(fsetdec) Hp Hg)) as H.
  pose proof (proj1 (eq_scoped _ _ _ _ _ Hg)) as HS.
  now rewrite !open_intro_co in H by (first [exact HS | fsetdec]).
Qed.

Lemma instantiate_pi G r A B a :
  AnnTyping G (a_Pi r A B) a_Star -> AnnTyping G a A ->
  AnnTyping G (open_tm_wrt_tm B a) a_Star.
Proof.
  intros HP Ha. inversion HP; subst.
  change (AnnTyping G (open_tm_wrt_tm B a) (open_tm_wrt_tm a_Star a)).
  eapply typing_beta_term; eauto.
Qed.

Lemma instantiate_cpi G a b A B g :
  AnnTyping G (a_CPi (Eq a b A) B) a_Star -> AnnDefEq G (dom G) g a b ->
  AnnTyping G (open_tm_wrt_co B g) a_Star.
Proof.
  intros HP Hg. inversion HP; subst.
  change (AnnTyping G (open_tm_wrt_co B g) (open_tm_wrt_co a_Star g)).
  eapply typing_beta_co; eauto.
Qed.

Lemma typing_lookup_wff G : AnnCtx G -> forall x A,
  binds x (Tm A) G -> AnnTyping G A a_Star.
Proof.
  induction 1; intros y T Hbind; [inversion Hbind| |].
  - destruct Hbind as [Heq|Hb]; [inversion Heq; subst|];
    eapply typing_weaken; eauto using An_ConsTm, cons_binds.
  - destruct Hbind as [Heq|Hb]; [discriminate|].
    eapply typing_weaken; eauto using An_ConsCo, cons_binds.
Qed.

Lemma type_validity_mut :
  (forall G a A, AnnTyping G a A -> AnnTyping G A a_Star) /\
  (forall G p, AnnPropWff G p -> True) /\
  (forall G D g p q, AnnIso G D g p q -> True) /\
  (forall G D g a b, AnnDefEq G D g a b -> True) /\
  (forall G, AnnCtx G -> True).
Proof.
  apply ann_ind; intros; try exact I; try assumption.
  all: try solve [eauto 5 using typing_ctx, typing_lookup_wff, instantiate_pi, instantiate_cpi with ann].
  all: try match goal with
  | |- AnnTyping _ (a_Pi _ _ _) _ => eapply An_Pi with (L := L); eauto
  | |- AnnTyping _ (a_CPi _ _) _ => eapply An_CPi with (L := L); eauto
  end.
  all: eapply typing_weaken; [eassumption | assumption | intros; contradiction].
Qed.
Definition type_validity := proj1 type_validity_mut.

(* Uniqueness of annotated typing and coercion endpoints. *)
Lemma opening_injective_tm x a b :
  x \notin support_tm a -> x \notin support_tm b ->
  open_tm_wrt_tm a (a_Var_f x) = open_tm_wrt_tm b (a_Var_f x) -> a = b.
Proof.
  intros Ha Hb H.
  apply (f_equal (close_term_tm 0 x)) in H. unfold open_tm_wrt_tm in H.
  now rewrite !close_open_tm_tm in H.
Qed.

Lemma opening_injective_co x a b :
  x \notin support_tm a -> x \notin support_tm b ->
  open_tm_wrt_co a (g_Var_f x) = open_tm_wrt_co b (g_Var_f x) -> a = b.
Proof.
  intros Ha Hb H.
  apply (f_equal (close_co_tm 0 x)) in H. unfold open_tm_wrt_co in H.
  now rewrite !close_open_co_tm in H.
Qed.

Ltac uniqueness_premises :=
  repeat match goal with
  | IH : forall B, AnnTyping ?G ?a B -> ?A = B,
    H : AnnTyping ?G ?a ?B |- _ =>
      tryif constr_eq A B then fail else
      let H' := fresh in
      pose proof (IH B H) as H'; clear IH; inversion H'; subst; try clear H'
  | IH : forall a' b', AnnDefEq ?G ?D ?g a' b' -> ?a = a' /\ ?b = b',
    H : AnnDefEq ?G ?D ?g ?a' ?b' |- _ =>
      tryif (constr_eq a a'; constr_eq b b') then fail else
      let H1 := fresh in let H2 := fresh in
      destruct (IH a' b' H) as [H1 H2]; clear IH;
      inversion H1; inversion H2; subst; try clear H1 H2
  | IH : forall p' q', AnnIso ?G ?D ?g p' q' -> ?p = p' /\ ?q = q',
    H : AnnIso ?G ?D ?g ?p' ?q' |- _ =>
      tryif (constr_eq p p'; constr_eq q q') then fail else
      let H1 := fresh in let H2 := fresh in
      destruct (IH p' q' H) as [H1 H2]; clear IH;
      inversion H1; inversion H2; subst; try clear H1 H2
  end.

Ltac unique_abs_open :=
  first [
    match goal with
    | IH : forall x, x \notin ?L -> forall B, AnnTyping (_ ++ _) (open_tm_wrt_tm ?a (a_Var_f x)) B -> open_tm_wrt_tm ?b (a_Var_f x) = B,
      H : forall x, x \notin ?L' -> AnnTyping (_ ++ _) (open_tm_wrt_tm ?a (a_Var_f x)) (open_tm_wrt_tm ?b' (a_Var_f x))
      |- ?b = ?b' =>
        let x := fresh "x" in let Fx := fresh "Fx" in
        take_fresh (L \u L' \u support_tm b \u support_tm b') x Fx;
        apply (opening_injective_tm x); [fsetdec | fsetdec | apply IH; [fsetdec | apply H; fsetdec]]
    end
  | match goal with
    | IH : forall x, x \notin ?L -> forall B, AnnTyping (_ ++ _) (open_tm_wrt_co ?a (g_Var_f x)) B -> open_tm_wrt_co ?b (g_Var_f x) = B,
      H : forall x, x \notin ?L' -> AnnTyping (_ ++ _) (open_tm_wrt_co ?a (g_Var_f x)) (open_tm_wrt_co ?b' (g_Var_f x))
      |- ?b = ?b' =>
        let x := fresh "x" in let Fx := fresh "Fx" in
        take_fresh (L \u L' \u support_tm b \u support_tm b') x Fx;
        apply (opening_injective_co x); [fsetdec | fsetdec | apply IH; [fsetdec | apply H; fsetdec]]
    end].

Ltac unique_cong_open :=
  first [
    match goal with
    | IH : forall x, x \notin ?L -> forall a' b', AnnDefEq ?G ?D (open_co_wrt_tm ?g (a_Var_f x)) a' b' ->
         open_tm_wrt_tm ?a (a_Var_f x) = a' /\ open_tm_wrt_tm ?b (a_Var_f x) = b',
      H : forall x, x \notin ?L' -> AnnDefEq _ ?D (open_co_wrt_tm ?g (a_Var_f x))
            (open_tm_wrt_tm ?a' (a_Var_f x)) (open_tm_wrt_tm ?b' (a_Var_f x)) |- _ =>
        let x := fresh "x" in let Fx := fresh "Fx" in
        take_fresh (L \u L' \u support_tm a \u support_tm a' \u support_tm b \u support_tm b') x Fx;
        let Ha := fresh in let Hb := fresh in
        destruct (IH x ltac:(fsetdec) _ _ (H x ltac:(fsetdec))) as [Ha Hb];
        apply (opening_injective_tm x) in Ha; [|fsetdec|fsetdec];
        apply (opening_injective_tm x) in Hb; [|fsetdec|fsetdec]; subst
    end
  | match goal with
    | IH : forall x, x \notin ?L -> forall a' b', AnnDefEq ?G ?D (open_co_wrt_co ?g (g_Var_f x)) a' b' ->
         open_tm_wrt_co ?a (g_Var_f x) = a' /\ open_tm_wrt_co ?b (g_Var_f x) = b',
      H : forall x, x \notin ?L' -> AnnDefEq _ ?D (open_co_wrt_co ?g (g_Var_f x))
            (open_tm_wrt_co ?a' (g_Var_f x)) (open_tm_wrt_co ?b' (g_Var_f x)) |- _ =>
        let x := fresh "x" in let Fx := fresh "Fx" in
        take_fresh (L \u L' \u support_tm a \u support_tm a' \u support_tm b \u support_tm b') x Fx;
        let Ha := fresh in let Hb := fresh in
        destruct (IH x ltac:(fsetdec) _ _ (H x ltac:(fsetdec))) as [Ha Hb];
        apply (opening_injective_co x) in Ha; [|fsetdec|fsetdec];
        apply (opening_injective_co x) in Hb; [|fsetdec|fsetdec]; subst
    end].

Ltac unique_cong_right :=
  first [
    match goal with
    | H : forall x, x \notin ?L -> open_tm_wrt_tm ?a (a_Var_f x) = open_tm_wrt_tm ?b ?u,
      H' : forall x, x \notin ?L' -> open_tm_wrt_tm ?a' (a_Var_f x) = open_tm_wrt_tm ?b ?u
      |- ?a = ?a' =>
        let x := fresh "x" in let Fx := fresh "Fx" in
        take_fresh (L \u L' \u support_tm a \u support_tm a') x Fx;
        apply (opening_injective_tm x); [fsetdec | fsetdec | rewrite H, H'; [reflexivity | fsetdec | fsetdec]]
    end
  | match goal with
    | H : forall x, x \notin ?L -> open_tm_wrt_co ?a (g_Var_f x) = open_tm_wrt_co ?b ?u,
      H' : forall x, x \notin ?L' -> open_tm_wrt_co ?a' (g_Var_f x) = open_tm_wrt_co ?b ?u
      |- ?a = ?a' =>
        let x := fresh "x" in let Fx := fresh "Fx" in
        take_fresh (L \u L' \u support_tm a \u support_tm a') x Fx;
        apply (opening_injective_co x); [fsetdec | fsetdec | rewrite H, H'; [reflexivity | fsetdec | fsetdec]]
    end].

Lemma ann_unique :
  (forall G a A, AnnTyping G a A -> forall B, AnnTyping G a B -> A = B) /\
  (forall G p, AnnPropWff G p -> True) /\
  (forall G D g p q, AnnIso G D g p q -> forall p' q', AnnIso G D g p' q' -> p = p' /\ q = q') /\
  (forall G D g a b, AnnDefEq G D g a b -> forall a' b', AnnDefEq G D g a' b' -> a = a' /\ b = b') /\
  (forall G, AnnCtx G -> True).
Proof.
  apply ann_ind; intros; try exact I;
  match goal with H : AnnTyping _ _ ?T |- _ = ?T => inversion H; subst; clear H
                 | H : AnnIso _ _ _ ?p ?q |- _ = ?p /\ _ = ?q => inversion H; subst; clear H
                 | H : AnnDefEq _ _ _ ?a ?b |- _ = ?a /\ _ = ?b => inversion H; subst; clear H end;
  try solve [auto].
  all: uniqueness_premises; try solve [auto].
  all: try match goal with
  | H : binds ?x ?s ?G, H' : binds ?x ?s' ?G, HC : AnnCtx ?G |- _ =>
    let E := fresh in
    assert (E : s = s') by (eapply binds_unique; [exact H|exact H'|apply ann_ctx_uniq; exact HC]);
    inversion E; subst; auto
  end.
  all: try match goal with
  | H : binds _ (Ax _ _) an_toplevel, H' : binds _ (Ax _ _) an_toplevel |- _ =>
    apply fix_binding in H as [? [? ?]]; apply fix_binding in H' as [? [? ?]]; congruence
  end.
  all: try unique_cong_open.
  all: repeat split; f_equal; try unique_abs_open; try unique_cong_right.
Qed.

Definition eq_unique := proj1 (proj2 (proj2 (proj2 ann_unique))).

(* Preservation of typing and of erased free-variable bounds. *)
Lemma erased_irrel_beta_support G A w B b z :
  AnnTyping G (a_Abs Irrel A w) (a_Pi Irrel A B) ->
  AnnTyping G b A ->
  z `in` support_tm (erase_tm (open_tm_wrt_tm w b)) ->
  z `in` support_tm (erase_tm w).
Proof.
  intros Hw Hb Hz.
  inversion Hw; subst.
  take_fresh (L \u support_tm (erase_tm w) \u {{z}}) x Hx.
  match goal with
  | H : forall y, y \notin L -> RhoCheck Irrel y _ |- _ =>
      specialize (H x ltac:(fsetdec)); inversion H; subst; clear H
  end.
  unfold open_tm_wrt_tm in *.
  rewrite erase_open_tm_tm in *.
  change (erase_tm (a_Var_f x)) with (a_Var_f x) in *.
  assert (HS : x \notin support_tm (open_tm_wrt_tm_rec 0 (a_Var_f x) (erase_tm w))).
  { change (a_Var_f x) with (erase_tm (a_Var_f x)).
    rewrite <- erase_open_tm_tm, support_erase_tm, erase_open_tm_tm.
    assumption. }
  pose proof (scoped_erase_tm _ _ _ (proj1 (typing_scoped _ _ _ Hb))) as Hbs.
  pose proof (open_intro_term (erase_tm w) (erase_tm b) x ltac:(fsetdec) Hbs) as Heq.
  unfold open_tm_wrt_tm in Heq.
  rewrite <- Heq in Hz; clear Heq.
  set (t := open_tm_wrt_tm_rec 0 (a_Var_f x) (erase_tm w)) in *.
  replace (subst_free_tm (replace_term x (erase_tm b)) g_Var_f t) with t in Hz
    by (symmetry; fix_subst_fresh).
  subst t.
  apply (proj2 (support_open_tm_tm (erase_tm w) 0 (a_Var_f x))) in Hz.
  simpl in Hz; fsetdec.
Qed.

Lemma head_erased_support : forall G a a',
  head_reduction G a a' -> forall A, AnnTyping G a A ->
  support_tm (erase_tm a') [<=] support_tm (erase_tm a).
Proof.
  induction 1; intros T HT z Hz.
  - inversion HT; subst. destruct rho; simpl in *;
      match goal with
      | IH : forall _, AnnTyping G a _ -> _ [<=] _, Ht : AnnTyping G a _ |- _ =>
          specialize (IH _ Ht); fsetdec
      end.
  - inversion HT; subst. destruct rho; simpl in *.
    + unfold open_tm_wrt_tm in Hz. rewrite erase_open_tm_tm in Hz.
      apply (proj2 (support_open_tm_tm (erase_tm w) 0 (erase_tm a))) in Hz.
      fsetdec.
    + inversion H6; subst; apply AtomSetImpl.union_2; eapply erased_irrel_beta_support; [eassumption|eassumption|exact Hz].
  - inversion HT; subst; simpl in *.
    match goal with
    | IH : forall _, AnnTyping G a _ -> _ [<=] _, Ht : AnnTyping G a _ |- _ =>
      specialize (IH _ Ht); fsetdec
    end.
  - unfold open_tm_wrt_co in Hz. rewrite erase_open_co_tm in Hz; simpl in *; fsetdec.
  - inversion HT; subst; simpl in *.
    match goal with
    | IH : forall x, x \notin L -> forall _, AnnTyping _ _ _ -> _ [<=] _,
      Ht : forall x, x \notin ?L' -> AnnTyping _ _ _ |- _ =>
      let x := fresh "x" in let Hx := fresh "Hx" in
      take_fresh (L \u L' \u {{z}}) x Hx;
      specialize (IH x ltac:(fsetdec) _ (Ht x ltac:(fsetdec)));
      unfold open_tm_wrt_tm in IH; rewrite !erase_open_tm_tm in IH; simpl in IH;
      pose proof (proj1 (support_open_tm_tm (erase_tm b') 0 (a_Var_f x))) as Hl;
      pose proof (proj2 (support_open_tm_tm (erase_tm b) 0 (a_Var_f x))) as Hr;
      simpl in Hr; fsetdec
    end.
  - apply fix_binding in H as [-> [-> ->]]. simpl in Hz. fsetdec.
  - inversion HT; subst; simpl in *.
    match goal with
    | IH : forall _, AnnTyping G a _ -> _ [<=] _, Ht : AnnTyping G a _ |- _ =>
      specialize (IH _ Ht); fsetdec
    end.
  - exact Hz.
  - subst b' g'. destruct rho; exact Hz.
  - subst g1' g'. exact Hz.
Qed.

Ltac invert_term_typing :=
  match goal with
  | H : AnnTyping _ (a_Abs _ _ _) _ |- _ => inversion H; subst; clear H
  | H : AnnTyping _ (a_CAbs _ _) _ |- _ => inversion H; subst; clear H
  | H : AnnTyping _ (a_Conv _ _) _ |- _ => inversion H; subst; clear H
  end.

Theorem preservation : forall G a A, AnnTyping G a A -> forall a', head_reduction G a a' -> AnnTyping G a' A.
Proof.
  intros G a T HT a' H. revert T HT.
  induction H; intros T HT; inversion HT; subst; clear HT.
  - eapply An_App; eauto.
  - invert_term_typing. eapply typing_beta_term; eauto.
  - eapply An_CApp; eauto.
  - invert_term_typing. eapply typing_beta_co; eauto.
  - eapply An_Abs with (L := L \u L0); [assumption| |].
    + intros x Hx. eapply H1; [fsetdec|].
      match goal with Ht : forall z, z \notin L0 -> AnnTyping _ _ _ |- _ => apply Ht; fsetdec end.
    + intros x Hx. constructor.
      pose proof (H0 x ltac:(fsetdec)) as Hstep.
      match goal with Ht : forall z, z \notin L0 -> AnnTyping _ _ _ |- _ =>
        pose proof (head_erased_support _ _ _ Hstep _ (Ht x ltac:(fsetdec))) as HS
      end.
      rewrite !support_erase_tm in HS.
      match goal with Hc : forall z, z \notin L0 -> RhoCheck Irrel z _ |- _ =>
        specialize (Hc x ltac:(fsetdec)); inversion Hc; fsetdec
      end.
  - apply fix_binding in H as [-> [-> ->]].
    match goal with Hb : binds _ _ an_toplevel |- _ =>
      apply fix_binding in Hb as [_ [_ ->]]
    end.
    now apply fix_def_typing.
  - eapply An_Conv; eauto.
  - invert_term_typing.
    eapply An_Conv; [eassumption| |assumption].
    eapply An_Trans with (A := a_Star) (A1 := a_Star) (g3 := g_Refl a_Star);
      try solve [eauto using type_validity].
    eapply An_Refl with (A := a_Star). constructor. eauto using typing_ctx.
  - invert_term_typing.
    match goal with
    | Hg : AnnDefEq G (dom G) g (a_Pi _ _ _) (a_Pi _ _ _),
      Hc : AnnDefEq G (dom G) g ?X (a_Pi _ _ _) |- _ =>
      let Ha := fresh in let Hb := fresh in
      destruct (eq_unique _ _ _ _ _ Hg _ _ Hc) as [Ha Hb];
      inversion Hb; subst; clear Hb Hc
    end.
    match goal with
    | Hv : AnnTyping G v _ |- _ =>
        let H := fresh in pose proof (type_validity _ _ _ Hv) as H;
        inversion H; subst; clear H
    end.
    match goal with Ht : AnnTyping G (a_Pi _ _ _) a_Star |- _ =>
      let H := fresh in inversion Ht as [ | | ? ? ? ? ? ? H | | | | | | | ]; subst
    end.
    assert (Hd : AnnDefEq G (dom G) (g_PiFst g) A1 A) by (eapply An_PiFst; eassumption).
    assert (Hs : AnnDefEq G (dom G) (g_Sym (g_PiFst g)) A A1).
    { eapply An_Sym with (g1 := g_Refl a_Star); try eassumption.
      apply An_Refl with (A := a_Star). constructor. eauto using typing_ctx. }
    assert (Hb' : AnnTyping G (a_Conv b (g_Sym (g_PiFst g))) A1)
      by (eapply An_Conv; eassumption).
    eapply An_Conv.
    + eapply An_App; eassumption.
    + eapply An_PiSnd; [eassumption | eapply An_EraseEq; [exact Hb'|eassumption|reflexivity|exact Hd]
                       |exact Hb'|eassumption].
    + eapply instantiate_pi; eassumption.
  - invert_term_typing.
    match goal with
    | Hg : AnnDefEq G (dom G) g (a_CPi _ _) (a_CPi _ _),
      Hc : AnnDefEq G (dom G) g ?X (a_CPi _ _) |- _ =>
      let Ha := fresh in let Hb := fresh in
      destruct (eq_unique _ _ _ _ _ Hg _ _ Hc) as [Ha Hb];
      inversion Hb; subst; clear Hb Hc
    end.
    destruct phi1 as [u w T].
    assert (Hcast : AnnDefEq G (dom G) (g_Cast g1 (g_Sym (g_CPiFst g))) u w).
    { eapply An_Cast; [eassumption|]. apply An_IsoSym.
      eapply An_CPiFst; eassumption. }
    eapply An_Conv.
    + eapply An_CApp; eassumption.
    + eapply An_CPiSnd; eassumption.
    + eapply instantiate_cpi; eassumption.
Qed.

(* Renaming a term binder. *)
Lemma open_close_rename :
  (forall e : tm, forall k x y, open_tm_wrt_tm_rec k (a_Var_f y) (close_term_tm k x e) = subst_free_tm (replace_term x (a_Var_f y)) g_Var_f e) /\
  (forall e : brs, forall k x y, open_brs_wrt_tm_rec k (a_Var_f y) (close_term_brs k x e) = subst_free_brs (replace_term x (a_Var_f y)) g_Var_f e) /\
  (forall e : co, forall k x y, open_co_wrt_tm_rec k (a_Var_f y) (close_term_co k x e) = subst_free_co (replace_term x (a_Var_f y)) g_Var_f e) /\
  (forall e : constraint, forall k x y, open_constraint_wrt_tm_rec k (a_Var_f y) (close_term_constraint k x e) = subst_free_constraint (replace_term x (a_Var_f y)) g_Var_f e).
Proof.
  apply syntax_ind; simpl; intros.
  all: try solve [f_equal; auto].
  - destruct (le_lt_dec k n).
    + change ((match lt_eq_lt_dec (S n) k with
               | inleft (left _) => a_Var_b (S n)
               | inleft (right _) => a_Var_f y
               | inright _ => a_Var_b (S n - 1) end) = a_Var_b n).
      destruct (lt_eq_lt_dec (S n) k) as [[?|?]|?]; try lia; f_equal; lia.
    + change ((match lt_eq_lt_dec n k with
               | inleft (left _) => a_Var_b n
               | inleft (right _) => a_Var_f y
               | inright _ => a_Var_b (n - 1) end) = a_Var_b n).
      destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try lia; reflexivity.
  - unfold replace_term.
    destruct (@eq_dec Atom.atom EqDec_eq_of_X x0 x) as [Heq|Hneq]; [|reflexivity].
    change ((match lt_eq_lt_dec k k with
               | inleft (left _) => a_Var_b k
               | inleft (right _) => a_Var_f y
               | inright _ => a_Var_b (k - 1) end) = a_Var_f y).
    destruct (lt_eq_lt_dec k k) as [[?|?]|?]; try lia; reflexivity.
Qed.

Lemma binder_rename a x y :
  x \notin support_tm a ->
  subst_free_tm (replace_term x (a_Var_f y)) g_Var_f (open_tm_wrt_tm a (a_Var_f x)) =
  open_tm_wrt_tm a (a_Var_f y).
Proof. intro H; now apply open_intro_term. Qed.

Lemma head_subst G a b :
  head_reduction G a b -> forall E W ft fc, typed_subst G E W ft fc ->
  head_reduction E (subst_free_tm ft fc a) (subst_free_tm ft fc b).
Proof.
  induction 1; intros E W ft fc HT; destruct HT as [Hm [HE HM]];
    cbn [subst_free_tm subst_free_co subst_free_constraint].
  - apply An_AppLeft; [eauto using lc_subst_tm | exact (IHhead_reduction E W ft fc (conj Hm (conj HE HM)))].
  - commute_subst_open. apply An_AppAbs; [eauto using lc_subst_tm|].
    exact (proj2 values_subst _ H0 _ _ _ Hm).
  - apply An_CAppLeft; [eauto using lc_subst_co | exact (IHhead_reduction E W ft fc (conj Hm (conj HE HM)))].
  - commute_subst_open. apply An_CAppCAbs.
    + eauto using lc_subst_constraint.
    + exact (lc_subst_tm _ _ _ _ Hm H0).
    + eauto using lc_subst_co.
  - assert (AT : AnnTyping E (subst_free_tm ft fc A) a_Star)
      by (exact (proj1 ann_subst _ _ _ H _ _ _ E (conj Hm (conj HE HM)))).
    apply An_AbsTerm with (L := L \u W \u dom E); [exact AT|].
    intros x Hx.
    assert (HE' : AnnCtx (x ~ Tm (subst_free_tm ft fc A) ++ E))
      by (apply An_ConsTm; [exact HE | exact AT | fsetdec]).
    assert (HM' : CtxMap (x ~ Tm A ++ G) (x ~ Tm (subst_free_tm ft fc A) ++ E) ft fc)
      by (apply extend_tm_ctx_map; [exact HE' | exact HM | eapply map_term_id; [exact Hm|fsetdec]]).
    pose proof (H1 x ltac:(fsetdec) _ _ _ _ (conj Hm (conj HE' HM'))) as HH.
    subst_open_fresh x; exact HH.
  - apply fix_binding in H as [-> [-> ->]]. change (head_reduction E (a_Fam Fix) FixDef).
    eapply An_Axiom with (A := FixTy). unfold an_toplevel; simpl; auto.
  - apply An_ConvTerm; [eauto using lc_subst_co | exact (IHhead_reduction E W ft fc (conj Hm (conj HE HM)))].
  - apply An_Combine; try solve [eauto using lc_subst_co].
    exact (proj2 values_subst _ H1 _ _ _ Hm).
  - subst b' g'. eapply An_Push.
    + exact (proj2 values_subst _ H _ _ _ Hm).
    + exact (proj1 (proj2 (proj2 (proj2 ann_subst))) _ _ _ _ _ H0 _ _ _ _
        _ (conj Hm (conj HE HM)) (ctx_map_co _ _ _ _ HM)).
    + reflexivity.
    + reflexivity.
  - subst g1' g'. eapply An_CPush.
    + exact (proj2 values_subst _ H _ _ _ Hm).
    + exact (proj1 (proj2 (proj2 (proj2 ann_subst))) _ _ _ _ _ H0 _ _ _ _
        _ (conj Hm (conj HE HM)) (ctx_map_co _ _ _ _ HM)).
    + reflexivity.
    + reflexivity.
Qed.

Lemma rename_head_binder G x y A :
  x <> y -> x \notin dom G -> y \notin dom G ->
  AnnTyping G A a_Star ->
  typed_subst (x ~ Tm A ++ G) (y ~ Tm A ++ G)
    ({{x}} \u support_tm (a_Var_f y)) (replace_term x (a_Var_f y)) g_Var_f.
Proof.
  intros Hxy Hx Hy HA.
  assert (HC : AnnCtx (y ~ Tm A ++ G)) by (constructor; eauto using typing_ctx).
  assert (HY : AnnTyping (y ~ Tm A ++ G) (a_Var_f y) A)
    by (constructor; [exact HC | simpl; auto]).
  destruct (subst_remove_tm (y ~ Tm A ++ G) x (a_Var_f y) A ltac:(simpl; fsetdec) HY) as [Hm [HE HM]].
  split; [exact Hm|split; [exact HE|]].
  constructor.
  - intros z B HB; apply (ctx_map_tm _ _ _ _ HM z B).
    exact (binds_weaken sort z (Tm B) (x ~ Tm A) (y ~ Tm A) G HB).
  - intros z b c B HB Hz; apply (ctx_map_co _ _ _ _ HM z b c B).
    + exact (binds_weaken sort z (Co (Eq b c B)) (x ~ Tm A) (y ~ Tm A) G HB).
    + simpl in *; fsetdec.
Qed.

(* Parallel reduction on erased syntax. *)
Fixpoint pure_tm a :=
  match a with
  | a_Star | a_Var_b _ | a_Var_f _ | a_Bullet | a_Fam _ | a_Const _ => True
  | a_UAbs _ b | a_UCAbs b => pure_tm b
  | a_App a _ b | a_Pi _ a b => pure_tm a /\ pure_tm b
  | a_CPi p B => pure_constraint p /\ pure_tm B
  | a_CApp a g => pure_tm a /\ g = g_Triv
  | _ => False
  end
with pure_constraint p :=
  match p with Eq a b A => pure_tm a /\ pure_tm b /\ pure_tm A end.

Lemma erase_pure :
  (forall a, pure_tm (erase_tm a)) /\ (forall b : brs, True) /\
  (forall g : co, True) /\ (forall p, pure_constraint (erase_constraint p)).
Proof. apply syntax_ind; simpl; intros; try destruct rho; simpl; tauto. Qed.
Definition erase_pure_tm := proj1 erase_pure.

Lemma pure_open_term :
  (forall a k u, pure_tm u -> (pure_tm (open_tm_wrt_tm_rec k u a) <-> pure_tm a)) /\
  (forall b : brs, True) /\ (forall g : co, True) /\
  (forall p k u, pure_tm u -> (pure_constraint (open_constraint_wrt_tm_rec k u p) <-> pure_constraint p)).
Proof.
  apply syntax_ind; simpl; intros; try tauto.
  all: try solve [destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto].
  all: try match goal with
  | |- (_ /\ open_co_wrt_tm_rec _ _ ?g = g_Triv <-> _) =>
      destruct g; simpl; try (split; intros [? Hc]; discriminate); auto
  end.
  all: repeat match goal with
  | H : forall k u, pure_tm u -> _ <-> _ |- _ =>
    first [rewrite (H k u) by assumption | rewrite (H (S k) u) by assumption]
  end; reflexivity.
Qed.

Lemma pure_co_open_var :
  (forall a k x, pure_tm (open_tm_wrt_co_rec k (g_Var_f x) a) -> pure_tm a) /\
  (forall b : brs, True) /\ (forall g : co, True) /\
  (forall p k x, pure_constraint (open_constraint_wrt_co_rec k (g_Var_f x) p) -> pure_constraint p).
Proof.
  apply syntax_ind; simpl; intros; destruct_ands; try contradiction; repeat split; eauto.
  all: match goal with H : open_co_wrt_co_rec _ _ ?g = g_Triv |- _ =>
    destruct g; simpl in H; try discriminate; auto;
    match type of H with context [lt_eq_lt_dec ?n ?k] =>
      destruct (lt_eq_lt_dec n k) as [[?|?]|?]; discriminate
    end
  end.
Qed.

Lemma pure_co_open :
  (forall a k g, pure_tm a -> open_tm_wrt_co_rec k g a = a) /\
  (forall b : brs, True) /\ (forall g : co, True) /\
  (forall p k g, pure_constraint p -> open_constraint_wrt_co_rec k g p = p).
Proof.
  apply syntax_ind; simpl; intros; destruct_ands; subst; try contradiction; f_equal; auto.
Qed.
Definition pure_co_open_tm := proj1 pure_co_open.

Lemma pure_subst_tm :
  (forall a ft, (forall x, pure_tm (ft x)) -> pure_tm a -> pure_tm (subst_free_tm ft g_Var_f a)) /\
  (forall b : brs, True) /\ (forall g : co, True) /\
  (forall p ft, (forall x, pure_tm (ft x)) -> pure_constraint p -> pure_constraint (subst_free_constraint ft g_Var_f p)).
Proof. apply syntax_ind; simpl; intros; destruct_ands; subst; simpl; tauto || auto. Qed.

Lemma pure_scoped_erased n : forall a, syntax_size_tm a < n ->
  scoped_tm 0 0 a -> pure_tm a -> erased_tm a.
Proof.
  induction n as [|n IH]; intros a Hn Hs Hp; [lia|].
  destruct a; simpl in Hn, Hs, Hp; try contradiction; try lia.
  all: destruct_ands.
  all: try solve [constructor; eauto].
  - eapply erased_a_Abs with (L := {}).
    intros x _. unfold open_tm_wrt_tm.
    apply IH; [rewrite size_open_tm_tm; lia | apply scoped_open_tm_tm; [lia|exact I|assumption]
              |apply (proj2 (proj1 pure_open_term _ 0 (a_Var_f x) I)); assumption].
  - constructor; apply IH; auto; lia.
  - eapply erased_a_Pi with (L := {}); [apply IH; auto; lia|].
    intros x _. unfold open_tm_wrt_tm.
    apply IH; [rewrite size_open_tm_tm; lia | apply scoped_open_tm_tm; [lia|exact I|assumption]
              |apply (proj2 (proj1 pure_open_term _ 0 (a_Var_f x) I)); assumption].
  - destruct phi. simpl in *. destruct_ands.
    eapply erased_a_CPi with (L := {}); try solve [apply IH; auto; lia].
    intros x _. unfold open_tm_wrt_co.
    apply IH; [rewrite size_open_co_tm; lia | apply scoped_open_co_tm; [lia|exact I|assumption]
              |now rewrite pure_co_open_tm].
  - eapply erased_a_CAbs with (L := {}).
    intros x _. unfold open_tm_wrt_co.
    apply IH; [rewrite size_open_co_tm; lia | apply scoped_open_co_tm; [lia|exact I|assumption]
              |now rewrite pure_co_open_tm].
  - subst. apply erased_a_CApp. apply IH; auto; lia.
Qed.

Lemma erased_of_scoped a : scoped_tm 0 0 a -> erased_tm (erase_tm a).
Proof.
  intro H.
  eapply pure_scoped_erased with (n := S (syntax_size_tm (erase_tm a)));
    [lia|now apply scoped_erase_tm|apply erase_pure_tm].
Qed.

Definition PR := Par nil {}.
Definition MP := MultiPar nil {}.

Lemma par_change_context G D a b :
  Par G D a b -> forall E D', Par E D' a b.
Proof. induction 1; intros; eauto using Par. Qed.

Lemma par_scoped G D a b :
  Par G D a b -> scoped_tm 0 0 a /\ scoped_tm 0 0 b.
Proof.
  induction 1; try solve [split; apply (proj1 lc_scoped); assumption].
  all: use_fresh_open; simpl in *; destruct_ands; repeat split; try assumption.
  all: try solve [discharge_scoped_open].
  apply fix_erased_binding in H as [-> [-> ->]]. simpl; repeat split; lia.
Qed.

Lemma par_pure G D a b :
  Par G D a b -> pure_tm a -> pure_tm b.
Proof.
  induction 1; simpl in *; intros Hp; try assumption.
  all: destruct_ands; repeat split; auto.
  - unfold open_tm_wrt_tm. apply (proj1 pure_open_term); auto.
  - unfold open_tm_wrt_co. rewrite pure_co_open_tm; auto.
  - use_fresh_open. apply (proj1 pure_open_term _ 0 (a_Var_f (proj1_sig (atom_fresh L))) I).
    apply H0. now apply (proj2 (proj1 pure_open_term _ 0 (a_Var_f (proj1_sig (atom_fresh L))) I)).
  - use_fresh_open. apply (proj1 pure_open_term _ 0 (a_Var_f (proj1_sig (atom_fresh L))) I).
    apply H1. now apply (proj2 (proj1 pure_open_term _ 0 (a_Var_f (proj1_sig (atom_fresh L))) I)).
  - use_fresh_open. eapply (proj1 pure_co_open_var _ 0). apply H0. unfold open_tm_wrt_co. now rewrite pure_co_open_tm.
  - use_fresh_open. eapply (proj1 pure_co_open_var _ 0). apply H2. unfold open_tm_wrt_co. now rewrite pure_co_open_tm.
  - apply fix_erased_binding in H as [-> [-> ->]]. apply erase_pure_tm.
Qed.

#[local] Hint Constructors Par MultiPar : par.

Lemma pure_tm_open_var a x :
  pure_tm (open_tm_wrt_tm a (a_Var_f x)) <-> pure_tm a.
Proof. apply (proj1 pure_open_term a 0 (a_Var_f x) I). Qed.

Lemma pure_tm_open_co a g :
  pure_tm a -> open_tm_wrt_co a g = a.
Proof. apply pure_co_open_tm. Qed.

Lemma par_map_refl G D W W' ft ft' :
  CleanMaps W ft g_Var_f -> CleanMaps W' ft' g_Var_f ->
  (forall x, Par G D (ft x) (ft' x)) ->
  forall n a, syntax_size_tm a < n -> pure_tm a -> scoped_tm 0 0 a ->
  Par G D (subst_free_tm ft g_Var_f a) (subst_free_tm ft' g_Var_f a).
Proof.
  intros Hm Hm' Hvar n. induction n as [|n IH]; intros a Hn Hp Hsc; [lia|].
  destruct a; simpl in Hn, Hp, Hsc |- *; try contradiction; try lia.
  all: destruct_ands; subst.
  all: try solve [apply Hvar | constructor; constructor].
  all: try solve [apply Par_App; apply IH; auto; lia | apply Par_CApp; apply IH; auto; lia].
  - eapply Par_Abs with (L := W \u W'). intros x Hx.
    assert (Hstep : Par G D (subst_free_tm ft g_Var_f (open_tm_wrt_tm a (a_Var_f x)))
                         (subst_free_tm ft' g_Var_f (open_tm_wrt_tm a (a_Var_f x)))).
    { apply IH; [unfold open_tm_wrt_tm; rewrite size_open_tm_tm; lia
               |now apply pure_tm_open_var | discharge_scoped_open]. }
    rewrite (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in Hstep.
    cbn [subst_free_tm] in Hstep.
    rewrite (map_term_id _ _ _ Hm x ltac:(fsetdec)),
            (map_term_id _ _ _ Hm' x ltac:(fsetdec)) in Hstep.
    exact Hstep.
  - eapply Par_Pi with (L := W \u W'); [apply IH; auto; lia |].
    intros x Hx.
    assert (Hstep : Par G D (subst_free_tm ft g_Var_f (open_tm_wrt_tm a2 (a_Var_f x)))
                         (subst_free_tm ft' g_Var_f (open_tm_wrt_tm a2 (a_Var_f x)))).
    { apply IH; [unfold open_tm_wrt_tm; rewrite size_open_tm_tm; lia
               |now apply pure_tm_open_var | discharge_scoped_open]. }
    rewrite (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in Hstep.
    cbn [subst_free_tm] in Hstep.
    rewrite (map_term_id _ _ _ Hm x ltac:(fsetdec)),
            (map_term_id _ _ _ Hm' x ltac:(fsetdec)) in Hstep.
    exact Hstep.
  - destruct phi; simpl in *; destruct_ands.
    eapply Par_CPi with (L := {}); try solve [apply IH; auto; lia].
    intros x _.
    assert (Hstep : Par G D (subst_free_tm ft g_Var_f (open_tm_wrt_co a (g_Var_f x)))
                         (subst_free_tm ft' g_Var_f (open_tm_wrt_co a (g_Var_f x)))).
    { apply IH; [unfold open_tm_wrt_co; rewrite size_open_co_tm; lia
               |now rewrite pure_tm_open_co |discharge_scoped_open]. }
    rewrite (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in Hstep. exact Hstep.
  - eapply Par_CAbs with (L := {}). intros x _.
    assert (Hstep : Par G D (subst_free_tm ft g_Var_f (open_tm_wrt_co a (g_Var_f x)))
                         (subst_free_tm ft' g_Var_f (open_tm_wrt_co a (g_Var_f x)))).
    { apply IH; [unfold open_tm_wrt_co; rewrite size_open_co_tm; lia
               |now rewrite pure_tm_open_co |discharge_scoped_open]. }
    rewrite (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in Hstep. exact Hstep.
Qed.

Lemma par_subst G D a b W W' ft ft' :
  CleanMaps W ft g_Var_f -> CleanMaps W' ft' g_Var_f ->
  (forall x, Par G D (ft x) (ft' x)) ->
  Par G D a b -> pure_tm a ->
  Par G D (subst_free_tm ft g_Var_f a) (subst_free_tm ft' g_Var_f b).
Proof.
  intros Hm Hm' Hvar H. induction H; simpl; intros Hp; destruct_ands.
  - eapply par_map_refl with (n := S (syntax_size_tm a));
      [exact Hm | exact Hm' | exact Hvar | lia | exact Hp | exact (proj1 lc_scoped _ H)].
  - rewrite (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')).
    apply Par_Beta; auto.
  - apply Par_App; auto.
  - rewrite (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')).
    apply Par_CBeta; auto.
  - apply Par_CApp; auto.
  - apply Par_Abs with (L := L \u W \u W'). intros x Hx.
    specialize (H0 x ltac:(fsetdec) Hvar (proj2 (pure_tm_open_var a x) Hp)).
    rewrite (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in H0.
    cbn [subst_free_tm] in H0.
    rewrite (map_term_id _ _ _ Hm x ltac:(fsetdec)),
            (map_term_id _ _ _ Hm' x ltac:(fsetdec)) in H0. exact H0.
  - apply Par_Pi with (L := L \u W \u W'); [auto|]. intros x Hx.
    specialize (H1 x ltac:(fsetdec) Hvar (proj2 (pure_tm_open_var B x) ltac:(assumption))).
    rewrite (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_tm_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in H1.
    cbn [subst_free_tm] in H1.
    rewrite (map_term_id _ _ _ Hm x ltac:(fsetdec)),
            (map_term_id _ _ _ Hm' x ltac:(fsetdec)) in H1. exact H1.
  - apply Par_CAbs with (L := L). intros x Hx.
    specialize (H0 x Hx Hvar ltac:(now rewrite pure_tm_open_co)).
    rewrite (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in H0; exact H0.
  - apply Par_CPi with (L := L); try solve [auto]. intros x Hx.
    specialize (H2 x Hx Hvar ltac:(now rewrite pure_tm_open_co)).
    rewrite (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm)),
            (subst_open_co_tm_0 _ _ _ _ (maps_scoped _ _ _ Hm')) in H2; exact H2.
  - apply fix_erased_binding in H as [-> [-> ->]]. change (Par G D (a_Fam Fix) (erase_tm FixDef)).
    eapply Par_Axiom with (A := erase_tm FixTy). unfold toplevel, an_toplevel; simpl; auto.
Qed.

Lemma par_open_term G D L a b u v :
  (forall x, x \notin L -> Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x))) ->
  pure_tm a -> Par G D u v ->
  Par G D (open_tm_wrt_tm a u) (open_tm_wrt_tm b v).
Proof.
  intros H Hp Huv. destruct (par_scoped _ _ _ _ Huv) as [Hs Hs'].
  take_fresh (L \u support_tm a \u support_tm b) x Hx.
  rewrite <- (open_intro_term a u x ltac:(fsetdec) Hs),
          <- (open_intro_term b v x ltac:(fsetdec) Hs').
  eapply par_subst; [apply replace_term_maps; exact Hs | apply replace_term_maps; exact Hs' | |apply H; fsetdec | now apply pure_tm_open_var].
  intros y. destruct (x == y) as [->|Hxy].
  - now rewrite !replace_term_eq.
  - rewrite !replace_term_neq by assumption. constructor. constructor.
Qed.

Lemma par_refl_scoped G D a : scoped_tm 0 0 a -> Par G D a a.
Proof. constructor; now apply scoped_lc_tm. Qed.
Lemma par_refl_left G D a b : Par G D a b -> Par G D a a.
Proof. intro H; apply par_refl_scoped; exact (proj1 (par_scoped _ _ _ _ H)). Qed.
Lemma par_refl_right G D a b : Par G D a b -> Par G D b b.
Proof. intro H; apply par_refl_scoped; exact (proj2 (par_scoped _ _ _ _ H)). Qed.

Lemma par_uabs_inv G D r a b :
  Par G D (a_UAbs r a) b ->
  exists b0 L, b = a_UAbs r b0 /\
    forall x, x \notin L ->
      Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b0 (a_Var_f x)).
Proof.
  intro H. inversion H; subst; eauto 8.
  exists a, {}. split; [reflexivity|]. intros x _.
  apply par_refl_scoped.
  pose proof (proj1 (par_scoped _ _ _ _ H)) as HC. simpl in HC.
  discharge_scoped_open.
Qed.

Lemma par_ucabs_inv G D a b :
  pure_tm a -> Par G D (a_UCAbs a) b ->
  exists b0, b = a_UCAbs b0 /\ Par G D a b0.
Proof.
  intros Hp H. inversion H; subst.
  - exists a. split; [reflexivity|].
    pose proof (proj1 (par_scoped _ _ _ _ H)) as HC. simpl in HC.
    replace a with (open_tm_wrt_co a (g_Var_f Fix)) by (now apply pure_tm_open_co).
    apply par_refl_scoped. discharge_scoped_open.
  - exists a'. split; [reflexivity|].
    use_fresh_open.
    pose proof (par_pure _ _ _ _ H Hp) as Hp'.
    now rewrite !pure_tm_open_co in H3 by assumption.
Qed.

Lemma par_rename G D x y a b :
  Par G D a b -> pure_tm a ->
  Par G D (subst_free_tm (replace_term x (a_Var_f y)) g_Var_f a)
          (subst_free_tm (replace_term x (a_Var_f y)) g_Var_f b).
Proof.
  intros H Hp. eapply par_subst; [ | | | exact H | exact Hp ];
    try solve [apply replace_term_maps; exact I].
  intro z. destruct (x == z) as [->|Hneq].
  - rewrite replace_term_eq. constructor; constructor.
  - rewrite replace_term_neq by assumption. constructor; constructor.
Qed.

Lemma par_binder_join G D L a b :
  pure_tm a -> pure_tm b ->
  (forall x, x \notin L -> exists w,
   Par G D (open_tm_wrt_tm a (a_Var_f x)) w /\
   Par G D (open_tm_wrt_tm b (a_Var_f x)) w) ->
  exists w, forall x, x \notin L ->
   Par G D (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm w (a_Var_f x)) /\
   Par G D (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm w (a_Var_f x)).
Proof.
  intros Ha Hb Hjoin. take_fresh (L \u support_tm a \u support_tm b) x HF.
  destruct (Hjoin x ltac:(fsetdec)) as [w [H1 H2]].
  exists (close_term_tm 0 x w). intros y Hy.
  change (open_tm_wrt_tm (close_term_tm 0 x w) (a_Var_f y)) with (open_tm_wrt_tm_rec 0 (a_Var_f y) (close_term_tm 0 x w)).
  rewrite (proj1 open_close_rename).
  split.
  - pose proof (par_rename _ _ x y _ _ H1 (proj2 (pure_tm_open_var a x) Ha)) as H.
    now rewrite binder_rename in H by fsetdec.
  - pose proof (par_rename _ _ x y _ _ H2 (proj2 (pure_tm_open_var b x) Hb)) as H.
    now rewrite binder_rename in H by fsetdec.
Qed.

Ltac par_subjoin :=
  match goal with
  | IH : forall c, Par ?G ?D ?a ?b -> Par ?G ?D ?a c -> _ -> exists w, Par ?G ?D ?b w /\ Par ?G ?D c w,
    Hfirst : Par ?G ?D ?a ?b, H : Par ?G ?D ?a ?c, Hp : pure_tm ?a |- _ =>
      tryif constr_eq b c then fail else
      let w := fresh "w" in let H1 := fresh in let H2 := fresh in
      destruct (IH c Hfirst H Hp) as [w [H1 H2]]; clear IH
  end.

Lemma par_diamond G D a b c :
  Par G D a b -> Par G D a c -> pure_tm a ->
  exists w, Par G D b w /\ Par G D c w.
Proof.
  intro H. pose proof H as Horig. revert c Horig.
  induction H; intros c Horig Hc Hp.
  all: try solve [exists c; split; [exact Hc | eapply par_refl_right; exact Hc]].
  all: inversion Hc; subst; try solve [eexists; split; [eapply par_refl_right; exact Horig |exact Horig]].
  all: simpl in Hp; destruct_ands.
  all: repeat par_subjoin.
  all: try match goal with
  | |- exists w, Par _ _ (a_App _ ?r _) w /\ Par _ _ (a_App _ ?r _) w =>
    eexists; split; apply Par_App; eassumption
  | |- exists w, Par _ _ (a_CApp _ g_Triv) w /\ Par _ _ (a_CApp _ g_Triv) w =>
    eexists; split; apply Par_CApp; eassumption
  end.
  all: try match goal with
  | H : Par ?G ?D ?u (a_UAbs ?r ?v), Hp : pure_tm ?u |- _ =>
    let Hv := fresh in pose proof (par_pure _ _ _ _ H Hp) as Hv; simpl in Hv;
    repeat match goal with
    | H : Par ?G ?D ?u (a_UAbs ?r ?v2) |- _ =>
        tryif constr_eq v v2 then fail else
        let Hv := fresh in pose proof (par_pure _ _ _ _ H Hp) as Hv; simpl in Hv; clear H
    end
  end.
  all: try match goal with
  | H : Par ?G ?D ?u (a_UCAbs ?v), Hp : pure_tm ?u |- _ =>
    let Hv := fresh in pose proof (par_pure _ _ _ _ H Hp) as Hv; simpl in Hv;
    repeat match goal with
    | H : Par ?G ?D ?u (a_UCAbs ?v2) |- _ =>
        tryif constr_eq v v2 then fail else
        let Hv := fresh in pose proof (par_pure _ _ _ _ H Hp) as Hv; simpl in Hv; clear H
    end
  end.
  all: try match goal with
  | H : Par ?G ?D (a_UAbs ?r ?v) ?wh |- exists w, _ =>
    let z := fresh "z" in let L := fresh "L" in let E := fresh in let Hcof := fresh in
    destruct (par_uabs_inv _ _ _ _ _ H) as [z [L [E Hcof]]]; subst wh; clear H;
    repeat match goal with
    | H2 : Par G D (a_UAbs r ?v2) (a_UAbs r z) |- _ =>
      let P2 := fresh in let L2 := fresh in let Z2 := fresh in let E2 := fresh in
      destruct (par_uabs_inv _ _ _ _ _ H2) as [Z2 [L2 [E2 P2]]];
      inversion E2; subst Z2; clear H2 E2
    end;
    match goal with
    | Hb : Par G D ?b ?u |- exists w, Par _ _ (open_tm_wrt_tm _ ?b) w /\ _ =>
      exists (open_tm_wrt_tm z u); split
    | Hb : Par G D ?b ?u |- exists w, _ /\ Par _ _ (open_tm_wrt_tm _ ?b) w =>
      exists (open_tm_wrt_tm z u); split
    end;
    first [eapply Par_Beta; eassumption |
      eapply par_open_term; [eassumption|assumption|eassumption]]
  end.
  all: try match goal with
  | H : Par ?G ?D (a_UCAbs ?v) ?wh, Hv : pure_tm ?v |- exists w, _ =>
    let z := fresh "z" in let E := fresh in let Hz := fresh in
    destruct (par_ucabs_inv _ _ _ _ Hv H) as [z [E Hz]]; subst wh;
    let Hpz := fresh in pose proof (par_pure _ _ _ _ Hz Hv) as Hpz;
    repeat match goal with
    | H2 : Par G D (a_UCAbs ?v2) (a_UCAbs z), Hv2 : pure_tm ?v2 |- _ =>
        tryif constr_eq v v2 then fail else
        let P2 := fresh in let Z2 := fresh in let E2 := fresh in
        destruct (par_ucabs_inv _ _ _ _ Hv2 H2) as [Z2 [E2 P2]];
        inversion E2; subst Z2; clear H2 E2
    end;
    exists (open_tm_wrt_co z g_Triv); split;
    first [eapply Par_CBeta; eassumption |
      rewrite !pure_tm_open_co by assumption; assumption]
  end.
  all: try match goal with
  | HB : binds _ _ toplevel, HC : binds _ _ toplevel |- _ =>
    apply fix_erased_binding in HB as [? [? ?]]; apply fix_erased_binding in HC as [? [? ?]];
    subst; eexists; split; apply par_refl_scoped; simpl; repeat split; lia
  end.
  all: try match goal with
  | IH : forall x, x \notin ?L -> forall c, Par ?G ?D (open_tm_wrt_tm ?a (a_Var_f x))
       (open_tm_wrt_tm ?b (a_Var_f x)) -> Par ?G ?D (open_tm_wrt_tm ?a (a_Var_f x)) c -> _ -> _,
    H1 : forall x, x \notin ?L -> Par ?G ?D (open_tm_wrt_tm ?a (a_Var_f x)) (open_tm_wrt_tm ?b (a_Var_f x)),
    H2 : forall x, x \notin ?L2 -> Par ?G ?D (open_tm_wrt_tm ?a (a_Var_f x)) (open_tm_wrt_tm ?c (a_Var_f x)),
    Hp : pure_tm ?a |- _ =>
      let Hb := fresh in let Hc := fresh in
      assert (Hb : pure_tm b) by
        (let x := fresh in let Hd := fresh in take_fresh L x Hd;
        apply (proj1 (pure_tm_open_var b x)); eapply par_pure; [apply H1; exact Hd|now apply pure_tm_open_var]);
      assert (Hc : pure_tm c) by
        (let x := fresh in let Hd := fresh in take_fresh L2 x Hd;
        apply (proj1 (pure_tm_open_var c x)); eapply par_pure; [apply H2; exact Hd|now apply pure_tm_open_var]);
      let w := fresh in let Hw := fresh in
      destruct (par_binder_join G D (L \u L2) b c Hb Hc) as [w Hw];
      [intros x Hx; apply IH; [fsetdec|apply H1; fsetdec|apply H2; fsetdec|now apply pure_tm_open_var]
      |eexists; split;
       first [eapply Par_Abs with (L := L \u L2) | eapply Par_Pi with (L := L \u L2)];
       try eassumption; intros x Hx; apply Hw; assumption]
  end.
  - take_fresh (L \u L0) x Hx.
    assert (HS : pure_tm (open_tm_wrt_co a (g_Var_f x))) by (now rewrite pure_tm_open_co).
    pose proof (H x ltac:(fsetdec)) as Hfirst.
    pose proof (H4 x ltac:(fsetdec)) as Hsecond.
    pose proof (par_pure _ _ _ _ Horig Hp) as Hb.
    pose proof (par_pure _ _ _ _ Hc Hp) as Hc'.
    destruct (H0 x ltac:(fsetdec) _ Hfirst Hsecond HS) as [w [Hw1 Hw2]].
    simpl in Hb, Hc'.
    rewrite (pure_tm_open_co a' _ Hb) in Hw1.
    rewrite (pure_tm_open_co a'0 _ Hc') in Hw2.
    pose proof (par_pure _ _ _ _ Hw1 Hb) as Hw.
    exists (a_UCAbs w); split; apply Par_CAbs with (L := {});
      intros y _; rewrite !pure_tm_open_co by assumption; assumption.
  - take_fresh (L \u L0) x Hx.
    assert (HS : pure_tm (open_tm_wrt_co a (g_Var_f x))) by (now rewrite pure_tm_open_co).
    pose proof (H1 x ltac:(fsetdec)) as Hfirst.
    pose proof (H13 x ltac:(fsetdec)) as Hsecond.
    assert (Hp : pure_tm (a_CPi (Eq A B A1) a)) by (simpl; auto).
    pose proof (par_pure _ _ _ _ Horig Hp) as Hb.
    pose proof (par_pure _ _ _ _ Hc Hp) as Hc'.
    simpl in Hb, Hc'. destruct_ands.
    destruct (H2 x ltac:(fsetdec) _ Hfirst Hsecond HS) as [w [Hw1 Hw2]].
    rewrite (pure_tm_open_co a' _ ltac:(assumption)) in Hw1.
    rewrite (pure_tm_open_co a'0 _ ltac:(assumption)) in Hw2.
    assert (Hw : pure_tm w) by (eapply par_pure; [exact Hw1|assumption]).
    exists (a_CPi (Eq w2 w1 w0) w); split; eapply Par_CPi with (L := {});
      try assumption; intros y _; rewrite !pure_tm_open_co by assumption; assumption.
Qed.

(* Joinability of parallel reductions. *)
Lemma mp_scoped a b : MP a b -> scoped_tm 0 0 a /\ scoped_tm 0 0 b.
Proof.
  induction 1.
  - split; now apply (proj1 lc_scoped).
  - destruct (par_scoped _ _ _ _ H); tauto.
Qed.
Lemma mp_pure a b : MP a b -> pure_tm a -> pure_tm b.
Proof. induction 1; intro Hp; [exact Hp|apply IHMultiPar; eapply par_pure; eassumption]. Qed.
Lemma mp_refl a : scoped_tm 0 0 a -> MP a a.
Proof. intro H; apply MP_Refl; now apply scoped_lc_tm. Qed.
Lemma mp_single a b : PR a b -> MP a b.
Proof. intro H; eapply MP_Step; [exact H|apply mp_refl; exact (proj2 (par_scoped _ _ _ _ H))]. Qed.
Lemma mp_trans a b c : MP a b -> MP b c -> MP a c.
Proof.
  induction 1; intro M; [exact M|].
  eapply MP_Step; [eapply par_change_context; eassumption | now apply IHMultiPar].
Qed.

Lemma mp_strip a b c : PR a b -> MP a c -> pure_tm a ->
  exists w, MP b w /\ PR c w.
Proof.
  intros H Hc. revert b H.
  induction Hc; intros d Hd Hp.
  - exists d; split; [apply mp_refl; exact (proj2 (par_scoped _ _ _ _ Hd))|exact Hd].
  - destruct (par_diamond _ _ _ _ _ (par_change_context _ _ _ _ H nil {}) Hd Hp) as [w [H1 H2]].
    destruct (IHHc w H1 (par_pure _ _ _ _ H Hp)) as [z [M P]].
    exists z. split; [eapply MP_Step; eassumption | exact P].
Qed.

Definition joinable a b := exists c, MP a c /\ MP b c.

Lemma mp_confluent a b c : MP a b -> MP a c -> pure_tm a -> joinable b c.
Proof.
  intros H. revert c. induction H; intros c Hc Hp.
  - exists c. split; [exact Hc|apply mp_refl; exact (proj2 (mp_scoped _ _ Hc))].
  - destruct (mp_strip _ _ _ (par_change_context _ _ _ _ H nil {}) Hc Hp) as [w [M P]].
    destruct (IHMultiPar w M (par_pure _ _ _ _ H Hp)) as [z [M1 M2]].
    exists z. split; [exact M1 | eapply MP_Step; eassumption].
Qed.

Lemma join_refl a : scoped_tm 0 0 a -> joinable a a.
Proof. intro H; exists a; split; now apply mp_refl. Qed.
Lemma join_sym a b : joinable a b -> joinable b a.
Proof. intros [c [H1 H2]]; exists c; auto. Qed.
Lemma join_trans a b c : joinable a b -> joinable b c -> pure_tm b -> joinable a c.
Proof.
  intros [u [H1 H2]] [v [H3 H4]] Hp.
  destruct (mp_confluent _ _ _ H2 H3 Hp) as [w [M1 M2]].
  exists w; split; eapply mp_trans; eassumption.
Qed.

Lemma mp_lift (f : tm -> tm) a b :
  (forall a, scoped_tm 0 0 a -> scoped_tm 0 0 (f a)) ->
  (forall a b, PR a b -> pure_tm a -> PR (f a) (f b)) ->
  MP a b -> pure_tm a -> MP (f a) (f b).
Proof.
  intros HS HP H. induction H; intros E.
  - apply mp_refl. apply HS. now apply (proj1 lc_scoped).
  - eapply MP_Step; [apply HP; [eapply par_change_context; eassumption|assumption] |apply IHMultiPar; eauto using par_pure].
Qed.

Lemma join_lift (f : tm -> tm) a b :
  (forall a, scoped_tm 0 0 a -> scoped_tm 0 0 (f a)) ->
  (forall a b, PR a b -> pure_tm a -> PR (f a) (f b)) ->
  pure_tm a -> pure_tm b -> joinable a b -> joinable (f a) (f b).
Proof. intros HS HP HA HB [c [H1 H2]]; exists (f c); split; eapply mp_lift; eauto. Qed.

Lemma join_scoped a b : joinable a b -> scoped_tm 0 0 a /\ scoped_tm 0 0 b.
Proof.
  intros [c [H1 H2]]. split; [exact (proj1 (mp_scoped _ _ H1))|exact (proj1 (mp_scoped _ _ H2))].
Qed.

Ltac join_lift_argument a b f :=
  apply (join_lift f a b);
  [ intros; cbn [scoped_tm scoped_constraint scoped_co]; tauto
  | intros; first [apply Par_App | apply Par_CApp | eapply Par_Pi with (L := {})
                  |eapply Par_CPi with (L := {})];
      try assumption; try (intros ? ?);
      apply par_refl_scoped; try assumption; try exact I; discharge_scoped_open
  |assumption|assumption|assumption].

Lemma join_app r a a' b b' :
  pure_tm a -> pure_tm a' -> pure_tm b -> pure_tm b' ->
  joinable a a' -> joinable b b' -> joinable (a_App a r b) (a_App a' r b').
Proof.
  intros Ha Ha' Hb Hb' H1 H2.
  destruct (join_scoped _ _ H1); destruct (join_scoped _ _ H2).
  eapply join_trans with (b := a_App a' r b); [ | | simpl; auto].
  - join_lift_argument a a' (fun t => a_App t r b).
  - join_lift_argument b b' (fun t => a_App a' r t).
Qed.

Lemma join_capp a b : pure_tm a -> pure_tm b -> joinable a b ->
  joinable (a_CApp a g_Triv) (a_CApp b g_Triv).
Proof. intros; join_lift_argument a b (fun t => a_CApp t g_Triv). Qed.

Lemma close_scoped x a : scoped_tm 0 0 a -> scoped_tm 1 0 (close_term_tm 0 x a).
Proof.
  intro H. apply (proj1 (scoped_open_tm_tm _ 0 (a_Var_f x) 0 0 ltac:(lia) I)).
  now rewrite open_close_tm_tm.
Qed.

Lemma close_par x a b :
  PR a b -> pure_tm a ->
  forall y, PR (open_tm_wrt_tm (close_term_tm 0 x a) (a_Var_f y))
               (open_tm_wrt_tm (close_term_tm 0 x b) (a_Var_f y)).
Proof.
  intros H Hp y. unfold open_tm_wrt_tm. rewrite !(proj1 open_close_rename).
  now apply par_rename.
Qed.

Lemma join_abs_lift L r a b :
  (forall x, x \notin L -> joinable (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x))) ->
  pure_tm a -> pure_tm b -> joinable (a_UAbs r a) (a_UAbs r b).
Proof.
  intros H Ha Hb.
  take_fresh (L \u support_tm a \u support_tm b) x Hx.
  pose proof (H x ltac:(fsetdec)) as HJ.
  pose proof ((join_lift (fun t => a_UAbs r (close_term_tm 0 x t))) _ _
    (fun t ht => close_scoped x t ht)
    (fun t u ht hp => Par_Abs {} nil {} r _ _ (fun y _ => close_par x t u ht hp y))
    (proj2 (pure_tm_open_var a x) Ha) (proj2 (pure_tm_open_var b x) Hb) HJ) as Hj.
  unfold open_tm_wrt_tm in Hj. now rewrite !close_open_tm_tm in Hj by fsetdec.
Qed.

Lemma join_pi_lift L r A A' B B' :
  (forall x, x \notin L -> joinable (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x))) ->
  pure_tm A -> pure_tm A' -> pure_tm B -> pure_tm B' ->
  joinable A A' -> joinable (a_Pi r A B) (a_Pi r A' B').
Proof.
  intros H HA HA' HB HB' HJ.
  take_fresh (L \u support_tm B \u support_tm B') x Hx.
  pose proof (H x ltac:(fsetdec)) as HJB.
  destruct (join_scoped _ _ HJ) as [Hsc Hsc'].
  destruct (join_scoped _ _ HJB) as [HBsc HBsc'].
  assert (HBclosed : scoped_tm 1 0 B)
    by (apply (proj1 (scoped_open_tm_tm B 0 (a_Var_f x) 0 0 ltac:(lia) I)); exact HBsc).
  assert (Hmid : joinable (a_Pi r A B) (a_Pi r A' B)).
  { join_lift_argument A A' (fun t => a_Pi r t B). }
  eapply join_trans; [exact Hmid | | simpl; auto].
  assert (HH : joinable (a_Pi r A' (close_term_tm 0 x (open_tm_wrt_tm B (a_Var_f x))))
                        (a_Pi r A' (close_term_tm 0 x (open_tm_wrt_tm B' (a_Var_f x))))).
  { eapply (join_lift (fun t => a_Pi r A' (close_term_tm 0 x t))).
    - intros t Ht; simpl; split; auto using close_scoped.
    - intros t u Ht Ht'. eapply Par_Pi with (L := {}); [now apply par_refl_scoped|].
      intros y _. now apply close_par.
    - now apply pure_tm_open_var.
    - now apply pure_tm_open_var.
    - exact HJB. }
  unfold open_tm_wrt_tm in HH. now rewrite !close_open_tm_tm in HH by fsetdec.
Qed.

Lemma join_ucabs_lift a b : pure_tm a -> pure_tm b ->
  joinable a b -> joinable (a_UCAbs a) (a_UCAbs b).
Proof.
  intros Ha Hb [u [M1 M2]]. exists (a_UCAbs u).
  split; eapply mp_lift; try eassumption.
  all: try solve [intros; simpl; eapply scoped_mono_tm; [| |eassumption]; lia].
  all: intros t v H Hp; apply Par_CAbs with (L := {}); intros x _.
  all: rewrite !pure_tm_open_co by eauto using par_pure; exact H.
Qed.

Lemma join_cpi_lift a a' b b' A A' B B' :
  pure_tm a -> pure_tm a' -> pure_tm b -> pure_tm b' ->
  pure_tm A -> pure_tm A' -> pure_tm B -> pure_tm B' ->
  joinable a a' -> joinable b b' -> joinable A A' -> joinable B B' ->
  joinable (a_CPi (Eq a b A) B) (a_CPi (Eq a' b' A') B').
Proof.
  intros Ha Ha' Hb Hb' HA HA' HB HB' H1 H2 H3 H4.
  destruct (join_scoped _ _ H1); destruct (join_scoped _ _ H2);
  destruct (join_scoped _ _ H3); destruct (join_scoped _ _ H4).
  assert (Hbody : scoped_tm 0 1 B) by (eapply scoped_mono_tm; [| | eassumption]; lia).
  eapply join_trans with (b := a_CPi (Eq a' b A) B); [ | |simpl; auto].
  - join_lift_argument a a' (fun t => a_CPi (Eq t b A) B).
  - eapply join_trans with (b := a_CPi (Eq a' b' A) B); [ | |simpl; auto].
    + join_lift_argument b b' (fun t => a_CPi (Eq a' t A) B).
    + eapply join_trans with (b := a_CPi (Eq a' b' A') B); [ | |simpl; auto].
      * join_lift_argument A A' (fun t => a_CPi (Eq a' b' t) B).
      * eapply (join_lift (fun t => a_CPi (Eq a' b' A') t)); try eassumption.
        -- intros t Ht. simpl. repeat split; try assumption.
           eapply scoped_mono_tm; [| |exact Ht]; lia.
        -- intros t v Hv Hp. eapply Par_CPi with (L := {}); try solve [apply par_refl_scoped; assumption].
           intros x _. rewrite !pure_tm_open_co by eauto using par_pure. assumption.
Qed.

(* Inversion and projection of erased function types. *)
Lemma mp_pi_inv t u :
  MP t u -> forall r A B, t = a_Pi r A B ->
  exists A' B' L, u = a_Pi r A' B' /\ MP A A' /\
    forall x, x \notin L -> MP (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  induction 1; intros r A B Heq; subst.
  - exists A, B, {}. split; [reflexivity|].
    pose proof (proj1 lc_scoped _ H) as HS. simpl in HS; destruct HS.
    split; [now apply mp_refl|intros x _; apply mp_refl; discharge_scoped_open].
  - inversion H; subst.
    + now apply IHMultiPar.
    + destruct (IHMultiPar _ _ _ eq_refl) as [U [V [L' [-> [MA MB]]]]].
      exists U, V, (L \u L'). split; [reflexivity|].
      split; [eapply MP_Step; [eapply par_change_context; eassumption|eassumption] |].
      intros x Hx. eapply MP_Step; [|apply MB; fsetdec].
      match goal with H : forall x, x \notin L -> Par _ _ _ _ |- _ => eapply par_change_context; apply H; fsetdec end.
Qed.

Lemma mp_cpi_inv t u :
  MP t u -> forall a b A B, t = a_CPi (Eq a b A) B ->
  exists a' b' A' B' L, u = a_CPi (Eq a' b' A') B' /\ MP a a' /\ MP b b' /\ MP A A' /\
    forall x, x \notin L -> MP (open_tm_wrt_co B (g_Var_f x)) (open_tm_wrt_co B' (g_Var_f x)).
Proof.
  induction 1; intros a0 b0 A B Heq; subst.
  - exists a0, b0, A, B, {}. split; [reflexivity|].
    pose proof (proj1 lc_scoped _ H) as HS. simpl in HS; destruct_ands.
    repeat split; try solve [now apply mp_refl].
    intros x _. apply mp_refl. discharge_scoped_open.
  - inversion H; subst.
    + now apply IHMultiPar.
    + destruct (IHMultiPar _ _ _ _ eq_refl) as [v [w [T [U [L' [-> [MA [MB [MC MD]]]]]]]]].
      exists v, w, T, U, (L \u L'). split; [reflexivity|].
      repeat split; try solve [eapply MP_Step; [eapply par_change_context; eassumption|eassumption]].
      intros x Hx. eapply MP_Step; [|apply MD; fsetdec].
      match goal with H : forall x, x \notin L -> Par _ _ _ _ |- _ => eapply par_change_context; apply H; fsetdec end.
Qed.

Lemma join_pi_fst r A B A' B' :
  joinable (a_Pi r A B) (a_Pi r A' B') -> joinable A A'.
Proof.
  intros [u [H1 H2]].
  destruct (mp_pi_inv _ _ H1 _ _ _ eq_refl) as [v [w [L [-> [M1 M2]]]]].
  destruct (mp_pi_inv _ _ H2 _ _ _ eq_refl) as [v' [w' [L' [Heq [M3 M4]]]]].
  inversion Heq; subst. exists v'; auto.
Qed.

Lemma join_open_term L a b u v :
  (forall x, x \notin L -> joinable (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x))) ->
  pure_tm a -> pure_tm b -> pure_tm u -> pure_tm v ->
  joinable u v -> joinable (open_tm_wrt_tm a u) (open_tm_wrt_tm b v).
Proof.
  intros H Ha Hb Hu Hv [w [Mu Mv]].
  take_fresh (L \u support_tm a \u support_tm b) x Hx.
  destruct (H x ltac:(fsetdec)) as [t [M1 M2]].
  destruct (mp_scoped _ _ Mu) as [Hus Hws].
  destruct (mp_scoped _ _ Mv) as [Hvs _].
  destruct (mp_scoped _ _ M1) as [_ Hts].
  assert (HP : pure_tm t)
    by (eapply mp_pure; [exact M1 | now apply pure_tm_open_var]).
  rewrite <- (open_intro_term a u x ltac:(fsetdec) Hus),
          <- (open_intro_term b v x ltac:(fsetdec) Hvs).
  exists (subst_free_tm (replace_term x w) g_Var_f t).
  assert (K : forall s s0, MP s t -> MP s0 w -> pure_tm s -> pure_tm s0 ->
    MP (subst_free_tm (replace_term x s0) g_Var_f s)
       (subst_free_tm (replace_term x w) g_Var_f t)).
  { intros s s0 M M0 Ps Ps0.
    pose proof (proj1 (mp_scoped _ _ M0)) as Hs0.
    pose proof (maps_scoped _ _ _ (replace_term_maps x s0 Hs0)) as Hm0.
    eapply mp_trans with (b := subst_free_tm (replace_term x s0) g_Var_f t).
    - eapply mp_lift; [ | |exact M|exact Ps].
      + intros y Hy. now apply scoped_subst_tm.
      + intros y z Hy Hpy.
        eapply par_subst; [apply replace_term_maps; exact Hs0|apply replace_term_maps; exact Hs0| |exact Hy|exact Hpy].
        intros i. apply par_refl_scoped. exact (proj1 Hm0 i).
    - eapply (mp_lift (fun q => subst_free_tm (replace_term x q) g_Var_f t)); [ | |exact M0|exact Ps0].
      + intros y Hy. apply scoped_subst_tm; auto.
        exact (maps_scoped _ _ _ (replace_term_maps _ _ Hy)).
      + intros y z Hy Hpy. destruct (par_scoped _ _ _ _ Hy) as [Hys Hzs].
        eapply par_map_refl with (n := S (syntax_size_tm t)); [apply replace_term_maps; exact Hys
          |apply replace_term_maps; exact Hzs | |lia |exact HP |exact Hts].
        intros i; destruct (x == i) as [->|Hneq].
        * now rewrite !replace_term_eq.
        * rewrite !replace_term_neq by assumption. apply par_refl_scoped. exact I. }
  split; eapply K; try eassumption; now apply pure_tm_open_var.
Qed.

Lemma join_pi_snd r A B A' B' u v :
  pure_tm B -> pure_tm B' -> pure_tm u -> pure_tm v ->
  joinable (a_Pi r A B) (a_Pi r A' B') -> joinable u v ->
  joinable (open_tm_wrt_tm B u) (open_tm_wrt_tm B' v).
Proof.
  intros HB HB' Hu Hv [z [H1 H2]] Huv.
  destruct (mp_pi_inv _ _ H1 _ _ _ eq_refl) as [A0 [B0 [L [-> [_ M1]]]]].
  destruct (mp_pi_inv _ _ H2 _ _ _ eq_refl) as [A1 [B1 [L' [Heq [_ M2]]]]].
  inversion Heq; subst.
  eapply join_open_term with (L := L \u L'); try eassumption.
  intros x Hx. exists (open_tm_wrt_tm B1 (a_Var_f x)); split; [apply M1|apply M2]; fsetdec.
Qed.

Definition prop_join p q :=
  match p, q with
  | Eq a b A, Eq a' b' A' => joinable a a' /\ joinable b b' /\ joinable A A'
  end.

Lemma join_cpi_fst a b A B a' b' A' B' :
  joinable (a_CPi (Eq a b A) B) (a_CPi (Eq a' b' A') B') ->
  prop_join (Eq a b A) (Eq a' b' A').
Proof.
  intros [z [H1 H2]].
  destruct (mp_cpi_inv _ _ H1 _ _ _ _ eq_refl) as [s [t [u [v [L [-> [M1 [M2 [M3 M4]]]]]]]]].
  destruct (mp_cpi_inv _ _ H2 _ _ _ _ eq_refl) as [s' [t' [u' [v' [L' [Eq [M5 [M6 [M7 M8]]]]]]]]].
  inversion Eq; subst. simpl. repeat split; eexists; split; eassumption.
Qed.

Lemma join_cpi_snd a b A B a' b' A' B' :
  pure_tm B -> pure_tm B' ->
  joinable (a_CPi (Eq a b A) B) (a_CPi (Eq a' b' A') B') -> joinable B B'.
Proof.
  intros HB HB' [z [H1 H2]].
  destruct (mp_cpi_inv _ _ H1 _ _ _ _ eq_refl) as [s [t [u [v [L [-> [_ [_ [_ M1]]]]]]]]].
  destruct (mp_cpi_inv _ _ H2 _ _ _ _ eq_refl) as [s' [t' [u' [v' [L' [Eq [_ [_ [_ M2]]]]]]]]].
  inversion Eq; subst.
  take_fresh (L \u L') x Hx. exists (open_tm_wrt_co v' (g_Var_f x)).
  specialize (M1 x ltac:(fsetdec)); specialize (M2 x ltac:(fsetdec)).
  rewrite (pure_tm_open_co B _ HB) in M1.
  rewrite (pure_tm_open_co B' _ HB') in M2. auto.
Qed.

Lemma mp_star_inv a : MP a_Star a -> a = a_Star.
Proof.
  remember a_Star as t eqn:E. induction 1; subst; auto.
  inversion H; subst; auto.
Qed.

Lemma join_pi_head r A B T :
  joinable (a_Pi r A B) T ->
  (T = a_Star -> False) /\
  (forall p U, T = a_CPi p U -> False) /\
  (forall s C D, T = a_Pi s C D -> r = s).
Proof.
  intros [z [H1 H2]].
  destruct (mp_pi_inv _ _ H1 _ _ _ eq_refl) as [u [v [L [-> _]]]].
  repeat split; intros; subst.
  - apply mp_star_inv in H2; discriminate.
  - destruct p. destruct (mp_cpi_inv _ _ H2 _ _ _ _ eq_refl) as [? [? [? [? [? [? _]]]]]]; discriminate.
  - destruct (mp_pi_inv _ _ H2 _ _ _ eq_refl) as [? [? [? [? _]]]]; congruence.
Qed.

Lemma join_cpi_head p B T :
  joinable (a_CPi p B) T ->
  (T = a_Star -> False) /\ (forall r A U, T = a_Pi r A U -> False).
Proof.
  destruct p. intros [z [H1 H2]].
  destruct (mp_cpi_inv _ _ H1 _ _ _ _ eq_refl) as [? [? [? [? [? [-> _]]]]]].
  split; intros; subst.
  - apply mp_star_inv in H2; discriminate.
  - destruct (mp_pi_inv _ _ H2 _ _ _ eq_refl) as [? [? [? [? _]]]]; discriminate.
Qed.

(* Soundness of annotated equality under Good. *)
Lemma erase_binding G x s :
  binds x s G -> binds x (erase_sort s) (erase_context G).
Proof. intro H. unfold erase_context. now apply binds_map. Qed.

Lemma valid_erase_sort s : scoped_sort s -> erased_sort (erase_sort s).
Proof.
  destruct s as [A|[a b A]]; simpl; intros H; destruct_ands;
    constructor; now apply erased_of_scoped.
Qed.

Lemma ann_good_extend G D x s :
  AnnGood G D -> scoped_sort s ->
  (forall p, s = Co p -> x \notin D) ->
  AnnGood (x ~ s ++ G) D.
Proof.
  intros [HE HG] Hs Hx. split.
  - simpl. constructor; [now apply valid_erase_sort|exact HE].
  - intros y a b A Hb Hy. destruct Hb as [Heq|Hb].
    + destruct s; inversion Heq; subst; exfalso; eapply Hx; [reflexivity|exact Hy].
    + destruct (HG _ _ _ _ Hb Hy) as [u [H1 H2]].
      exists u; split; eapply par_change_context; eassumption.
Qed.

Lemma ann_good_tm_extend G D x A :
  AnnGood G D -> scoped_tm 0 0 A -> AnnGood (x ~ Tm A ++ G) D.
Proof. intros. apply ann_good_extend; auto; discriminate. Qed.
Lemma ann_good_co_extend G D x p :
  AnnGood G D -> scoped_constraint 0 0 p -> x \notin D ->
  AnnGood (x ~ Co p ++ G) D.
Proof. intros. apply ann_good_extend; auto. Qed.

Lemma erase_join_refl a :
  scoped_tm 0 0 a -> joinable (erase_tm a) (erase_tm a).
Proof. intro H; apply join_refl; now apply scoped_erase_tm. Qed.

Lemma typing_join_refl G a A :
  AnnTyping G a A -> joinable (erase_tm a) (erase_tm a).
Proof. intro H; apply erase_join_refl; exact (proj1 (typing_scoped _ _ _ H)). Qed.

Lemma beta_par a b : Beta a b -> scoped_tm 0 0 a -> PR a b.
Proof.
  destruct 1; intro HS; simpl in HS; destruct_ands.
  - eapply Par_Beta; apply par_refl_scoped; simpl; assumption.
  - eapply Par_CBeta; apply par_refl_scoped; simpl; assumption.
  - eapply Par_Axiom; eassumption.
Qed.

Lemma par_join a b : PR a b -> joinable a b.
Proof.
  intro H. exists b. split; [now apply mp_single |].
  apply mp_refl. exact (proj2 (par_scoped _ _ _ _ H)).
Qed.

Lemma erase_cast_body L a b g :
  (forall x, x \notin L -> open_tm_wrt_tm a (a_Var_f x) =
    open_tm_wrt_tm b (a_Conv (a_Var_f x) g)) ->
  erase_tm a = erase_tm b.
Proof.
  intro H. take_fresh (L \u support_tm (erase_tm a) \u support_tm (erase_tm b)) x Hx.
  apply (opening_injective_tm x); try fsetdec.
  pose proof (f_equal erase_tm (H x ltac:(fsetdec))) as HE.
  unfold open_tm_wrt_tm in *. now rewrite !erase_open_tm_tm in HE.
Qed.

Lemma erase_co_cast_body L a b g :
  (forall x, x \notin L -> open_tm_wrt_co a (g_Var_f x) =
    open_tm_wrt_co b (g_Cast (g_Var_f x) g)) ->
  erase_tm a = erase_tm b.
Proof.
  intro H. take_fresh L x Hx.
  pose proof (f_equal erase_tm (H x Hx)) as HE.
  unfold open_tm_wrt_co in HE. now rewrite !erase_open_co_tm in HE.
Qed.

Lemma cofinite_erase_tm_join L a b :
  (forall x, x \notin L ->
    joinable (erase_tm (open_tm_wrt_tm a (a_Var_f x)))
             (erase_tm (open_tm_wrt_tm b (a_Var_f x)))) ->
  forall x, x \notin L ->
    joinable (open_tm_wrt_tm (erase_tm a) (a_Var_f x))
             (open_tm_wrt_tm (erase_tm b) (a_Var_f x)).
Proof.
  intros H x Hx. specialize (H x Hx).
  unfold open_tm_wrt_tm in *. now rewrite !erase_open_tm_tm in H.
Qed.

Ltac erased_binder_body_join :=
  apply cofinite_erase_tm_join; intros x Hx;
  match goal with
  | IH : forall x, x \notin ?L -> AnnGood _ _ -> _,
    Ht : AnnTyping ?G ?A a_Star |- _ =>
      apply IH; [exact Hx | apply ann_good_tm_extend; [assumption|exact (proj1 (typing_scoped _ _ _ Ht))]]
  end.

Ltac erased_co_body_join :=
  match goal with
  | IH : forall x, x \notin ?L -> AnnGood _ ?D -> _,
    H : AnnGood ?G ?D, P : AnnPropWff ?G ?p |- _ =>
      let x := fresh "x" in let Hx := fresh "Hx" in take_fresh (L \u D) x Hx;
      let HJ := fresh in
      pose proof (IH x ltac:(fsetdec)
        (ann_good_co_extend G D x p H (prop_scoped _ _ P) ltac:(fsetdec))) as HJ;
      unfold open_tm_wrt_co in HJ; rewrite !erase_open_co_tm in HJ; exact HJ
  end.

Lemma ann_sound :
  (forall G a A, AnnTyping G a A -> True) /\
  (forall G p, AnnPropWff G p -> True) /\
  (forall G D g p q, AnnIso G D g p q -> AnnGood G D ->
    prop_join (erase_constraint p) (erase_constraint q)) /\
  (forall G D g a b, AnnDefEq G D g a b -> AnnGood G D ->
    joinable (erase_tm a) (erase_tm b)) /\
  (forall G, AnnCtx G -> True).
Proof.
  apply ann_ind; intros; try exact I.
  - simpl. repeat split; auto.
    apply erase_join_refl. match goal with H : AnnPropWff _ (Eq _ _ A) |- _ =>
      pose proof (prop_scoped _ _ H); simpl in *; tauto end.
  - destruct phi1, phi2; simpl in *.
    apply join_cpi_fst with (B := erase_tm A2) (B' := erase_tm B2); auto.
  - destruct phi1, phi2; simpl in *; specialize (H H0); destruct_ands; repeat split; now apply join_sym.
  - simpl. repeat split; auto.
    + rewrite <- e. inversion a0; eapply typing_join_refl; eassumption.
    + rewrite <- e0. inversion a0; eapply typing_join_refl; eassumption.
  - destruct H0 as [_ HG].
    destruct (HG _ _ _ _ (erase_binding _ _ _ b0) i) as [u [H1 H2]].
    exists u; split; apply mp_single; eapply par_change_context; eassumption.
  - eapply typing_join_refl; eassumption.
  - rewrite <- e. eapply typing_join_refl; eassumption.
  - apply join_sym; auto.
  - eapply join_trans; [apply H|apply H0|apply erase_pure_tm]; assumption.
  - apply par_join, beta_par; [assumption|].
    apply scoped_erase_tm. exact (proj1 (typing_scoped _ _ _ a)).
  - simpl. rewrite (erase_cast_body L B3 B2 (g_Sym g1) e).
    eapply join_pi_lift with (L := L); try solve [apply erase_pure_tm | auto].
    inversion a1; subst. erased_binder_body_join.
  - simpl. rewrite (erase_cast_body L b3 b2 (g_Sym g1) e).
    eapply join_abs_lift with (L := L); [erased_binder_body_join|apply erase_pure_tm|apply erase_pure_tm].
  - destruct rho; simpl; apply join_app; try solve [apply erase_pure_tm | exact I | auto].
    apply join_refl; exact I.
  - eapply join_pi_fst; apply H; assumption.
  - unfold open_tm_wrt_tm at 1 2. rewrite !erase_open_tm_tm.
    change (joinable (open_tm_wrt_tm (erase_tm B1) (erase_tm a1))
                     (open_tm_wrt_tm (erase_tm B2) (erase_tm a2))).
    eapply join_pi_snd with (r := rho) (A := erase_tm A1) (A' := erase_tm A2);
      try solve [apply erase_pure_tm | auto].
  - assert (HB : joinable (erase_tm B1) (erase_tm B2)).
    { match goal with Ht : AnnTyping _ (a_CPi phi1 B1) _ |- _ => inversion Ht; subst end.
      erased_co_body_join. }
    simpl. rewrite (erase_co_cast_body L B3 B2 (g_Sym g1) e).
    destruct phi1, phi2; simpl in *.
    specialize (H ltac:(assumption)). destruct_ands.
    eapply join_cpi_lift; try solve [apply erase_pure_tm | assumption].
  - assert (HB : joinable (erase_tm a1) (erase_tm a2)).
    { match goal with Ht : AnnTyping _ (a_CAbs phi1 a1) _ |- _ => inversion Ht; subst end.
      erased_co_body_join. }
    simpl. rewrite (erase_co_cast_body L a3 a2 (g_Sym g1) e).
    now apply join_ucabs_lift; try apply erase_pure_tm.
  - simpl. now apply join_capp; try apply erase_pure_tm; auto.
  - unfold open_tm_wrt_co. rewrite !erase_open_co_tm.
    eapply join_cpi_snd with (a := erase_tm a) (b := erase_tm a') (A := erase_tm A)
      (a' := erase_tm b) (b' := erase_tm b') (A' := erase_tm B);
      try apply erase_pure_tm; auto.
  - simpl in H0. specialize (H0 ltac:(assumption)); destruct H0 as [M1 [M2 _]].
    eapply join_trans; [now apply join_sym, M1 | |apply erase_pure_tm].
    eapply join_trans; [apply H; assumption | exact M2 | apply erase_pure_tm].
  - simpl in H. specialize (H ltac:(assumption)); tauto.
Qed.
Definition ann_eq_sound := proj1 (proj2 (proj2 (proj2 ann_sound))).

(* Canonical forms and progress. *)
Lemma ann_good_extend_dom G x A :
  x \notin dom G -> AnnGood G (dom G) ->
  scoped_tm 0 0 A -> AnnGood (x ~ Tm A ++ G) (dom (x ~ Tm A ++ G)).
Proof.
  intros Hx HG Hs.
  destruct (ann_good_tm_extend G (dom G) x A HG Hs) as [HE HG'].
  split; [exact HE|].
  intros y a b T Hb HD.
  assert (HD' : y `in` dom G).
  { destruct Hb as [Heq|Hb]; [discriminate|].
    pose proof (binds_In _ _ _ _ Hb) as HD'.
    unfold erase_context in HD'. rewrite dom_map in HD'. exact HD'. }
  destruct (HG' _ _ _ _ Hb HD') as [u [H1 H2]].
  exists u; split; eapply par_change_context; eassumption.
Qed.

Lemma irrelevant_open G x A a :
  x \notin dom G ->
  scoped_tm 0 0 A ->
  irrelevant G (dom G) (a_Abs Irrel A a) ->
  RhoCheck Irrel x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) ->
  irrelevant (x ~ Tm A ++ G) (dom (x ~ Tm A ++ G)) (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros Hx HA [Hfv HG] Hr. split.
  - intros y T Hb. destruct Hb as [Heq|Hb].
    + inversion Heq; subst. now inversion Hr.
    + specialize (Hfv y T Hb). simpl in Hfv.
      pose proof (binds_In _ _ _ _ Hb) as Hd.
      rewrite <- support_erase_tm in Hfv |- *.
      unfold open_tm_wrt_tm. rewrite erase_open_tm_tm.
      pose proof (proj2 (support_open_tm_tm (erase_tm a) 0 (a_Var_f x))) as HS.
      simpl in HS; fsetdec.
  - now apply ann_good_extend_dom.
Qed.

Lemma irrelevant_app_l G r a b :
  irrelevant G (dom G) (a_App a r b) -> irrelevant G (dom G) a.
Proof. intros [H HG]; split; auto. intros x A Hb; specialize (H x A Hb). destruct r; simpl in H; fsetdec. Qed.

Lemma value_typed_pi G v T r A B :
  Value v -> AnnTyping G v T ->
  joinable (erase_tm T) (erase_tm (a_Pi r A B)) ->
  exists A0 B0 b, v = a_Abs r A0 b /\ T = a_Pi r A0 B0.
Proof.
  intros HV HT HJ. apply join_sym in HJ. simpl in HJ.
  destruct (join_pi_head _ _ _ _ HJ) as [Hstar [Hcpi Hpi]].
  inversion HV; subst; inversion HT; subst; simpl in *;
    try solve [exfalso; apply Hstar; reflexivity | exfalso; eapply Hcpi; reflexivity].
  all: first [assert (Hr : r = Rel) by (eapply Hpi; reflexivity)
             |assert (Hr : r = Irrel) by (eapply Hpi; reflexivity)];
    subst r; do 3 eexists; split; reflexivity.
Qed.

Lemma value_typed_cpi G v T p B :
  Value v -> AnnTyping G v T ->
  joinable (erase_tm T) (erase_tm (a_CPi p B)) ->
  exists p0 B0 b, v = a_CAbs p0 b /\ T = a_CPi p0 B0.
Proof.
  intros HV HT HJ. apply join_sym in HJ. simpl in HJ.
  destruct (join_cpi_head _ _ _ HJ) as [Hstar Hpi].
  inversion HV; subst; inversion HT; subst; simpl in *;
    try solve [exfalso; apply Hstar; reflexivity | exfalso; eapply Hpi; reflexivity].
  do 3 eexists; split; reflexivity.
Qed.

Lemma progress_app G f r a A B :
  CoercedValue f -> AnnGood G (dom G) ->
  AnnTyping G f (a_Pi r A B) -> AnnTyping G a A ->
  exists t, head_reduction G (a_App f r a) t.
Proof.
  intros HF HG HT HA.
  inversion HF; subst.
  - match goal with HV : Value ?v |- _ =>
      destruct (value_typed_pi G v _ r A B HV HT (erase_join_refl _ (proj2 (typing_scoped _ _ _ HT)))) as
        [A0 [B0 [b [-> EQ]]]]
    end.
    eexists; apply An_AppAbs; eauto using typing_lc.
  - inversion HT; subst.
    match goal with
    | HV : Value ?v, HVt : AnnTyping G ?v ?T, HE : AnnDefEq G (dom G) ?g ?T (a_Pi r A B) |- _ =>
      let HJ := fresh in
      pose proof (ann_eq_sound _ _ _ _ _ HE HG) as HJ;
      destruct (value_typed_pi G v T r A B HV HVt HJ) as [? [? [? [-> ->]]]]
    end.
    eexists; eapply An_Push; [eassumption|eassumption|reflexivity|reflexivity].
Qed.

Lemma progress_capp G f g a b A B :
  CoercedValue f -> AnnGood G (dom G) ->
  AnnTyping G f (a_CPi (Eq a b A) B) -> AnnDefEq G (dom G) g a b ->
  exists t, head_reduction G (a_CApp f g) t.
Proof.
  intros HF HG HT Hg. inversion HF; subst.
  - match goal with
    | HV : Value ?v |- _ =>
      destruct (value_typed_cpi G v _ (Eq a b A) B HV HT (erase_join_refl _ (proj2 (typing_scoped _ _ _ HT)))) as
        [p [B0 [w [-> EQ]]]]
    end.
    inversion HT; subst.
    eexists; eapply An_CAppCAbs; eauto using prop_lc, typing_lc, eq_lc.
  - inversion HT; subst.
    match goal with
    | HV : Value ?v, HVt : AnnTyping G ?v ?T, HE : AnnDefEq G (dom G) ?g ?T (a_CPi (Eq a b A) B) |- _ =>
      let HJ := fresh in pose proof (ann_eq_sound _ _ _ _ _ HE HG) as HJ;
      destruct (value_typed_cpi G v T (Eq a b A) B HV HVt HJ) as [? [? [? [-> ->]]]]
    end.
    eexists; eapply An_CPush; [eassumption|eassumption|reflexivity|reflexivity].
Qed.

Lemma progress_irrel_abs L G A a :
  AnnTyping G A a_Star ->
  irrelevant G (dom G) (a_Abs Irrel A a) ->
  (forall x, x \notin L -> RhoCheck Irrel x (erase_tm (open_tm_wrt_tm a (a_Var_f x)))) ->
  (forall x, x \notin L -> irrelevant (x ~ Tm A ++ G) (dom (x ~ Tm A ++ G)) (open_tm_wrt_tm a (a_Var_f x)) ->
    CoercedValue (open_tm_wrt_tm a (a_Var_f x)) \/ exists t,
      head_reduction (x ~ Tm A ++ G) (open_tm_wrt_tm a (a_Var_f x)) t) ->
  CoercedValue (a_Abs Irrel A a) \/ exists t, head_reduction G (a_Abs Irrel A a) t.
Proof.
  intros HA HI HR IH.
  take_fresh (L \u dom G \u support_tm a) x Hx.
  assert (HO : irrelevant (x ~ Tm A ++ G) (dom (x ~ Tm A ++ G)) (open_tm_wrt_tm a (a_Var_f x))).
  { apply irrelevant_open; [fsetdec|exact (proj1 (typing_scoped _ _ _ HA))|exact HI|apply HR; fsetdec]. }
  destruct (IH x ltac:(fsetdec) HO) as [HV|[t Hred]].
  - left. apply CV. eapply Value_AbsIrrel with (L := {}); [eauto using typing_lc|].
    intros y _. pose proof (proj1 values_subst _ HV _ _ _ (replace_term_maps x (a_Var_f y) I)) as HH.
    now rewrite binder_rename in HH by fsetdec.
  - right. exists (a_Abs Irrel A (close_term_tm 0 x t)).
    eapply An_AbsTerm with (L := dom G \u {{x}}); [exact HA|].
    intros y Hy. pose proof (head_subst _ _ _ Hred _ _ _ _
      (rename_head_binder G x y A ltac:(fsetdec) ltac:(fsetdec) ltac:(fsetdec) HA)) as HH.
    rewrite binder_rename in HH by fsetdec.
    unfold open_tm_wrt_tm at 2. now rewrite (proj1 open_close_rename).
Qed.

Theorem progress : forall G a A, irrelevant G (dom G) a -> AnnTyping G a A -> CoercedValue a \/ exists a', head_reduction G a a'.
Proof.
  intros G a A HI HT. revert HI.
  induction HT; intros HI.
  - left; apply CV; constructor.
  - exfalso. destruct HI as [Hfv _].
    match goal with HB : binds x (Tm A) G |- _ => specialize (Hfv x A HB) end.
    simpl in Hfv. fsetdec.
  - left; apply CV; constructor.
    + eapply typing_lc; eassumption.
    + eapply typing_lc; eapply An_Pi with (L := L); eassumption.
  - destruct rho.
    + left; apply CV; constructor.
      * eapply typing_lc; eassumption.
      * eapply typing_lc; eapply An_Abs with (L := L); eassumption.
    + eapply progress_irrel_abs with (L := L); eassumption.
  - right. destruct (IHHT1 (irrelevant_app_l _ _ _ _ HI)) as [HV | [t HR]].
    + eapply progress_app; [exact HV | exact (proj2 HI) | eassumption | eassumption].
    + eexists; eapply An_AppLeft; eauto using typing_lc.
  - change (irrelevant G (dom G) a) in HI.
    destruct (IHHT1 HI) as [HV | [t HR]].
    + inversion HV; subst.
      * left; apply CC; eauto using eq_lc.
      * right; eexists; eapply An_Combine; eauto using eq_lc.
    + right; eexists; eapply An_ConvTerm; eauto using eq_lc.
  - left; apply CV; constructor.
    + eauto using prop_lc.
    + eapply typing_lc; eapply An_CPi with (L := L); eassumption.
  - left; apply CV; constructor.
    + eauto using prop_lc.
    + eapply typing_lc; eapply An_CAbs with (L := L); eassumption.
  - assert (HI' : irrelevant G (dom G) a1).
    { destruct HI as [Hfv HG]. split; [|exact HG].
      intros x T Hb. specialize (Hfv x T Hb). simpl in Hfv. fsetdec. }
    right. destruct (IHHT HI') as [HV | [t HR]].
    + eapply progress_capp; [exact HV | exact (proj2 HI) | eassumption | eassumption].
    + eexists; eapply An_CAppLeft; eauto using eq_lc.
  - right; eexists; eapply An_Axiom; eassumption.
Qed.
