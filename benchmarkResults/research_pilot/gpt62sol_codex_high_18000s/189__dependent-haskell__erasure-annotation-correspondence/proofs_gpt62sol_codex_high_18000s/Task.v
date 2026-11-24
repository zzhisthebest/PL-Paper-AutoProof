Require Import Language.

Scheme task_tm_ind := Induction for tm Sort Prop
with task_brs_ind := Induction for brs Sort Prop
with task_co_ind := Induction for co Sort Prop
with task_constraint_ind := Induction for constraint Sort Prop.

Lemma task_erase_open_tm_rec : forall a k u,
  erase_tm (open_tm_wrt_tm_rec k u a) =
  open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a).
Proof.
  apply (task_tm_ind
    (fun a => forall k u, erase_tm (open_tm_wrt_tm_rec k u a) =
       open_tm_wrt_tm_rec k (erase_tm u) (erase_tm a))
    (fun _ => True) (fun _ => True)
    (fun p => forall k u, erase_constraint (open_constraint_wrt_tm_rec k u p) =
       open_constraint_wrt_tm_rec k (erase_tm u) (erase_constraint p)));
    intros; try exact I; cbn;
    try match goal with
    | |- context [lt_eq_lt_dec ?n ?k] => destruct (lt_eq_lt_dec n k) as [[?|?]|?]
    | |- context [match ?r with Rel => _ | Irrel => _ end] => destruct r
    end;
    cbn; f_equal; auto.
Qed.

Lemma task_erase_open_co_rec : forall a k g h,
  erase_tm (open_tm_wrt_co_rec k g a) =
  open_tm_wrt_co_rec k h (erase_tm a).
Proof.
  apply (task_tm_ind
    (fun a => forall k g h, erase_tm (open_tm_wrt_co_rec k g a) =
       open_tm_wrt_co_rec k h (erase_tm a))
    (fun _ => True) (fun _ => True)
    (fun p => forall k g h, erase_constraint (open_constraint_wrt_co_rec k g p) =
       open_constraint_wrt_co_rec k h (erase_constraint p)));
    intros; try exact I; cbn;
    try match goal with
    | |- context [match ?r with Rel => _ | Irrel => _ end] => destruct r
    end;
    cbn; f_equal; eauto.
Qed.

Lemma task_erase_open_tm : forall a u,
  erase_tm (open_tm_wrt_tm a u) = open_tm_wrt_tm (erase_tm a) (erase_tm u).
Proof. exact (fun a => task_erase_open_tm_rec a 0). Qed.

Lemma task_erase_open_co : forall a g h,
  erase_tm (open_tm_wrt_co a g) = open_tm_wrt_co (erase_tm a) h.
Proof. exact (fun a => task_erase_open_co_rec a 0). Qed.

Lemma task_dom_erase : forall G, dom (erase_context G) = dom G.
Proof. unfold erase_context; induction G as [|[x s] G IH]; simpl; f_equal; auto. Qed.

Lemma task_binds_erase : forall G x s,
  binds x s G -> binds x (erase_sort s) (erase_context G).
Proof. intros; apply binds_map; assumption. Qed.

Scheme task_ann_prop_ind := Induction for AnnPropWff Sort Prop
with task_ann_typing_ind := Induction for AnnTyping Sort Prop
with task_ann_iso_ind := Induction for AnnIso Sort Prop
with task_ann_defeq_ind := Induction for AnnDefEq Sort Prop
with task_ann_ctx_ind := Induction for AnnCtx Sort Prop
with task_ann_sig_ind := Induction for AnnSig Sort Prop.
Combined Scheme task_ann_ind from task_ann_prop_ind, task_ann_typing_ind,
  task_ann_iso_ind, task_ann_defeq_ind, task_ann_ctx_ind, task_ann_sig_ind.

Scheme task_prop_ind := Induction for PropWff Sort Prop
with task_typing_ind := Induction for Typing Sort Prop
with task_iso_ind := Induction for Iso Sort Prop
with task_defeq_ind := Induction for DefEq Sort Prop
with task_ctx_ind := Induction for Ctx Sort Prop.
Combined Scheme task_implicit_ind from task_prop_ind, task_typing_ind,
  task_iso_ind, task_defeq_ind, task_ctx_ind.

Definition task_extends (G H : context) :=
  forall x s, binds x s G -> binds x s H.

Lemma task_extends_cons : forall G H x s,
  task_extends G H -> task_extends (x ~ s ++ G) (x ~ s ++ H).
Proof.
  unfold task_extends, binds; simpl; intuition.
Qed.

Lemma task_extends_dom : forall G H,
  task_extends G H -> AtomSetImpl.Subset (dom G) (dom H).
Proof.
  unfold task_extends, AtomSetImpl.Subset.
  intros G H Ext x Hin; destruct (binds_In_inv _ _ _ Hin) as [s Hb].
  eauto using binds_In.
Qed.

Lemma task_ann_weaken :
  (forall G p, AnnPropWff G p -> forall H,
    AnnCtx H -> task_extends G H -> AnnPropWff H p) /\
  (forall G a A, AnnTyping G a A -> forall H,
    AnnCtx H -> task_extends G H -> AnnTyping H a A) /\
  (forall G D g p q, AnnIso G D g p q -> forall H E,
    AnnCtx H -> task_extends G H -> AtomSetImpl.Subset D E -> AnnIso H E g p q) /\
  (forall G D g a b, AnnDefEq G D g a b -> forall H E,
    AnnCtx H -> task_extends G H -> AtomSetImpl.Subset D E -> AnnDefEq H E g a b) /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof.
  apply task_ann_ind; intros; try exact I.
  all: try solve [eauto 8 using An_Wff, An_Star, An_Var, An_App, An_Conv,
    An_CApp, An_Fam, An_PropCong, An_CPiFst, An_IsoSym, An_IsoConv,
    An_Assn, An_Refl, An_EraseEq, An_Sym, An_Trans, An_Beta,
    An_AppCong, An_PiFst, An_PiSnd, An_CAppCong, An_CPiSnd, An_Cast, An_IsoSnd,
    task_extends_dom].
  all: try match goal with
  | Ext : task_extends ?G ?H |- _ =>
    assert (HD : AtomSetImpl.Subset (dom G) (dom H))
      by (apply task_extends_dom; exact Ext)
  end.
  all: try match goal with
   | Hc : AnnCtx ?H, HE : task_extends ?G ?H |- _ =>
     first [
       match goal with HA : AnnTyping G (a_Pi _ ?A _) a_Star |- _ =>
         assert (AnnTyping H A a_Star) by (inversion HA; subst; eauto)
       end
     | match goal with HA : AnnTyping G (a_CPi ?p _) a_Star |- _ =>
         assert (AnnPropWff H p) by (inversion HA; subst; eauto)
       end
     | match goal with HA : AnnTyping G (a_CAbs ?p _) _ |- _ =>
         assert (AnnPropWff H p) by (inversion HA; subst; eauto)
       end
     | idtac ]
  end.
  all: try solve [
    match goal with
    | HD0 : forall H E, AnnCtx H -> task_extends _ H -> AtomSetImpl.Subset (dom _) E ->
            AnnDefEq H E ?g0 _ _ |-
           AnnDefEq _ _ (g_CAppCong ?g1 ?g2 ?g3) _ _ =>
       eapply An_CAppCong;
       [solve [eauto] | solve [eauto] | solve [eauto] | solve [eauto] |
        solve [eauto] | solve [eauto]]
    end].
  all: try match goal with
   | HC : AnnCtx ?H, HL : forall x : atom, x `notin` ?L -> _ |- _ =>
       first [eapply An_Pi with (L := L \u dom H) |
               eapply An_Abs with (L := L \u dom H) |
               eapply An_CPi with (L := L \u dom H) |
               eapply An_CAbs with (L := L \u dom H) |
               eapply An_PiCong with (L := L \u dom H) |
               eapply An_AbsCong with (L := L \u dom H) |
               eapply An_CPiCong with (L := L \u dom H) |
               eapply An_CAbsCong with (L := L \u dom H)]
  end.
  all: try solve [eauto].
  all: try solve [intros; eauto using An_ConsTm, An_ConsCo, task_extends_cons
                       with core].
  all: match goal with
   | Hty : forall J, AnnCtx J -> task_extends ?G J ->
                      AnnTyping J ?a ?A,
     HC : AnnCtx ?H, HE : task_extends ?G ?H |- _ =>
      let HH := fresh in
      pose proof (Hty H HC HE) as HH;
      inversion HH; subst; clear HH;
      intros; solve [eauto using An_ConsTm, An_ConsCo, task_extends_cons]
  end.
Qed.

Lemma task_binds_unerase : forall G x s,
  binds x s (erase_context G) ->
  exists u, erase_sort u = s /\ binds x u G.
Proof. unfold erase_context; intros; eapply binds_map_3; eassumption. Qed.

Lemma task_fix_type_annotated : AnnTyping nil FixTy a_Star.
Proof.
  unfold FixTy.
  apply An_Pi with (L := empty).
  - intros x _; cbn.
    pose proof (An_Star nil An_Empty) as Hstar.
    assert (HX : AnnCtx (x ~ Tm a_Star))
      by (apply An_ConsTm; [exact An_Empty | exact Hstar | simpl; fsetdec]).
    assert (HT : AnnTyping (x ~ Tm a_Star) (a_Var_f x) a_Star)
      by (apply An_Var; [exact HX | simpl; auto]).
    assert (HP : AnnTyping (x ~ Tm a_Star)
                (a_Pi Rel (a_Var_f x) (a_Var_f x)) a_Star).
    { apply An_Pi with (L := {{x}}); [|exact HT].
      intros y Hy; cbn.
      apply An_Var.
      - apply An_ConsTm; [exact HX | exact HT | simpl; fsetdec].
      - simpl; auto. }
    apply An_Pi with (L := {{x}}); [|exact HP].
    intros y Hy; cbn.
    apply An_Var.
    + apply An_ConsTm; [exact HX | exact HP | simpl; fsetdec].
    + simpl; auto.
  - apply An_Star, An_Empty.
Qed.

(* Syntax operations for opening and closing binders. *)
Fixpoint task_walk_tm (f_t f_c : nat -> atom -> _) (b_t b_c : nat -> nat -> _) (i j : nat) (s : tm) {struct s} : tm :=
  match s with
  | a_Star => a_Star
  | a_Var_b n => b_t i n
  | a_Var_f x => f_t i x
  | a_Abs rho A b => a_Abs rho (task_walk_tm f_t f_c b_t b_c i j A) (task_walk_tm f_t f_c b_t b_c (S i) j b)
  | a_UAbs rho b => a_UAbs rho (task_walk_tm f_t f_c b_t b_c (S i) j b)
  | a_App a rho b => a_App (task_walk_tm f_t f_c b_t b_c i j a) rho (task_walk_tm f_t f_c b_t b_c i j b)
  | a_Fam F => a_Fam F
  | a_Const T => a_Const T
  | a_Pi rho A B => a_Pi rho (task_walk_tm f_t f_c b_t b_c i j A) (task_walk_tm f_t f_c b_t b_c (S i) j B)
  | a_Conv a g => a_Conv (task_walk_tm f_t f_c b_t b_c i j a) (task_walk_co f_t f_c b_t b_c i j g)
  | a_CPi phi B => a_CPi (task_walk_constraint f_t f_c b_t b_c i j phi) (task_walk_tm f_t f_c b_t b_c i (S j) B)
  | a_CAbs phi b => a_CAbs (task_walk_constraint f_t f_c b_t b_c i j phi) (task_walk_tm f_t f_c b_t b_c i (S j) b)
  | a_UCAbs b => a_UCAbs (task_walk_tm f_t f_c b_t b_c i (S j) b)
  | a_CApp a g => a_CApp (task_walk_tm f_t f_c b_t b_c i j a) (task_walk_co f_t f_c b_t b_c i j g)
  | a_Bullet => a_Bullet
  | a_DataCon K => a_DataCon K
  | a_Case a brs5 => a_Case (task_walk_tm f_t f_c b_t b_c i j a) (task_walk_brs f_t f_c b_t b_c i j brs5)
  end
with task_walk_brs (f_t f_c : nat -> atom -> _) (b_t b_c : nat -> nat -> _) (i j : nat) (s : brs) {struct s} : brs :=
  match s with
  | br_None => br_None
  | br_One K a brs5 => br_One K (task_walk_tm f_t f_c b_t b_c i j a) (task_walk_brs f_t f_c b_t b_c i j brs5)
  end
with task_walk_co (f_t f_c : nat -> atom -> _) (b_t b_c : nat -> nat -> _) (i j : nat) (s : co) {struct s} : co :=
  match s with
  | g_Triv => g_Triv
  | g_Var_b n => b_c j n
  | g_Var_f c => f_c j c
  | g_Beta a b => g_Beta (task_walk_tm f_t f_c b_t b_c i j a) (task_walk_tm f_t f_c b_t b_c i j b)
  | g_Refl a => g_Refl (task_walk_tm f_t f_c b_t b_c i j a)
  | g_Refl2 a b g => g_Refl2 (task_walk_tm f_t f_c b_t b_c i j a) (task_walk_tm f_t f_c b_t b_c i j b) (task_walk_co f_t f_c b_t b_c i j g)
  | g_Sym g => g_Sym (task_walk_co f_t f_c b_t b_c i j g)
  | g_Trans g1 g2 => g_Trans (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c i j g2)
  | g_PiCong rho g1 g2 => g_PiCong rho (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c (S i) j g2)
  | g_AbsCong rho g1 g2 => g_AbsCong rho (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c (S i) j g2)
  | g_AppCong g1 rho g2 => g_AppCong (task_walk_co f_t f_c b_t b_c i j g1) rho (task_walk_co f_t f_c b_t b_c i j g2)
  | g_PiFst g => g_PiFst (task_walk_co f_t f_c b_t b_c i j g)
  | g_CPiFst g => g_CPiFst (task_walk_co f_t f_c b_t b_c i j g)
  | g_IsoSnd g => g_IsoSnd (task_walk_co f_t f_c b_t b_c i j g)
  | g_PiSnd g1 g2 => g_PiSnd (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c i j g2)
  | g_CPiCong g1 g3 => g_CPiCong (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c i (S j) g3)
  | g_CAbsCong g1 g3 g4 => g_CAbsCong (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c i (S j) g3) (task_walk_co f_t f_c b_t b_c i j g4)
  | g_CAppCong g g1 g2 => g_CAppCong (task_walk_co f_t f_c b_t b_c i j g) (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c i j g2)
  | g_CPiSnd g g1 g2 => g_CPiSnd (task_walk_co f_t f_c b_t b_c i j g) (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c i j g2)
  | g_Cast g1 g2 => g_Cast (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_co f_t f_c b_t b_c i j g2)
  | g_EqCong g1 A g2 => g_EqCong (task_walk_co f_t f_c b_t b_c i j g1) (task_walk_tm f_t f_c b_t b_c i j A) (task_walk_co f_t f_c b_t b_c i j g2)
  | g_IsoConv phi1 phi2 g => g_IsoConv (task_walk_constraint f_t f_c b_t b_c i j phi1) (task_walk_constraint f_t f_c b_t b_c i j phi2) (task_walk_co f_t f_c b_t b_c i j g)
  | g_Eta a => g_Eta (task_walk_tm f_t f_c b_t b_c i j a)
  | g_Left g g' => g_Left (task_walk_co f_t f_c b_t b_c i j g) (task_walk_co f_t f_c b_t b_c i j g')
  | g_Right g g' => g_Right (task_walk_co f_t f_c b_t b_c i j g) (task_walk_co f_t f_c b_t b_c i j g')
  end
with task_walk_constraint (f_t f_c : nat -> atom -> _) (b_t b_c : nat -> nat -> _) (i j : nat) (s : constraint) {struct s} : constraint :=
  match s with
  | Eq a b A => Eq (task_walk_tm f_t f_c b_t b_c i j a) (task_walk_tm f_t f_c b_t b_c i j b) (task_walk_tm f_t f_c b_t b_c i j A)
  end.

Fixpoint task_scope_tm (i j : nat) (s : tm) {struct s} : Prop :=
  match s with
  | a_Star => True
  | a_Var_b n => n < i
  | a_Var_f x => True
  | a_Abs rho A b => task_scope_tm i j A /\ task_scope_tm (S i) j b
  | a_UAbs rho b => task_scope_tm (S i) j b
  | a_App a rho b => task_scope_tm i j a /\ task_scope_tm i j b
  | a_Fam F => True
  | a_Const T => True
  | a_Pi rho A B => task_scope_tm i j A /\ task_scope_tm (S i) j B
  | a_Conv a g => task_scope_tm i j a /\ task_scope_co i j g
  | a_CPi phi B => task_scope_constraint i j phi /\ task_scope_tm i (S j) B
  | a_CAbs phi b => task_scope_constraint i j phi /\ task_scope_tm i (S j) b
  | a_UCAbs b => task_scope_tm i (S j) b
  | a_CApp a g => task_scope_tm i j a /\ task_scope_co i j g
  | a_Bullet => True
  | a_DataCon K => True
  | a_Case a brs5 => task_scope_tm i j a /\ task_scope_brs i j brs5
  end
with task_scope_brs (i j : nat) (s : brs) {struct s} : Prop :=
  match s with
  | br_None => True
  | br_One K a brs5 => task_scope_tm i j a /\ task_scope_brs i j brs5
  end
with task_scope_co (i j : nat) (s : co) {struct s} : Prop :=
  match s with
  | g_Triv => True
  | g_Var_b n => n < j
  | g_Var_f c => True
  | g_Beta a b => task_scope_tm i j a /\ task_scope_tm i j b
  | g_Refl a => task_scope_tm i j a
  | g_Refl2 a b g => task_scope_tm i j a /\ task_scope_tm i j b /\ task_scope_co i j g
  | g_Sym g => task_scope_co i j g
  | g_Trans g1 g2 => task_scope_co i j g1 /\ task_scope_co i j g2
  | g_PiCong rho g1 g2 => task_scope_co i j g1 /\ task_scope_co (S i) j g2
  | g_AbsCong rho g1 g2 => task_scope_co i j g1 /\ task_scope_co (S i) j g2
  | g_AppCong g1 rho g2 => task_scope_co i j g1 /\ task_scope_co i j g2
  | g_PiFst g => task_scope_co i j g
  | g_CPiFst g => task_scope_co i j g
  | g_IsoSnd g => task_scope_co i j g
  | g_PiSnd g1 g2 => task_scope_co i j g1 /\ task_scope_co i j g2
  | g_CPiCong g1 g3 => task_scope_co i j g1 /\ task_scope_co i (S j) g3
  | g_CAbsCong g1 g3 g4 => task_scope_co i j g1 /\ task_scope_co i (S j) g3 /\ task_scope_co i j g4
  | g_CAppCong g g1 g2 => task_scope_co i j g /\ task_scope_co i j g1 /\ task_scope_co i j g2
  | g_CPiSnd g g1 g2 => task_scope_co i j g /\ task_scope_co i j g1 /\ task_scope_co i j g2
  | g_Cast g1 g2 => task_scope_co i j g1 /\ task_scope_co i j g2
  | g_EqCong g1 A g2 => task_scope_co i j g1 /\ task_scope_tm i j A /\ task_scope_co i j g2
  | g_IsoConv phi1 phi2 g => task_scope_constraint i j phi1 /\ task_scope_constraint i j phi2 /\ task_scope_co i j g
  | g_Eta a => task_scope_tm i j a
  | g_Left g g' => task_scope_co i j g /\ task_scope_co i j g'
  | g_Right g g' => task_scope_co i j g /\ task_scope_co i j g'
  end
with task_scope_constraint (i j : nat) (s : constraint) {struct s} : Prop :=
  match s with
  | Eq a b A => task_scope_tm i j a /\ task_scope_tm i j b /\ task_scope_tm i j A
  end.

Fixpoint task_vars_tm  (s : tm) {struct s} : atoms :=
  match s with
  | a_Star => empty
  | a_Var_b n => empty
  | a_Var_f x => singleton x
  | a_Abs rho A b => task_vars_tm A \u task_vars_tm b
  | a_UAbs rho b => task_vars_tm b
  | a_App a rho b => task_vars_tm a \u task_vars_tm b
  | a_Fam F => singleton F
  | a_Const T => empty
  | a_Pi rho A B => task_vars_tm A \u task_vars_tm B
  | a_Conv a g => task_vars_tm a \u task_vars_co g
  | a_CPi phi B => task_vars_constraint phi \u task_vars_tm B
  | a_CAbs phi b => task_vars_constraint phi \u task_vars_tm b
  | a_UCAbs b => task_vars_tm b
  | a_CApp a g => task_vars_tm a \u task_vars_co g
  | a_Bullet => empty
  | a_DataCon K => empty
  | a_Case a brs5 => task_vars_tm a \u task_vars_brs brs5
  end
with task_vars_brs  (s : brs) {struct s} : atoms :=
  match s with
  | br_None => empty
  | br_One K a brs5 => task_vars_tm a \u task_vars_brs brs5
  end
with task_vars_co  (s : co) {struct s} : atoms :=
  match s with
  | g_Triv => empty
  | g_Var_b n => empty
  | g_Var_f c => singleton c
  | g_Beta a b => task_vars_tm a \u task_vars_tm b
  | g_Refl a => task_vars_tm a
  | g_Refl2 a b g => task_vars_tm a \u task_vars_tm b \u task_vars_co g
  | g_Sym g => task_vars_co g
  | g_Trans g1 g2 => task_vars_co g1 \u task_vars_co g2
  | g_PiCong rho g1 g2 => task_vars_co g1 \u task_vars_co g2
  | g_AbsCong rho g1 g2 => task_vars_co g1 \u task_vars_co g2
  | g_AppCong g1 rho g2 => task_vars_co g1 \u task_vars_co g2
  | g_PiFst g => task_vars_co g
  | g_CPiFst g => task_vars_co g
  | g_IsoSnd g => task_vars_co g
  | g_PiSnd g1 g2 => task_vars_co g1 \u task_vars_co g2
  | g_CPiCong g1 g3 => task_vars_co g1 \u task_vars_co g3
  | g_CAbsCong g1 g3 g4 => task_vars_co g1 \u task_vars_co g3 \u task_vars_co g4
  | g_CAppCong g g1 g2 => task_vars_co g \u task_vars_co g1 \u task_vars_co g2
  | g_CPiSnd g g1 g2 => task_vars_co g \u task_vars_co g1 \u task_vars_co g2
  | g_Cast g1 g2 => task_vars_co g1 \u task_vars_co g2
  | g_EqCong g1 A g2 => task_vars_co g1 \u task_vars_tm A \u task_vars_co g2
  | g_IsoConv phi1 phi2 g => task_vars_constraint phi1 \u task_vars_constraint phi2 \u task_vars_co g
  | g_Eta a => task_vars_tm a
  | g_Left g g' => task_vars_co g \u task_vars_co g'
  | g_Right g g' => task_vars_co g \u task_vars_co g'
  end
with task_vars_constraint  (s : constraint) {struct s} : atoms :=
  match s with
  | Eq a b A => task_vars_tm a \u task_vars_tm b \u task_vars_tm A
  end.


Definition task_id_ft (_ : nat) := a_Var_f.
Definition task_id_fc (_ : nat) := g_Var_f.
Definition task_id_bt (_ : nat) := a_Var_b.
Definition task_id_bc (_ : nat) := g_Var_b.

Ltac task_syn_ind P1 P2 P3 P4 :=
  split; [apply (task_tm_ind P1 P2 P3 P4) |
  split; [apply (task_brs_ind P1 P2 P3 P4) |
  split; [apply (task_co_ind P1 P2 P3 P4) |
          apply (task_constraint_ind P1 P2 P3 P4)]]].

From Stdlib Require Import Lia.

Ltac task_structure :=
  let P1 := match goal with |- (forall t, @?P t) /\ _ => constr:(P) end in
  let P2 := match goal with |- _ /\ (forall t, @?P t) /\ _ => constr:(P) end in
  let P3 := match goal with |- _ /\ _ /\ (forall t, @?P t) /\ _ => constr:(P) end in
  let P4 := match goal with |- _ /\ _ /\ _ /\ (forall t, @?P t) => constr:(P) end in
  task_syn_ind P1 P2 P3 P4.

Lemma task_scope_mono :
  (forall t i j k l, i <= k -> j <= l -> task_scope_tm i j t -> task_scope_tm k l t) /\
  (forall t i j k l, i <= k -> j <= l -> task_scope_brs i j t -> task_scope_brs k l t) /\
  (forall t i j k l, i <= k -> j <= l -> task_scope_co i j t -> task_scope_co k l t) /\
  (forall t i j k l, i <= k -> j <= l -> task_scope_constraint i j t -> task_scope_constraint k l t).
Proof.
  task_structure; intros; cbn in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try assumption; try lia;
    match goal with
    | IH : forall (_ _ _ _ : nat), _ |- _ =>
      solve [eapply IH; [| |eassumption]; lia]
    end.
Qed.

Lemma task_scope_open_t :
  (forall t k j x, task_scope_tm k j (open_tm_wrt_tm_rec k (a_Var_f x) t) <-> task_scope_tm (S k) j t) /\
  (forall t k j x, task_scope_brs k j (open_brs_wrt_tm_rec k (a_Var_f x) t) <-> task_scope_brs (S k) j t) /\
  (forall t k j x, task_scope_co k j (open_co_wrt_tm_rec k (a_Var_f x) t) <-> task_scope_co (S k) j t) /\
  (forall t k j x, task_scope_constraint k j (open_constraint_wrt_tm_rec k (a_Var_f x) t) <-> task_scope_constraint (S k) j t).
Proof.
  task_structure; intros; cbn;
  repeat match goal with H : forall _ _ _, _ <-> _ |- _ => rewrite H || clear H end;
  try reflexivity;
  match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; lia
  end.
Qed.

Lemma task_scope_open_c :
  (forall t i k x, task_scope_tm i k (open_tm_wrt_co_rec k (g_Var_f x) t) <-> task_scope_tm i (S k) t) /\
  (forall t i k x, task_scope_brs i k (open_brs_wrt_co_rec k (g_Var_f x) t) <-> task_scope_brs i (S k) t) /\
  (forall t i k x, task_scope_co i k (open_co_wrt_co_rec k (g_Var_f x) t) <-> task_scope_co i (S k) t) /\
  (forall t i k x, task_scope_constraint i k (open_constraint_wrt_co_rec k (g_Var_f x) t) <-> task_scope_constraint i (S k) t).
Proof.
  task_structure; intros; cbn;
  repeat match goal with H : forall _ _ _, _ <-> _ |- _ => rewrite H || clear H end;
  try reflexivity;
  match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; lia
  end.
Qed.

Ltac task_break_and :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac task_split_and :=
  repeat match goal with |- _ /\ _ => split end.

Ltac task_choose_fresh F tactic :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  destruct (atom_fresh F) as [x Hx]; tactic x Hx.

Scheme task_lc_constraint_ind := Induction for lc_constraint Sort Prop
with task_lc_co_ind := Induction for lc_co Sort Prop
with task_lc_brs_ind := Induction for lc_brs Sort Prop
with task_lc_tm_ind := Induction for lc_tm Sort Prop.
Combined Scheme task_lc_ind from task_lc_constraint_ind, task_lc_co_ind,
  task_lc_brs_ind, task_lc_tm_ind.

Lemma task_scope_from_lc :
  (forall p, lc_constraint p -> task_scope_constraint 0 0 p) /\
  (forall g, lc_co g -> task_scope_co 0 0 g) /\
  (forall b, lc_brs b -> task_scope_brs 0 0 b) /\
  (forall a, lc_tm a -> task_scope_tm 0 0 a).
Proof.
  pose proof task_scope_open_t as [ET [_ [EC _]]].
  pose proof task_scope_open_c as [CT [_ [CC _]]].
  apply task_lc_ind; intros; cbn; task_split_and; auto;
    first [apply (proj1 (ET _ 0 0 Fix))
          |apply (proj1 (EC _ 0 0 Fix))
          |apply (proj1 (CT _ 0 0 Fix))
          |apply (proj1 (CC _ 0 0 Fix))]; eauto.
Qed.
Lemma task_scope_idle_t :
  (forall s i j (u : tm), task_scope_tm i j s -> open_tm_wrt_tm_rec i u s = s) /\
  (forall s i j (u : tm), task_scope_brs i j s -> open_brs_wrt_tm_rec i u s = s) /\
  (forall s i j (u : tm), task_scope_co i j s -> open_co_wrt_tm_rec i u s = s) /\
  (forall s i j (u : tm), task_scope_constraint i j s -> open_constraint_wrt_tm_rec i u s = s).
Proof.
  task_structure; intros; cbn in *; task_break_and;
  try solve [f_equal; eauto];
  match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try reflexivity; lia
  end.
Qed.

Lemma task_scope_idle_c :
  (forall s i j (u : co), task_scope_tm i j s -> open_tm_wrt_co_rec j u s = s) /\
  (forall s i j (u : co), task_scope_brs i j s -> open_brs_wrt_co_rec j u s = s) /\
  (forall s i j (u : co), task_scope_co i j s -> open_co_wrt_co_rec j u s = s) /\
  (forall s i j (u : co), task_scope_constraint i j s -> open_constraint_wrt_co_rec j u s = s).
Proof.
  task_structure; intros; cbn in *; task_break_and;
  try solve [f_equal; eauto];
  match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try reflexivity; lia
  end.
Qed.

Record task_substitution := {
  task_ft : atom -> tm;
  task_fc : atom -> co;
  task_ft_scope : forall x, task_scope_tm 0 0 (task_ft x);
  task_fc_scope : forall x, task_scope_co 0 0 (task_fc x);
  task_support : atoms;
  task_ft_fresh : forall x, x `notin` task_support -> task_ft x = a_Var_f x;
  task_fc_fresh : forall x, x `notin` task_support -> task_fc x = g_Var_f x;
  task_ft_vars : forall x y, y `notin` task_support ->
                      y `in` task_vars_tm (task_ft x) -> x = y;
  task_fc_vars : forall x y, y `notin` task_support ->
                      y `in` task_vars_co (task_fc x) -> x = y
}.
Definition task_sub_tm S := task_walk_tm (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc 0 0.
Definition task_sub_brs S := task_walk_brs (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc 0 0.
Definition task_sub_co S := task_walk_co (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc 0 0.
Definition task_sub_constraint S := task_walk_constraint (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc 0 0.
Lemma task_sub_walk_depth :
  (forall s S i j k l, task_walk_tm (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_walk_tm (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc k l s) /\
  (forall s S i j k l, task_walk_brs (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_walk_brs (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc k l s) /\
  (forall s S i j k l, task_walk_co (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_walk_co (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc k l s) /\
  (forall s S i j k l, task_walk_constraint (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_walk_constraint (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc k l s).
Proof.
  task_structure; intros; cbn; try reflexivity; f_equal; auto.
Qed.

Lemma task_sub_tm_walk : forall S i j s, task_walk_tm (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_sub_tm S s.
Proof. intros; unfold task_sub_tm; apply task_sub_walk_depth. Qed.
Lemma task_sub_brs_walk : forall S i j s, task_walk_brs (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_sub_brs S s.
Proof. intros; unfold task_sub_brs; apply task_sub_walk_depth. Qed.
Lemma task_sub_co_walk : forall S i j s, task_walk_co (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_sub_co S s.
Proof. intros; unfold task_sub_co; apply task_sub_walk_depth. Qed.
Lemma task_sub_constraint_walk : forall S i j s, task_walk_constraint (fun _ => task_ft S) (fun _ => task_fc S) task_id_bt task_id_bc i j s = task_sub_constraint S s.
Proof. intros; unfold task_sub_constraint; apply task_sub_walk_depth. Qed.
#[local] Hint Rewrite task_sub_tm_walk task_sub_brs_walk task_sub_co_walk
  task_sub_constraint_walk : task_sub.
Lemma task_sub_scope :
  (forall s S i j, task_scope_tm i j s -> task_scope_tm i j (task_sub_tm S s)) /\
  (forall s S i j, task_scope_brs i j s -> task_scope_brs i j (task_sub_brs S s)) /\
  (forall s S i j, task_scope_co i j s -> task_scope_co i j (task_sub_co S s)) /\
  (forall s S i j, task_scope_constraint i j s -> task_scope_constraint i j (task_sub_constraint S s)).
Proof.
  pose proof task_scope_mono as [MT [_ [MC _]]].
  task_structure; intros; cbn in *; autorewrite with task_sub; task_break_and;
  task_split_and; auto;
  first [eapply (MT _ 0 0); [lia | lia | apply task_ft_scope]
        |eapply (MC _ 0 0); [lia | lia | apply task_fc_scope]].
Qed.

Lemma task_sub_open_t_rec :
  (forall s S k (u : tm), task_sub_tm S (open_tm_wrt_tm_rec k u s) = open_tm_wrt_tm_rec k (task_sub_tm S u) (task_sub_tm S s)) /\
  (forall s S k (u : tm), task_sub_brs S (open_brs_wrt_tm_rec k u s) = open_brs_wrt_tm_rec k (task_sub_tm S u) (task_sub_brs S s)) /\
  (forall s S k (u : tm), task_sub_co S (open_co_wrt_tm_rec k u s) = open_co_wrt_tm_rec k (task_sub_tm S u) (task_sub_co S s)) /\
  (forall s S k (u : tm), task_sub_constraint S (open_constraint_wrt_tm_rec k u s) = open_constraint_wrt_tm_rec k (task_sub_tm S u) (task_sub_constraint S s)).
Proof.
  pose proof task_scope_idle_t as [IT [_ [IC _]]].
  pose proof task_scope_mono as [MT [_ [MC _]]].
  task_structure; intros; cbn; autorewrite with task_sub;
  try solve [f_equal; eauto];
  first
    [symmetry; apply (IT _ k 0); eapply (MT _ 0 0); [lia | lia | apply task_ft_scope]
    |symmetry; apply (IC _ k 0); eapply (MC _ 0 0); [lia | lia | apply task_fc_scope]
    |match goal with |- context [lt_eq_lt_dec ?n ?k] =>
       destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity
     end].
Qed.

Lemma task_sub_open_c_rec :
  (forall s S k (u : co), task_sub_tm S (open_tm_wrt_co_rec k u s) = open_tm_wrt_co_rec k (task_sub_co S u) (task_sub_tm S s)) /\
  (forall s S k (u : co), task_sub_brs S (open_brs_wrt_co_rec k u s) = open_brs_wrt_co_rec k (task_sub_co S u) (task_sub_brs S s)) /\
  (forall s S k (u : co), task_sub_co S (open_co_wrt_co_rec k u s) = open_co_wrt_co_rec k (task_sub_co S u) (task_sub_co S s)) /\
  (forall s S k (u : co), task_sub_constraint S (open_constraint_wrt_co_rec k u s) = open_constraint_wrt_co_rec k (task_sub_co S u) (task_sub_constraint S s)).
Proof.
  pose proof task_scope_idle_c as [IT [_ [IC _]]].
  pose proof task_scope_mono as [MT [_ [MC _]]].
  task_structure; intros; cbn; autorewrite with task_sub;
  try solve [f_equal; eauto];
  first
    [symmetry; apply (IT _ 0 k); eapply (MT _ 0 0); [lia | lia | apply task_ft_scope]
    |symmetry; apply (IC _ 0 k); eapply (MC _ 0 0); [lia | lia | apply task_fc_scope]
    |match goal with |- context [lt_eq_lt_dec ?n ?k] =>
       destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity
     end].
Qed.

Lemma task_scope_plug_t :
  (forall s i j (u : tm), task_scope_tm i j u -> task_scope_tm (S i) j s -> task_scope_tm i j (open_tm_wrt_tm_rec i u s)) /\
  (forall s i j (u : tm), task_scope_tm i j u -> task_scope_brs (S i) j s -> task_scope_brs i j (open_brs_wrt_tm_rec i u s)) /\
  (forall s i j (u : tm), task_scope_tm i j u -> task_scope_co (S i) j s -> task_scope_co i j (open_co_wrt_tm_rec i u s)) /\
  (forall s i j (u : tm), task_scope_tm i j u -> task_scope_constraint (S i) j s -> task_scope_constraint i j (open_constraint_wrt_tm_rec i u s)).
Proof.
  pose proof task_scope_mono as [MT [_ [MC _]]].
  task_structure; intros; cbn in *; task_break_and; task_split_and;
  try solve [auto];
  try match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; try assumption; lia
  end;
  match goal with
  | IH : forall (_ _ : nat) (_ : tm), _ |- _ =>
    solve [eapply IH; [first [eassumption | eapply MT; [| | eassumption]; lia] | eassumption]]
  end.
Qed.

Lemma task_scope_plug_c :
  (forall s i j (u : co), task_scope_co i j u -> task_scope_tm i (S j) s -> task_scope_tm i j (open_tm_wrt_co_rec j u s)) /\
  (forall s i j (u : co), task_scope_co i j u -> task_scope_brs i (S j) s -> task_scope_brs i j (open_brs_wrt_co_rec j u s)) /\
  (forall s i j (u : co), task_scope_co i j u -> task_scope_co i (S j) s -> task_scope_co i j (open_co_wrt_co_rec j u s)) /\
  (forall s i j (u : co), task_scope_co i j u -> task_scope_constraint i (S j) s -> task_scope_constraint i j (open_constraint_wrt_co_rec j u s)).
Proof.
  pose proof task_scope_mono as [MT [_ [MC _]]].
  task_structure; intros; cbn in *; task_break_and; task_split_and;
  try solve [auto];
  try match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; try assumption; lia
  end;
  match goal with
  | IH : forall (_ _ : nat) (_ : co), _ |- _ =>
    solve [eapply IH; [first [eassumption | eapply MC; [| | eassumption]; lia] | eassumption]]
  end.
Qed.


Definition task_scope_sort s :=
  match s with
  | Tm A => task_scope_tm 0 0 A
  | Co p => task_scope_constraint 0 0 p
  end.

Lemma task_ann_scope :
  (forall G p, AnnPropWff G p -> task_scope_constraint 0 0 p) /\
  (forall G a A, AnnTyping G a A -> task_scope_tm 0 0 a /\ task_scope_tm 0 0 A) /\
  (forall G D g p q, AnnIso G D g p q ->
    task_scope_co 0 0 g /\ task_scope_constraint 0 0 p /\ task_scope_constraint 0 0 q) /\
  (forall G D g a b, AnnDefEq G D g a b ->
    task_scope_co 0 0 g /\ task_scope_tm 0 0 a /\ task_scope_tm 0 0 b) /\
  (forall G, AnnCtx G -> forall x s, binds x s G -> task_scope_sort s) /\
  (forall S, AnnSig S -> True).
Proof.
  pose proof task_scope_open_t as [ET [_ [EC _]]].
  pose proof task_scope_open_c as [CT [_ [CC _]]].
  pose proof task_scope_plug_t as [PT [_ [PC _]]].
  pose proof task_scope_plug_c as [QT [_ [QC _]]].
  apply task_ann_ind; intros;
    unfold open_tm_wrt_tm, open_co_wrt_tm, open_tm_wrt_co, open_co_wrt_co in *.
  all: try match goal with
    | H : forall x : atom, x `notin` ?L -> _ |- _ =>
      task_choose_fresh L ltac:(fun x Hx =>
        repeat match goal with
        | H' : forall y : atom, y `notin` L -> _ |- _ => specialize (H' x Hx)
        end)
    end.
  all: repeat match goal with
    | HS : forall x s, binds x s ?G -> task_scope_sort s,
      HB : binds ?x ?s ?G |- _ =>
       let HW := fresh in pose proof (HS x s HB) as HW; clear HB
    end.
  all: cbn in *; task_break_and; task_split_and; auto.
  all: try match goal with H : _ = _ |- _ => rewrite H in * end.
  all: try solve [
     match goal with x : atom |- _ =>
       first [apply (proj1 (ET _ 0 0 x))
             |apply (proj1 (EC _ 0 0 x))
             |apply (proj1 (CT _ 0 0 x))
             |apply (proj1 (CC _ 0 0 x))];
       try match goal with Q : _ = _ |- _ => rewrite Q end;
       solve [eassumption | eapply PT; [simpl; auto | eassumption]
                          | eapply QT; [simpl; auto | eassumption]]
     end].
  all: try solve [eapply PT; [eassumption | eassumption] |
                  eapply QT; [eassumption | eassumption]].
  all: try contradiction.
  all: match goal with H : _ \/ _ |- _ =>
    destruct H as [Heq | Hb]; [inversion Heq; subst; simpl; auto | eauto]
  end.
Qed.
Fixpoint task_size_tm  (s : tm) {struct s} : nat :=
  match s with
  | a_Star => 1
  | a_Var_b n => 1
  | a_Var_f x => 1
  | a_Abs rho A b => S (task_size_tm A + task_size_tm b)
  | a_UAbs rho b => S (task_size_tm b)
  | a_App a rho b => S (task_size_tm a + task_size_tm b)
  | a_Fam F => 1
  | a_Const T => 1
  | a_Pi rho A B => S (task_size_tm A + task_size_tm B)
  | a_Conv a g => S (task_size_tm a + task_size_co g)
  | a_CPi phi B => S (task_size_constraint phi + task_size_tm B)
  | a_CAbs phi b => S (task_size_constraint phi + task_size_tm b)
  | a_UCAbs b => S (task_size_tm b)
  | a_CApp a g => S (task_size_tm a + task_size_co g)
  | a_Bullet => 1
  | a_DataCon K => 1
  | a_Case a brs5 => S (task_size_tm a + task_size_brs brs5)
  end
with task_size_brs  (s : brs) {struct s} : nat :=
  match s with
  | br_None => 1
  | br_One K a brs5 => S (task_size_tm a + task_size_brs brs5)
  end
with task_size_co  (s : co) {struct s} : nat :=
  match s with
  | g_Triv => 1
  | g_Var_b n => 1
  | g_Var_f c => 1
  | g_Beta a b => S (task_size_tm a + task_size_tm b)
  | g_Refl a => S (task_size_tm a)
  | g_Refl2 a b g => S (task_size_tm a + task_size_tm b + task_size_co g)
  | g_Sym g => S (task_size_co g)
  | g_Trans g1 g2 => S (task_size_co g1 + task_size_co g2)
  | g_PiCong rho g1 g2 => S (task_size_co g1 + task_size_co g2)
  | g_AbsCong rho g1 g2 => S (task_size_co g1 + task_size_co g2)
  | g_AppCong g1 rho g2 => S (task_size_co g1 + task_size_co g2)
  | g_PiFst g => S (task_size_co g)
  | g_CPiFst g => S (task_size_co g)
  | g_IsoSnd g => S (task_size_co g)
  | g_PiSnd g1 g2 => S (task_size_co g1 + task_size_co g2)
  | g_CPiCong g1 g3 => S (task_size_co g1 + task_size_co g3)
  | g_CAbsCong g1 g3 g4 => S (task_size_co g1 + task_size_co g3 + task_size_co g4)
  | g_CAppCong g g1 g2 => S (task_size_co g + task_size_co g1 + task_size_co g2)
  | g_CPiSnd g g1 g2 => S (task_size_co g + task_size_co g1 + task_size_co g2)
  | g_Cast g1 g2 => S (task_size_co g1 + task_size_co g2)
  | g_EqCong g1 A g2 => S (task_size_co g1 + task_size_tm A + task_size_co g2)
  | g_IsoConv phi1 phi2 g => S (task_size_constraint phi1 + task_size_constraint phi2 + task_size_co g)
  | g_Eta a => S (task_size_tm a)
  | g_Left g g' => S (task_size_co g + task_size_co g')
  | g_Right g g' => S (task_size_co g + task_size_co g')
  end
with task_size_constraint  (s : constraint) {struct s} : nat :=
  match s with
  | Eq a b A => S (task_size_tm a + task_size_tm b + task_size_tm A)
  end.

Lemma task_size_open_t :
  (forall s k x, task_size_tm (open_tm_wrt_tm_rec k (a_Var_f x) s) = task_size_tm s) /\
  (forall s k x, task_size_brs (open_brs_wrt_tm_rec k (a_Var_f x) s) = task_size_brs s) /\
  (forall s k x, task_size_co (open_co_wrt_tm_rec k (a_Var_f x) s) = task_size_co s) /\
  (forall s k x, task_size_constraint (open_constraint_wrt_tm_rec k (a_Var_f x) s) = task_size_constraint s).
Proof.
  task_structure; intros; cbn;
  repeat match goal with H : forall k x, _ = _ |- _ => rewrite H || clear H end;
  try reflexivity;
  match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity
  end.
Qed.

Lemma task_size_open_c :
  (forall s k x, task_size_tm (open_tm_wrt_co_rec k (g_Var_f x) s) = task_size_tm s) /\
  (forall s k x, task_size_brs (open_brs_wrt_co_rec k (g_Var_f x) s) = task_size_brs s) /\
  (forall s k x, task_size_co (open_co_wrt_co_rec k (g_Var_f x) s) = task_size_co s) /\
  (forall s k x, task_size_constraint (open_constraint_wrt_co_rec k (g_Var_f x) s) = task_size_constraint s).
Proof.
  task_structure; intros; cbn;
  repeat match goal with H : forall k x, _ = _ |- _ => rewrite H || clear H end;
  try reflexivity;
  match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity
  end.
Qed.


Lemma task_lc_from_scope_size : forall n,
  (forall s, task_size_tm s <= n -> task_scope_tm 0 0 s -> lc_tm s) /\
  (forall s, task_size_brs s <= n -> task_scope_brs 0 0 s -> lc_brs s) /\
  (forall s, task_size_co s <= n -> task_scope_co 0 0 s -> lc_co s) /\
  (forall s, task_size_constraint s <= n -> task_scope_constraint 0 0 s -> lc_constraint s).
Proof.
  pose proof task_size_open_t as [ST [_ [GT _]]].
  pose proof task_size_open_c as [SC [_ [GC _]]].
  pose proof task_scope_open_t as [ET [_ [EC _]]].
  pose proof task_scope_open_c as [CT [_ [CC _]]].
  induction n as [|n [T [B [C P]]]].
  - repeat split; destruct s; cbn; lia.
  - split; [|split; [|split]]; intros s; destruct s; cbn;
      intros Hsize Hscope; try lia; task_break_and; try solve [constructor];
      constructor;
      unfold open_tm_wrt_tm, open_tm_wrt_co, open_co_wrt_tm, open_co_wrt_co;
      intros.
    all: first [apply T | apply B | apply C | apply P].
    all: try solve [try rewrite ST; try rewrite GT; try rewrite SC; try rewrite GC; lia].
    all: first [assumption | apply ET | apply EC | apply CT | apply CC]; assumption.
Qed.

Lemma task_lc_from_scope_tm : forall a, task_scope_tm 0 0 a -> lc_tm a.
Proof. intros; eapply (proj1 (task_lc_from_scope_size (task_size_tm a))); eauto. Qed.
Definition task_close_t_free (x : atom) (k : nat) (y : atom) :=
  if Atom.eq_dec y x then a_Var_b k else a_Var_f y.
Definition task_close_t_bound (k n : nat) :=
  if lt_dec n k then a_Var_b n else a_Var_b (S n).
Definition task_close_t_tm x := task_walk_tm (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc 0 0.
Definition task_close_t_co x := task_walk_co (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc 0 0.
Lemma task_close_open_t :
  (forall s i j x, x `notin` task_vars_tm s -> task_walk_tm (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j (open_tm_wrt_tm_rec i (a_Var_f x) s) = s) /\
  (forall s i j x, x `notin` task_vars_brs s -> task_walk_brs (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j (open_brs_wrt_tm_rec i (a_Var_f x) s) = s) /\
  (forall s i j x, x `notin` task_vars_co s -> task_walk_co (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j (open_co_wrt_tm_rec i (a_Var_f x) s) = s) /\
  (forall s i j x, x `notin` task_vars_constraint s -> task_walk_constraint (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j (open_constraint_wrt_tm_rec i (a_Var_f x) s) = s).
Proof.
  task_structure; intros; cbn in *;
  try solve [reflexivity | f_equal; eauto using notin_union_1, notin_union_2];
  unfold task_close_t_free, task_close_t_bound in *;
  try match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; cbn;
    unfold task_close_t_free, task_close_t_bound
  end;
  repeat match goal with
  | |- context [Atom.eq_dec ?x ?y] => destruct (Atom.eq_dec x y); try subst
  | |- context [lt_dec ?n ?k] => destruct (lt_dec n k)
  end;
  try reflexivity; try solve [exfalso; fsetdec | exfalso; lia | f_equal; lia].
  all: f_equal;
      match goal with
      | IH : forall (_ _ : nat) (_ : atom), _ |- _ =>
          solve [eapply IH; fsetdec]
      end.
Qed.

Definition task_close_c_free (x : atom) (k : nat) (y : atom) :=
  if Atom.eq_dec y x then g_Var_b k else g_Var_f y.
Definition task_close_c_bound (k n : nat) :=
  if lt_dec n k then g_Var_b n else g_Var_b (S n).
Definition task_close_c_tm x := task_walk_tm task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound 0 0.
Definition task_close_c_co x := task_walk_co task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound 0 0.
Lemma task_close_open_c :
  (forall s i j x, x `notin` task_vars_tm s -> task_walk_tm task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j (open_tm_wrt_co_rec j (g_Var_f x) s) = s) /\
  (forall s i j x, x `notin` task_vars_brs s -> task_walk_brs task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j (open_brs_wrt_co_rec j (g_Var_f x) s) = s) /\
  (forall s i j x, x `notin` task_vars_co s -> task_walk_co task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j (open_co_wrt_co_rec j (g_Var_f x) s) = s) /\
  (forall s i j x, x `notin` task_vars_constraint s -> task_walk_constraint task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j (open_constraint_wrt_co_rec j (g_Var_f x) s) = s).
Proof.
  task_structure; intros; cbn in *;
  try solve [reflexivity | f_equal; eauto using notin_union_1, notin_union_2];
  unfold task_close_c_free, task_close_c_bound in *;
  try match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; cbn;
    unfold task_close_c_free, task_close_c_bound
  end;
  repeat match goal with
  | |- context [Atom.eq_dec ?x ?y] => destruct (Atom.eq_dec x y); try subst
  | |- context [lt_dec ?n ?k] => destruct (lt_dec n k)
  end;
  try reflexivity; try solve [exfalso; fsetdec | exfalso; lia | f_equal; lia].
  all: f_equal;
      match goal with
      | IH : forall (_ _ : nat) (_ : atom), _ |- _ =>
          solve [eapply IH; fsetdec]
      end.
Qed.


Ltac task_cofinite_injective :=
  match goal with
  | H : forall x : atom, x `notin` ?L ->
           open_tm_wrt_tm ?a (a_Var_f x) = open_tm_wrt_tm ?b (a_Var_f x)
    |- ?a = ?b =>
    task_choose_fresh (L \u task_vars_tm a \u task_vars_tm b) ltac:(fun x Hx =>
      pose proof (H x (ltac:(fsetdec))) as Heq;
      apply (f_equal (task_close_t_tm x)) in Heq;
      unfold task_close_t_tm, open_tm_wrt_tm in Heq;
      rewrite !(proj1 task_close_open_t) in Heq by fsetdec; exact Heq)
  | H : forall x : atom, x `notin` ?L ->
           open_tm_wrt_co ?a (g_Var_f x) = open_tm_wrt_co ?b (g_Var_f x)
    |- ?a = ?b =>
    task_choose_fresh (L \u task_vars_tm a \u task_vars_tm b) ltac:(fun x Hx =>
      pose proof (H x (ltac:(fsetdec))) as Heq;
      apply (f_equal (task_close_c_tm x)) in Heq;
      unfold task_close_c_tm, open_tm_wrt_co in Heq;
      rewrite !(proj1 task_close_open_c) in Heq by fsetdec; exact Heq)
  end.

Lemma task_open_tm_injective : forall L a b,
  (forall x, x `notin` L -> open_tm_wrt_tm a (a_Var_f x) = open_tm_wrt_tm b (a_Var_f x)) ->
  a = b.
Proof. intros; task_cofinite_injective. Qed.

Lemma task_open_co_injective : forall L a b,
  (forall x, x `notin` L -> open_tm_wrt_co a (g_Var_f x) = open_tm_wrt_co b (g_Var_f x)) ->
  a = b.
Proof. intros; task_cofinite_injective. Qed.

(* Uniqueness of annotated types and coercion endpoints. *)

Lemma task_ann_ctx_ok : forall G, AnnCtx G -> uniq G.
Proof.
  induction 1; auto using uniq_nil, uniq_cons.
Qed.

Lemma task_ann_unique :
  (forall G p, AnnPropWff G p -> True) /\
  (forall G a A, AnnTyping G a A -> forall B, AnnTyping G a B -> A = B) /\
  (forall G D g p q, AnnIso G D g p q -> forall E p' q',
      AnnIso G E g p' q' -> p = p' /\ q = q') /\
  (forall G D g a b, AnnDefEq G D g a b -> forall E a' b',
      AnnDefEq G E g a' b' -> a = a' /\ b = b') /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof.
  apply task_ann_ind; intros; try exact I.
  all: lazymatch goal with H : ?T |- _ =>
    lazymatch T with
    | AnnTyping _ _ _ => inversion H; subst; try clear H
    | AnnDefEq _ _ _ _ _ => inversion H; subst; try clear H
    | AnnIso _ _ _ _ _ => inversion H; subst; try clear H
    end
  end.
  all: try solve [split; reflexivity | reflexivity].
  all: try match goal with
   | H1 : binds ?x ?s ?G, H2 : binds ?x ?t ?G |- _ =>
     tryif constr_eq s t then fail else
       let Q := fresh in
       assert (Q : s = t)
         by (eapply binds_unique; [exact H1 | exact H2 | eauto using task_ann_ctx_ok, uniq_cons, uniq_nil]);
       inversion Q; subst; clear Q
  end.
  all: repeat match goal with
   | IH : forall _ : tm, _,
     HT : AnnTyping ?G ?a ?B |- _ =>
       let ty := type of (IH B HT) in
       lazymatch ty with
       | ?A = ?B => tryif constr_eq A B then fail else
         let Q := fresh in
         pose proof (IH B HT) as Q; inversion Q; subst; try clear Q; clear IH
       end
   | IH : forall (_ : available_props) (_ _ : tm), _,
     HE : AnnDefEq ?G ?E ?g ?a ?b |- _ =>
       let ty := type of (IH E a b HE) in
       lazymatch ty with ?A = ?X /\ ?B = ?Y =>
         tryif (constr_eq A X; constr_eq B Y) then fail else
         let Q := fresh in
         pose proof (IH E a b HE) as Q; destruct Q as [Q1 Q2];
         inversion Q1; inversion Q2; subst; try clear Q1; try clear Q2; clear IH
       end
   | IH : forall (_ : available_props) (_ _ : constraint), _,
     HI : AnnIso ?G ?E ?g ?p ?q |- _ =>
       let ty := type of (IH E p q HI) in
       lazymatch ty with ?P = ?X /\ ?Q = ?Y =>
         tryif (constr_eq P X; constr_eq Q Y) then fail else
         let Hnew := fresh in
         pose proof (IH E p q HI) as Hnew; destruct Hnew as [Q1 Q2];
         inversion Q1; inversion Q2; subst; try clear Q1; try clear Q2; clear IH
       end
  end.
  all: try solve [split; reflexivity | reflexivity | congruence].

  all: repeat match goal with
  | IH : forall x, x `notin` ?L -> forall E a b,
                      AnnDefEq _ E (open_co_wrt_tm ?g (a_Var_f x)) a b ->
                      open_tm_wrt_tm ?a0 (a_Var_f x) = a /\
                      open_tm_wrt_tm ?b0 (a_Var_f x) = b,
    H : forall x, x `notin` ?M ->
                  AnnDefEq _ ?E (open_co_wrt_tm ?g (a_Var_f x))
                    (open_tm_wrt_tm ?a1 (a_Var_f x)) (open_tm_wrt_tm ?b1 (a_Var_f x)) |- _ =>
    tryif (constr_eq a0 a1; constr_eq b0 b1) then fail else
    let Q := fresh in
    assert (Q : forall x, x `notin` (L \u M) ->
       open_tm_wrt_tm a0 (a_Var_f x) = open_tm_wrt_tm a1 (a_Var_f x) /\
       open_tm_wrt_tm b0 (a_Var_f x) = open_tm_wrt_tm b1 (a_Var_f x))
      by (intros x Hx; eapply IH; [fsetdec | apply H; fsetdec]);
    let Q1 := fresh in let Q2 := fresh in
    assert (Q1 : a0 = a1) by (eapply task_open_tm_injective; intros y Hy; exact (proj1 (Q y Hy)));
    assert (Q2 : b0 = b1) by (eapply task_open_tm_injective; intros y Hy; exact (proj2 (Q y Hy)));
    subst; try clear IH; clear Q
  | IH : forall x, x `notin` ?L -> forall E a b,
                      AnnDefEq _ E (open_co_wrt_co ?g (g_Var_f x)) a b ->
                      open_tm_wrt_co ?a0 (g_Var_f x) = a /\
                      open_tm_wrt_co ?b0 (g_Var_f x) = b,
    H : forall x, x `notin` ?M ->
                  AnnDefEq _ ?E (open_co_wrt_co ?g (g_Var_f x))
                    (open_tm_wrt_co ?a1 (g_Var_f x)) (open_tm_wrt_co ?b1 (g_Var_f x)) |- _ =>
    tryif (constr_eq a0 a1; constr_eq b0 b1) then fail else
    let Q := fresh in
    assert (Q : forall x, x `notin` (L \u M) ->
       open_tm_wrt_co a0 (g_Var_f x) = open_tm_wrt_co a1 (g_Var_f x) /\
       open_tm_wrt_co b0 (g_Var_f x) = open_tm_wrt_co b1 (g_Var_f x))
      by (intros x Hx; eapply IH; [fsetdec | apply H; fsetdec]);
    let Q1 := fresh in let Q2 := fresh in
    assert (Q1 : a0 = a1) by (eapply task_open_co_injective; intros y Hy; exact (proj1 (Q y Hy)));
    assert (Q2 : b0 = b1) by (eapply task_open_co_injective; intros y Hy; exact (proj2 (Q y Hy)));
    subst; try clear IH; clear Q
  end.
  all: task_split_and; f_equal; try reflexivity.
  all: try match goal with
    | IH : forall x, x `notin` ?L -> forall A, AnnTyping _ _ A -> _,
      H : forall x, x `notin` ?M -> AnnTyping _ _ _ |- _ =>
      first [
        solve [apply task_open_tm_injective with (L := L \u M); intros; apply IH; [fsetdec|apply H; fsetdec]]
      | solve [apply task_open_co_injective with (L := L \u M); intros; apply IH; [fsetdec|apply H; fsetdec]]]
    end.
  all: try match goal with
    | H1 : forall x, x `notin` ?L -> open_tm_wrt_tm ?a (a_Var_f x) = _,
      H2 : forall x, x `notin` ?M -> open_tm_wrt_tm ?b (a_Var_f x) = _ |- ?a = ?b =>
      apply task_open_tm_injective with (L := L \u M); intros;
       rewrite H1, H2 by fsetdec; reflexivity
    | H1 : forall x, x `notin` ?L -> open_tm_wrt_co ?a (g_Var_f x) = _,
      H2 : forall x, x `notin` ?M -> open_tm_wrt_co ?b (g_Var_f x) = _ |- ?a = ?b =>
      apply task_open_co_injective with (L := L \u M); intros;
       rewrite H1, H2 by fsetdec; reflexivity
    end.
Qed.

(* Implicit judgments contain terms fixed by erasure. *)

Lemma task_erase_id_prop :
 (forall a, erase_tm (erase_tm a) = erase_tm a) /\
 (forall s : brs, True) /\ (forall g : co, True) /\
 (forall p, erase_constraint (erase_constraint p) = erase_constraint p).
Proof.
  task_structure; intros; try exact I;
  try match goal with r : relflag |- _ => destruct r end;
  cbn; try solve [auto]; f_equal; auto.
Qed.

Lemma task_implicit_canonical :
  (forall G p, PropWff G p -> erase_constraint p = p) /\
  (forall G a A, Typing G a A -> erase_tm a = a /\ erase_tm A = A) /\
  (forall G D p q, Iso G D p q -> erase_constraint p = p /\ erase_constraint q = q) /\
  (forall G D a b A, DefEq G D a b A ->
    erase_tm a = a /\ erase_tm b = b /\ erase_tm A = A) /\
  (forall G, Ctx G -> forall x s, binds x s G -> erase_sort s = s).
Proof.
  apply task_implicit_ind; intros;
    task_break_and; task_split_and; try reflexivity.
  all: cbn [erase_tm erase_constraint] in *;
       try rewrite task_erase_open_tm;
       try rewrite (task_erase_open_co _ _ g_Triv).
  all: repeat match goal with
    | H : erase_tm _ = _ |- _ => progress rewrite H in *
    | H : erase_constraint _ = _ |- _ => progress rewrite H in *
    end.
  all: try reflexivity.
  all: try solve [apply (proj1 task_erase_id_prop)].
  all: try match goal with
    | C : forall x s, binds x s ?G -> erase_sort s = s,
      H : binds ?x ?s ?G |- _ =>
      pose proof (C x s H) as Q; cbn in Q; inversion Q
    end.
  all: try solve [reflexivity | congruence].
  all: try match goal with
    | H : binds ?F (Ax ?a ?A) toplevel |- _ =>
      change ((Fix, Ax (erase_tm FixDef) (erase_tm FixTy)) = (F, Ax a A) \/ False) in H;
      destruct H as [H|[]]; inversion H; subst;
      apply (proj1 task_erase_id_prop)
    end.
  all: try solve [
    match goal with HB : binds _ _ (_ :: _) |- _ =>
      apply binds_cons_1 in HB; destruct HB as [[? ?]|?]; subst; simpl; congruence || eauto
    | HB : binds _ _ nil |- _ => inversion HB
    end].
  all: try solve [
    f_equal; try (simpl in *; congruence);
    match goal with
    | IH : forall x, x `notin` ?L -> _ |- erase_tm _ = _ =>
      first [
       solve [apply task_open_tm_injective with (L := L); intros x Hx;
          specialize (IH x Hx); rewrite ?task_erase_open_tm in IH; intuition]
      |solve [apply task_open_co_injective with (L := L); intros x Hx;
          specialize (IH x Hx); rewrite ?(task_erase_open_co _ (g_Var_f x) (g_Var_f x)) in IH; intuition]]
    end].
  all: apply binds_cons_1 in H1;
       destruct H1 as [[? ?] | Hb];
       [subst; simpl; congruence | eauto].
Qed.

Lemma task_erase_scope :
  (forall s i j, task_scope_tm i j s -> task_scope_tm i j (erase_tm s)) /\
  (forall s : brs, True) /\ (forall s : co, True) /\
  (forall s i j, task_scope_constraint i j s -> task_scope_constraint i j (erase_constraint s)).
Proof.
  task_structure; intros; try exact I; cbn in *;
  try match goal with |- context [match ?r with Rel => _ | Irrel => _ end] => destruct r end;
  cbn in *; task_break_and; task_split_and; auto.
Qed.

Lemma task_erase_vars :
  (forall s x, x `in` task_vars_tm (erase_tm s) -> x `in` task_vars_tm s) /\
  (forall s : brs, True) /\ (forall s : co, True) /\
  (forall s x, x `in` task_vars_constraint (erase_constraint s) -> x `in` task_vars_constraint s).
Proof.
  task_structure; intros; try exact I; cbn in *;
  try match goal with r : relflag |- _ => destruct r; cbn in * end.
  all: repeat match goal with H : _ `in` union _ _ |- _ =>
    apply AtomSetImpl.union_1 in H; destruct H
  end.
  all: try solve [fsetdec].
  all: match goal with
   | HI : forall x : atom, _,
     HM : ?x `in` _ |- _ =>
     solve [let HH := fresh in pose proof (HI x HM) as HH; fsetdec]
  end.
Qed.

Definition task_erased_sub (S : task_substitution) : task_substitution.
Proof.
  refine {| task_ft := fun x => erase_tm (task_ft S x);
            task_fc := g_Var_f; task_support := task_support S |}.
  - intros; apply (proj1 task_erase_scope); apply task_ft_scope.
  - simpl; auto.
  - intros; rewrite task_ft_fresh by assumption; reflexivity.
  - auto.
  - intros; eapply task_ft_vars; [eassumption|]; eapply (proj1 task_erase_vars); eassumption.
  - simpl; intros; fsetdec.
Defined.

Lemma task_sub_erase :
  (forall s S, erase_tm (task_sub_tm S s) = task_sub_tm (task_erased_sub S) (erase_tm s)) /\
  (forall s : brs, True) /\ (forall s : co, True) /\
  (forall s S, erase_constraint (task_sub_constraint S s) = task_sub_constraint (task_erased_sub S) (erase_constraint s)).
Proof.
  task_structure; intros; try exact I; cbn;
  try match goal with |- context [match ?r with Rel => _ | Irrel => _ end] => destruct r end;
  cbn; autorewrite with task_sub; try reflexivity; f_equal; auto.
  all: match goal with
    | |- ?L = task_walk_tm _ _ _ _ ?i ?j ?t =>
      change (L = task_walk_tm (fun _ => task_ft (task_erased_sub S))
         (fun _ => task_fc (task_erased_sub S)) task_id_bt task_id_bc i j t);
      rewrite task_sub_tm_walk; auto
    end.
Qed.

Lemma task_fv_vars :
  (forall s x, x `in` fv_tm_tm_tm s -> x `in` task_vars_tm s) /\
  (forall s x, x `in` fv_tm_tm_brs s -> x `in` task_vars_brs s) /\
  (forall s x, x `in` fv_tm_tm_co s -> x `in` task_vars_co s) /\
  (forall s x, x `in` fv_tm_tm_constraint s -> x `in` task_vars_constraint s).
Proof.
  task_structure; intros; cbn in *.
  all: repeat match goal with H : _ `in` union _ _ |- _ =>
    apply AtomSetImpl.union_1 in H; destruct H
  end.
  all: try solve [fsetdec].
  all: match goal with
   | HI : forall x : atom, _,
     HM : ?x `in` _ |- _ =>
     solve [let HH := fresh in pose proof (HI x HM) as HH; fsetdec]
  end.
Qed.

Lemma task_sub_rho_erase : forall rho x a S,
  x `notin` task_support S -> RhoCheck rho x (erase_tm a) ->
  RhoCheck rho x (erase_tm (task_sub_tm S a)).
Proof.
  assert (Hform :
    (forall a x S, x `notin` task_support S -> x `notin` fv_tm_tm_tm (erase_tm a) ->
      x `notin` fv_tm_tm_tm (erase_tm (task_sub_tm S a))) /\
    (forall s : brs, True) /\ (forall s : co, True) /\
    (forall a x S, x `notin` task_support S -> x `notin` fv_tm_tm_constraint (erase_constraint a) ->
      x `notin` fv_tm_tm_constraint (erase_constraint (task_sub_constraint S a)))).
  {
    task_structure; intros; try exact I; cbn in *;
    try match goal with
    | H : context [match ?r with Rel => _ | Irrel => _ end] |- _ => destruct r
    end;
    cbn in *; autorewrite with task_sub; cbn; try solve [fsetdec | eauto].
    all: try solve [
      match goal with
      | IH : forall x S, _ -> _ -> _, Hs : ?x `notin` task_support ?S |- _ =>
        pose proof (IH x S Hs (ltac:(fsetdec))) as Htmp; fsetdec
      end].
    all: try match goal with
      | IH : forall x S, _ -> _ -> _, Hs : ?x `notin` task_support ?S |- _ =>
        let Hdone := fresh in
        pose proof (IH x S Hs (ltac:(fsetdec))) as Hdone; clear IH
      end.
    all: try solve [fsetdec].
    all: intro Hin.
    all: match goal with
    | Hs : ?y `notin` task_support ?S,
      H : ?y `in` fv_tm_tm_tm (erase_tm (task_ft ?S ?x)) |- _ =>
      pose proof ((proj1 task_fv_vars) _ _ H) as A;
      pose proof ((proj1 task_erase_vars) _ _ A) as B;
      pose proof (task_ft_vars S x y Hs B); subst; fsetdec
    end.
  }
  intros rho x a S HF HR; inversion HR; subst.
  - apply Rho_Rel; exact I.
  - apply Rho_IrrRel; eapply (proj1 Hform); eassumption.
Qed.

Lemma task_sub_lc_tm : forall S a, lc_tm a -> lc_tm (task_sub_tm S a).
Proof.
  intros; apply task_lc_from_scope_tm; apply (proj1 task_sub_scope).
  apply (proj2 (proj2 (proj2 task_scope_from_lc))); assumption.
Qed.

Lemma task_sub_lc_co : forall S g, lc_co g -> lc_co (task_sub_co S g).
Proof.
  intros S g Hg.
  apply (proj1 (proj2 (proj2 (task_lc_from_scope_size (task_size_co (task_sub_co S g))))));
    [apply Nat.le_refl|].
  apply (proj1 (proj2 (proj2 task_sub_scope))).
  apply (proj1 (proj2 task_scope_from_lc)); assumption.
Qed.

Lemma task_sub_lc_constraint : forall S p, lc_constraint p -> lc_constraint (task_sub_constraint S p).
Proof.
  intros S p Hp.
  apply (proj2 (proj2 (proj2 (task_lc_from_scope_size
    (task_size_constraint (task_sub_constraint S p)))))); [apply Nat.le_refl|].
  apply (proj2 (proj2 (proj2 task_sub_scope))).
  apply (proj1 task_scope_from_lc); assumption.
Qed.

Scheme task_cvalue_ind := Induction for CoercedValue Sort Prop
with task_value_ind := Induction for Value Sort Prop.
Combined Scheme task_values_ind from task_cvalue_ind, task_value_ind.

Lemma task_sub_value :
  (forall a, CoercedValue a -> forall S, CoercedValue (task_sub_tm S a)) /\
  (forall a, Value a -> forall S, Value (task_sub_tm S a)).
Proof.
  pose proof task_sub_open_t_rec as [OT _].
  apply task_values_ind; intros; try exact I.
  all: repeat match goal with
    | S : task_substitution, H : lc_tm ?a |- _ =>
      lazymatch a with task_sub_tm _ _ => fail | _ => let HL := fresh in pose proof (task_sub_lc_tm S a H) as HL; clear H end
    | S : task_substitution, H : lc_constraint ?p |- _ =>
      lazymatch p with task_sub_constraint _ _ => fail | _ => let HL := fresh in pose proof (task_sub_lc_constraint S p H) as HL; clear H end
    | S : task_substitution, H : lc_co ?g |- _ =>
      lazymatch g with task_sub_co _ _ => fail | _ => let HL := fresh in pose proof (task_sub_lc_co S g H) as HL; clear H end
  end.
  all: cbn in *; autorewrite with task_sub in *;
    try solve [eauto using CV, CC, Value_Star, Value_Pi, Value_CPi, Value_AbsRel,
        Value_UAbsRel, Value_CAbs, Value_UCAbs].
  all: lazymatch goal with
       | S : task_substitution, L : vars |- Value (a_UAbs Irrel _) =>
           eapply Value_UAbsIrrel with (L := L \u task_support S)
       | S : task_substitution, L : vars |- Value (a_Abs Irrel _ _) =>
           eapply Value_AbsIrrel with (L := L \u task_support S)
       end.
  all: try solve [assumption].
  all: intros x Hx; unfold open_tm_wrt_tm in *;
    match goal with
    | S : task_substitution,
      IH : forall x : atom, x `notin` ?L -> forall S, _ |- _ =>
      specialize (IH x (ltac:(fsetdec)) S);
      rewrite OT in IH;
      change (task_sub_tm S (a_Var_f x)) with (task_ft S x) in IH;
      rewrite task_ft_fresh in IH by fsetdec;
      exact IH
    end.
Qed.

Lemma task_ann_sig_bind : forall F a A,
  binds F (Ax a A) an_toplevel -> F = Fix /\ a = FixDef /\ A = FixTy.
Proof.
  intros F a A H.
  change ((Fix, Ax FixDef FixTy) = (F, Ax a A) \/ False) in H.
  intuition congruence.
Qed.

Lemma task_imp_sig_bind : forall F a A,
  binds F (Ax a A) toplevel -> F = Fix /\ a = erase_tm FixDef /\ A = erase_tm FixTy.
Proof.
  intros F a A H.
  change ((Fix, Ax (erase_tm FixDef) (erase_tm FixTy)) = (F, Ax a A) \/ False) in H.
  intuition congruence.
Qed.

Lemma task_sub_beta : forall a b,
  Beta a b -> forall S, Beta (task_sub_tm S a) (task_sub_tm S b).
Proof.
  pose proof task_sub_open_t_rec as [OT _].
  pose proof task_sub_open_c_rec as [OC _].
  intros a b H; destruct H; intros S.
  - unfold open_tm_wrt_tm; rewrite OT.
    pose proof (proj2 task_sub_value _ H0 S) as HV.
    cbn in HV |- *; autorewrite with task_sub in *.
    apply Beta_AppAbs; auto using task_sub_lc_tm.
  - unfold open_tm_wrt_co; rewrite OC.
    pose proof (task_sub_lc_tm S _ H) as HL.
    cbn in HL |- *; autorewrite with task_sub in *.
    apply Beta_CAppCAbs; exact HL.
  - apply task_imp_sig_bind in H; destruct H as [-> [-> ->]].
    change (Beta (a_Fam Fix) (erase_tm FixDef)).
    eapply Beta_Axiom with (A := erase_tm FixTy).
    change ((Fix, Ax (erase_tm FixDef) (erase_tm FixTy)) =
            (Fix, Ax (erase_tm FixDef) (erase_tm FixTy)) \/ False).
    left; reflexivity.
Qed.

Definition task_sub_sort S s :=
  match s with
  | Tm A => Tm (task_sub_tm S A)
  | Co p => Co (task_sub_constraint S p)
  end.

Definition task_sub_assum S G H D E :=
  forall c a b A, binds c (Co (Eq a b A)) G -> c `in` D ->
    AnnDefEq H E (task_fc S c) (task_sub_tm S a) (task_sub_tm S b).

Record task_sub_ctx S G H := {
  task_sub_ctx_ok : AnnCtx H;
  task_sub_ctx_var : forall x A, binds x (Tm A) G ->
      AnnTyping H (task_ft S x) (task_sub_tm S A);
  task_sub_ctx_co : task_sub_assum S G H (dom G) (dom H)
}.

Arguments task_sub_ctx_ok {S G H}.
Arguments task_sub_ctx_var {S G H}.
Arguments task_sub_ctx_co {S G H}.

Lemma task_sub_assum_cons : forall S G H D E x s,
  x `notin` D -> AnnCtx (x ~ task_sub_sort S s ++ H) ->
  task_sub_assum S G H D E ->
  task_sub_assum S (x ~ s ++ G) (x ~ task_sub_sort S s ++ H) D E.
Proof.
  unfold task_sub_assum; intros S G H D E x s Hfresh Hctx HM c a b A Hb Hd.
  apply binds_cons_1 in Hb; destruct Hb as [[-> _]|Hb]; [contradiction|].
  eapply (proj1 (proj2 (proj2 (proj2 task_ann_weaken)))).
  - eapply HM; eassumption.
  - exact Hctx.
  - unfold task_extends; eauto using binds_app_3.
  - unfold AtomSetImpl.Subset; auto.
Qed.

Lemma task_sub_ctx_cons : forall S G H x s,
  x `notin` task_support S -> AnnCtx (x ~ task_sub_sort S s ++ H) ->
  task_sub_ctx S G H -> task_sub_ctx S (x ~ s ++ G) (x ~ task_sub_sort S s ++ H).
Proof.
  intros S G H x s Hfresh Hctx M.
  constructor.
  - exact Hctx.
  - intros y A Hb. apply binds_cons_1 in Hb.
    destruct Hb as [[-> <-]|Hb].
    + rewrite task_ft_fresh by assumption.
      cbn; apply An_Var; eauto using binds_cons_2.
    + eapply (proj1 (proj2 task_ann_weaken)).
      * exact (task_sub_ctx_var M _ _ Hb).
      * exact Hctx.
      * unfold task_extends; eauto using binds_app_3.
  - unfold task_sub_assum; intros c a b A Hb _.
    apply binds_cons_1 in Hb; destruct Hb as [[-> <-]|Hb].
    + rewrite task_fc_fresh by assumption.
      cbn [task_sub_sort task_sub_constraint task_walk_constraint].
      autorewrite with task_sub.
      eapply An_Assn; [exact Hctx | apply binds_cons_2; reflexivity | simpl; fsetdec].
    + eapply (proj1 (proj2 (proj2 (proj2 task_ann_weaken)))).
      * exact (task_sub_ctx_co M _ _ _ _ Hb (binds_In _ _ _ _ Hb)).
      * exact Hctx.
      * unfold task_extends; eauto using binds_app_3.
      * simpl; unfold AtomSetImpl.Subset; intros; fsetdec.
Qed.

Ltac task_reduce_sub :=
  cbn [task_sub_tm task_sub_co task_sub_constraint
       task_walk_tm task_walk_co task_walk_constraint] in *;
  autorewrite with task_sub in *.

Ltac task_rewrite_sub_open :=
  unfold open_tm_wrt_tm, open_co_wrt_tm, open_tm_wrt_co, open_co_wrt_co in *;
  rewrite ?(proj1 task_sub_open_t_rec), ?(proj1 (proj2 (proj2 task_sub_open_t_rec))),
          ?(proj1 task_sub_open_c_rec), ?(proj1 (proj2 (proj2 task_sub_open_c_rec))) in *.

Lemma task_ann_substitute :
  (forall G p, AnnPropWff G p -> forall S H,
    task_sub_ctx S G H -> AnnPropWff H (task_sub_constraint S p)) /\
  (forall G a A, AnnTyping G a A -> forall S H,
    task_sub_ctx S G H -> AnnTyping H (task_sub_tm S a) (task_sub_tm S A)) /\
  (forall G D g p q, AnnIso G D g p q -> forall S H E,
    task_sub_ctx S G H -> task_sub_assum S G H D E ->
    AnnIso H E (task_sub_co S g) (task_sub_constraint S p) (task_sub_constraint S q)) /\
  (forall G D g a b, AnnDefEq G D g a b -> forall S H E,
    task_sub_ctx S G H -> task_sub_assum S G H D E ->
    AnnDefEq H E (task_sub_co S g) (task_sub_tm S a) (task_sub_tm S b)) /\
  (forall G, AnnCtx G -> True) /\ (forall W, AnnSig W -> True).
Proof.
  pose proof (@task_sub_ctx_ok) as Hctx.
  pose proof (@task_sub_ctx_co) as Hco.
  unfold task_sub_assum in Hco.
  apply task_ann_ind; intros; try exact I.
  all: try solve [
     match goal with
     | HH : task_sub_ctx ?S ?G ?H, HB : binds ?x (Tm ?A) ?G |- _ =>
        exact (task_sub_ctx_var HH x A HB)
     | HH : task_sub_assum ?S ?G ?H ?D ?E, HB : binds ?x (Co (Eq ?a ?b ?A)) ?G |- _ =>
        apply (HH x a b A HB); assumption
     end].
  all: task_reduce_sub; task_rewrite_sub_open.
  all: repeat match goal with
   | M : task_sub_ctx ?S ?G ?H,
     I : forall (S : task_substitution) J, task_sub_ctx S ?G J -> _ |- _ =>
       specialize (I S H M)
   | M : task_sub_ctx ?S ?G ?H,
     I : forall (S : task_substitution) J E, task_sub_ctx S ?G J ->
              task_sub_assum S ?G J (dom ?G) E -> _ |- _ =>
       specialize (I S H (dom H) M (task_sub_ctx_co M))
   | M : task_sub_ctx ?S ?G ?H, MA : task_sub_assum ?S ?G ?H ?D ?E,
     I : forall (S : task_substitution) J E, task_sub_ctx S ?G J ->
              task_sub_assum S ?G J ?D E -> _ |- _ =>
       specialize (I S H E M MA)
  end.
  all: task_reduce_sub.
  all: try solve [eauto 5 using An_Wff, An_Star, An_App, An_Conv, An_CApp,
    An_PropCong, An_CPiFst, An_IsoSym, An_IsoConv, An_Refl,
    An_EraseEq, An_Sym, An_Trans, An_Beta, An_AppCong, An_PiFst,
    An_PiSnd, An_CAppCong, An_CPiSnd, An_Cast, An_IsoSnd, task_sub_ctx_ok].
  all: try solve [
    first [eapply An_Wff | eapply An_EraseEq | eapply An_IsoConv | eapply An_Beta];
    try eassumption; rewrite !(proj1 task_sub_erase);
    eauto using task_sub_beta; congruence].
  all: try solve [
    match goal with
    | |- AnnTyping _ _ (open_tm_wrt_tm_rec 0 _ ?B) =>
        eapply An_App with (B := B); eassumption
    | |- AnnTyping _ _ (open_tm_wrt_co_rec 0 _ ?B) =>
        eapply An_CApp with (B := B); eassumption
    | |- AnnDefEq _ _ (g_PiSnd _ _) (open_tm_wrt_tm_rec 0 _ ?B) (open_tm_wrt_tm_rec 0 _ ?C) =>
        eapply An_PiSnd with (B1 := B) (B2 := C); eassumption
    | |- AnnDefEq _ _ (g_CPiSnd _ _ _) (open_tm_wrt_co_rec 0 _ ?B) (open_tm_wrt_co_rec 0 _ ?C) =>
        eapply An_CPiSnd with (B1 := B) (B2 := C); eassumption
    | HB : binds ?F (Ax ?a ?A) an_toplevel |- AnnTyping _ (a_Fam ?F) _ =>
        destruct (task_ann_sig_bind F a A HB) as [-> [-> ->]];
        eapply An_Fam with (a := FixDef);
          [eauto using task_sub_ctx_ok | exact HB | eassumption]
    end].
  all: try match goal with
   | L : vars, S : task_substitution, M : task_sub_ctx ?S ?G ?H |- _ =>
      let F := constr:(L \u dom H \u task_support S) in
      first [eapply An_Pi with (L := F) | eapply An_Abs with (L := F) |
             eapply An_CPi with (L := F) | eapply An_CAbs with (L := F) |
             let fresh_names := constr:(F \u D) in
             first [eapply An_PiCong with (L := fresh_names) (B2 := task_sub_tm S B2) |
                    eapply An_AbsCong with (L := fresh_names) (b2 := task_sub_tm S b2) |
                    eapply An_CPiCong with (L := fresh_names) (B2 := task_sub_tm S B2) |
                    eapply An_CAbsCong with (L := fresh_names) (a2 := task_sub_tm S a2)]];
      try eassumption
  end.
  all: try match goal with |- forall x : atom, x `notin` _ -> _ => intros x Hx; task_rewrite_sub_open end.
  all: try solve [
    match goal with
    | S : task_substitution, R : forall x : atom, x `notin` ?L -> RhoCheck _ _ _ |- RhoCheck _ ?x (erase_tm (open_tm_wrt_tm_rec 0 (a_Var_f ?x) ?a)) =>
      specialize (R x (ltac:(fsetdec)));
      let H := fresh in pose proof (task_sub_rho_erase _ _ _ S (ltac:(fsetdec)) R) as H;
      rewrite (proj1 task_sub_open_t_rec) in H;
      change (task_sub_tm S (a_Var_f x)) with (task_ft S x) in H;
      rewrite task_ft_fresh in H by fsetdec; exact H
    end].
  all: try solve [
    match goal with
    | S : task_substitution,
      Eq : forall x : atom, x `notin` ?L -> _ = _ |- _ = _ =>
      specialize (Eq x (ltac:(fsetdec)));
      let Q := fresh in
      pose proof (f_equal (task_sub_tm S) Eq) as Q;
      task_rewrite_sub_open; task_reduce_sub;
      try rewrite (task_ft_fresh S x) in Q by fsetdec;
      try rewrite (task_fc_fresh S x) in Q by fsetdec;
      exact Q
    end].
  all: try match goal with
    | H : AnnTyping ?G (a_Pi _ _ _) _ |- AnnDefEq (_ :: ?G) _ _ _ _ => inversion H; subst; clear H
    end.
  all: try match goal with
    | H : AnnTyping ?G (a_CPi _ _) _ |- AnnDefEq (_ :: ?G) _ _ _ _ => inversion H; subst; clear H
    | H : AnnTyping ?G (a_CAbs _ _) _ |- AnnDefEq (_ :: ?G) _ _ _ _ => inversion H; subst; clear H
    end.
  all: try solve [
    match goal with
    | M : task_sub_ctx ?S ?G ?H,
      IH : forall x : atom, x `notin` ?L -> forall S J,
              task_sub_ctx S (x ~ ?U ++ ?G) J -> _ |- _ =>
      let Hext := fresh in
      assert (Hext : AnnCtx (x ~ task_sub_sort S U ++ H))
         by (cbn [task_sub_sort]; first [apply An_ConsTm | apply An_ConsCo];
             first [eapply task_sub_ctx_ok; exact M | eassumption | fsetdec]);
      specialize (IH x (ltac:(fsetdec)) S _ (task_sub_ctx_cons _ _ _ _ _ (ltac:(fsetdec)) Hext M));
      task_rewrite_sub_open; task_reduce_sub;
      try rewrite (task_ft_fresh S x) in IH by fsetdec;
      try rewrite (task_fc_fresh S x) in IH by fsetdec;
      exact IH
    end].
  all: try solve [
    match goal with
    | M : task_sub_ctx ?S ?G ?H,
      MA : task_sub_assum ?S ?G ?H ?D ?E,
      IH : forall x : atom, x `notin` ?L -> forall S J E,
              task_sub_ctx S (x ~ ?U ++ ?G) J ->
              task_sub_assum S (x ~ ?U ++ ?G) J ?D E -> _ |- _ =>
      let Hext := fresh in
      assert (Hext : AnnCtx (x ~ task_sub_sort S U ++ H))
         by (cbn [task_sub_sort]; first [apply An_ConsTm | apply An_ConsCo];
             first [eapply task_sub_ctx_ok; exact M | eassumption | fsetdec]);
      specialize (IH x (ltac:(fsetdec)) S _ E
           (task_sub_ctx_cons _ _ _ _ _ (ltac:(fsetdec)) Hext M)
           (task_sub_assum_cons _ _ _ _ _ _ _ (ltac:(fsetdec)) Hext MA));
      task_rewrite_sub_open; task_reduce_sub;
      try rewrite (task_ft_fresh S x) in IH by fsetdec;
      try rewrite (task_fc_fresh S x) in IH by fsetdec;
      exact IH
    end].
  all: try solve [
    match goal with
    | IH : forall (_ : atom), _ -> forall (_ : task_substitution) (_ : context), _,
      S : task_substitution, HF : ?x `notin` _ |- AnnTyping ?J _ _ =>
      let K := constr:(IH x (ltac:(fsetdec)) S J) in
      let TK := type of K in
      lazymatch TK with
      | ?Premise -> _ =>
        let M' := fresh in
        assert (M' : Premise)
          by (eapply task_sub_ctx_cons; [fsetdec | first [apply An_ConsTm | apply An_ConsCo];
                                       eauto using task_sub_ctx_ok; fsetdec | eassumption]);
        let HS := fresh in pose proof (K M') as HS;
        task_rewrite_sub_open; task_reduce_sub;
        try rewrite (task_ft_fresh S x) in HS by fsetdec;
        try rewrite (task_fc_fresh S x) in HS by fsetdec;
        exact HS
      end
    end].
  all: try match goal with
    | HT : AnnTyping ?H (a_Pi _ ?A _) a_Star |- AnnDefEq (?x ~ Tm ?A ++ ?H) _ _ _ _ =>
      let HA := fresh in assert (HA : AnnTyping H A a_Star) by (inversion HT; subst; assumption)
    | HT : AnnTyping ?H (a_CPi ?p _) a_Star |- AnnDefEq (?x ~ Co ?p ++ ?H) _ _ _ _ =>
      let HA := fresh in assert (HA : AnnPropWff H p) by (inversion HT; subst; assumption)
    | HT : AnnTyping ?H (a_CAbs ?p _) _ |- AnnDefEq (?x ~ Co ?p ++ ?H) _ _ _ _ =>
      let HA := fresh in assert (HA : AnnPropWff H p) by (inversion HT; subst; assumption)
  end.
  all: try solve [
    match goal with
    | IH : forall (_ : atom), _ -> forall (_ : task_substitution) (_ : context) (_ : available_props), _,
      S : task_substitution, HF : ?x `notin` _ |- AnnDefEq ?J ?E _ _ _ =>
      let K := constr:(IH x (ltac:(fsetdec)) S J E) in
      let TK := type of K in
      lazymatch TK with
      | ?M -> ?MA -> _ =>
        let M' := fresh in let MA' := fresh in
        assert (M' : M)
          by (eapply task_sub_ctx_cons; [fsetdec | first [apply An_ConsTm | apply An_ConsCo];
                                       eauto using task_sub_ctx_ok; fsetdec | eassumption]);
        assert (MA' : MA) by (eapply task_sub_assum_cons; [fsetdec|exact (task_sub_ctx_ok M')|eassumption]);
        let HS := fresh in pose proof (K M' MA') as HS;
        task_rewrite_sub_open; task_reduce_sub;
        try rewrite (task_ft_fresh S x) in HS by fsetdec;
        try rewrite (task_fc_fresh S x) in HS by fsetdec;
        exact HS
      end
    end].
  all: try solve [
    match goal with
    | R : forall (_ : atom), _ -> _,
      S : task_substitution |- RhoCheck _ ?x _ =>
      let RF := constr:(R x (ltac:(fsetdec))) in
      let T := type of RF in
      lazymatch T with RhoCheck ?rho ?y (erase_tm ?a) =>
        let Q := fresh in
        pose proof (task_sub_rho_erase rho y a S (ltac:(fsetdec)) RF) as Q;
        rewrite (proj1 task_sub_open_t_rec) in Q;
        change (task_sub_tm S (a_Var_f x)) with (task_ft S x) in Q;
        rewrite (task_ft_fresh S x) in Q by fsetdec; exact Q
      end
    end].
Qed.
Definition task_single_t (x : atom) (u : tm) (Hu : task_scope_tm 0 0 u) :
  task_substitution.
Proof.
  refine {| task_ft := fun y => if Atom.eq_dec y x then u else a_Var_f y;
            task_fc := g_Var_f;
            task_support := {{x}} \u task_vars_tm u |}; simpl; intros;
   try match goal with |- context [Atom.eq_dec ?y ?x] => destruct (Atom.eq_dec y x); subst end;
   try match goal with H : context [Atom.eq_dec ?y ?x] |- _ => destruct (Atom.eq_dec y x); subst end;
   simpl in *; try exact I; try assumption; try reflexivity; fsetdec.
Defined.

Lemma task_single_t_inert :
  (forall s x (u : tm) Hu, x `notin` task_vars_tm s -> task_sub_tm (task_single_t x u Hu) s = s) /\
  (forall s x (u : tm) Hu, x `notin` task_vars_brs s -> task_sub_brs (task_single_t x u Hu) s = s) /\
  (forall s x (u : tm) Hu, x `notin` task_vars_co s -> task_sub_co (task_single_t x u Hu) s = s) /\
  (forall s x (u : tm) Hu, x `notin` task_vars_constraint s -> task_sub_constraint (task_single_t x u Hu) s = s).
Proof.
  task_structure; intros; cbn; autorewrite with task_sub; try reflexivity;
  repeat first
    [rewrite (task_sub_tm_walk (task_single_t x u Hu))
    |rewrite (task_sub_brs_walk (task_single_t x u Hu))
    |rewrite (task_sub_co_walk (task_single_t x u Hu))
    |rewrite (task_sub_constraint_walk (task_single_t x u Hu))];
  try match goal with |- context [KeySetFacts.eq_dec ?y ?x] =>
    destruct (Atom.eq_dec y x); subst; [exfalso; simpl in *; fsetdec | reflexivity]
  end;
  try reflexivity;
  f_equal;
  match goal with
    | IH : forall (_ : atom) (_ : tm) _, _ |- _ =>
      solve [eapply IH; simpl in *; fsetdec]
  end.
Qed.

Definition task_single_c (x : atom) (u : co) (Hu : task_scope_co 0 0 u) :
  task_substitution.
Proof.
  refine {| task_ft := a_Var_f;
            task_fc := fun y => if Atom.eq_dec y x then u else g_Var_f y;
            task_support := {{x}} \u task_vars_co u |}; simpl; intros;
   try match goal with |- context [Atom.eq_dec ?y ?x] => destruct (Atom.eq_dec y x); subst end;
   try match goal with H : context [Atom.eq_dec ?y ?x] |- _ => destruct (Atom.eq_dec y x); subst end;
   simpl in *; try exact I; try assumption; try reflexivity; fsetdec.
Defined.

Lemma task_single_c_inert :
  (forall s x (u : co) Hu, x `notin` task_vars_tm s -> task_sub_tm (task_single_c x u Hu) s = s) /\
  (forall s x (u : co) Hu, x `notin` task_vars_brs s -> task_sub_brs (task_single_c x u Hu) s = s) /\
  (forall s x (u : co) Hu, x `notin` task_vars_co s -> task_sub_co (task_single_c x u Hu) s = s) /\
  (forall s x (u : co) Hu, x `notin` task_vars_constraint s -> task_sub_constraint (task_single_c x u Hu) s = s).
Proof.
  task_structure; intros; cbn; autorewrite with task_sub; try reflexivity;
  repeat first
    [rewrite (task_sub_tm_walk (task_single_c x u Hu))
    |rewrite (task_sub_brs_walk (task_single_c x u Hu))
    |rewrite (task_sub_co_walk (task_single_c x u Hu))
    |rewrite (task_sub_constraint_walk (task_single_c x u Hu))];
  try match goal with |- context [KeySetFacts.eq_dec ?y ?x] =>
    destruct (Atom.eq_dec y x); subst; [exfalso; simpl in *; fsetdec | reflexivity]
  end;
  try reflexivity;
  f_equal;
  match goal with
    | IH : forall (_ : atom) (_ : co) _, _ |- _ =>
      solve [eapply IH; simpl in *; fsetdec]
  end.
Qed.


Definition task_vars_sort s :=
  match s with Tm A => task_vars_tm A | Co p => task_vars_constraint p end.

Fixpoint task_vars_context (G : context) :=
  match G with nil => empty | (_,s)::G => task_vars_sort s \u task_vars_context G end.

Lemma task_vars_binds : forall G x s,
  binds x s G -> AtomSetImpl.Subset (task_vars_sort s) (task_vars_context G).
Proof.
  unfold AtomSetImpl.Subset.
  induction G as [|[x t] G IH]; intros y s Hb z Hz; simpl in *;
    [contradiction|].
  destruct Hb as [E | Hb]; [inversion E; subst; fsetdec | eapply IH in Hz; eauto; fsetdec].
Qed.

Lemma task_bound_type : forall G x s,
  AnnCtx G -> binds x s G ->
  match s with Tm A => AnnTyping G A a_Star | Co p => AnnPropWff G p end.
Proof.
  intros G x s HCtx; induction HCtx; intro HB; simpl in HB; try contradiction.
  all: destruct HB as [Q | HB]; [inversion Q; subst; clear Q |
                                  specialize (IHHCtx HB)].
  all: match goal with |- context [match ?s with Tm _ => _ | Co _ => _ end] =>
    destruct s
  | |- _ => idtac end.
  all: first [eapply (proj1 task_ann_weaken) | eapply (proj1 (proj2 task_ann_weaken))];
      [eassumption | eauto using An_ConsCo, An_ConsTm | unfold task_extends; eauto using binds_app_3].
Qed.

Lemma task_single_t_for_ctx : forall G H x u U Hu,
  x `notin` dom G -> x `notin` task_vars_context G ->
  x `notin` task_vars_tm U -> AnnCtx H -> task_extends G H ->
  AnnTyping H u U ->
  task_sub_ctx (task_single_t x u Hu) (x ~ Tm U ++ G) H.
Proof.
  intros G H x u U Hu Hx Hfv HU HC HE HT.
  constructor; [exact HC| |].
  - intros y R Hb; apply binds_cons_1 in Hb; destruct Hb as [[-> Q]|Hb].
    + inversion Q; subst; clear Q.
      rewrite (proj1 task_single_t_inert) by exact HU.
      cbn; destruct (Atom.eq_dec x x); congruence.
    + rewrite (proj1 task_single_t_inert)
        by (pose proof (task_vars_binds _ _ _ Hb) as K; intro Hin; apply Hfv; eapply K; exact Hin).
      cbn; destruct (Atom.eq_dec y x) as [->|Hneq].
      * exfalso; apply Hx; eapply binds_In; eassumption.
      * apply An_Var; eauto.
  - unfold task_sub_assum; intros c a b A Hb _.
    apply binds_cons_1 in Hb; destruct Hb as [[? Hbad]|Hb]; try discriminate.
    pose proof (task_vars_binds _ _ _ Hb) as K.
    assert (HF : x `notin` task_vars_constraint (Eq a b A)) by
     (intro Hin; apply Hfv; eapply K; exact Hin).
    cbn in HF.
    rewrite !(proj1 task_single_t_inert) by fsetdec.
    cbn; eapply An_Assn; [exact HC|apply HE; exact Hb|eapply binds_In; apply HE; exact Hb].
Qed.

Lemma task_single_c_for_ctx : forall G H x g a b A Hg,
  x `notin` dom G -> x `notin` task_vars_context G ->
  x `notin` task_vars_constraint (Eq a b A) ->
  AnnCtx H -> task_extends G H -> AnnDefEq H (dom H) g a b ->
  task_sub_ctx (task_single_c x g Hg) (x ~ Co (Eq a b A) ++ G) H.
Proof.
  intros G H x g a b A Hg Hx Hfv HF HC HE HG.
  constructor; [exact HC| |].
  - intros y R Hb; apply binds_cons_1 in Hb; destruct Hb as [[? Hbad]|Hb]; try discriminate.
    rewrite (proj1 task_single_c_inert)
      by (pose proof (task_vars_binds _ _ _ Hb) as K; intro Hin; apply Hfv; eapply K; exact Hin).
    apply An_Var; eauto.
  - unfold task_sub_assum; intros y a1 b1 A1 Hb _.
    apply binds_cons_1 in Hb; destruct Hb as [[-> Heq]|Hb].
    + inversion Heq; subst; clear Heq.
      cbn in HF.
      rewrite !(proj1 task_single_c_inert) by fsetdec.
      cbn; destruct (Atom.eq_dec x x); congruence.
    + pose proof (task_vars_binds _ _ _ Hb) as K.
      assert (HK : x `notin` task_vars_constraint (Eq a1 b1 A1)) by
       (intro Hin; apply Hfv; eapply K; exact Hin).
      cbn in HK.
      rewrite !(proj1 task_single_c_inert) by fsetdec.
      cbn; destruct (Atom.eq_dec y x) as [->|Hneq].
      * exfalso; apply Hx; eapply binds_In; eassumption.
      * eapply An_Assn; [exact HC|apply HE; exact Hb|eapply binds_In; apply HE; exact Hb].
Qed.

Lemma task_single_t_for_availability : forall G H D x u U Hu,
  x `notin` task_vars_context G -> AnnCtx H -> task_extends G H ->
  task_sub_assum (task_single_t x u Hu) (x ~ Tm U ++ G) H D D.
Proof.
  unfold task_sub_assum; intros G H D x u U Hu Hfv HC HE c a b A Hb Hin.
  apply binds_cons_1 in Hb; destruct Hb as [[? Hbad]|Hb]; try discriminate.
  pose proof (task_vars_binds _ _ _ Hb) as K.
  assert (HF : x `notin` task_vars_constraint (Eq a b A)) by
   (intro HIn; apply Hfv; eapply K; exact HIn).
  cbn in HF; rewrite !(proj1 task_single_t_inert) by fsetdec.
  eapply An_Assn; eauto.
Qed.

Lemma task_single_c_for_availability : forall G H D x g p Hg,
  x `notin` D -> x `notin` task_vars_context G -> AnnCtx H -> task_extends G H ->
  task_sub_assum (task_single_c x g Hg) (x ~ Co p ++ G) H D D.
Proof.
  unfold task_sub_assum; intros G H D x g p Hg Hx Hfv HC HE c a b A Hb Hin.
  apply binds_cons_1 in Hb; destruct Hb as [[-> _]|Hb]; [contradiction|].
  pose proof (task_vars_binds _ _ _ Hb) as K.
  assert (HF : x `notin` task_vars_constraint (Eq a b A)) by
   (intro HIn; apply Hfv; eapply K; exact HIn).
  cbn in HF; rewrite !(proj1 task_single_c_inert) by fsetdec.
  cbn; destruct (Atom.eq_dec c x); [subst; contradiction|].
  eapply An_Assn; eauto.
Qed.

Lemma task_ann_ctx_of :
  (forall G p, AnnPropWff G p -> AnnCtx G) /\
  (forall G a A, AnnTyping G a A -> AnnCtx G) /\
  (forall G D g p q, AnnIso G D g p q -> AnnCtx G) /\
  (forall G D g a b, AnnDefEq G D g a b -> AnnCtx G) /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof. apply task_ann_ind; intros; auto. Qed.

Lemma task_ann_instantiate_t : forall G L A B u,
  AnnTyping G u A ->
  (forall x, x `notin` L -> AnnTyping (x ~ Tm A ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star) ->
  AnnTyping G (open_tm_wrt_tm B u) a_Star.
Proof.
  intros G L A B u Htyped Hbody.
  pose proof (proj1 (proj2 task_ann_scope) _ _ _ Htyped) as [Hu _].
  pose proof (proj1 (proj2 task_ann_ctx_of) _ _ _ Htyped) as HG.
  task_choose_fresh (L \u dom G \u task_vars_context G \u task_vars_tm A \u task_vars_tm B)
    ltac:(fun x Hx =>
      pose proof (task_single_t_for_ctx G G x u A Hu (ltac:(fsetdec))
         (ltac:(fsetdec)) (ltac:(fsetdec)) HG (ltac:(unfold task_extends; auto)) Htyped) as M;
      specialize (Hbody x (ltac:(fsetdec)));
      pose proof (proj1 (proj2 task_ann_substitute) _ _ _ Hbody _ _ M) as K;
      unfold open_tm_wrt_tm in *;
      rewrite (proj1 task_sub_open_t_rec) in K;
      rewrite (proj1 task_single_t_inert B x u Hu) in K by fsetdec;
      change (task_sub_tm (task_single_t x u Hu) (a_Var_f x)) with
             (if Atom.eq_dec x x then u else a_Var_f x) in K;
      destruct (Atom.eq_dec x x); [exact K|contradiction]).
Qed.

Lemma task_ann_instantiate_c : forall G L a b A B g,
  AnnDefEq G (dom G) g a b ->
  (forall c, c `notin` L ->
      AnnTyping (c ~ Co (Eq a b A) ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star) ->
  AnnTyping G (open_tm_wrt_co B g) a_Star.
Proof.
  intros G L a b A B g Htyped Hbody.
  pose proof (proj1 (proj2 (proj2 (proj2 task_ann_scope))) _ _ _ _ _ Htyped) as [Hg _].
  pose proof (proj1 (proj2 (proj2 (proj2 task_ann_ctx_of))) _ _ _ _ _ Htyped) as HG.
  task_choose_fresh (L \u dom G \u task_vars_context G \u task_vars_constraint (Eq a b A) \u task_vars_tm B)
    ltac:(fun c Hc =>
      pose proof (task_single_c_for_ctx G G c g a b A Hg (ltac:(fsetdec))
         (ltac:(fsetdec)) (ltac:(fsetdec)) HG (ltac:(unfold task_extends; auto)) Htyped) as M;
      specialize (Hbody c (ltac:(fsetdec)));
      pose proof (proj1 (proj2 task_ann_substitute) _ _ _ Hbody _ _ M) as K;
      unfold open_tm_wrt_co in *;
      rewrite (proj1 task_sub_open_c_rec) in K;
      rewrite (proj1 task_single_c_inert B c g Hg) in K by fsetdec;
      change (task_sub_co (task_single_c c g Hg) (g_Var_f c)) with
             (if Atom.eq_dec c c then g else g_Var_f c) in K;
      destruct (Atom.eq_dec c c); [exact K|contradiction]).
Qed.

Lemma task_ann_type : forall G a A, AnnTyping G a A -> AnnTyping G A a_Star.
Proof.
  apply (task_ann_typing_ind
    (fun _ _ _ => True)
    (fun G _ A _ => AnnTyping G A a_Star)
    (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ => True)
    (fun _ _ => True)
    (fun _ _ => True)); intros; try exact I; try assumption.
  - now apply An_Star.
  - exact (task_bound_type G x (Tm A) a b).
  - eapply An_Pi with (L := L); eauto.
  - match goal with I : AnnTyping _ (a_Pi _ _ _) a_Star |- _ =>
      inversion I; subst
    end.
    eauto using task_ann_instantiate_t.
  - apply An_Star; eapply (proj1 task_ann_ctx_of); eassumption.
  - eapply An_CPi with (L := L); eauto.
  - match goal with I : AnnTyping _ (a_CPi _ _) a_Star |- _ =>
      inversion I; subst
    end.
    eauto using task_ann_instantiate_c.
  - eapply (proj1 (proj2 task_ann_weaken)); [eassumption | eassumption | unfold task_extends; intros x s Hb; inversion Hb].
Qed.

Lemma task_imp_weaken :
  (forall G p, PropWff G p -> forall H,
    Ctx H -> task_extends G H -> PropWff H p) /\
  (forall G a A, Typing G a A -> forall H,
    Ctx H -> task_extends G H -> Typing H a A) /\
  (forall G D p q, Iso G D p q -> forall H E,
    Ctx H -> task_extends G H -> AtomSetImpl.Subset D E -> Iso H E p q) /\
  (forall G D a b A, DefEq G D a b A -> forall H E,
    Ctx H -> task_extends G H -> AtomSetImpl.Subset D E -> DefEq H E a b A) /\
  (forall G, Ctx G -> True).
Proof.
  apply task_implicit_ind; intros; try exact I.
  all: try solve [first
    [solve [eapply E_Wff; eauto 4 using task_extends_dom]
    |solve [eapply E_Star; eauto 4 using task_extends_dom]
    |solve [eapply E_Var; eauto 4 using task_extends_dom]
    |solve [eapply E_App; eauto 4 using task_extends_dom]
    |solve [eapply E_IApp; eauto 4 using task_extends_dom]
    |solve [eapply E_Conv; eauto 4 using task_extends_dom]
    |solve [eapply E_CApp; eauto 4 using task_extends_dom]
    |solve [eapply E_Fam; eauto 4 using task_extends_dom]
    |solve [eapply E_PropCong; eauto 4 using task_extends_dom]
    |solve [eapply E_IsoConv; eauto 4 using task_extends_dom]
    |solve [eapply E_CPiFst; eauto 4 using task_extends_dom]
    |solve [eapply E_Assn; eauto 4 using task_extends_dom]
    |solve [eapply E_Refl; eauto 4 using task_extends_dom]
    |solve [eapply E_Sym; eauto 4 using task_extends_dom]
    |solve [eapply E_Trans; eauto 4 using task_extends_dom]
    |solve [eapply E_Beta; eauto 4 using task_extends_dom]
    |solve [eapply E_AppCong; eauto 4 using task_extends_dom]
    |solve [eapply E_IAppCong; eauto 4 using task_extends_dom]
    |solve [eapply E_PiFst; eauto 4 using task_extends_dom]
    |solve [eapply E_PiSnd; eauto 4 using task_extends_dom]
    |solve [eapply E_CAppCong; eauto 4 using task_extends_dom]
    |solve [eapply E_CPiSnd; eauto 4 using task_extends_dom]
    |solve [eapply E_Cast; eauto 4 using task_extends_dom]
    |solve [eapply E_EqConv; eauto 4 using task_extends_dom]
    |solve [eapply E_IsoSnd; eauto 4 using task_extends_dom]]].
  all: try match goal with HC : Ctx ?H, HL : forall x : atom, x `notin` ?L -> _ |- _ =>
     first [eapply E_Pi with (L := L \u dom H) |
            eapply E_Abs with (L := L \u dom H) |
            eapply E_CPi with (L := L \u dom H) |
            eapply E_CAbs with (L := L \u dom H) |
            eapply E_PiCong with (L := L \u dom H) |
            eapply E_AbsCong with (L := L \u dom H) |
            eapply E_CPiCong with (L := L \u dom H) |
            eapply E_CAbsCong with (L := L \u dom H)]
  end.
  all: try solve [eauto].
  all: try solve [intros; eauto using E_ConsTm, E_ConsCo, task_extends_cons].
Qed.

Lemma task_sub_rho : forall S rho x a,
  (forall c, task_fc S c = g_Var_f c) ->
  x `notin` task_support S -> RhoCheck rho x a -> RhoCheck rho x (task_sub_tm S a).
Proof.
  assert (F :
    (forall a S x, (forall c, task_fc S c = g_Var_f c) ->
      x `notin` task_support S -> x `notin` fv_tm_tm_tm a -> x `notin` fv_tm_tm_tm (task_sub_tm S a)) /\
    (forall a S x, (forall c, task_fc S c = g_Var_f c) ->
      x `notin` task_support S -> x `notin` fv_tm_tm_brs a -> x `notin` fv_tm_tm_brs (task_sub_brs S a)) /\
    (forall a S x, (forall c, task_fc S c = g_Var_f c) ->
      x `notin` task_support S -> x `notin` fv_tm_tm_co a -> x `notin` fv_tm_tm_co (task_sub_co S a)) /\
    (forall a S x, (forall c, task_fc S c = g_Var_f c) ->
      x `notin` task_support S -> x `notin` fv_tm_tm_constraint a -> x `notin` fv_tm_tm_constraint (task_sub_constraint S a))).
  { task_structure; intros; cbn in *; autorewrite with task_sub;
    try match goal with H : forall _, task_fc _ _ = _ |- context [task_fc _ _] => rewrite H end;
    cbn; try solve [fsetdec].
    all: repeat match goal with
    | IH : forall (S : task_substitution) x, _ -> _ -> _ -> _,
      HS : ?x `notin` task_support ?S,
      HC : forall c, task_fc ?S c = _ |- _ =>
        let K := fresh in
        pose proof (IH S x HC HS (ltac:(fsetdec))) as K; clear IH
    end.
    all: try solve [fsetdec].
    all: intro Hin.
    all: match goal with
    | Hs : ?y `notin` task_support ?S,
      H : ?y `in` fv_tm_tm_tm (task_ft ?S ?x) |- _ =>
      pose proof ((proj1 task_fv_vars) _ _ H) as A;
      pose proof (task_ft_vars S x y Hs A); subst; fsetdec
    end. }
  intros S rho x a HC HS HR. inversion HR; subst; constructor.
  - exact I.
  - eapply (proj1 F); eassumption.
Qed.

Definition task_imp_sub_assum S G H D E :=
  forall c a b A, binds c (Co (Eq a b A)) G -> c `in` D ->
    DefEq H E (task_sub_tm S a) (task_sub_tm S b) (task_sub_tm S A).

Record task_imp_sub_ctx S G H := {
  task_imp_sub_ctx_co_identity : forall c, task_fc S c = g_Var_f c;
  task_imp_sub_ctx_ok : Ctx H;
  task_imp_sub_ctx_var : forall x A, binds x (Tm A) G ->
      Typing H (task_ft S x) (task_sub_tm S A);
  task_imp_sub_ctx_co : task_imp_sub_assum S G H (dom G) (dom H)
}.

Arguments task_imp_sub_ctx_co_identity {S G H}.
Arguments task_imp_sub_ctx_ok {S G H}.
Arguments task_imp_sub_ctx_var {S G H}.
Arguments task_imp_sub_ctx_co {S G H}.

Lemma task_imp_sub_assum_cons : forall S G H D E x s,
  x `notin` D -> Ctx (x ~ task_sub_sort S s ++ H) ->
  task_imp_sub_assum S G H D E ->
  task_imp_sub_assum S (x ~ s ++ G) (x ~ task_sub_sort S s ++ H) D E.
Proof.
  unfold task_imp_sub_assum; intros S G H D E x s Hfresh Hctx HM c a b A Hb Hd.
  apply binds_cons_1 in Hb; destruct Hb as [[-> _]|Hb]; [contradiction|].
  eapply (proj1 (proj2 (proj2 (proj2 task_imp_weaken)))).
  - eapply HM; eassumption.
  - exact Hctx.
  - unfold task_extends; eauto using binds_app_3.
  - unfold AtomSetImpl.Subset; auto.
Qed.

Lemma task_imp_sub_ctx_cons : forall S G H x s,
  x `notin` task_support S -> Ctx (x ~ task_sub_sort S s ++ H) ->
  task_imp_sub_ctx S G H -> task_imp_sub_ctx S (x ~ s ++ G) (x ~ task_sub_sort S s ++ H).
Proof.
  intros S G H x s Hfresh Hctx M.
  constructor.
  - exact (task_imp_sub_ctx_co_identity M).
  - exact Hctx.
  - intros y A Hb. apply binds_cons_1 in Hb.
    destruct Hb as [[-> <-]|Hb].
    + rewrite task_ft_fresh by assumption.
      cbn; apply E_Var; eauto using binds_cons_2.
    + eapply (proj1 (proj2 task_imp_weaken)).
      * exact (task_imp_sub_ctx_var M _ _ Hb).
      * exact Hctx.
      * unfold task_extends; eauto using binds_app_3.
  - unfold task_imp_sub_assum; intros c a b A Hb _.
    apply binds_cons_1 in Hb; destruct Hb as [[-> <-]|Hb].
    + cbn [task_sub_sort task_sub_constraint task_walk_constraint].
      autorewrite with task_sub.
      eapply E_Assn with (c := x); [exact Hctx | apply binds_cons_2; reflexivity | simpl; fsetdec].
    + eapply (proj1 (proj2 (proj2 (proj2 task_imp_weaken)))).
      * exact (task_imp_sub_ctx_co M _ _ _ _ Hb (binds_In _ _ _ _ Hb)).
      * exact Hctx.
      * unfold task_extends; eauto using binds_app_3.
      * simpl; unfold AtomSetImpl.Subset; intros; fsetdec.
Qed.

Lemma task_imp_substitute :
  (forall G p, PropWff G p -> forall S H,
    task_imp_sub_ctx S G H -> PropWff H (task_sub_constraint S p)) /\
  (forall G a A, Typing G a A -> forall S H,
    task_imp_sub_ctx S G H -> Typing H (task_sub_tm S a) (task_sub_tm S A)) /\
  (forall G D p q, Iso G D p q -> forall S H E,
    task_imp_sub_ctx S G H -> task_imp_sub_assum S G H D E ->
    Iso H E (task_sub_constraint S p) (task_sub_constraint S q)) /\
  (forall G D a b A, DefEq G D a b A -> forall S H E,
    task_imp_sub_ctx S G H -> task_imp_sub_assum S G H D E ->
    DefEq H E (task_sub_tm S a) (task_sub_tm S b) (task_sub_tm S A)) /\
  (forall G, Ctx G -> True).
Proof.
  apply task_implicit_ind; intros; try exact I.
  all: try solve [
    match goal with
    | H : task_imp_sub_ctx ?S ?G ?J, HB : binds ?x (Tm ?A) ?G |- _ =>
      exact (task_imp_sub_ctx_var H x A HB)
    | H : task_imp_sub_assum ?S ?G ?J ?D ?E, HB : binds ?c (Co (Eq ?a ?b ?A)) ?G |- _ =>
      exact (H c a b A HB ltac:(assumption))
    end].
  all: task_reduce_sub; task_rewrite_sub_open;
    repeat match goal with
    | M : task_imp_sub_ctx ?S ?G ?H,
      I : forall (S : task_substitution) J, task_imp_sub_ctx S ?G J -> _ |- _ =>
        specialize (I S H M)
    | M : task_imp_sub_ctx ?S ?G ?H,
      I : forall (S : task_substitution) J E, task_imp_sub_ctx S ?G J ->
              task_imp_sub_assum S ?G J (dom ?G) E -> _ |- _ =>
        specialize (I S H (dom H) M (task_imp_sub_ctx_co M))
    | M : task_imp_sub_ctx ?S ?G ?H, MA : task_imp_sub_assum ?S ?G ?H ?D ?E,
      I : forall (S : task_substitution) J E, task_imp_sub_ctx S ?G J ->
              task_imp_sub_assum S ?G J ?D E -> _ |- _ =>
        specialize (I S H E M MA)
    end.
  all: task_reduce_sub.
  all: try solve [first
   [solve [eapply E_Wff; eassumption]
   |solve [eapply E_Star; eauto using task_imp_sub_ctx_ok]
   |solve [eapply E_Conv; eassumption]
   |solve [eapply E_PropCong; eassumption]
   |solve [eapply E_IsoConv; eassumption]
   |solve [eapply E_CPiFst; eassumption]
   |solve [eapply E_Refl; eassumption]
   |solve [eapply E_Sym; eassumption]
   |solve [eapply E_Trans; eassumption]
   |solve [eapply E_Beta; eauto using task_sub_beta]
   |solve [eapply E_PiFst; eassumption]
   |solve [eapply E_Cast; eassumption]
   |solve [eapply E_EqConv; eassumption]
   |solve [eapply E_IsoSnd; eassumption]]].
  all: try solve [
    match goal with
    | |- Typing _ _ (open_tm_wrt_tm_rec 0 _ ?B) =>
        first [solve [eapply E_App with (B := B); eassumption]
              |solve [eapply E_IApp with (B := B); eassumption]]
    | |- Typing _ _ (open_tm_wrt_co_rec 0 _ ?B) =>
        eapply E_CApp with (B1 := B); eassumption
    | |- DefEq _ _ _ _ (open_tm_wrt_tm_rec 0 _ ?B) =>
        first [solve [eapply E_AppCong with (B := B); eassumption]
              |solve [eapply E_IAppCong with (B := B); eassumption]]
    | |- DefEq _ _ _ _ (open_tm_wrt_co_rec 0 _ ?B) =>
        eapply E_CAppCong with (B := B); eassumption
    | |- DefEq _ _ (open_tm_wrt_tm_rec 0 _ ?B) (open_tm_wrt_tm_rec 0 _ ?C) a_Star =>
        eapply E_PiSnd with (B1 := B) (B2 := C); eassumption
    | |- DefEq _ _ (open_tm_wrt_co_rec 0 _ ?B) (open_tm_wrt_co_rec 0 _ ?C) a_Star =>
        eapply E_CPiSnd with (B1 := B) (B2 := C); eassumption
    | HB : binds ?F (Ax ?a ?A) toplevel |- Typing _ (a_Fam ?F) _ =>
        destruct (task_imp_sig_bind F a A HB) as [-> [-> ->]];
        eapply E_Fam with (a := erase_tm FixDef);
          [eauto using task_imp_sub_ctx_ok | exact HB | eassumption]
    end].
  all: try match goal with
   | L : vars, S : task_substitution, M : task_imp_sub_ctx ?S ?G ?H |- _ =>
      let F := constr:(L \u dom H \u task_support S) in
      first [eapply E_Pi with (L := F) | eapply E_Abs with (L := F) |
             eapply E_CPi with (L := F) | eapply E_CAbs with (L := F) |
             let FN := constr:(F \u D) in
             first [eapply E_PiCong with (L := FN)
                   |eapply E_AbsCong with (L := FN)
                   |eapply E_CPiCong with (L := FN)
                   |eapply E_CAbsCong with (L := FN)]];
      try eassumption
  end.
  all: try match goal with |- forall x : atom, x `notin` _ -> _ => intros x Hx; task_rewrite_sub_open end.
  all: try solve [
    match goal with
    | IH : forall (_ : atom), _ -> forall (_ : task_substitution) (_ : context), _,
      S : task_substitution, HF : ?x `notin` _ |- Typing ?J _ _ =>
      let K := constr:(IH x (ltac:(fsetdec)) S J) in
      let TK := type of K in
      lazymatch TK with
      | ?Premise -> _ =>
        let M' := fresh in
        assert (M' : Premise)
          by (eapply task_imp_sub_ctx_cons; [fsetdec | first [apply E_ConsTm | apply E_ConsCo];
                                       eauto using task_imp_sub_ctx_ok; fsetdec | eassumption]);
        let HS := fresh in pose proof (K M') as HS;
        task_rewrite_sub_open; task_reduce_sub;
        try rewrite (task_ft_fresh S x) in HS by fsetdec;
        try rewrite (task_fc_fresh S x) in HS by fsetdec;
        exact HS
      end
    end].
  all: try solve [
    match goal with
    | IH : forall (_ : atom), _ -> forall (_ : task_substitution) (_ : context) (_ : available_props), _,
      S : task_substitution, HF : ?x `notin` _ |- DefEq ?J ?E _ _ _ =>
      let K := constr:(IH x (ltac:(fsetdec)) S J E) in
      let TK := type of K in
      lazymatch TK with
      | ?M -> ?MA -> _ =>
        let M' := fresh in let MA' := fresh in
        assert (M' : M)
          by (eapply task_imp_sub_ctx_cons; [fsetdec | first [apply E_ConsTm | apply E_ConsCo];
                                       eauto using task_imp_sub_ctx_ok; fsetdec | eassumption]);
        assert (MA' : MA) by (eapply task_imp_sub_assum_cons; [fsetdec | exact (task_imp_sub_ctx_ok M') | eassumption]);
        let HS := fresh in pose proof (K M' MA') as HS;
        task_rewrite_sub_open; task_reduce_sub;
        try rewrite (task_ft_fresh S x) in HS by fsetdec;
        try rewrite (task_fc_fresh S x) in HS by fsetdec;
        exact HS
      end
    end].
  all: try solve [
    match goal with
    | R : forall (_ : atom), _ -> _,
      M : task_imp_sub_ctx ?S _ _ |- RhoCheck _ ?x _ =>
      let RF := constr:(R x (ltac:(fsetdec))) in
      let T := type of RF in
      lazymatch T with RhoCheck ?rho ?y ?a =>
        let Q := fresh in
        pose proof (task_sub_rho S rho y a (task_imp_sub_ctx_co_identity M) (ltac:(fsetdec)) RF) as Q;
        rewrite (proj1 task_sub_open_t_rec) in Q;
        change (task_sub_tm S (a_Var_f x)) with (task_ft S x) in Q;
        rewrite (task_ft_fresh S x) in Q by fsetdec; exact Q
      end
    end].
  - eapply E_App with (B := task_sub_tm S B) (A := task_sub_tm S A); eassumption.
  - eapply E_IApp with (B := task_sub_tm S B) (A := task_sub_tm S A) (a := task_sub_tm S a); eassumption.
  - eapply E_AppCong with (B := task_sub_tm S B) (A := task_sub_tm S A); eassumption.
  - eapply E_IAppCong with (B := task_sub_tm S B) (A := task_sub_tm S A) (a := task_sub_tm S a); eassumption.
  - eapply E_CAppCong with (B := task_sub_tm S B) (A := task_sub_tm S A)
        (a := task_sub_tm S a) (b := task_sub_tm S b); eassumption.
Qed.

Lemma task_imp_scope :
  (forall G p, PropWff G p -> task_scope_constraint 0 0 p) /\
  (forall G a A, Typing G a A -> task_scope_tm 0 0 a /\ task_scope_tm 0 0 A) /\
  (forall G D p q, Iso G D p q ->
    task_scope_constraint 0 0 p /\ task_scope_constraint 0 0 q) /\
  (forall G D a b A, DefEq G D a b A ->
    task_scope_tm 0 0 a /\ task_scope_tm 0 0 b /\ task_scope_tm 0 0 A) /\
  (forall G, Ctx G -> forall x s, binds x s G -> task_scope_sort s).
Proof.
  pose proof task_scope_open_t as [ET _].
  pose proof task_scope_open_c as [CT _].
  pose proof task_scope_plug_t as [PT _].
  pose proof task_scope_plug_c as [QT _].
  apply task_implicit_ind; intros;
    unfold open_tm_wrt_tm, open_tm_wrt_co in *.
  all: try match goal with
    | H : forall x : atom, x `notin` ?L -> _ |- _ =>
      task_choose_fresh L ltac:(fun x Hx =>
        repeat match goal with
        | H' : forall y : atom, y `notin` L -> _ |- _ => specialize (H' x Hx)
        end)
    end.
  all: repeat match goal with
    | HS : forall x s, binds x s ?G -> task_scope_sort s,
      HB : binds ?x ?s ?G |- _ =>
       let HW := fresh in pose proof (HS x s HB) as HW; clear HB
    end.
  all: cbn in *; task_break_and; task_split_and; auto.
  all: try solve [
     match goal with x : atom |- _ =>
       first [apply (proj1 (ET _ 0 0 x))
             |apply (proj1 (CT _ 0 0 x))];
       eassumption
     end].
  all: try solve [eapply PT; [eassumption | eassumption] |
                  eapply QT; [exact I | eassumption]].
  all: try match goal with
    | H : binds ?F (Ax ?a ?A) toplevel |- _ =>
      destruct (task_imp_sig_bind F a A H) as [-> [-> ->]]; cbn; tauto
    end.
  all: try contradiction.
  all: try solve [
    match goal with H : binds _ _ _ |- _ =>
      apply binds_cons_1 in H; destruct H as [Heq | Hb];
         [destruct Heq; subst; cbn; auto | eauto]
    end].
  all: match goal with H : _ \/ _ |- _ => destruct H as [Heq | Hb]; [inversion Heq; subst; simpl; auto | eauto] end.
Qed.

Lemma task_imp_ctx_of :
  (forall G p, PropWff G p -> Ctx G) /\
  (forall G a A, Typing G a A -> Ctx G) /\
  (forall G D p q, Iso G D p q -> Ctx G) /\
  (forall G D a b A, DefEq G D a b A -> Ctx G) /\
  (forall G, Ctx G -> True).
Proof. apply task_implicit_ind; intros; auto. Qed.

Lemma task_imp_bound_type : forall G x s,
  Ctx G -> binds x s G ->
  match s with Tm A => Typing G A a_Star | Co p => PropWff G p end.
Proof.
  intros G x s HCtx; induction HCtx; intro HB; simpl in HB; try contradiction.
  all: destruct HB as [Q | HB]; [inversion Q; subst; clear Q | specialize (IHHCtx HB)].
  all: match goal with |- context [match ?s with Tm _ => _ | Co _ => _ end] =>
    destruct s | |- _ => idtac end.
  all: first [eapply (proj1 task_imp_weaken) | eapply (proj1 (proj2 task_imp_weaken))];
      [eassumption | eauto using E_ConsCo, E_ConsTm | unfold task_extends; eauto using binds_app_3].
Qed.

Lemma task_pi_body : forall G rho A B T,
  Typing G (a_Pi rho A B) T ->
  exists L, (forall x, x `notin` L -> Typing (x ~ Tm A ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star).
Proof.
  intros G rho A B T H.
  remember (a_Pi rho A B) as t eqn:Eq.
  induction H; inversion Eq; subst; eauto.
Qed.

Lemma task_cpi_body : forall G p B T,
  Typing G (a_CPi p B) T ->
  exists L, (forall x, x `notin` L -> Typing (x ~ Co p ++ G) (open_tm_wrt_co B (g_Var_f x)) a_Star).
Proof.
  intros G p B T H.
  remember (a_CPi p B) as t eqn:Eq.
  induction H; inversion Eq; subst; eauto.
Qed.

Lemma task_imp_single_t_ctx : forall G x u U Hu,
  x `notin` dom G -> x `notin` task_vars_context G ->
  x `notin` task_vars_tm U -> Ctx G -> Typing G u U ->
  task_imp_sub_ctx (task_single_t x u Hu) (x ~ Tm U ++ G) G.
Proof.
  intros G x u U Hu Hx Hfv HU HC HT.
  constructor; [reflexivity | exact HC | |].
  - intros y R Hb; apply binds_cons_1 in Hb; destruct Hb as [[-> Q]|Hb].
    + inversion Q; subst; clear Q.
      rewrite (proj1 task_single_t_inert) by exact HU.
      cbn; destruct (Atom.eq_dec x x); congruence.
    + rewrite (proj1 task_single_t_inert)
        by (pose proof (task_vars_binds _ _ _ Hb) as K; intro Hin; apply Hfv; eapply K; exact Hin).
      cbn; destruct (Atom.eq_dec y x) as [->|Hneq].
      * exfalso; apply Hx; eapply binds_In; eassumption.
      * now apply E_Var.
  - unfold task_imp_sub_assum; intros c a b A Hb _.
    apply binds_cons_1 in Hb; destruct Hb as [[? Hbad]|Hb]; try discriminate.
    pose proof (task_vars_binds _ _ _ Hb) as K.
    assert (HF : x `notin` task_vars_constraint (Eq a b A)) by
     (intro Hin; apply Hfv; eapply K; exact Hin).
    cbn in HF; rewrite !(proj1 task_single_t_inert) by fsetdec.
    eapply E_Assn; [exact HC|exact Hb|eapply binds_In; exact Hb].
Qed.

Definition task_identity_sub : task_substitution.
Proof.
  refine {| task_ft := a_Var_f; task_fc := g_Var_f; task_support := empty |};
    simpl; intros; try exact I; try reflexivity; fsetdec.
Defined.

Lemma task_sub_identity :
  (forall a, task_sub_tm task_identity_sub a = a) /\
  (forall a, task_sub_brs task_identity_sub a = a) /\
  (forall a, task_sub_co task_identity_sub a = a) /\
  (forall a, task_sub_constraint task_identity_sub a = a).
Proof.
  task_structure; intros; cbn;
  repeat first [rewrite (task_sub_tm_walk task_identity_sub)
               |rewrite (task_sub_brs_walk task_identity_sub)
               |rewrite (task_sub_co_walk task_identity_sub)
               |rewrite (task_sub_constraint_walk task_identity_sub)];
  try reflexivity; f_equal; auto.
Qed.

Lemma task_imp_single_c_ctx : forall G x a b A,
  Ctx G -> DefEq G (dom G) a b A ->
  task_imp_sub_ctx task_identity_sub (x ~ Co (Eq a b A) ++ G) G.
Proof.
  intros G x a b A HC HG.
  constructor; [reflexivity | exact HC | | ].
  - intros y R Hb; apply binds_cons_1 in Hb; destruct Hb as [[? Hbad]|Hb]; try discriminate.
    rewrite (proj1 task_sub_identity); now apply E_Var.
  - unfold task_imp_sub_assum; intros y a1 b1 A1 Hb _.
    rewrite !(proj1 task_sub_identity).
    apply binds_cons_1 in Hb; destruct Hb as [[-> Heq]|Hb].
    + inversion Heq; subst; exact HG.
    + eapply E_Assn; [exact HC|exact Hb|eapply binds_In; exact Hb].
Qed.

Lemma task_imp_instantiate_t : forall G L A B u,
  Typing G u A ->
  (forall x, x `notin` L -> Typing (x ~ Tm A ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star) ->
  Typing G (open_tm_wrt_tm B u) a_Star.
Proof.
  intros G L A B u Htyped Hbody.
  pose proof (proj1 (proj2 task_imp_scope) _ _ _ Htyped) as [Hu _].
  pose proof (proj1 (proj2 task_imp_ctx_of) _ _ _ Htyped) as HG.
  task_choose_fresh (L \u dom G \u task_vars_context G \u task_vars_tm A \u task_vars_tm B)
    ltac:(fun x Hx =>
      pose proof (task_imp_single_t_ctx G x u A Hu (ltac:(fsetdec))
         (ltac:(fsetdec)) (ltac:(fsetdec)) HG Htyped) as M;
      specialize (Hbody x (ltac:(fsetdec)));
      pose proof (proj1 (proj2 task_imp_substitute) _ _ _ Hbody _ _ M) as K;
      unfold open_tm_wrt_tm in *;
      rewrite (proj1 task_sub_open_t_rec) in K;
      rewrite (proj1 task_single_t_inert B x u Hu) in K by fsetdec;
      change (task_sub_tm (task_single_t x u Hu) (a_Var_f x)) with
             (if Atom.eq_dec x x then u else a_Var_f x) in K;
      destruct (Atom.eq_dec x x); [exact K|contradiction]).
Qed.

Lemma task_imp_instantiate_c : forall G L a b A B,
  erase_tm B = B ->
  DefEq G (dom G) a b A ->
  (forall c, c `notin` L ->
      Typing (c ~ Co (Eq a b A) ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star) ->
  Typing G (open_tm_wrt_co B g_Triv) a_Star.
Proof.
  intros G L a b A B Hcan Htyped Hbody.
  pose proof (proj1 (proj2 (proj2 (proj2 task_imp_ctx_of))) _ _ _ _ _ Htyped) as HG.
  task_choose_fresh L ltac:(fun c Hc =>
      pose proof (task_imp_single_c_ctx G c a b A HG Htyped) as M;
      specialize (Hbody c Hc);
      pose proof (proj1 (proj2 task_imp_substitute) _ _ _ Hbody _ _ M) as K;
      rewrite !(proj1 task_sub_identity) in K;
      pose proof (proj1 (proj1 (proj2 task_implicit_canonical) _ _ _ Hbody)) as HB;
      rewrite (task_erase_open_co B (g_Var_f c) g_Triv), Hcan in HB;
      rewrite HB; exact K).
Qed.

Lemma task_imp_type : forall G a A, Typing G a A -> Typing G A a_Star.
Proof.
  apply (task_typing_ind
    (fun _ _ _ => True)
    (fun G _ A _ => Typing G A a_Star)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ => True)
    (fun _ _ => True)); intros; try exact I; try assumption.
  - now apply E_Star.
  - eapply task_imp_bound_type with (s := Tm A); eassumption.
  - eapply E_Pi with (L := L); eauto.
  - match goal with P : Typing _ (a_Pi _ _ _) _ |- _ =>
      destruct (task_pi_body _ _ _ _ _ P) as [L Q]
    end; eapply task_imp_instantiate_t; eassumption.
  - match goal with P : Typing _ (a_Pi _ _ _) _ |- _ =>
      destruct (task_pi_body _ _ _ _ _ P) as [L Q]
    end; eapply task_imp_instantiate_t; eassumption.
  - apply E_Star; eapply (proj1 task_imp_ctx_of); eassumption.
  - eapply E_CPi with (L := L); eauto.
  - destruct (task_cpi_body _ _ _ _ H) as [L Q].
    pose proof (proj1 (proj1 (proj2 task_implicit_canonical) _ _ _ H)) as C.
    cbn [erase_tm erase_constraint] in C.
    apply task_imp_instantiate_c with (L := L) (a := a) (b := b) (A := A) (B := B1).
    + congruence.
    + exact d.
    + exact Q.
  - eapply (proj1 (proj2 task_imp_weaken)); [eassumption | eassumption | unfold task_extends; intros x s Hb; inversion Hb].
Qed.
Lemma task_open_close_t :
  (forall s i j x y, open_tm_wrt_tm_rec i (a_Var_f y) (task_walk_tm (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j s) = task_sub_tm (task_single_t x (a_Var_f y) I) s) /\
  (forall s i j x y, open_brs_wrt_tm_rec i (a_Var_f y) (task_walk_brs (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j s) = task_sub_brs (task_single_t x (a_Var_f y) I) s) /\
  (forall s i j x y, open_co_wrt_tm_rec i (a_Var_f y) (task_walk_co (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j s) = task_sub_co (task_single_t x (a_Var_f y) I) s) /\
  (forall s i j x y, open_constraint_wrt_tm_rec i (a_Var_f y) (task_walk_constraint (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j s) = task_sub_constraint (task_single_t x (a_Var_f y) I) s).
Proof.
  task_structure; intros; cbn -[lt_eq_lt_dec]; autorewrite with task_sub;
  repeat first
    [rewrite (task_sub_tm_walk (task_single_t x (a_Var_f y) I))
    |rewrite (task_sub_brs_walk (task_single_t x (a_Var_f y) I))
    |rewrite (task_sub_co_walk (task_single_t x (a_Var_f y) I))
    |rewrite (task_sub_constraint_walk (task_single_t x (a_Var_f y) I))];
  try solve [reflexivity | f_equal; eauto];
  unfold task_close_t_free, task_close_t_bound;
  repeat match goal with
  | |- context [Atom.eq_dec ?y ?x] => destruct (Atom.eq_dec y x); try subst
  | |- context [lt_dec ?n ?k] => destruct (lt_dec n k)
  end;
  cbn -[lt_eq_lt_dec];
  repeat match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try reflexivity
  end;
  try reflexivity; try solve [exfalso; lia | unfold task_id_bt, task_id_bc; f_equal; lia].
Qed.

Lemma task_erase_close_t :
  (forall t i j x, erase_tm (task_walk_tm (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j t) =
                  task_walk_tm (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j (erase_tm t)) /\
  (forall s : brs, True) /\ (forall g : co, True) /\
  (forall p i j x, erase_constraint (task_walk_constraint (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j p) =
                  task_walk_constraint (task_close_t_free x) task_id_fc task_close_t_bound task_id_bc i j (erase_constraint p)).
Proof.
  task_structure; intros; try exact I;
  try match goal with r : relflag |- _ => destruct r end; cbn;
  try solve [reflexivity | f_equal; eauto];
  unfold task_close_t_free, task_close_t_bound;
  repeat match goal with
  | |- context [Atom.eq_dec ?y ?x] => destruct (Atom.eq_dec y x); try subst
  | |- context [lt_dec ?n ?k] => destruct (lt_dec n k)
  end; reflexivity.
Qed.

Lemma task_open_close_c :
  (forall s i j x y, open_tm_wrt_co_rec j (g_Var_f y) (task_walk_tm task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j s) = task_sub_tm (task_single_c x (g_Var_f y) I) s) /\
  (forall s i j x y, open_brs_wrt_co_rec j (g_Var_f y) (task_walk_brs task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j s) = task_sub_brs (task_single_c x (g_Var_f y) I) s) /\
  (forall s i j x y, open_co_wrt_co_rec j (g_Var_f y) (task_walk_co task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j s) = task_sub_co (task_single_c x (g_Var_f y) I) s) /\
  (forall s i j x y, open_constraint_wrt_co_rec j (g_Var_f y) (task_walk_constraint task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j s) = task_sub_constraint (task_single_c x (g_Var_f y) I) s).
Proof.
  task_structure; intros; cbn -[lt_eq_lt_dec]; autorewrite with task_sub;
  repeat first
    [rewrite (task_sub_tm_walk (task_single_c x (g_Var_f y) I))
    |rewrite (task_sub_brs_walk (task_single_c x (g_Var_f y) I))
    |rewrite (task_sub_co_walk (task_single_c x (g_Var_f y) I))
    |rewrite (task_sub_constraint_walk (task_single_c x (g_Var_f y) I))];
  try solve [reflexivity | f_equal; eauto];
  unfold task_close_c_free, task_close_c_bound;
  repeat match goal with
  | |- context [Atom.eq_dec ?y ?x] => destruct (Atom.eq_dec y x); try subst
  | |- context [lt_dec ?n ?k] => destruct (lt_dec n k)
  end;
  cbn -[lt_eq_lt_dec];
  repeat match goal with |- context [lt_eq_lt_dec ?n ?k] =>
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try reflexivity
  end;
  try reflexivity; try solve [exfalso; lia | unfold task_id_bt, task_id_bc; f_equal; lia].
Qed.

Lemma task_erase_close_c :
  (forall t i j x, erase_tm (task_walk_tm task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j t) =
                  task_walk_tm task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j (erase_tm t)) /\
  (forall s : brs, True) /\ (forall g : co, True) /\
  (forall p i j x, erase_constraint (task_walk_constraint task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j p) =
                  task_walk_constraint task_id_ft (task_close_c_free x) task_id_bt task_close_c_bound i j (erase_constraint p)).
Proof.
  task_structure; intros; try exact I;
  try match goal with r : relflag |- _ => destruct r end; cbn;
  try solve [reflexivity | f_equal; eauto];
  unfold task_close_c_free, task_close_c_bound;
  repeat match goal with
  | |- context [Atom.eq_dec ?y ?x] => destruct (Atom.eq_dec y x); try subst
  | |- context [lt_dec ?n ?k] => destruct (lt_dec n k)
  end; reflexivity.
Qed.


Lemma task_ann_identity_ctx : forall G,
  AnnCtx G -> task_sub_ctx task_identity_sub G G.
Proof.
  intros G HC; constructor; [exact HC| |].
  - intros x A Hb; rewrite (proj1 task_sub_identity); now apply An_Var.
  - unfold task_sub_assum; intros c a b A Hb HD.
    rewrite !(proj1 task_sub_identity); eapply An_Assn; eassumption.
Qed.

Lemma task_ann_eq_full : forall G D g a b,
  AnnDefEq G D g a b -> AnnDefEq G (dom G) g a b.
Proof.
  intros G D g a b HQ.
  pose proof (proj1 (proj2 (proj2 (proj2 task_ann_ctx_of))) _ _ _ _ _ HQ) as HG.
  pose proof (task_ann_identity_ctx G HG) as M.
  assert (MA : task_sub_assum task_identity_sub G G D (dom G)).
  { unfold task_sub_assum; intros c a0 b0 A Hb HD.
    rewrite !(proj1 task_sub_identity).
    eapply An_Assn; [exact HG|exact Hb|eapply binds_In; exact Hb]. }
  pose proof (proj1 (proj2 (proj2 (proj2 task_ann_substitute))) _ _ _ _ _ HQ
    task_identity_sub G (dom G) M MA) as K.
  rewrite !(proj1 task_sub_identity), (proj1 (proj2 (proj2 task_sub_identity))) in K.
  exact K.
Qed.

Lemma task_ann_reclose_t : forall G x U a A,
  x `notin` dom G -> x `notin` task_vars_context G -> x `notin` task_vars_tm U ->
  AnnTyping G U a_Star ->
  AnnTyping (x ~ Tm U ++ G) a A ->
  forall y, y `notin` dom G ->
    AnnTyping (y ~ Tm U ++ G) (open_tm_wrt_tm (task_close_t_tm x a) (a_Var_f y))
                            (open_tm_wrt_tm (task_close_t_tm x A) (a_Var_f y)).
Proof.
  intros G x U a A Xd Xv Xu HU HA y Yd.
  assert (HG : AnnCtx G) by (eapply (proj1 (proj2 task_ann_ctx_of)); eassumption).
  assert (HY : AnnCtx (y ~ Tm U ++ G)) by (apply An_ConsTm; assumption).
  assert (HV : AnnTyping (y ~ Tm U ++ G) (a_Var_f y) U)
    by (apply An_Var; [exact HY | apply binds_cons_2; reflexivity]).
  pose proof (task_single_t_for_ctx G _ x (a_Var_f y) U I Xd Xv Xu HY
              (ltac:(unfold task_extends; eauto using binds_app_3)) HV) as M.
  unfold task_close_t_tm, open_tm_wrt_tm.
  rewrite !(proj1 task_open_close_t).
  exact (proj1 (proj2 task_ann_substitute) _ _ _ HA _ _ M).
Qed.

Lemma task_ann_reclose_abstraction : forall G L x U rho a T,
  x `notin` dom G -> x `notin` task_vars_context G ->
  x `notin` task_vars_tm U -> x `notin` task_vars_tm a ->
  AnnTyping G U a_Star ->
  AnnTyping (x ~ Tm U ++ G) (open_tm_wrt_tm a (a_Var_f x)) T ->
  (forall y, y `notin` L -> RhoCheck rho y (erase_tm (open_tm_wrt_tm a (a_Var_f y)))) ->
  AnnTyping G (a_Abs rho U a) (a_Pi rho U (task_close_t_tm x T)).
Proof.
  intros G L x U rho a T XD XV XU XA HU HT HR.
  eapply An_Abs with (L := L \u dom G); [exact HU| | eauto].
  - intros y HY.
    pose proof (task_ann_reclose_t _ _ _ _ _ XD XV XU HU HT y (ltac:(fsetdec))) as Q.
    unfold task_close_t_tm, open_tm_wrt_tm in Q.
    rewrite (proj1 task_close_open_t) in Q by assumption.
    exact Q.
Qed.

Lemma task_ann_abs_endpoints : forall G D L rho g1 A1 A2 b1 b2 b3 B,
  AnnDefEq G D g1 A1 A2 ->
  AnnTyping G A1 a_Star ->
  AnnTyping G A2 a_Star ->
  AnnTyping G (a_Abs rho A1 b2) B ->
  (forall x, x `notin` L -> exists T,
    AnnTyping (x ~ Tm A1 ++ G) (open_tm_wrt_tm b1 (a_Var_f x)) T) ->
  (forall x, x `notin` L -> open_tm_wrt_tm b3 (a_Var_f x) =
     open_tm_wrt_tm b2 (a_Conv (a_Var_f x) (g_Sym g1))) ->
  (forall x, x `notin` L -> RhoCheck rho x (erase_tm (open_tm_wrt_tm b1 (a_Var_f x)))) ->
  (forall x, x `notin` L -> RhoCheck rho x (erase_tm (open_tm_wrt_tm b3 (a_Var_f x)))) ->
  exists T U, AnnTyping G (a_Abs rho A1 b1) T /\ AnnTyping G (a_Abs rho A2 b3) U.
Proof.
  intros G D L rho g1 A1 A2 b1 b2 b3 B HG H1 H2 HB HD HE HR1 HR3.
  inversion HB as [| | | Lb Gb rb Ab ab Bb HF HBody Rb | | | | | | ]; subst; clear HB.
  assert (HC : AnnCtx G) by (eapply (proj1 (proj2 task_ann_ctx_of)); eassumption).
  assert (HS : AnnDefEq G (dom G) (g_Sym g1) A2 A1).
  { eapply An_Sym with (B := a_Star) (A := a_Star) (g1 := g_Refl a_Star);
      eauto using An_Refl, An_Star, task_ann_eq_full. }
  task_choose_fresh (L \u Lb \u dom G \u task_vars_context G \u task_vars_tm A1 \u
     task_vars_tm A2 \u task_vars_tm b1 \u task_vars_tm b2 \u task_vars_tm b3)
    ltac:(fun x X =>
      destruct (HD x (ltac:(fsetdec))) as [T HT];
      assert (HX : AnnCtx (x ~ Tm A2 ++ G)) by (apply An_ConsTm; [exact HC|exact H2|fsetdec]);
      assert (HXV : AnnTyping (x ~ Tm A2 ++ G) (a_Var_f x) A2)
        by (apply An_Var; [exact HX | apply binds_cons_2; reflexivity]);
      assert (HX1 : AnnTyping (x ~ Tm A2 ++ G) A1 a_Star)
        by (eapply (proj1 (proj2 task_ann_weaken)); [exact H1|exact HX|unfold task_extends; eauto using binds_app_3]);
      assert (HXG : AnnDefEq (x ~ Tm A2 ++ G) (dom (x ~ Tm A2 ++ G)) (g_Sym g1) A2 A1)
        by (eapply (proj1 (proj2 (proj2 (proj2 task_ann_weaken))));
            [exact HS|exact HX|unfold task_extends; eauto using binds_app_3|simpl; unfold AtomSetImpl.Subset; intros; fsetdec]);
      assert (HXCV : AnnTyping (x ~ Tm A2 ++ G) (a_Conv (a_Var_f x) (g_Sym g1)) A1)
        by (eapply An_Conv; eassumption);
      pose proof (proj1 (proj2 task_ann_scope) _ _ _ HXCV) as [HSC _];
      pose proof (task_single_t_for_ctx G _ x _ A1 HSC (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec))
                  HX (ltac:(unfold task_extends; eauto using binds_app_3)) HXCV) as M;
      specialize (HBody x (ltac:(fsetdec)));
      specialize (HE x (ltac:(fsetdec)));
      pose proof (proj1 (proj2 task_ann_substitute) _ _ _ HBody _ _ M) as K;
      unfold open_tm_wrt_tm in K, HE;
      rewrite (proj1 task_sub_open_t_rec) in K;
      rewrite (proj1 task_single_t_inert b2) in K by fsetdec;
      change (task_sub_tm (task_single_t x (a_Conv (a_Var_f x) (g_Sym g1)) HSC) (a_Var_f x))
        with (if Atom.eq_dec x x then a_Conv (a_Var_f x) (g_Sym g1) else a_Var_f x) in K;
      destruct (Atom.eq_dec x x); [|contradiction];
      rewrite <- HE in K;
      let TK := type of K in
      lazymatch TK with AnnTyping _ _ ?U =>
        exists (a_Pi rho A1 (task_close_t_tm x T)), (a_Pi rho A2 (task_close_t_tm x U));
        split; eapply task_ann_reclose_abstraction with (L := L) (x := x);
          try eassumption; fsetdec
      end).
  Unshelve.
  all: exact D.
Qed.

Lemma task_ann_regular :
  (forall G p, AnnPropWff G p -> True) /\
  (forall G a A, AnnTyping G a A -> True) /\
  (forall G D g p q, AnnIso G D g p q -> AnnPropWff G p /\ AnnPropWff G q) /\
  (forall G D g a b, AnnDefEq G D g a b -> exists A B, AnnTyping G a A /\ AnnTyping G b B) /\
  (forall G, AnnCtx G -> True) /\ (forall S, AnnSig S -> True).
Proof.
  apply task_ann_ind; intros; try exact I.
  all: repeat match goal with H : exists A B, _ |- _ => destruct H as [? [? [? ?]]] end.
  all: task_break_and.
  all: try solve [eexists; eexists; split; eassumption | split; eassumption].
  all: try match goal with
  | HB : binds ?c (Co ?p) ?G, HC : AnnCtx ?G |- _ =>
      let HW := fresh in pose proof (task_bound_type G c (Co p) HC HB) as HW
  end.
  all: repeat match goal with
  | H : AnnTyping _ (a_Pi _ _ _) _ |- _ => inversion H; subst; clear H
  | H : AnnTyping _ (a_CPi _ _) _ |- _ => inversion H; subst; clear H
  | H : AnnPropWff _ (Eq _ _ _) |- _ => inversion H; subst; clear H
  end.
  all: try solve [eexists; eexists; split; eassumption | split; eassumption].
  all: try solve [
      eapply task_ann_abs_endpoints; try eassumption;
      intros x Hx; eauto].
  all: try solve [
     exists a_Star, a_Star; split;
     eauto using task_ann_instantiate_t, task_ann_instantiate_c, task_ann_type].
  - cbn in H0; inversion H0; subst; eexists; eexists; split; eassumption.
  - eapply task_ann_abs_endpoints with (L := L) (D := D) (b2 := b2) (B := B) (g1 := g1);
      try eassumption.
    intros y Hy; destruct (H0 y Hy) as [T [U [HT HU]]]; eauto.
Qed.

Lemma task_imp_iso_sym : forall G D p q, Iso G D p q -> Iso G D q p.
Proof. destruct 1; eauto using E_PropCong, E_IsoConv, E_CPiFst, E_Sym. Qed.

Lemma task_imp_pi_domain : forall G rho A B T,
  Typing G (a_Pi rho A B) T -> Typing G A a_Star.
Proof.
  intros G rho A B T H.
  remember (a_Pi rho A B) as t eqn:Eq.
  induction H; inversion Eq; subst; eauto.
Qed.

Lemma task_imp_cpi_domain : forall G p B T,
  Typing G (a_CPi p B) T -> PropWff G p.
Proof.
  intros G p B T H.
  remember (a_CPi p B) as t eqn:Eq.
  induction H; inversion Eq; subst; eauto.
Qed.

Section TaskEraseProof.
Hypothesis local_task_imp_type : forall G a A, Typing G a A -> Typing G A a_Star.
Hypothesis local_task_typing_unique : forall G a A B,
  AnnTyping G a A -> AnnTyping G a B -> A = B.
Hypothesis local_task_ann_type : forall G a A,
  AnnTyping G a A -> AnnTyping G A a_Star.
Hypothesis local_task_ann_iso_wff : forall G D g p q,
  AnnIso G D g p q -> AnnPropWff G p /\ AnnPropWff G q.
Hypothesis local_task_ann_eq_typing : forall G D g a b,
  AnnDefEq G D g a b -> exists A B, AnnTyping G a A /\ AnnTyping G b B.
Hypothesis local_task_an_binding_co : forall G x p,
  AnnCtx G -> binds x (Co p) G -> AnnPropWff G p.
Hypothesis local_task_ann_eq_unique : forall G D E g a b a' b',
  AnnDefEq G D g a b -> AnnDefEq G E g a' b' -> a = a' /\ b = b'.

Ltac task_use_unique :=
  repeat match goal with
  | H1 : AnnTyping ?G ?a ?T, H2 : AnnTyping ?G ?a ?U |- _ =>
    tryif constr_eq T U then fail else
      let Eq := fresh "Eq" in
      pose proof (local_task_typing_unique _ _ _ _ H1 H2) as Eq;
      try (inversion Eq; subst); try clear Eq; clear H2
  end.

(* Keep the typing of the original argument when an application erases
   its irrelevant argument to a_Bullet. *)
Definition task_implicit_argument G t :=
  forall f r u V B, t = a_App f r u ->
  AnnTyping G f (a_Pi r V B) -> Typing (erase_context G) (erase_tm u) (erase_tm V).

Lemma task_erase_core :
  (forall G p, AnnPropWff G p -> PropWff (erase_context G) (erase_constraint p)) /\
  (forall G a A, AnnTyping G a A ->
    Typing (erase_context G) (erase_tm a) (erase_tm A) /\ task_implicit_argument G a) /\
  (forall G D g p q, AnnIso G D g p q ->
    Iso (erase_context G) D (erase_constraint p) (erase_constraint q)) /\
  (forall G D g a b, AnnDefEq G D g a b -> forall A, AnnTyping G a A ->
    DefEq (erase_context G) D (erase_tm a) (erase_tm b) (erase_tm A)) /\
  (forall G, AnnCtx G -> Ctx (erase_context G)) /\
  (forall S, AnnSig S -> True).
Proof.
  apply task_ann_ind; intros; try exact I.
  all: repeat match goal with H : Typing _ _ _ /\ _ |- _ =>
    let HT := fresh "Harg" in destruct H as [H HT]
  end.
  all: try match goal with |- Typing _ _ _ /\ task_implicit_argument _ _ =>
    split; [idtac | unfold task_implicit_argument; let HE := fresh in intros ? ? ? ? ? HE ?;
                    inversion HE; subst; task_use_unique; assumption]
  end.
  all: cbn [erase_sort erase_tm erase_constraint] in *;
    rewrite ?task_dom_erase, ?task_erase_open_tm in *.
  - match goal with 
    | HW : AnnTyping ?G ?a ?A, IH : Typing (erase_context ?G) (erase_tm ?b) (erase_tm ?B),
          E : erase_tm ?A = erase_tm ?B |- _ =>
      apply E_Wff; [assumption | rewrite E; exact IH | eauto using local_task_imp_type]
    end.
  - now apply E_Star.

  - match goal with
    | H : binds ?x (Tm ?A) ?G |- _ =>
      eapply E_Var; [assumption | exact (task_binds_erase G x (Tm A) H)]
    end.
  - eapply E_Pi with (L := L); [|assumption].
    intros x Hx.
    pose proof (proj1 (H x Hx)) as K; rewrite task_erase_open_tm in K; exact K.
  - eapply E_Abs with (L := L); [|assumption|].
    + intros x Hx.
      match goal with IH : forall x, x `notin` L -> Typing _ _ _ /\ _ |- _ =>
        pose proof (proj1 (IH x Hx)) as K; rewrite !task_erase_open_tm in K; exact K
      end.
    + intros x Hx.
      match goal with R : forall x, x `notin` L -> RhoCheck _ _ _ |- _ =>
        specialize (R x Hx); rewrite task_erase_open_tm in R; exact R
      end.
  - destruct rho; eauto using E_App, E_IApp.
  - eapply E_Conv with (A := erase_tm A); [eassumption| |eassumption].
    rewrite task_dom_erase; apply (H0 a_Star); eauto using local_task_ann_type.
  - eapply E_CPi with (L := L); [|assumption].
    intros c Hc.
    match goal with
    | IH : forall c, c `notin` L -> Typing _ _ _ /\ _ |- _ =>
      pose proof (proj1 (IH c Hc)) as K; rewrite (task_erase_open_co _ _ (g_Var_f c)) in K; exact K
    end.
  - eapply E_CAbs with (L := L); [|assumption].
    intros c Hc.
    match goal with
    | IH : forall c, c `notin` L -> Typing _ _ _ /\ _ |- _ =>
      pose proof (proj1 (IH c Hc)) as K; rewrite !(task_erase_open_co _ _ (g_Var_f c)) in K; exact K
    end.
  - rewrite (task_erase_open_co _ _ g_Triv).
    pose proof (local_task_ann_type _ _ _ a0) as TP; inversion TP; subst;
      match goal with W : AnnPropWff _ _ |- _ => inversion W; subst end.
    eapply E_CApp with (a := erase_tm a) (b := erase_tm b) (A := erase_tm A1).
    + exact H.
    + rewrite task_dom_erase; apply (H0 A1); assumption.
  - eapply E_Fam with (a := erase_tm a); [eassumption| |eassumption].
    unfold toplevel, erase_sig; exact (binds_map _ _ erase_csort F (Ax a A) an_toplevel b).
  - repeat match goal with W : AnnPropWff _ (Eq _ _ _) |- _ => inversion W; clear W; subst end.
    apply E_PropCong; eauto.
    match goal with
    | E : erase_tm A = _ |- _ => rewrite E
    end; eauto.
  - match goal with
    | Q : AnnDefEq ?G ?D ?g (a_CPi ?p ?B) (a_CPi ?q ?C) |- _ =>
      destruct (local_task_ann_eq_typing _ _ _ _ _ Q) as [U [V [TU TV]]];
      inversion TU; subst;
      eapply E_CPiFst with (B1 := erase_tm B) (B2 := erase_tm C)
    end; apply (H a_Star); assumption.
  - eauto using task_imp_iso_sym.
  - repeat match goal with W : AnnPropWff _ (Eq _ _ _) |- _ => inversion W; clear W; subst end.
    rewrite <- e, <- e0 in *.
    apply E_IsoConv; [apply (H a_Star); eauto using local_task_ann_type | exact H0 | exact H1].
  - match goal with
    | HB : binds ?c (Co (Eq ?a ?b ?T)) ?G,
      HC : AnnCtx ?G, HT : AnnTyping ?G ?a ?U |- _ =>
      pose proof (local_task_an_binding_co G c (Eq a b T) HC HB) as W;
      inversion W; subst;
      task_use_unique;
      eapply E_Assn with (c := c); [eassumption | exact (task_binds_erase _ _ _ HB) | assumption]
    end.
  - task_use_unique; eauto using E_Refl.
  - task_use_unique; rewrite <- e; eauto using E_Refl.
  - task_use_unique.
    eapply E_EqConv with (A := erase_tm B).
    + apply E_Sym, (H2 B); assumption.
    + rewrite task_dom_erase; apply (H1 a_Star); eauto using local_task_ann_type.
  - task_use_unique.
    eapply E_Trans with (a1 := erase_tm a1).
    + match goal with |- DefEq _ _ _ _ (erase_tm ?T) => apply (H T); assumption end.
    + eapply E_EqConv with (A := erase_tm A1).
      * apply (H0 A1); assumption.
      * rewrite task_dom_erase; apply E_Sym, (H3 a_Star); eauto using local_task_ann_type.
  - task_use_unique; rewrite <- e in H0; eauto using E_Beta.
  - match goal with T : AnnTyping _ (a_Pi _ _ _) _ |- _ => inversion T; subst; clear T end.
    eapply E_PiCong with (L := L \u L0); [apply (H a_Star); assumption | | eauto using task_imp_pi_domain | eassumption | eassumption].
    intros x Hx.
      match goal with
      | IH : forall x, x `notin` L -> forall T, AnnTyping _ _ T -> DefEq _ _ _ _ _ |- _ =>
        specialize (IH x (ltac:(fsetdec)) a_Star);
        rewrite !task_erase_open_tm in IH;
        match goal with
        | E : forall x, x `notin` L -> open_tm_wrt_tm B3 (a_Var_f x) = _ |- _ =>
          specialize (E x (ltac:(fsetdec)));
          apply (f_equal erase_tm) in E;
          rewrite !task_erase_open_tm in E;
          simpl in E; rewrite E; apply IH; eauto; fsetdec
        end
      end.
  - match goal with T : AnnTyping _ (a_Abs _ _ _) _ |- _ => inversion T; subst end.
    eapply E_AbsCong with (L := L \u L0).
    + intros x Hx.
      match goal with
      | IH : forall x, x `notin` L -> forall T, AnnTyping _ _ T -> DefEq _ _ _ _ _ |- _ =>
        let K := fresh in
        pose proof (IH x (ltac:(fsetdec)) _ (ltac:(eauto; fsetdec))) as K;
        rewrite !task_erase_open_tm in K;
        match goal with
        | E : forall x, x `notin` L -> open_tm_wrt_tm b3 (a_Var_f x) = _ |- _ =>
          specialize (E x (ltac:(fsetdec)));
          apply (f_equal erase_tm) in E;
          rewrite !task_erase_open_tm in E;
          simpl in E; rewrite E; exact K
        end
      end.
    + eassumption.
    + intros x Hx; specialize (r x (ltac:(fsetdec))); rewrite task_erase_open_tm in r; exact r.
    + intros x Hx; specialize (r0 x (ltac:(fsetdec))); rewrite task_erase_open_tm in r0; exact r0.
  - match goal with T : AnnTyping _ (a_App _ _ _) _ |- _ => inversion T; subst end.
    rewrite task_erase_open_tm.
    destruct rho; simpl.
    + eapply E_AppCong with (A := erase_tm A1) (B := erase_tm B0).
      * apply (H (a_Pi Rel A1 B0)); assumption.
      * apply (H0 A1); assumption.
    + eapply E_IAppCong with (A := erase_tm A1) (B := erase_tm B0) (a := erase_tm a2).
      * apply (H (a_Pi Irrel A1 B0)); assumption.
      * match goal with IH : task_implicit_argument G (a_App a1 Irrel a2) |- _ =>
          apply (IH a1 Irrel a2 A1 B0); [reflexivity|assumption]
        end.
  - match goal with
    | E : AnnDefEq _ _ _ (a_Pi _ _ _) (a_Pi _ _ _) |- _ =>
      destruct (local_task_ann_eq_typing _ _ _ _ _ E) as [? [? [T _]]];
      inversion T; subst
    end.
    task_use_unique.
    eapply E_PiFst with (rho := rho) (B1 := erase_tm B1) (B2 := erase_tm B2).
    apply (H a_Star); assumption.
  - match goal with
    | E : AnnDefEq _ _ _ (a_Pi _ _ _) (a_Pi _ _ _) |- _ =>
      destruct (local_task_ann_eq_typing _ _ _ _ _ E) as [? [? [T _]]];
      inversion T; subst
    end.
    assert (TyOpen : AnnTyping G (open_tm_wrt_tm B1 a1) a_Star)
      by (eapply task_ann_instantiate_t; eassumption).
    task_use_unique.
    eapply E_PiSnd with (rho := rho) (B1 := erase_tm B1) (B2 := erase_tm B2)
      (a1 := erase_tm a1) (a2 := erase_tm a2) (A1 := erase_tm A1) (A2 := erase_tm A2).
    + apply (H a_Star); assumption.
    + apply (H0 A1); assumption.
  - match goal with T : AnnTyping _ (a_CPi _ _) _ |- _ => inversion T; subst end.
    eapply E_CPiCong with (L := L \u L0);
      [eassumption | | eauto using task_imp_cpi_domain | eassumption | eassumption].
    intros c Hc.
      match goal with
      | IH : forall c, c `notin` L -> forall T, AnnTyping _ _ T -> DefEq _ _ _ _ _ |- _ =>
        specialize (IH c (ltac:(fsetdec)) a_Star);
        rewrite !(task_erase_open_co _ _ (g_Var_f c)) in IH;
        match goal with
        | E : forall c, c `notin` L -> open_tm_wrt_co B3 (g_Var_f c) = _ |- _ =>
          specialize (E c (ltac:(fsetdec))); apply (f_equal erase_tm) in E;
          rewrite !(task_erase_open_co _ _ (g_Var_f c)) in E; rewrite E; apply IH; eauto; fsetdec
        end
      end.
  - task_use_unique.
    match goal with T : AnnTyping _ (a_CAbs _ _) (a_CPi phi1 B1) |- _ => inversion T; subst end.
    eapply E_CAbsCong with (L := L \u L0).
    + intros c Hc.
      match goal with
      | IH : forall c, c `notin` L -> forall T, AnnTyping _ _ T -> DefEq _ _ _ _ _ |- _ =>
        let K := fresh in
        pose proof (IH c (ltac:(fsetdec)) _ (ltac:(eauto; fsetdec))) as K;
        rewrite !(task_erase_open_co _ _ (g_Var_f c)) in K;
        match goal with
        | E : forall c, c `notin` L -> open_tm_wrt_co a3 (g_Var_f c) = _ |- _ =>
          specialize (E c (ltac:(fsetdec))); apply (f_equal erase_tm) in E;
          rewrite !(task_erase_open_co _ _ (g_Var_f c)) in E; rewrite E; exact K
        end
      end.
    + eauto using local_task_imp_type, task_imp_cpi_domain.
  - task_use_unique.
    match goal with T : AnnTyping _ (a_CApp a1 g2) _ |- _ => inversion T; subst end.
    match goal with
    | T : AnnTyping _ ?a (a_CPi (Eq ?u ?v ?U) ?B) |- _ =>
      let K := fresh in pose proof (local_task_ann_type _ _ _ T) as K; inversion K; subst; clear K
    end.
    match goal with
    | H : AnnDefEq ?G ?D ?g ?a ?b, K : AnnDefEq ?G ?E ?g ?c ?d |- _ =>
      tryif (constr_eq a c; constr_eq b d) then fail else
      destruct (local_task_ann_eq_unique _ _ _ _ _ _ _ _ H K); subst
    end.
    match goal with W : AnnPropWff _ (Eq _ _ _) |- _ => inversion W; subst end.
    rewrite (task_erase_open_co _ _ g_Triv).
    eapply E_CAppCong; rewrite ?task_dom_erase; eauto.
    apply (H (a_CPi (Eq a9 b A1) B0)); assumption.
  - match goal with
    | E : AnnDefEq _ _ _ (a_CPi _ _) (a_CPi _ _) |- _ =>
      destruct (local_task_ann_eq_typing _ _ _ _ _ E) as [? [? [T U]]];
      inversion T; inversion U; subst
    end.
    assert (TyOpen : AnnTyping G (open_tm_wrt_co B1 g2) a_Star)
      by (eapply task_ann_instantiate_c; eassumption).
    task_use_unique.
    repeat match goal with W : AnnPropWff _ (Eq _ _ _) |- _ => inversion W; clear W; subst end.
    rewrite !(task_erase_open_co _ _ g_Triv).
    eapply E_CPiSnd with (a1 := erase_tm a) (a2 := erase_tm a') (A := erase_tm A)
          (a1' := erase_tm b) (a2' := erase_tm b') (A' := erase_tm B).
    + apply (H a_Star); assumption.
    + rewrite task_dom_erase; apply (H0 A); assumption.
    + rewrite task_dom_erase; apply (H1 B); assumption.
  - match goal with E : AnnIso _ _ _ (Eq _ _ _) (Eq _ _ _) |- _ =>
      destruct (local_task_ann_iso_wff _ _ _ _ _ E) as [T U];
      inversion T; inversion U; subst
    end.
    task_use_unique.
    eapply E_Cast; eauto.
  - match goal with E : AnnIso _ _ _ (Eq _ _ _) (Eq _ _ _) |- _ =>
      destruct (local_task_ann_iso_wff _ _ _ _ _ E) as [T U];
      inversion T; inversion U; subst
    end.
    assert (TyStar : AnnTyping G A a_Star) by eauto using local_task_ann_type.
    task_use_unique.
    eapply E_IsoSnd; eauto.
  - exact E_Empty.
  - apply E_ConsTm; rewrite ?task_dom_erase; assumption.
  - apply E_ConsCo; rewrite ?task_dom_erase; assumption.
Qed.
End TaskEraseProof.
Theorem erase_mutual :
  (forall G a A, AnnTyping G a A ->
          Typing (erase_context G) (erase_tm a) (erase_tm A)) /\
  (forall G phi, AnnPropWff G phi ->
          PropWff (erase_context G) (erase_constraint phi)) /\
  (forall G D g p1 p2, AnnIso G D g p1 p2 ->
          Iso (erase_context G) D
              (erase_constraint p1) (erase_constraint p2)) /\
  (forall G D g a b,
      AnnDefEq G D g a b ->
      forall A, AnnTyping G a A ->
             DefEq (erase_context G) D (erase_tm a) (erase_tm b) (erase_tm A)) /\
  (forall G, AnnCtx G -> Ctx (erase_context G) /\
    forall c t, binds c t G -> binds c (erase_sort t) (erase_context G)).

Proof.
  pose proof (task_erase_core task_imp_type (fun G a A B H1 H2 => proj1 (proj2 task_ann_unique) G a A H1 B H2)
      task_ann_type (proj1 (proj2 (proj2 task_ann_regular)))
      (proj1 (proj2 (proj2 (proj2 task_ann_regular))))
      (fun G x p HC HB => task_bound_type G x (Co p) HC HB)
      (fun G D E g u v u' v' H1 H2 =>
        proj1 (proj2 (proj2 (proj2 task_ann_unique))) G D g u v H1 E u' v' H2))
    as [HW [HT [HI [HE [HC HS]]]]].
  split.
  - intros G a A H; exact (proj1 (HT G a A H)).
  - split; [exact HW |].
    split; [exact HI |].
    split; [exact HE |].
    intros G HG; split.
    + exact (HC G HG).
    + intros; eauto using task_binds_erase.
Qed.


(* Construction of annotations from implicit derivations. *)

Lemma task_ann_same_erasure : forall G D a b A B,
  AnnTyping G a A -> AnnTyping G b B ->
  erase_tm a = erase_tm b -> erase_tm A = erase_tm B ->
  AnnDefEq G D (g_Refl2 a b (g_Refl2 A B (g_Refl a_Star))) a b.
Proof.
  intros G D a b A B Ta Tb E ET.
  eapply An_EraseEq with (A := A) (B := B); try eassumption.
  eapply An_EraseEq with (A := a_Star) (B := a_Star); eauto using task_ann_type.
  eapply An_Refl with (A := a_Star); apply An_Star; eapply (proj1 (proj2 task_ann_ctx_of)); eassumption.
Qed.

Lemma task_ann_retype : forall G a A B,
  AnnTyping G a A -> AnnTyping G B a_Star -> erase_tm A = erase_tm B ->
  exists a', erase_tm a' = erase_tm a /\ AnnTyping G a' B.
Proof.
  intros G a A B HT HB HE.
  exists (a_Conv a (g_Refl2 A B (g_Refl2 a_Star a_Star (g_Refl a_Star)))).
  split; [reflexivity|].
  eapply An_Conv; [exact HT| |exact HB].
  eapply task_ann_same_erasure; eauto using task_ann_type.
Qed.

Lemma task_ann_eq_trans_same_type : forall G D g h a b c A,
  AnnDefEq G D g a b -> AnnDefEq G D h b c ->
  AnnTyping G a A -> AnnTyping G b A ->
  AnnDefEq G D (g_Trans g h) a c.
Proof.
  intros.
  eapply An_Trans with (g3 := g_Refl A); eauto using An_Refl, task_ann_type.
Qed.

Lemma task_ann_eq_sym_same_type : forall G D g a b A,
  AnnDefEq G D g a b -> AnnTyping G a A -> AnnTyping G b A ->
  AnnDefEq G D (g_Sym g) b a.
Proof.
  intros.
  eapply An_Sym with (g1 := g_Refl A); eauto using An_Refl, task_ann_type.
Qed.

Lemma task_ann_pi_representative : forall G T K rho A B,
  AnnTyping G T K -> erase_tm T = a_Pi rho A B ->
  exists A' B', erase_tm A' = A /\ erase_tm B' = B /\
    AnnTyping G (a_Pi rho A' B') a_Star.
Proof.
  intros G T K rho A B H; induction H; intro Eq; cbn in Eq;
    try match goal with r : relflag |- _ => destruct r; cbn in Eq end;
    try discriminate; inversion Eq; subst; eauto using An_Pi.
  all: exists A0, B0; split; [reflexivity|split; [reflexivity|eapply An_Pi with (L := L); eassumption]].
Qed.

Lemma task_ann_cpi_representative : forall G T K p B,
  AnnTyping G T K -> erase_tm T = a_CPi p B ->
  exists p' B', erase_constraint p' = p /\ erase_tm B' = B /\
    AnnTyping G (a_CPi p' B') a_Star.
Proof.
  intros G T K p B H; induction H; intro Eq; cbn in Eq;
    try match goal with r : relflag |- _ => destruct r; cbn in Eq end;
    try discriminate; inversion Eq; subst; eauto using An_CPi.
  exists phi, B0; split; [reflexivity|split; [reflexivity|eapply An_CPi with (L := L); eassumption]].
Qed.

Lemma task_ann_types_agree : forall G D A B,
  AnnTyping G A a_Star -> AnnTyping G B a_Star -> erase_tm A = erase_tm B ->
  AnnDefEq G D (g_Refl2 A B (g_Refl a_Star)) A B.
Proof.
  intros.
  eapply An_EraseEq with (A := a_Star) (B := a_Star); try eassumption; try reflexivity.
  eapply An_Refl with (A := a_Star); apply An_Star;
    eapply (proj1 (proj2 task_ann_ctx_of)); eassumption.
Qed.

Lemma task_ann_eq_reconcile_at : forall G D g a b A a' b' A' B' h1 h2,
  AnnDefEq G D g a b -> AnnTyping G a A -> AnnTyping G b A ->
  AnnTyping G a' A' -> AnnTyping G b' B' ->
  erase_tm a' = erase_tm a -> erase_tm b = erase_tm b' ->
  AnnDefEq G (dom G) h1 A' A -> AnnDefEq G (dom G) h2 A B' ->
  exists q, AnnDefEq G D q a' b'.
Proof.
  intros G D g a b A a' b' A' B' h1 h2 H Ta Tb Ta' Tb' Ea Eb X Y.
  exists (g_Trans (g_Trans (g_Refl2 a' a h1) g) (g_Refl2 b b' h2)).
  eapply An_Trans with (A := A') (A1 := A) (g3 := h1); try eassumption.
  - eapply An_Trans with (A := A') (A1 := A) (g3 := h1); try eassumption.
    eapply An_EraseEq; eassumption.
  - eapply An_EraseEq; eassumption.
Qed.

Lemma task_ann_eq_reconcile : forall G D g a b A a' b' A' B',
  AnnDefEq G D g a b -> AnnTyping G a A -> AnnTyping G b A ->
  AnnTyping G a' A' -> AnnTyping G b' B' ->
  erase_tm a' = erase_tm a -> erase_tm b = erase_tm b' ->
  erase_tm A' = erase_tm A -> erase_tm A = erase_tm B' ->
  exists q, AnnDefEq G D q a' b'.
Proof.
  intros.
  eapply task_ann_eq_reconcile_at; try eassumption;
    eapply task_ann_types_agree; eauto using task_ann_type.
Qed.

Lemma task_ann_eq_same_grade : forall G D g a b A B,
  AnnDefEq G D g a b -> AnnTyping G a A -> AnnTyping G b A ->
  AnnTyping G B a_Star -> erase_tm A = erase_tm B ->
  exists q a' b', erase_tm a' = erase_tm a /\ erase_tm b' = erase_tm b /\
      AnnDefEq G D q a' b' /\ AnnTyping G a' B /\ AnnTyping G b' B.
Proof.
  intros G D g a b A B H Ta Tb TK E.
  destruct (task_ann_retype _ _ _ _ Ta TK E) as [a' [Ea Va]].
  destruct (task_ann_retype _ _ _ _ Tb TK E) as [b' [Eb Vb]].
  destruct (task_ann_eq_reconcile G D g a b A a' b' B B H Ta Tb Va Vb)
    as [q Hq]; eauto.
  exists q, a', b'; auto.
Qed.

Lemma task_ann_reclose_eq_t : forall G D x U g a b,
  x `notin` dom G -> x `notin` task_vars_context G -> x `notin` task_vars_tm U ->
  AnnTyping G U a_Star ->
  AnnDefEq (x ~ Tm U ++ G) D g a b ->
  forall y, y `notin` dom G ->
    AnnDefEq (y ~ Tm U ++ G) D (open_co_wrt_tm (task_close_t_co x g) (a_Var_f y))
      (open_tm_wrt_tm (task_close_t_tm x a) (a_Var_f y))
      (open_tm_wrt_tm (task_close_t_tm x b) (a_Var_f y)).
Proof.
  intros G D x U g a b XD XV XU HU HE y YD.
  assert (HG : AnnCtx G) by (eapply (proj1 (proj2 task_ann_ctx_of)); eassumption).
  assert (HY : AnnCtx (y ~ Tm U ++ G)) by (apply An_ConsTm; assumption).
  assert (HV : AnnTyping (y ~ Tm U ++ G) (a_Var_f y) U)
    by (apply An_Var; [exact HY | apply binds_cons_2; reflexivity]).
  assert (Ext : task_extends G (y ~ Tm U ++ G)) by (unfold task_extends; eauto using binds_app_3).
  pose proof (task_single_t_for_ctx G _ x (a_Var_f y) U I XD XV XU HY Ext HV) as M.
  pose proof (task_single_t_for_availability G _ D x (a_Var_f y) U I XV HY Ext) as MA.
  unfold task_close_t_tm, task_close_t_co, open_tm_wrt_tm, open_co_wrt_tm.
  rewrite !(proj1 task_open_close_t), (proj1 (proj2 (proj2 task_open_close_t))).
  exact (proj1 (proj2 (proj2 (proj2 task_ann_substitute))) _ _ _ _ _ HE _ _ _ M MA).
Qed.

Lemma task_ann_reclose_c : forall G x p a A,
  x `notin` dom G -> x `notin` task_vars_context G -> x `notin` task_vars_constraint p ->
  AnnPropWff G p -> AnnTyping (x ~ Co p ++ G) a A ->
  forall y, y `notin` dom G ->
    AnnTyping (y ~ Co p ++ G) (open_tm_wrt_co (task_close_c_tm x a) (g_Var_f y))
                              (open_tm_wrt_co (task_close_c_tm x A) (g_Var_f y)).
Proof.
  intros G x [s t T] a A XD XV XP HP HA y YD.
  assert (HG : AnnCtx G) by (eapply (proj1 task_ann_ctx_of); eassumption).
  assert (HY : AnnCtx (y ~ Co (Eq s t T) ++ G)) by (apply An_ConsCo; assumption).
  assert (HV : AnnDefEq (y ~ Co (Eq s t T) ++ G) (dom (y ~ Co (Eq s t T) ++ G)) (g_Var_f y) s t)
    by (eapply An_Assn with (A := T); [exact HY | apply binds_cons_2; reflexivity | simpl; fsetdec]).
  pose proof (task_single_c_for_ctx G _ x (g_Var_f y) s t T I XD XV XP HY
              (ltac:(unfold task_extends; eauto using binds_app_3)) HV) as M.
  unfold task_close_c_tm, open_tm_wrt_co.
  rewrite !(proj1 task_open_close_c).
  exact (proj1 (proj2 task_ann_substitute) _ _ _ HA _ _ M).
Qed.

Lemma task_ann_reclose_eq_c : forall G D x p g a b,
  x `notin` D -> x `notin` dom G -> x `notin` task_vars_context G -> x `notin` task_vars_constraint p ->
  AnnPropWff G p -> AnnDefEq (x ~ Co p ++ G) D g a b ->
  forall y, y `notin` dom G ->
    AnnDefEq (y ~ Co p ++ G) D (open_co_wrt_co (task_close_c_co x g) (g_Var_f y))
      (open_tm_wrt_co (task_close_c_tm x a) (g_Var_f y))
      (open_tm_wrt_co (task_close_c_tm x b) (g_Var_f y)).
Proof.
  intros G D x [s t T] g a b XE XD XV XP HP HE y YD.
  assert (HG : AnnCtx G) by (eapply (proj1 task_ann_ctx_of); eassumption).
  assert (HY : AnnCtx (y ~ Co (Eq s t T) ++ G)) by (apply An_ConsCo; assumption).
  assert (HV : AnnDefEq (y ~ Co (Eq s t T) ++ G) (dom (y ~ Co (Eq s t T) ++ G)) (g_Var_f y) s t)
    by (eapply An_Assn with (A := T); [exact HY | apply binds_cons_2; reflexivity | simpl; fsetdec]).
  assert (Ext : task_extends G (y ~ Co (Eq s t T) ++ G)) by (unfold task_extends; eauto using binds_app_3).
  pose proof (task_single_c_for_ctx G _ x (g_Var_f y) s t T I XD XV XP HY Ext HV) as M.
  pose proof (task_single_c_for_availability G _ D x (g_Var_f y) (Eq s t T) I XE XV HY Ext) as MA.
  unfold task_close_c_tm, task_close_c_co, open_tm_wrt_co, open_co_wrt_co.
  rewrite !(proj1 task_open_close_c), (proj1 (proj2 (proj2 task_open_close_c))).
  exact (proj1 (proj2 (proj2 (proj2 task_ann_substitute))) _ _ _ _ _ HE _ _ _ M MA).
Qed.

Lemma task_close_t_erase_open : forall x t b,
  x `notin` task_vars_tm b -> erase_tm t = open_tm_wrt_tm b (a_Var_f x) ->
  erase_tm (task_close_t_tm x t) = b.
Proof.
  unfold task_close_t_tm, open_tm_wrt_tm; intros.
  rewrite (proj1 task_erase_close_t), H0, (proj1 task_close_open_t) by assumption.
  reflexivity.
Qed.

Lemma task_close_c_erase_open : forall x t b,
  x `notin` task_vars_tm b -> erase_tm t = open_tm_wrt_co b (g_Var_f x) ->
  erase_tm (task_close_c_tm x t) = b.
Proof.
  unfold task_close_c_tm, open_tm_wrt_co; intros.
  rewrite (proj1 task_erase_close_c), H0, (proj1 task_close_open_c) by assumption.
  reflexivity.
Qed.

Lemma task_as_kind : forall G a A,
  AnnTyping G a A -> erase_tm A = a_Star ->
  exists a', erase_tm a' = erase_tm a /\ AnnTyping G a' a_Star.
Proof.
  intros G a A H E.
  eapply task_ann_retype; [exact H | apply An_Star; eapply (proj1 (proj2 task_ann_ctx_of)); eassumption | exact E].
Qed.

Lemma task_ann_eq_as_kind : forall G D g a b A,
  AnnDefEq G D g a b -> AnnTyping G a A -> AnnTyping G b A -> erase_tm A = a_Star ->
  exists q a' b', erase_tm a' = erase_tm a /\ erase_tm b' = erase_tm b /\
      AnnDefEq G D q a' b' /\ AnnTyping G a' a_Star /\ AnnTyping G b' a_Star.
Proof.
  intros G D g a b A H Ta Tb E.
  eapply task_ann_eq_same_grade; try eassumption.
  apply An_Star; eapply (proj1 (proj2 task_ann_ctx_of)); eassumption.
Qed.

Lemma task_ann_eq_force_rhs : forall G D g a b A B h,
  AnnDefEq G D g a b -> AnnTyping G a A -> AnnTyping G b B ->
  AnnDefEq G (dom G) h A B ->
  exists q b', erase_tm b' = erase_tm b /\ AnnDefEq G D q a b' /\ AnnTyping G b' A.
Proof.
  intros G D g a b A B h H Ta Tb E.
  assert (TA : AnnTyping G A a_Star) by (eapply task_ann_type; exact Ta).
  assert (TB : AnnTyping G B a_Star) by (eapply task_ann_type; exact Tb).
  assert (EH : AnnDefEq G (dom G) (g_Sym h) B A)
    by (eapply task_ann_eq_sym_same_type; eassumption).
  assert (Hconv : AnnTyping G (a_Conv b (g_Sym h)) A)
    by (eapply An_Conv; eassumption).
  exists (g_Trans g (g_Refl2 b (a_Conv b (g_Sym h)) (g_Sym h))), (a_Conv b (g_Sym h)).
  split; [reflexivity | split; [ | exact Hconv ]].
  eapply An_Trans with (A := A) (A1 := B) (g3 := h); try eassumption.
  eapply An_EraseEq; try eassumption; reflexivity.
Qed.

Lemma task_ann_iso_full : forall G D g p q,
  AnnIso G D g p q -> AnnIso G (dom G) g p q.
Proof.
  intros G D g p q HQ.
  pose proof (proj1 (proj2 (proj2 task_ann_ctx_of)) _ _ _ _ _ HQ) as HG.
  pose proof (task_ann_identity_ctx G HG) as M.
  assert (MA : task_sub_assum task_identity_sub G G D (dom G)).
  { unfold task_sub_assum; intros c a0 b0 A Hb HD.
    rewrite !(proj1 task_sub_identity).
    eapply An_Assn; [exact HG|exact Hb|eapply binds_In; exact Hb]. }
  pose proof (proj1 (proj2 (proj2 task_ann_substitute)) _ _ _ _ _ HQ
    task_identity_sub G (dom G) M MA) as K.
  rewrite !(proj2 (proj2 (proj2 task_sub_identity))), (proj1 (proj2 (proj2 task_sub_identity))) in K.
  exact K.
Qed.

Lemma task_ann_wff_retype : forall G a b A B,
  AnnPropWff G (Eq a b A) -> AnnTyping G B a_Star -> erase_tm A = erase_tm B ->
  exists a' b', erase_tm a' = erase_tm a /\ erase_tm b' = erase_tm b /\
    AnnTyping G a' B /\ AnnTyping G b' B /\ AnnPropWff G (Eq a' b' B).
Proof.
  intros G a b A B HW HB E; inversion HW as [G0 y z U V Ty Tz Eq]; subst.
  destruct (task_ann_retype _ _ _ _ Ty HB E) as [a' [Ea Ta]].
  destruct (task_ann_retype G b _ B Tz HB) as [b' [Eb Tb]].
  - congruence.
  - exists a', b'; repeat split; try assumption.
    eapply An_Wff; eauto.
Qed.

Lemma task_pi_type : forall G m T rho A B,
  AnnTyping G m T -> erase_tm T = a_Pi rho A B ->
  exists U V, erase_tm U = A /\ erase_tm V = B /\
    AnnTyping G (a_Pi rho U V) a_Star /\ AnnTyping G U a_Star.
Proof.
  intros G m T rho A B HT E.
  destruct (task_ann_pi_representative _ _ _ _ _ _ (task_ann_type _ _ _ HT) E)
    as [U [V [EU [EV HP]]]].
  exists U, V; repeat split; try assumption.
  inversion HP; subst; assumption.
Qed.

Lemma task_cpi_type : forall G m T p B,
  AnnTyping G m T -> erase_tm T = a_CPi p B ->
  exists q V, erase_constraint q = p /\ erase_tm V = B /\
    AnnTyping G (a_CPi q V) a_Star /\ AnnPropWff G q.
Proof.
  intros G m T p B HT E.
  destruct (task_ann_cpi_representative _ _ _ _ _ (task_ann_type _ _ _ HT) E)
    as [q [V [EQ [EV HP]]]].
  exists q, V; repeat split; try assumption.
  inversion HP; subst; assumption.
Qed.

Lemma task_ann_application : forall G rho f a T U A B,
  AnnTyping G f T -> AnnTyping G a U -> erase_tm T = a_Pi rho A B -> erase_tm U = A ->
  exists f' a' R, erase_tm f' = erase_tm f /\ erase_tm a' = erase_tm a /\
    erase_tm R = open_tm_wrt_tm B (erase_tm a) /\ AnnTyping G (a_App f' rho a') R.
Proof.
  intros G rho f a T U A B F X ET EU.
  destruct (task_pi_type _ _ _ _ _ _ F ET) as [V [W [EV [EW [HP HV]]]]].
  destruct (task_ann_retype G f T (a_Pi rho V W) F HP) as [f' [EF TF]]; [cbn; congruence|].
  destruct (task_ann_retype G a U V X HV) as [a' [EA TA]]; [congruence|].
  exists f', a', (open_tm_wrt_tm W a'); repeat split; try assumption.
  - rewrite task_erase_open_tm; congruence.
  - eapply An_App; eassumption.
Qed.

Lemma task_ann_co_application : forall G f T g a b A u v U B,
  AnnTyping G f T -> AnnDefEq G (dom G) g a b ->
  AnnTyping G a A -> AnnTyping G b A ->
  erase_tm T = a_CPi (Eq u v U) B ->
  erase_tm a = u -> erase_tm b = v -> erase_tm A = U ->
  exists f' g' R, erase_tm f' = erase_tm f /\
    erase_tm R = open_tm_wrt_co B g_Triv /\ AnnTyping G (a_CApp f' g') R.
Proof.
  intros G f T g a b A u v U B TF EE TA TB ET EA EB EU.
  destruct (task_cpi_type _ _ _ _ _ TF ET) as [[a0 b0 A0] [W [EP [EW [HP HW]]]]].
  cbn in EP; injection EP as E1 E2 E3.
  destruct (task_ann_retype G f T (a_CPi (Eq a0 b0 A0) W) TF HP) as [f' [EF F]];
    [cbn; congruence|].
  inversion HW as [G0 a1 b1 A1 B0 Ta Tb ETy]; subst.
  destruct (task_ann_eq_reconcile G (dom G) g a b A a0 b0 A0 B0 EE TA TB Ta Tb)
    as [q HQ]; try congruence.
  exists f', q, (open_tm_wrt_co W q); repeat split; try assumption.
  - rewrite (task_erase_open_co _ _ g_Triv); congruence.
  - eapply An_CApp; eassumption.
Qed.

Lemma task_ann_pi_eq : forall G D g u v T rho A1 B1 A2 B2,
  AnnDefEq G D g u v -> AnnTyping G u T -> AnnTyping G v T ->
  erase_tm T = a_Star -> erase_tm u = a_Pi rho A1 B1 -> erase_tm v = a_Pi rho A2 B2 ->
  exists q U X V Y, erase_tm U = A1 /\ erase_tm X = B1 /\ erase_tm V = A2 /\ erase_tm Y = B2 /\
    AnnDefEq G D q (a_Pi rho U X) (a_Pi rho V Y) /\
    AnnTyping G (a_Pi rho U X) a_Star /\ AnnTyping G (a_Pi rho V Y) a_Star.
Proof.
  intros G D g u v T rho A1 B1 A2 B2 Q TU TV ET EU EV.
  destruct (task_ann_pi_representative _ _ _ _ _ _ TU EU) as [U [X [E1 [E2 TX]]]].
  destruct (task_ann_pi_representative _ _ _ _ _ _ TV EV) as [V [Y [E3 [E4 TY]]]].
  destruct (task_ann_eq_reconcile G D g u v T (a_Pi rho U X) (a_Pi rho V Y) a_Star a_Star Q TU TV TX TY)
    as [q HQ]; try (cbn; congruence).
  exists q, U, X, V, Y; repeat split; assumption.
Qed.

Lemma task_ann_cpi_eq : forall G D g u v T p q X Y,
  AnnDefEq G D g u v -> AnnTyping G u T -> AnnTyping G v T ->
  erase_tm T = a_Star -> erase_tm u = a_CPi p X -> erase_tm v = a_CPi q Y ->
  exists h p' X' q' Y', erase_constraint p' = p /\ erase_tm X' = X /\ erase_constraint q' = q /\ erase_tm Y' = Y /\
    AnnDefEq G D h (a_CPi p' X') (a_CPi q' Y') /\
    AnnTyping G (a_CPi p' X') a_Star /\ AnnTyping G (a_CPi q' Y') a_Star.
Proof.
  intros G D g u v T p q X Y Q TU TV ET EU EV.
  destruct (task_ann_cpi_representative _ _ _ _ _ TU EU) as [p' [X' [E1 [E2 TX]]]].
  destruct (task_ann_cpi_representative _ _ _ _ _ TV EV) as [q' [Y' [E3 [E4 TY]]]].
  destruct (task_ann_eq_reconcile G D g u v T (a_CPi p' X') (a_CPi q' Y') a_Star a_Star Q TU TV TX TY)
    as [h HQ]; try (cbn; congruence).
  exists h, p', X', q', Y'; repeat split; assumption.
Qed.

Lemma task_ann_constraint_eq : forall G D g u v T a b A,
  AnnDefEq G D g u v -> AnnTyping G u T -> AnnTyping G v T ->
  AnnPropWff G (Eq a b A) ->
  erase_tm a = erase_tm u -> erase_tm b = erase_tm v -> erase_tm A = erase_tm T ->
  exists h, AnnDefEq G D h a b.
Proof.
  intros G D g u v T a b A HQ TU TV HW E1 E2 ET.
  inversion HW as [G0 a0 b0 A0 B0 TA TB E]; subst.
  eapply task_ann_eq_reconcile; try eassumption; congruence.
Qed.

Lemma task_ann_iso_refl : forall G D p,
  AnnPropWff G p -> exists q, AnnIso G D q p p.
Proof.
  intros G D p HW; inversion HW; subst.
  eexists (g_EqCong (g_Refl a) A (g_Refl b)).
  apply An_PropCong; eauto using An_Refl.
Qed.
Definition task_push_t_bound (g : co) (k n : nat) :=
  if Nat.eq_dec n k then a_Conv (a_Var_b n) g else a_Var_b n.
Definition task_push_t g := task_walk_tm task_id_ft task_id_fc (task_push_t_bound g) task_id_bc 0 0.

Lemma task_open_push_t :
  (forall s i j x g, task_scope_co 0 0 g -> open_tm_wrt_tm_rec i (a_Var_f x) (task_walk_tm task_id_ft task_id_fc (task_push_t_bound g) task_id_bc i j s) = open_tm_wrt_tm_rec i (a_Conv (a_Var_f x) g) s) /\
  (forall s i j x g, task_scope_co 0 0 g -> open_brs_wrt_tm_rec i (a_Var_f x) (task_walk_brs task_id_ft task_id_fc (task_push_t_bound g) task_id_bc i j s) = open_brs_wrt_tm_rec i (a_Conv (a_Var_f x) g) s) /\
  (forall s i j x g, task_scope_co 0 0 g -> open_co_wrt_tm_rec i (a_Var_f x) (task_walk_co task_id_ft task_id_fc (task_push_t_bound g) task_id_bc i j s) = open_co_wrt_tm_rec i (a_Conv (a_Var_f x) g) s) /\
  (forall s i j x g, task_scope_co 0 0 g -> open_constraint_wrt_tm_rec i (a_Var_f x) (task_walk_constraint task_id_ft task_id_fc (task_push_t_bound g) task_id_bc i j s) = open_constraint_wrt_tm_rec i (a_Conv (a_Var_f x) g) s).
Proof.
  pose proof task_scope_idle_t as [_ [_ [Idle _]]].
  pose proof task_scope_mono as [_ [_ [Mono _]]].
  task_structure; intros; cbn -[lt_eq_lt_dec]; try solve [reflexivity | f_equal; eauto];
  unfold task_push_t_bound;
  destruct (Nat.eq_dec n i) as [-> | Hneq]; cbn -[lt_eq_lt_dec];
  destruct (lt_eq_lt_dec n i) as [[?|?]|?] || destruct (lt_eq_lt_dec i i) as [[?|?]|?];
    try contradiction; try lia; try reflexivity;
  f_equal; eapply (Idle _ i j);
  eapply (Mono _ 0 0); lia || assumption.
Qed.

Lemma task_erase_push_t :
  (forall t i j g, erase_tm (task_walk_tm task_id_ft task_id_fc (task_push_t_bound g) task_id_bc i j t) = erase_tm t) /\
  (forall s : brs, True) /\ (forall g : co, True) /\
  (forall p i j g, erase_constraint (task_walk_constraint task_id_ft task_id_fc (task_push_t_bound g) task_id_bc i j p) = erase_constraint p).
Proof.
  task_structure; intros; try exact I;
  try match goal with r : relflag |- _ => destruct r end; cbn;
  try solve [auto | f_equal; auto];
  unfold task_push_t_bound;
  match goal with |- context [Nat.eq_dec ?n ?k] =>
    destruct (Nat.eq_dec n k); reflexivity
  end.
Qed.

Definition task_push_c_bound (g : co) (k n : nat) :=
  if Nat.eq_dec n k then g_Cast (g_Var_b n) g else g_Var_b n.
Definition task_push_c g := task_walk_tm task_id_ft task_id_fc task_id_bt (task_push_c_bound g) 0 0.

Lemma task_open_push_c :
  (forall s i j x g, task_scope_co 0 0 g -> open_tm_wrt_co_rec j (g_Var_f x) (task_walk_tm task_id_ft task_id_fc task_id_bt (task_push_c_bound g) i j s) = open_tm_wrt_co_rec j (g_Cast (g_Var_f x) g) s) /\
  (forall s i j x g, task_scope_co 0 0 g -> open_brs_wrt_co_rec j (g_Var_f x) (task_walk_brs task_id_ft task_id_fc task_id_bt (task_push_c_bound g) i j s) = open_brs_wrt_co_rec j (g_Cast (g_Var_f x) g) s) /\
  (forall s i j x g, task_scope_co 0 0 g -> open_co_wrt_co_rec j (g_Var_f x) (task_walk_co task_id_ft task_id_fc task_id_bt (task_push_c_bound g) i j s) = open_co_wrt_co_rec j (g_Cast (g_Var_f x) g) s) /\
  (forall s i j x g, task_scope_co 0 0 g -> open_constraint_wrt_co_rec j (g_Var_f x) (task_walk_constraint task_id_ft task_id_fc task_id_bt (task_push_c_bound g) i j s) = open_constraint_wrt_co_rec j (g_Cast (g_Var_f x) g) s).
Proof.
  pose proof task_scope_idle_c as [_ [_ [Idle _]]].
  pose proof task_scope_mono as [_ [_ [Mono _]]].
  task_structure; intros; cbn -[lt_eq_lt_dec]; try solve [reflexivity | f_equal; eauto];
  unfold task_push_c_bound;
  destruct (Nat.eq_dec n j) as [-> | Hneq]; cbn -[lt_eq_lt_dec];
  destruct (lt_eq_lt_dec n j) as [[?|?]|?] || destruct (lt_eq_lt_dec j j) as [[?|?]|?];
    try contradiction; try lia; try reflexivity;
  f_equal; eapply (Idle _ i j);
  eapply (Mono _ 0 0); lia || assumption.
Qed.

Lemma task_erase_push_c :
  (forall t i j g, erase_tm (task_walk_tm task_id_ft task_id_fc task_id_bt (task_push_c_bound g) i j t) = erase_tm t) /\
  (forall s : brs, True) /\ (forall g : co, True) /\
  (forall p i j g, erase_constraint (task_walk_constraint task_id_ft task_id_fc task_id_bt (task_push_c_bound g) i j p) = erase_constraint p).
Proof.
  task_structure; intros; try exact I;
  try match goal with r : relflag |- _ => destruct r end; cbn;
  try solve [auto | f_equal; auto];
  unfold task_push_c_bound;
  match goal with |- context [Nat.eq_dec ?n ?k] =>
    destruct (Nat.eq_dec n k); reflexivity
  end.
Qed.


Lemma task_ann_push_t : forall G D L A C g b B,
  AnnTyping G A a_Star -> AnnTyping G C a_Star -> AnnDefEq G D g A C ->
  (forall x, x `notin` L ->
     AnnTyping (x ~ Tm A ++ G) (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  exists L', forall x, x `notin` L' ->
     AnnTyping (x ~ Tm C ++ G)
       (open_tm_wrt_tm (task_push_t (g_Sym g) b) (a_Var_f x))
       (open_tm_wrt_tm (task_push_t (g_Sym g) B) (a_Var_f x)).
Proof.
  intros G D L A C g b B HA HC Eq HB.
  assert (HG : AnnCtx G) by (eapply (proj1 (proj2 task_ann_ctx_of)); eassumption).
  assert (Rev : AnnDefEq G (dom G) (g_Sym g) C A).
  { eapply task_ann_eq_sym_same_type; [exact (task_ann_eq_full G D g A C Eq)|exact HA|exact HC]. }
  pose proof (proj1 (proj2 (proj2 (proj2 task_ann_scope))) _ _ _ _ _ Rev) as [Sg _].
  exists (L \u dom G \u task_vars_context G \u task_vars_tm A \u task_vars_tm b \u task_vars_tm B).
  intros x HX.
  assert (HY : AnnCtx (x ~ Tm C ++ G)) by (apply An_ConsTm; [exact HG|exact HC|fsetdec]).
  assert (HV : AnnTyping (x ~ Tm C ++ G) (a_Var_f x) C)
    by (apply An_Var; [exact HY | apply binds_cons_2; reflexivity]).
  assert (Ext : task_extends G (x ~ Tm C ++ G)) by (unfold task_extends; eauto using binds_app_3).
  assert (HR : AnnDefEq (x ~ Tm C ++ G) (dom (x ~ Tm C ++ G)) (g_Sym g) C A)
    by (eapply (proj1 (proj2 (proj2 (proj2 task_ann_weaken))));
        [exact Rev|exact HY|exact Ext|apply task_extends_dom; exact Ext]).
  assert (TA : AnnTyping (x ~ Tm C ++ G) A a_Star)
    by (eapply (proj1 (proj2 task_ann_weaken)); eassumption).
  assert (TV : AnnTyping (x ~ Tm C ++ G) (a_Conv (a_Var_f x) (g_Sym g)) A)
    by (eapply An_Conv; eassumption).
  pose proof (proj1 (proj2 task_ann_scope) _ _ _ TV) as [SV _].
  pose proof (task_single_t_for_ctx G (x ~ Tm C ++ G) x (a_Conv (a_Var_f x) (g_Sym g)) A SV
              (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) HY Ext TV) as M.
  pose proof (proj1 (proj2 task_ann_substitute) _ _ _ (HB x (ltac:(fsetdec))) _ _ M) as K.
  unfold task_push_t, open_tm_wrt_tm in *.
  rewrite !(proj1 task_open_push_t) by exact Sg.
  rewrite !(proj1 task_sub_open_t_rec) in K.
  rewrite (proj1 task_single_t_inert b), (proj1 task_single_t_inert B) in K by fsetdec.
  change (task_sub_tm (task_single_t x (a_Conv (a_Var_f x) (g_Sym g)) SV) (a_Var_f x))
    with (if Atom.eq_dec x x then a_Conv (a_Var_f x) (g_Sym g) else a_Var_f x) in K.
  destruct (Atom.eq_dec x x); [exact K|contradiction].
Qed.

Lemma task_ann_push_c : forall G D L p q g b B,
  AnnPropWff G p -> AnnPropWff G q -> AnnIso G D g p q ->
  (forall x, x `notin` L ->
     AnnTyping (x ~ Co p ++ G) (open_tm_wrt_co b (g_Var_f x)) (open_tm_wrt_co B (g_Var_f x))) ->
  exists L', forall x, x `notin` L' ->
     AnnTyping (x ~ Co q ++ G)
       (open_tm_wrt_co (task_push_c (g_Sym g) b) (g_Var_f x))
       (open_tm_wrt_co (task_push_c (g_Sym g) B) (g_Var_f x)).
Proof.
  intros G D L [a b0 A] [c d C] g b B HP HQ Hiso HB.
  assert (HG : AnnCtx G) by (eapply (proj1 task_ann_ctx_of); eassumption).
  assert (Rev : AnnIso G (dom G) (g_Sym g) (Eq c d C) (Eq a b0 A)).
  { apply An_IsoSym; exact (task_ann_iso_full G D g (Eq a b0 A) (Eq c d C) Hiso). }
  pose proof (proj1 (proj2 (proj2 task_ann_scope)) _ _ _ _ _ Rev) as [Sg _].
  exists (L \u dom G \u task_vars_context G \u task_vars_constraint (Eq a b0 A) \u task_vars_tm b \u task_vars_tm B).
  intros x HX.
  assert (HY : AnnCtx (x ~ Co (Eq c d C) ++ G)) by (apply An_ConsCo; [exact HG|exact HQ|fsetdec]).
  assert (HV : AnnDefEq (x ~ Co (Eq c d C) ++ G) (dom (x ~ Co (Eq c d C) ++ G)) (g_Var_f x) c d)
    by (eapply An_Assn with (A := C); [exact HY | apply binds_cons_2; reflexivity | simpl; fsetdec]).
  assert (Ext : task_extends G (x ~ Co (Eq c d C) ++ G)) by (unfold task_extends; eauto using binds_app_3).
  assert (HR : AnnIso (x ~ Co (Eq c d C) ++ G) (dom (x ~ Co (Eq c d C) ++ G)) (g_Sym g) (Eq c d C) (Eq a b0 A))
    by (eapply (proj1 (proj2 (proj2 task_ann_weaken)));
        [exact Rev|exact HY|exact Ext|apply task_extends_dom; exact Ext]).
  assert (TV : AnnDefEq (x ~ Co (Eq c d C) ++ G) (dom (x ~ Co (Eq c d C) ++ G))
                         (g_Cast (g_Var_f x) (g_Sym g)) a b0)
    by (eapply An_Cast; eassumption).
  pose proof (proj1 (proj2 (proj2 (proj2 task_ann_scope))) _ _ _ _ _ TV) as [SV _].
  pose proof (task_single_c_for_ctx G (x ~ Co (Eq c d C) ++ G) x (g_Cast (g_Var_f x) (g_Sym g)) a b0 A SV
              (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) HY Ext TV) as M.
  pose proof (proj1 (proj2 task_ann_substitute) _ _ _ (HB x (ltac:(fsetdec))) _ _ M) as K.
  unfold task_push_c, open_tm_wrt_co in *.
  rewrite !(proj1 task_open_push_c) by exact Sg.
  rewrite !(proj1 task_sub_open_c_rec) in K.
  rewrite (proj1 task_single_c_inert b), (proj1 task_single_c_inert B) in K by fsetdec.
  change (task_sub_co (task_single_c x (g_Cast (g_Var_f x) (g_Sym g)) SV) (g_Var_f x))
    with (if Atom.eq_dec x x then g_Cast (g_Var_f x) (g_Sym g) else g_Var_f x) in K.
  destruct (Atom.eq_dec x x); [exact K|contradiction].
Qed.

Lemma task_annotate_core :
  (forall G p, PropWff G p -> forall J, erase_context J = G -> AnnCtx J ->
      exists p', erase_constraint p' = p /\ AnnPropWff J p') /\
  (forall G a A, Typing G a A -> forall J, erase_context J = G -> AnnCtx J ->
      exists a' A', erase_tm a' = a /\ erase_tm A' = A /\ AnnTyping J a' A') /\
  (forall G D p q, Iso G D p q -> forall J, erase_context J = G -> AnnCtx J ->
      exists g p' q', erase_constraint p' = p /\ erase_constraint q' = q /\ AnnIso J D g p' q') /\
  (forall G D a b A, DefEq G D a b A -> forall J, erase_context J = G -> AnnCtx J ->
      exists g a' b' A', erase_tm a' = a /\ erase_tm b' = b /\ erase_tm A' = A /\
        AnnDefEq J D g a' b' /\ AnnTyping J a' A' /\ AnnTyping J b' A') /\
  (forall G, Ctx G -> True).
Proof.
  apply task_implicit_ind; intros; try exact I; subst G.
  - destruct (H J eq_refl H3) as [a' [A' [Ea [EA Ta]]]].
    destruct (H0 J eq_refl H3) as [b' [B' [Eb [EB Tb]]]].
    exists (Eq a' b' A'); split; [simpl; congruence | eapply An_Wff; eauto; congruence].
  - exists a_Star, a_Star; repeat split; auto using An_Star.
  - destruct (task_binds_unerase _ _ _ b) as [s [E Hb]].
    destruct s as [U|p]; simpl in E; [ | discriminate].
    injection E as E.
    exists (a_Var_f x), U; repeat split; auto using An_Var.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H0 J eq_refl HC) as [A0 [K0 [EA [EK TK]]]];
      destruct (task_as_kind _ _ _ TK EK) as [U [EU TU]];
      assert (Hdomain : erase_tm U = A) by congruence;
      task_choose_fresh (L \u dom J \u task_vars_context J \u task_vars_tm U \u task_vars_tm B)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Tm U ++ J)) by (apply An_ConsTm; [exact HC|exact TU|fsetdec]);
          assert (Hctx : erase_context (x ~ Tm U ++ J) = x ~ Tm A ++ erase_context J)
            by (change ((x,Tm (erase_tm U))::erase_context J = (x,Tm A)::erase_context J); rewrite Hdomain; reflexivity);
          destruct (H x (ltac:(fsetdec)) _ Hctx HJ) as [B0 [T0 [EB [ET TB]]]];
          destruct (task_as_kind _ _ _ TB ET) as [V [EV TV]];
          assert (Eclose : erase_tm (task_close_t_tm x V) = B)
            by (apply task_close_t_erase_open; [fsetdec|congruence]);
          exists (a_Pi rho U (task_close_t_tm x V)), a_Star;
          split; [simpl; congruence |split; [reflexivity | eapply An_Pi with (L := dom J); [|exact TU]]];
          intros y HY;
          exact (task_ann_reclose_t J x U V a_Star (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU TV y HY))
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H0 J eq_refl HC) as [A0 [K0 [EA [EK TK]]]];
      destruct (task_as_kind _ _ _ TK EK) as [U [EU TU]];
      assert (Hdomain : erase_tm U = A) by congruence;
      task_choose_fresh (L \u dom J \u task_vars_context J \u task_vars_tm U \u task_vars_tm a \u task_vars_tm B)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Tm U ++ J)) by (apply An_ConsTm; [exact HC|exact TU|fsetdec]);
          assert (Hctx : erase_context (x ~ Tm U ++ J) = x ~ Tm A ++ erase_context J)
            by (change ((x,Tm (erase_tm U))::erase_context J = (x,Tm A)::erase_context J); rewrite Hdomain; reflexivity);
          destruct (H x (ltac:(fsetdec)) _ Hctx HJ) as [a0 [B0 [Ea [EB TB]]]];
          assert (Ebody : erase_tm (task_close_t_tm x a0) = a) by (apply task_close_t_erase_open; [fsetdec|exact Ea]);
          assert (Etype : erase_tm (task_close_t_tm x B0) = B) by (apply task_close_t_erase_open; [fsetdec|exact EB]);
          exists (a_Abs rho U (task_close_t_tm x a0)), (a_Pi rho U (task_close_t_tm x B0));
          split; [simpl; congruence |split; [simpl; congruence | eapply An_Abs with (L := L \u dom J)]];
          [ exact TU
          | intros y HY; exact (task_ann_reclose_t J x U a0 B0 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU TB y (ltac:(fsetdec)))
          | intros y HY; rewrite task_erase_open_tm, Ebody; apply r; fsetdec])
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [f [T [F [ET TF]]]];
      destruct (H0 J eq_refl HC) as [u [U [E [EU TU]]]];
      destruct (task_ann_application _ _ _ _ _ _ _ _ TF TU ET EU)
        as [f' [u' [R [FF [FE [FR HR]]]]]];
      exists (a_App f' Rel u'), R; cbn; intuition congruence
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [f [T [F [ET TF]]]];
      destruct (H0 J eq_refl HC) as [u [U [E [EU TU]]]];
      destruct (task_ann_application _ _ _ _ _ _ _ _ TF TU ET EU)
        as [f' [u' [R [FF [FE [FR HR]]]]]];
      exists (a_App f' Irrel u'), R; cbn; intuition congruence
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [u [U [E [EU TU]]]];
      destruct (H0 J eq_refl HC) as [g [A0 [B0 [K [EA [EB [EK [Q [TA TB]]]]]]]]];
      destruct (H1 J eq_refl HC) as [B1 [K1 [EB1 [EK1 TB1]]]];
      destruct (task_as_kind _ _ _ TB1 EK1) as [V [EV TV]];
      assert (TS : AnnTyping J U a_Star) by (eapply task_ann_type; exact TU);
      rewrite task_dom_erase in Q;
      destruct (task_ann_eq_reconcile J (dom J) g A0 B0 K U V a_Star a_Star Q TA TB TS TV)
        as [q HQ]; try (cbn; congruence);
      exists (a_Conv u q), V; repeat split; cbn; try congruence;
      eapply An_Conv; eassumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H0 J eq_refl HC) as [q [EQ HQ]];
      task_choose_fresh (L \u dom J \u task_vars_context J \u task_vars_constraint q \u task_vars_tm B)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Co q ++ J)) by (apply An_ConsCo; [exact HC|exact HQ|fsetdec]);
          assert (Hctx : erase_context (x ~ Co q ++ J) = x ~ Co phi ++ erase_context J)
            by (change ((x,Co (erase_constraint q))::erase_context J = (x,Co phi)::erase_context J);
                rewrite EQ; reflexivity);
          destruct (H x (ltac:(fsetdec)) _ Hctx HJ) as [B0 [T0 [EB [ET TB]]]];
          destruct (task_as_kind _ _ _ TB ET) as [V [EV TV]];
          assert (Eclose : erase_tm (task_close_c_tm x V) = B)
            by (apply task_close_c_erase_open; [fsetdec|congruence]);
          exists (a_CPi q (task_close_c_tm x V)), a_Star;
          split; [simpl; congruence |split; [reflexivity | eapply An_CPi with (L := dom J); [exact HQ|]]];
          intros y HY;
          exact (task_ann_reclose_c J x q V a_Star (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) HQ TV y HY))
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H0 J eq_refl HC) as [q [EQ HQ]];
      task_choose_fresh (L \u dom J \u task_vars_context J \u task_vars_constraint q \u task_vars_tm a \u task_vars_tm B)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Co q ++ J)) by (apply An_ConsCo; [exact HC|exact HQ|fsetdec]);
          assert (Hctx : erase_context (x ~ Co q ++ J) = x ~ Co phi ++ erase_context J)
            by (change ((x,Co (erase_constraint q))::erase_context J = (x,Co phi)::erase_context J);
                rewrite EQ; reflexivity);
          destruct (H x (ltac:(fsetdec)) _ Hctx HJ) as [a0 [B0 [Ea [EB TB]]]];
          assert (Ebody : erase_tm (task_close_c_tm x a0) = a) by (apply task_close_c_erase_open; [fsetdec|exact Ea]);
          assert (Etype : erase_tm (task_close_c_tm x B0) = B) by (apply task_close_c_erase_open; [fsetdec|exact EB]);
          exists (a_CAbs q (task_close_c_tm x a0)), (a_CPi q (task_close_c_tm x B0));
          split; [simpl; congruence |split; [simpl; congruence | eapply An_CAbs with (L := dom J)]];
          [ exact HQ
          | intros y HY; exact (task_ann_reclose_c J x q a0 B0 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) HQ TB y HY)])
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [f [T [F [ET TF]]]];
      destruct (H0 J eq_refl HC) as [g [u [v [U [Ea [Eb [EU [HQ [TA TB]]]]]]]]];
      rewrite task_dom_erase in HQ;
      destruct (task_ann_co_application _ _ _ _ _ _ _ _ _ _ _ TF HQ TA TB ET Ea Eb EU)
        as [f' [q [R [Ef [Er TR]]]]];
      exists (a_CApp f' q), R; cbn; intuition congruence
    end.
  - match goal with HB : binds F (Ax a A) toplevel, HC : AnnCtx J |- _ =>
      destruct (task_imp_sig_bind _ _ _ HB) as [-> [-> ->]];
      exists (a_Fam Fix), FixTy; repeat split; try reflexivity;
      eapply An_Fam with (a := FixDef); [exact HC | change ((Fix, Ax FixDef FixTy) = (Fix, Ax FixDef FixTy) \/ False); auto
                                      | exact task_fix_type_annotated ]
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u1 [u2 [T [E1 [E2 [ET [Q [T1 T2]]]]]]]]];
      destruct (H0 J eq_refl HC) as [h [v1 [v2 [U [F1 [F2 [EU [R [U1 U2]]]]]]]]];
      assert (WK : AnnTyping J T a_Star) by (eapply task_ann_type; exact T1);
      destruct (task_ann_eq_same_grade _ _ _ _ _ _ _ R U1 U2 WK)
        as [k [w1 [w2 [W1 [W2 [S [V1 V2]]]]]]]; [congruence|];
      exists (g_EqCong g T k), (Eq u1 w1 T), (Eq u2 w2 T);
      repeat split; try (cbn; congruence);
      eapply An_PropCong; try eassumption;
      eapply An_Wff; eauto
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [U0 [V0 [T [E1 [E2 [ET [Q [T1 T2]]]]]]]]];
      destruct (task_ann_eq_as_kind _ _ _ _ _ _ Q T1 T2 ET)
        as [q [U [V [EU [EV [HQ [TU TV]]]]]]];
      destruct (H0 J eq_refl HC) as [[a b A0] [P1 W1]];
      destruct (H1 J eq_refl HC) as [[s00 t00 B0] [P2 W2]];
      cbn in P1, P2;
      injection P1 as X1 X2 X3;
      injection P2 as Y1 Y2 Y3;
      destruct (task_ann_wff_retype _ _ _ _ _ W1 TU) as [s1 [s2 [ES1 [ES2 [S1 [S2 WU]]]]]];
        [congruence|];
      destruct (task_ann_wff_retype _ _ _ _ _ W2 TV) as [t1 [t2 [ET1 [ET2 [T01 [T02 WV]]]]]];
        [congruence|];
      exists (g_IsoConv (Eq s1 s2 U) (Eq t1 t2 V) q), (Eq s1 s2 U), (Eq t1 t2 V);
      repeat split; try (cbn; congruence);
      eapply An_IsoConv; try eassumption; congruence
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u [v [T [E1 [E2 [ET [Q [T1 T2]]]]]]]]];
      destruct (task_ann_cpi_representative _ _ _ _ _ T1 E1) as [p [X [EP [EX PX]]]];
      destruct (task_ann_cpi_representative _ _ _ _ _ T2 E2) as [q [Y [EQ [EY PY]]]];
      destruct (task_ann_eq_reconcile J D g u v T (a_CPi p X) (a_CPi q Y) a_Star a_Star Q T1 T2 PX PY)
        as [h HH]; try (cbn; congruence);
      exists (g_CPiFst h), p, q; repeat split; try assumption;
      eapply An_CPiFst; eassumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (task_binds_unerase _ _ _ b0) as [s [ES HB]];
      destruct s as [T|[u v U]]; [discriminate|];
      cbn in ES; injection ES as Ea Eb EA;
      pose proof (task_bound_type J c (Co (Eq u v U)) HC HB) as HW;
      cbn in HW;
      inversion HW as [G0 a0 b1 A0 V TU TV ET]; subst;
      assert (Q : AnnDefEq J D (g_Var_f c) u v)
        by (eapply An_Assn with (A := U); eassumption);
      assert (R : AnnDefEq J (dom J) (g_Refl2 U V (g_Refl a_Star)) U V)
        by (apply task_ann_types_agree; eauto using task_ann_type);
      destruct (task_ann_eq_force_rhs _ _ _ _ _ _ _ _ Q TU TV R)
        as [g [v' [EV [HQ HV]]]];
      exists g, u, v', U; repeat split; try assumption; congruence
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [u [U [EU [EA TU]]]];
      exists (g_Refl u), u, u, U;
      repeat split; try assumption; eapply An_Refl; eassumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [v [u [U [EV [EU [EA [Q [TV TU]]]]]]]]];
      exists (g_Sym g), u, v, U;
      repeat split; try assumption; eapply task_ann_eq_sym_same_type; eassumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u [v [U [E1 [E2 [EU [Q [TU TV]]]]]]]]];
      destruct (H0 J eq_refl HC) as [h [w [z [V [E3 [E4 [EV [R [TW TZ]]]]]]]]];
      assert (WK : AnnTyping J U a_Star) by (eapply task_ann_type; exact TU);
      destruct (task_ann_eq_same_grade _ _ _ _ _ _ _ R TW TZ WK)
        as [k [w' [z' [EW [EZ [S [TW' TZ']]]]]]]; [congruence|];
      assert (ET : AnnDefEq J D (g_Refl2 v w' (g_Refl U)) v w')
        by (eapply An_EraseEq with (A := U) (B := U); try eassumption;
            eauto using An_Refl; congruence);
      assert (EQ : AnnDefEq J D (g_Trans g (g_Refl2 v w' (g_Refl U))) u w')
        by (eapply task_ann_eq_trans_same_type; eassumption);
      exists (g_Trans (g_Trans g (g_Refl2 v w' (g_Refl U))) k), u, z', U;
      repeat split; try congruence; try assumption;
      eapply task_ann_eq_trans_same_type; eassumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [u [U [E1 [EU TU]]]];
      destruct (H0 J eq_refl HC) as [v [V [E2 [EV TV]]]];
      assert (WK : AnnTyping J U a_Star) by (eapply task_ann_type; exact TU);
      destruct (task_ann_retype _ _ _ _ TV WK) as [v' [EV' TV']]; [congruence|];
      exists (g_Beta u v'), u, v', U;
      repeat split; try congruence; try assumption;
      eapply An_Beta; try eassumption; try reflexivity;
      rewrite E1, EV', E2; assumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u0 [v0 [K [EU [EV [EK [Q [TU0 TV0]]]]]]]]];
      destruct (task_ann_eq_as_kind _ _ _ _ _ _ Q TU0 TV0 EK)
        as [q [U [V [E1 [E2 [HQ [TU TV]]]]]]];
      assert (Ed : erase_tm U = A1) by congruence;
      task_choose_fresh (L \u dom J \u task_vars_context J \u task_vars_tm U \u task_vars_tm B1 \u task_vars_tm B2)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Tm U ++ J)) by (apply An_ConsTm; [exact HC|exact TU|fsetdec]);
          assert (Hctx : erase_context (x ~ Tm U ++ J) = x ~ Tm A1 ++ erase_context J)
            by (change ((x,Tm (erase_tm U))::erase_context J = (x,Tm A1)::erase_context J); rewrite Ed; reflexivity);
          destruct (H0 x (ltac:(fsetdec)) _ Hctx HJ) as [h [s0 [midbody [K0 [E3 [E4 [EK0 [HE [TS0 TT0]]]]]]]]];
          destruct (task_ann_eq_as_kind _ _ _ _ _ _ HE TS0 TT0 EK0)
            as [k [s [rightbody [ES0 [ET0 [HK [TS TT]]]]]]];
          set (X := task_close_t_tm x s);
          set (Y := task_close_t_tm x rightbody);
          set (Z := task_push_t (g_Sym q) Y);
          assert (EX : erase_tm X = B1) by (apply task_close_t_erase_open; [fsetdec|congruence]);
          assert (EY : erase_tm Y = B2) by (apply task_close_t_erase_open; [fsetdec|congruence]);
          assert (EZ : erase_tm Z = B2) by (unfold Z, task_push_t; rewrite (proj1 task_erase_push_t); exact EY);
          assert (T1 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Tm U ++ J) (open_tm_wrt_tm X (a_Var_f y)) a_Star)
            by (intros y HY; exact (task_ann_reclose_t J x U s a_Star
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU TS y HY));
          assert (T2 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Tm U ++ J) (open_tm_wrt_tm Y (a_Var_f y)) a_Star)
            by (intros y HY; exact (task_ann_reclose_t J x U rightbody a_Star
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU TT y HY));
          destruct (task_ann_push_t J D (dom J) U V q Y a_Star TU TV HQ T2) as [M T3];
          assert (PX : AnnTyping J (a_Pi rho U X) a_Star) by (eapply An_Pi with (L := dom J); eassumption);
          assert (PY : AnnTyping J (a_Pi rho U Y) a_Star) by (eapply An_Pi with (L := dom J); eassumption);
          assert (PZ : AnnTyping J (a_Pi rho V Z) a_Star) by (eapply An_Pi with (L := M); eassumption);
          exists (g_PiCong rho q (task_close_t_co x k)), (a_Pi rho U X), (a_Pi rho V Z), a_Star;
          repeat split; try (cbn; congruence); try assumption;
          eapply An_PiCong with (L := dom J) (B2 := Y); try eassumption;
          [ intros y HY; exact (task_ann_reclose_eq_t J D x U k s rightbody
                (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU HK y HY)
          | intros y HY; unfold Z, task_push_t, open_tm_wrt_tm;
            apply (proj1 task_open_push_t) with (j := 0);
            change (task_scope_co 0 0 q);
            exact (proj1 (proj1 (proj2 (proj2 (proj2 task_ann_scope))) _ _ _ _ _ HQ)) ])
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H0 J eq_refl HC) as [A0 [K0 [EA [EK TK]]]];
      destruct (task_as_kind _ _ _ TK EK) as [U [EU TU]];
      assert (Ed : erase_tm U = A1) by congruence;
      task_choose_fresh (L \u dom J \u task_vars_context J \u task_vars_tm U \u task_vars_tm b1 \u task_vars_tm b2 \u task_vars_tm B)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Tm U ++ J)) by (apply An_ConsTm; [exact HC|exact TU|fsetdec]);
          assert (Hctx : erase_context (x ~ Tm U ++ J) = x ~ Tm A1 ++ erase_context J)
            by (change ((x,Tm (erase_tm U))::erase_context J = (x,Tm A1)::erase_context J); rewrite Ed; reflexivity);
          destruct (H x (ltac:(fsetdec)) _ Hctx HJ) as [k [s [rightbody [W [ES [ET [EW [HK [TS TT]]]]]]]]];
          set (X := task_close_t_tm x s);
          set (Y := task_close_t_tm x rightbody);
          set (T := task_close_t_tm x W);
          set (q := g_Refl U);
          set (Z := task_push_t (g_Sym q) Y);
          set (R := task_push_t (g_Sym q) T);
          assert (EX : erase_tm X = b1) by (apply task_close_t_erase_open; [fsetdec|exact ES]);
          assert (EY : erase_tm Y = b2) by (apply task_close_t_erase_open; [fsetdec|exact ET]);
          assert (EType : erase_tm T = B) by (apply task_close_t_erase_open; [fsetdec|exact EW]);
          assert (EZ : erase_tm Z = b2) by (unfold Z, task_push_t; rewrite (proj1 task_erase_push_t); exact EY);
          assert (ER : erase_tm R = B) by (unfold R, task_push_t; rewrite (proj1 task_erase_push_t); exact EType);
          assert (T1 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Tm U ++ J) (open_tm_wrt_tm X (a_Var_f y)) (open_tm_wrt_tm T (a_Var_f y)))
            by (intros y HY; exact (task_ann_reclose_t J x U s W
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU TS y HY));
          assert (T2 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Tm U ++ J) (open_tm_wrt_tm Y (a_Var_f y)) (open_tm_wrt_tm T (a_Var_f y)))
            by (intros y HY; exact (task_ann_reclose_t J x U rightbody W
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU TT y HY));
          assert (HQ : AnnDefEq J D q U U) by (eapply An_Refl; exact TU);
          destruct (task_ann_push_t J D (dom J) U U q Y T TU TU HQ T2) as [M T3];
          assert (PX : AnnTyping J (a_Abs rho U X) (a_Pi rho U T))
            by (eapply An_Abs with (L := L \u dom J); [exact TU|intros; apply T1; fsetdec|intros; rewrite task_erase_open_tm, EX; apply r; fsetdec]);
          assert (PY : AnnTyping J (a_Abs rho U Y) (a_Pi rho U T))
            by (eapply An_Abs with (L := L \u dom J); [exact TU|intros; apply T2; fsetdec|intros; rewrite task_erase_open_tm, EY; apply r0; fsetdec]);
          assert (PZ : AnnTyping J (a_Abs rho U Z) (a_Pi rho U R))
            by (eapply An_Abs with (L := L \u M); [exact TU|intros; apply T3; fsetdec|intros; rewrite task_erase_open_tm, EZ; apply r0; fsetdec]);
          assert (HQeq : AnnDefEq J D (g_AbsCong rho q (task_close_t_co x k)) (a_Abs rho U X) (a_Abs rho U Z))
            by (eapply An_AbsCong with (L := L \u dom J) (b2 := Y) (B := a_Pi rho U T); try eassumption;
                [ intros y HY; exact (task_ann_reclose_eq_t J D x U k s rightbody
                    (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) TU HK y (ltac:(fsetdec)))
                | intros y HY; unfold Z, task_push_t, open_tm_wrt_tm; apply (proj1 task_open_push_t) with (j := 0);
                  change (task_scope_tm 0 0 U); exact (proj1 (proj1 (proj2 task_ann_scope) _ _ _ TU))
                | intros; rewrite task_erase_open_tm, EX; apply r; fsetdec
                | intros; rewrite task_erase_open_tm, EZ; apply r0; fsetdec ]);
          assert (HTyEq : AnnDefEq J (dom J) (g_Refl2 (a_Pi rho U T) (a_Pi rho U R) (g_Refl a_Star))
                            (a_Pi rho U T) (a_Pi rho U R))
            by (apply task_ann_types_agree; [eapply task_ann_type; exact PX | eapply task_ann_type; exact PZ | cbn; congruence]);
          destruct (task_ann_eq_force_rhs _ _ _ _ _ _ _ _ HQeq PX PZ HTyEq) as [h [z [Ezz [He Hz]]]];
          change (erase_tm z = a_UAbs rho (erase_tm Z)) in Ezz; rewrite EZ in Ezz;
          exists h, (a_Abs rho U X), z, (a_Pi rho U T);
          repeat split; try (cbn; congruence); eassumption)
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [f [f0 [T [Ef [Ef0 [ET [Q [TF TF0]]]]]]]]];
      destruct (H0 J eq_refl HC) as [h [u [u0 [S [Eu [Eu0 [ES [E [TU TU0]]]]]]]]];
      destruct (task_pi_type _ _ _ _ _ _ TF ET) as [V [W [EV [EW [TP TV]]]]];
      destruct (task_ann_eq_same_grade _ _ _ _ _ _ _ Q TF TF0 TP)
        as [q [f1 [f2 [E1 [E2 [QF [F1 F2]]]]]]]; [cbn; congruence|];
      destruct (task_ann_eq_same_grade _ _ _ _ _ _ _ E TU TU0 TV)
        as [k [u1 [u2 [D1 [D2 [QU [U1 U2]]]]]]]; [congruence|];
      set (X := open_tm_wrt_tm W u1);
      set (Y := open_tm_wrt_tm W u2);
      assert (TX : AnnTyping J (a_App f1 Rel u1) X) by (eapply An_App; eassumption);
      assert (TY : AnnTyping J (a_App f2 Rel u2) Y) by (eapply An_App; eassumption);
      assert (QT : AnnDefEq J (dom J) (g_PiSnd (g_Refl (a_Pi Rel V W)) k) X Y)
        by (eapply An_PiSnd with (A1 := V) (A2 := V) (rho := Rel);
             [eapply An_Refl; exact TP | exact (task_ann_eq_full _ _ _ _ _ QU) | exact U1 | exact U2]);
      assert (QA : AnnDefEq J D (g_AppCong q Rel k) (a_App f1 Rel u1) (a_App f2 Rel u2))
        by (eapply An_AppCong with (g3 := g_PiSnd (g_Refl (a_Pi Rel V W)) k); eassumption);
      destruct (task_ann_eq_force_rhs _ _ _ _ _ _ _ _ QA TX TY QT) as [j [z [EZ [QZ TZ]]]];
      change (erase_tm z = a_App (erase_tm f2) Rel (erase_tm u2)) in EZ;
      assert (HX : erase_tm X = open_tm_wrt_tm B a2)
        by (unfold X; rewrite task_erase_open_tm; congruence);
      exists j, (a_App f1 Rel u1), z, X;
      repeat split; try (cbn; congruence); assumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [f [f0 [T [Ef [Ef0 [ET [Q [TF TF0]]]]]]]]];
      destruct (H0 J eq_refl HC) as [u [S [Eu [ES TU]]]];
      destruct (task_pi_type _ _ _ _ _ _ TF ET) as [V [W [EV [EW [TP TV]]]]];
      destruct (task_ann_eq_same_grade _ _ _ _ _ _ _ Q TF TF0 TP)
        as [q [f1 [f2 [E1 [E2 [QF [F1 F2]]]]]]]; [cbn; congruence|];
      destruct (task_ann_retype _ _ _ _ TU TV) as [u1 [D1 U1]]; [congruence|];
      set (X := open_tm_wrt_tm W u1);
      assert (TX : AnnTyping J (a_App f1 Irrel u1) X) by (eapply An_App; eassumption);
      assert (TY : AnnTyping J (a_App f2 Irrel u1) X) by (eapply An_App; eassumption);
      assert (HX : erase_tm X = open_tm_wrt_tm B a) by (unfold X; rewrite task_erase_open_tm; congruence);
      exists (g_AppCong q Irrel (g_Refl u1)), (a_App f1 Irrel u1), (a_App f2 Irrel u1), X;
      repeat split; try (cbn; congruence); try assumption;
      eapply An_AppCong with (g3 := g_Refl X); try eassumption;
        [eapply An_Refl; exact U1 | eapply An_Refl; eapply task_ann_type; exact TX]
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u [v [T [E1 [E2 [ET [Q [TU TV]]]]]]]]];
      destruct (task_ann_pi_eq _ _ _ _ _ _ _ _ _ _ _ Q TU TV ET E1 E2)
        as [q [U [X [V [Y [EU [EX [EV [EY [HQ [TX TY]]]]]]]]]]];
      exists (g_PiFst q), U, V, a_Star;
      repeat split; try assumption; try reflexivity;
      [eapply An_PiFst; exact HQ | inversion TX; subst; assumption | inversion TY; subst; assumption]
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u [v [T [E1 [E2 [ET [Q [TU TV]]]]]]]]];
      destruct (task_ann_pi_eq _ _ _ _ _ _ _ _ _ _ _ Q TU TV ET E1 E2)
        as [q [U [X [V [Y [EU [EX [EV [EY [HQ [TX TY]]]]]]]]]]];
      destruct (H0 J eq_refl HC) as [h [s [t1 [S [Es [Et [ES [R [TS TT]]]]]]]]];
      assert (T1 : AnnTyping J U a_Star) by (inversion TX; subst; assumption);
      assert (T2 : AnnTyping J V a_Star) by (inversion TY; subst; assumption);
      destruct (task_ann_eq_same_grade _ _ _ _ _ _ _ R TS TT T1)
        as [k [s1 [s2 [F1 [F2 [VQ [VS VT]]]]]]]; [congruence|];
      assert (QD : AnnDefEq J (dom J) (g_PiFst q) U V)
        by (eapply An_PiFst; exact (task_ann_eq_full _ _ _ _ _ HQ));
      set (s3 := a_Conv s2 (g_PiFst q));
      assert (V3 : AnnTyping J s3 V) by (eapply An_Conv; eassumption);
      assert (QE : AnnDefEq J D (g_Refl2 s2 s3 (g_PiFst q)) s2 s3)
        by (eapply An_EraseEq with (A := U) (B := V); eauto);
      set (m := g_Trans k (g_Refl2 s2 s3 (g_PiFst q)));
      assert (QM : AnnDefEq J D m s1 s3) by (eapply task_ann_eq_trans_same_type; eassumption);
      exists (g_PiSnd q m), (open_tm_wrt_tm X s1), (open_tm_wrt_tm Y s3), a_Star;
      repeat split; try reflexivity;
      [ rewrite task_erase_open_tm; congruence
      | rewrite task_erase_open_tm; cbn [s3 erase_tm]; congruence
      | eapply An_PiSnd; eassumption
      | inversion TX; subst; eapply task_ann_instantiate_t; eassumption
      | inversion TY; subst; eapply task_ann_instantiate_t; eassumption ]
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [q [pleft [pright [EP [EP' HQ]]]]];
      destruct (proj1 (proj2 (proj2 task_ann_regular)) _ _ _ _ _ HQ) as [WP WP'];
      task_choose_fresh (L \u D \u dom J \u task_vars_context J \u task_vars_constraint pleft \u task_vars_tm A \u task_vars_tm B)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Co pleft ++ J)) by (apply An_ConsCo; [exact HC|exact WP|fsetdec]);
          assert (Hctx : erase_context (x ~ Co pleft ++ J) = x ~ Co phi1 ++ erase_context J)
            by (change ((x,Co (erase_constraint pleft))::erase_context J = (x,Co phi1)::erase_context J); rewrite EP; reflexivity);
          destruct (H0 x (ltac:(fsetdec)) _ Hctx HJ) as [h [s0 [midbody [K0 [E3 [E4 [EK0 [HE [TS0 TT0]]]]]]]]];
          destruct (task_ann_eq_as_kind _ _ _ _ _ _ HE TS0 TT0 EK0)
            as [k [s [rightbody [ES0 [ET0 [HK [TS TT]]]]]]];
          set (X := task_close_c_tm x s);
          set (Y := task_close_c_tm x rightbody);
          set (Z := task_push_c (g_Sym q) Y);
          assert (EX : erase_tm X = A) by (apply task_close_c_erase_open; [fsetdec|congruence]);
          assert (EY : erase_tm Y = B) by (apply task_close_c_erase_open; [fsetdec|congruence]);
          assert (EZ : erase_tm Z = B) by (unfold Z, task_push_c; rewrite (proj1 task_erase_push_c); exact EY);
          assert (T1 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Co pleft ++ J) (open_tm_wrt_co X (g_Var_f y)) a_Star)
            by (intros y HY; exact (task_ann_reclose_c J x pleft s a_Star
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) WP TS y HY));
          assert (T2 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Co pleft ++ J) (open_tm_wrt_co Y (g_Var_f y)) a_Star)
            by (intros y HY; exact (task_ann_reclose_c J x pleft rightbody a_Star
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) WP TT y HY));
          destruct (task_ann_push_c J D (dom J) pleft pright q Y a_Star WP WP' HQ T2) as [M T3];
          assert (PX : AnnTyping J (a_CPi pleft X) a_Star) by (eapply An_CPi with (L := dom J); eassumption);
          assert (PY : AnnTyping J (a_CPi pleft Y) a_Star) by (eapply An_CPi with (L := dom J); eassumption);
          assert (PZ : AnnTyping J (a_CPi pright Z) a_Star) by (eapply An_CPi with (L := M); eassumption);
          exists (g_CPiCong q (task_close_c_co x k)), (a_CPi pleft X), (a_CPi pright Z), a_Star;
          repeat split; try (cbn; congruence); try assumption;
          eapply An_CPiCong with (L := dom J) (B2 := Y); try eassumption;
          [ intros y HY; exact (task_ann_reclose_eq_c J D x pleft k s rightbody
                (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) WP HK y HY)
          | intros y HY; unfold Z, task_push_c, open_tm_wrt_co;
            apply (proj1 task_open_push_c) with (i := 0);
            change (task_scope_co 0 0 q);
            exact (proj1 (proj1 (proj2 (proj2 task_ann_scope)) _ _ _ _ _ HQ)) ])
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H0 J eq_refl HC) as [pleft [EP WP]];
      task_choose_fresh (L \u D \u dom J \u task_vars_context J \u task_vars_constraint pleft \u task_vars_tm a \u task_vars_tm b \u task_vars_tm B)
        ltac:(fun x HX =>
          assert (HJ : AnnCtx (x ~ Co pleft ++ J)) by (apply An_ConsCo; [exact HC|exact WP|fsetdec]);
          assert (Hctx : erase_context (x ~ Co pleft ++ J) = x ~ Co phi1 ++ erase_context J)
            by (change ((x,Co (erase_constraint pleft))::erase_context J = (x,Co phi1)::erase_context J); rewrite EP; reflexivity);
          destruct (H x (ltac:(fsetdec)) _ Hctx HJ) as [k [s [rightbody [W [ES [ET [EW [HK [TS TT]]]]]]]]];
          set (X := task_close_c_tm x s);
          set (Y := task_close_c_tm x rightbody);
          set (T := task_close_c_tm x W);
          destruct (task_ann_iso_refl J D pleft WP) as [q HQ];
          set (Z := task_push_c (g_Sym q) Y);
          set (R := task_push_c (g_Sym q) T);
          assert (EX : erase_tm X = a) by (apply task_close_c_erase_open; [fsetdec|exact ES]);
          assert (EY : erase_tm Y = b) by (apply task_close_c_erase_open; [fsetdec|exact ET]);
          assert (EType : erase_tm T = B) by (apply task_close_c_erase_open; [fsetdec|exact EW]);
          assert (EZ : erase_tm Z = b) by (unfold Z, task_push_c; rewrite (proj1 task_erase_push_c); exact EY);
          assert (ER : erase_tm R = B) by (unfold R, task_push_c; rewrite (proj1 task_erase_push_c); exact EType);
          assert (T1 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Co pleft ++ J) (open_tm_wrt_co X (g_Var_f y)) (open_tm_wrt_co T (g_Var_f y)))
            by (intros y HY; exact (task_ann_reclose_c J x pleft s W
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) WP TS y HY));
          assert (T2 : forall y, y `notin` dom J ->
            AnnTyping (y ~ Co pleft ++ J) (open_tm_wrt_co Y (g_Var_f y)) (open_tm_wrt_co T (g_Var_f y)))
            by (intros y HY; exact (task_ann_reclose_c J x pleft rightbody W
                 (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) WP TT y HY));
          destruct (task_ann_push_c J D (dom J) pleft pleft q Y T WP WP HQ T2) as [M T3];
          assert (PX : AnnTyping J (a_CAbs pleft X) (a_CPi pleft T))
            by (eapply An_CAbs with (L := dom J); eassumption);
          assert (PY : AnnTyping J (a_CAbs pleft Y) (a_CPi pleft T))
            by (eapply An_CAbs with (L := dom J); eassumption);
          assert (PZ : AnnTyping J (a_CAbs pleft Z) (a_CPi pleft R))
            by (eapply An_CAbs with (L := M); eassumption);
          set (F := g_Refl2 (a_CPi pleft T) (a_CPi pleft R) (g_Refl a_Star));
          assert (HTyEq : AnnDefEq J (dom J) F (a_CPi pleft T) (a_CPi pleft R))
            by (apply task_ann_types_agree; [eapply task_ann_type; exact PX | eapply task_ann_type; exact PZ | cbn; congruence]);
          assert (HQeq : AnnDefEq J D (g_CAbsCong q (task_close_c_co x k) F) (a_CAbs pleft X) (a_CAbs pleft Z))
            by (eapply An_CAbsCong with (L := dom J) (a2 := Y) (B := a_CPi pleft T); try eassumption;
                [ intros y HY; exact (task_ann_reclose_eq_c J D x pleft k s rightbody
                    (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) (ltac:(fsetdec)) WP HK y HY)
                | intros y HY; unfold Z, task_push_c, open_tm_wrt_co; apply (proj1 task_open_push_c) with (i := 0);
                  change (task_scope_co 0 0 q); exact (proj1 (proj1 (proj2 (proj2 task_ann_scope)) _ _ _ _ _ HQ)) ]);
          destruct (task_ann_eq_force_rhs _ _ _ _ _ _ _ _ HQeq PX PZ HTyEq) as [h [z [Ezz [He Hz]]]];
          change (erase_tm z = a_UCAbs (erase_tm Z)) in Ezz; rewrite EZ in Ezz;
          exists h, (a_CAbs pleft X), z, (a_CPi pleft T);
          repeat split; try (cbn; congruence); eassumption)
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [f [f0 [T [Ef [Ef0 [ET [Q [TF TF0]]]]]]]]];
      destruct (H0 J eq_refl HC) as [h [u [v [S [Eu [Ev [ES [E [TU TV]]]]]]]]];
      rewrite task_dom_erase in E;
      destruct (task_cpi_type _ _ _ _ _ TF ET) as [[a0 b0 U] [W [EP [EW [TP WP]]]]];
      cbn in EP;
      destruct (task_ann_constraint_eq J (dom J) h u v S a0 b0 U E TU TV WP)
        as [k HK]; try congruence;
      destruct (task_ann_eq_same_grade _ _ _ _ _ _ _ Q TF TF0 TP)
        as [q [f1 [f2 [E1 [E2 [QF [F1 F2]]]]]]]; [cbn; congruence|];
      set (X := open_tm_wrt_co W k);
      assert (TX : AnnTyping J (a_CApp f1 k) X) by (eapply An_CApp; eassumption);
      assert (TY : AnnTyping J (a_CApp f2 k) X) by (eapply An_CApp; eassumption);
      assert (HX : erase_tm X = open_tm_wrt_co B g_Triv)
        by (unfold X; rewrite (task_erase_open_co _ _ g_Triv); congruence);
      exists (g_CAppCong q k k), (a_CApp f1 k), (a_CApp f2 k), X;
      repeat split; try (cbn; congruence); try assumption;
      eapply An_CAppCong with (g4 := g_Refl X); try eassumption;
      eapply An_Refl; eapply task_ann_type; exact TX
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u [v [T [E1 [E2 [ET [Q [TU TV]]]]]]]]];
      destruct (task_ann_cpi_eq _ _ _ _ _ _ _ _ _ _ Q TU TV ET E1 E2)
        as [q [[s1 t1 U] [X [[s2 t2 V] [Y [EP [EX [EP' [EY [HQ [TX TY]]]]]]]]]]];
      assert (WP : AnnPropWff J (Eq s1 t1 U)) by (inversion TX; subst; assumption);
      assert (WP' : AnnPropWff J (Eq s2 t2 V)) by (inversion TY; subst; assumption);
      destruct (H0 J eq_refl HC) as [h [u1 [v1 [T1 [EU1 [EV1 [ET1 [R1 [TU1 TV1]]]]]]]]];
      destruct (H1 J eq_refl HC) as [k [u2 [v2 [T2 [EU2 [EV2 [ET2 [R2 [TU2 TV2]]]]]]]]];
      rewrite task_dom_erase in R1, R2; cbn in EP, EP';
      destruct (task_ann_constraint_eq J (dom J) h u1 v1 T1 s1 t1 U R1 TU1 TV1 WP)
        as [q1 Hq1]; try congruence;
      destruct (task_ann_constraint_eq J (dom J) k u2 v2 T2 s2 t2 V R2 TU2 TV2 WP')
        as [q2 Hq2]; try congruence;
      exists (g_CPiSnd q q1 q2), (open_tm_wrt_co X q1), (open_tm_wrt_co Y q2), a_Star;
      repeat split; try reflexivity;
      [ rewrite (task_erase_open_co _ _ g_Triv); congruence
      | rewrite (task_erase_open_co _ _ g_Triv); congruence
      | eapply An_CPiSnd; eassumption
      | inversion TX; subst; eapply task_ann_instantiate_c; eassumption
      | inversion TY; subst; eapply task_ann_instantiate_c; eassumption ]
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u [v [T [E1 [E2 [ET [Q [TU TV]]]]]]]]];
      destruct (H0 J eq_refl HC) as [h [[s t U] [[s' t' V] [EP [EP' HQ]]]]];
      destruct (proj1 (proj2 (proj2 task_ann_regular)) _ _ _ _ _ HQ) as [WP WP'];
      cbn in EP, EP';
      destruct (task_ann_constraint_eq J D g u v T s t U Q TU TV WP)
        as [q Hq]; try congruence;
      assert (S : AnnDefEq J D (g_Cast q h) s' t') by (eapply An_Cast; eassumption);
      inversion WP' as [G0 a0 b0 A0 B0 TA TB E]; subst;
      assert (K : AnnDefEq J (dom J) (g_Refl2 V B0 (g_Refl a_Star)) V B0)
        by (apply task_ann_types_agree; eauto using task_ann_type);
      destruct (task_ann_eq_force_rhs _ _ _ _ _ _ _ _ S TA TB K) as [j [z [EZ [HZ TZ]]]];
      exists j, s', z, V;
      repeat split; try assumption; congruence
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [g [u [v [T [E1 [E2 [ET [Q [TU TV]]]]]]]]];
      destruct (H0 J eq_refl HC) as [h [p [r [S [EP [ER [ES [R [TP TR]]]]]]]]];
      rewrite task_dom_erase in R;
      destruct (task_as_kind _ _ _ TR ES) as [V [EV KV]];
      assert (KT : AnnTyping J T a_Star) by (eapply task_ann_type; exact TU);
      destruct (task_ann_eq_reconcile J (dom J) h p r S T V a_Star a_Star R TP TR KT KV)
        as [q HQ]; try (cbn; congruence);
      assert (KQ : AnnDefEq J (dom J) (g_Sym q) V T)
        by (eapply task_ann_eq_sym_same_type; eassumption);
      assert (TX : AnnTyping J (a_Conv u q) V) by (eapply An_Conv; eassumption);
      assert (TY : AnnTyping J (a_Conv v q) V) by (eapply An_Conv; eassumption);
      destruct (task_ann_eq_reconcile_at J D g u v T (a_Conv u q) (a_Conv v q) V V (g_Sym q) q
        Q TU TV TX TY eq_refl eq_refl KQ HQ) as [k HK];
      exists k, (a_Conv u q), (a_Conv v q), V;
      repeat split; try (cbn; congruence); assumption
    end.
  - lazymatch goal with HC : AnnCtx J |- _ =>
      destruct (H J eq_refl HC) as [h [[s t U] [[s' t' V] [EP [EP' HQ]]]]];
      destruct (proj1 (proj2 (proj2 task_ann_regular)) _ _ _ _ _ HQ) as [WP WP'];
      cbn in EP, EP';
      exists (g_IsoSnd h), U, V, a_Star;
      repeat split; try (cbn; congruence);
      [ eapply An_IsoSnd; exact HQ
      | inversion WP; subst; eapply task_ann_type; eassumption
      | inversion WP'; subst; eapply task_ann_type; eassumption ]
    end.
Qed.

Theorem annotation_mutual :
  (forall G a A, Typing G a A ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists a0 A0,
         (erase_tm a0) = a /\
         (erase_tm A0) = A /\
         AnnTyping G0 a0 A0) /\
  (forall G phi, PropWff G phi ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists phi0,
          erase_constraint phi0 = phi /\
          AnnPropWff G0 phi0) /\
  (forall G D p1 p2, Iso G D p1 p2 ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists g0 p1' p2',
       (erase_constraint p1') = p1 /\
       (erase_constraint p2') = p2 /\
       AnnIso G0 D g0 p1' p2') /\
  (forall G D a b A, DefEq G D a b A ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists g a0 b0 A0,
       (erase_tm a0) = a /\
       (erase_tm b0) = b /\
       (erase_tm A0) = A /\
       AnnDefEq G0 D g a0 b0 /\ AnnTyping G0 a0 A0 /\ AnnTyping G0 b0 A0) /\
  (forall G, Ctx G -> True).

Proof.
  destruct task_annotate_core as [HP [HT [HI [HE HC]]]].
  exact (conj HT (conj HP (conj HI (conj HE HC)))).
Qed.
