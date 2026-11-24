Require Import Qual.geq.
Require Import Qual.defeq.
From Stdlib Require Import Lia Relation_Operators.

Set Implicit Arguments.
Local Open Scope grade_scope.

(* Type constructors are represented by distinct constants in a lambda
   calculus. Runtime eliminators will use ordinary beta conversion. *)
Inductive consistency_constant : Set :=
| ct_type : sort -> consistency_constant
| ct_unit : consistency_constant
| ct_pi : grade -> consistency_constant
| ct_wsigma : grade -> consistency_constant
| ct_ssigma : grade -> consistency_constant
| ct_sum : consistency_constant
| ct_dummy : consistency_constant.

Inductive code : Set :=
| cv : nat -> code
| cc : consistency_constant -> code
| cl : code -> code
| ca : code -> code -> code.

Definition push {X : Type} (x : X) (f : nat -> X) (n : nat) :=
  match n with O => x | S m => f m end.

Fixpoint rename_code (f : nat -> nat) (t : code) : code :=
  match t with
  | cv n => cv (f n)
  | cc c => cc c
  | cl b => cl (rename_code (push O (fun n => S (f n))) b)
  | ca a b => ca (rename_code f a) (rename_code f b)
  end.

Definition lift_code (f : nat -> code) :=
  push (cv 0) (fun n => rename_code S (f n)).

Fixpoint subst_code (f : nat -> code) (t : code) : code :=
  match t with
  | cv n => f n
  | cc c => cc c
  | cl b => cl (subst_code (lift_code f) b)
  | ca a b => ca (subst_code f a) (subst_code f b)
  end.

Definition apply_body (b a : code) := subst_code (push a cv) b.

Local Lemma rename_code_ext : forall t f g,
  (forall n, f n = g n) -> rename_code f t = rename_code g t.
Proof.
  intro t; induction t; intros f g H; simpl; f_equal; auto.
  apply IHt. intros [|n]; simpl; auto.
Qed.

Local Lemma subst_code_ext : forall t f g,
  (forall n, f n = g n) -> subst_code f t = subst_code g t.
Proof.
  intro t; induction t; intros f g H; simpl; f_equal; auto.
  apply IHt. intros [|n]; simpl; auto. now rewrite H.
Qed.

Local Lemma rename_code_comp : forall t f g,
  rename_code f (rename_code g t) = rename_code (fun n => f (g n)) t.
Proof.
  intro t; induction t; intros f g; simpl; f_equal; auto.
  rewrite IHt. apply rename_code_ext. now intros [|n].
Qed.

Local Lemma subst_rename_code : forall t f g,
  subst_code f (rename_code g t) = subst_code (fun n => f (g n)) t.
Proof.
  intro t; induction t; intros f g; simpl; f_equal; auto.
  rewrite IHt. apply subst_code_ext. now intros [|n].
Qed.

Local Lemma rename_subst_code : forall t f g,
  rename_code f (subst_code g t) = subst_code (fun n => rename_code f (g n)) t.
Proof.
  intro t; induction t; intros f g; simpl; f_equal; auto.
  rewrite IHt. apply subst_code_ext. intros [|n]; simpl; auto.
  now rewrite !rename_code_comp.
Qed.

Local Lemma subst_code_comp : forall t f g,
  subst_code f (subst_code g t) = subst_code (fun n => subst_code f (g n)) t.
Proof.
  intro t; induction t; intros f g; simpl; f_equal; auto.
  rewrite IHt. apply subst_code_ext. intros [|n]; simpl; auto.
  now rewrite subst_rename_code, rename_subst_code.
Qed.

Local Lemma subst_code_id : forall t, subst_code cv t = t.
Proof.
  intro term; induction term as [n | c | body IH | a IHa b IHb];
    simpl; f_equal; auto.
  transitivity (subst_code cv body); [|exact IH].
  apply subst_code_ext. now intros [|n].
Qed.

Local Lemma subst_code_unshift : forall a t,
  subst_code (push a cv) (rename_code S t) = t.
Proof. intros; rewrite subst_rename_code; apply subst_code_id. Qed.

Local Lemma subst_apply_body : forall b a f,
  subst_code f (apply_body b a) =
  apply_body (subst_code (lift_code f) b) (subst_code f a).
Proof.
  intros; unfold apply_body. rewrite !subst_code_comp.
  apply subst_code_ext. intros [|n]; simpl; auto.
  symmetry. apply subst_code_unshift.
Qed.

Inductive code_parallel : code -> code -> Prop :=
| cp_var : forall n, code_parallel (cv n) (cv n)
| cp_const : forall c, code_parallel (cc c) (cc c)
| cp_lam : forall b b', code_parallel b b' -> code_parallel (cl b) (cl b')
| cp_app : forall a a' b b',
    code_parallel a a' -> code_parallel b b' ->
    code_parallel (ca a b) (ca a' b')
| cp_beta : forall b b' a a',
    code_parallel b b' -> code_parallel a a' ->
    code_parallel (ca (cl b) a) (apply_body b' a').

Local Hint Constructors code_parallel : code.
Local Lemma code_parallel_refl : forall t, code_parallel t t.
Proof. intro t; induction t; auto with code. Qed.
Local Hint Resolve code_parallel_refl : code.

Local Lemma code_parallel_rename : forall t u,
  code_parallel t u -> forall f, code_parallel (rename_code f t) (rename_code f u).
Proof.
  intros t u H; induction H; intros f; simpl; auto with code.
  unfold apply_body. rewrite rename_subst_code.
  replace (subst_code (fun n => rename_code f (push a' cv n)) b')
    with (apply_body (rename_code (push 0 (fun n => S (f n))) b') (rename_code f a')).
  - auto with code.
  - unfold apply_body. rewrite subst_rename_code.
    apply subst_code_ext. now intros [|n].
Qed.

Local Lemma code_parallel_subst : forall t u,
  code_parallel t u -> forall f g,
  (forall n, code_parallel (f n) (g n)) ->
  code_parallel (subst_code f t) (subst_code g u).
Proof.
  intros t u H; induction H; intros f g Hfg; simpl; auto with code.
  - apply cp_lam, IHcode_parallel. intros [|n]; simpl; auto with code.
    now apply code_parallel_rename.
  - rewrite subst_apply_body. apply cp_beta; auto.
    apply IHcode_parallel1. intros [|n]; simpl; auto with code.
    now apply code_parallel_rename.
Qed.

Fixpoint develop_code (t : code) : code :=
  match t with
  | cl b => cl (develop_code b)
  | ca (cl b) a => apply_body (develop_code b) (develop_code a)
  | ca f a => ca (develop_code f) (develop_code a)
  | t => t
  end.

Local Lemma develop_code_spec : forall t u,
  code_parallel t u -> code_parallel u (develop_code t).
Proof.
  intros t u H; induction H; simpl; auto with code.
  - destruct a; simpl in *; auto with code.
    inversion H; subst. inversion IHcode_parallel1; subst. auto with code.
  - unfold apply_body. apply code_parallel_subst; auto.
    intros [|n]; simpl; auto with code.
Qed.

Local Lemma code_parallel_diamond : forall t a b,
  code_parallel t a -> code_parallel t b ->
  exists c, code_parallel a c /\ code_parallel b c.
Proof. intros term a b Ha Hb; exists (develop_code term); auto using develop_code_spec. Qed.

Local Notation code_steps := (clos_refl_trans_1n code code_parallel).
Local Definition code_eq (a b : code) :=
  exists c, code_steps a c /\ code_steps b c.

Local Hint Constructors clos_refl_trans_1n : code.

Local Lemma code_steps_trans : forall a b c,
  code_steps a b -> code_steps b c -> code_steps a c.
Proof. intros a b c H; induction H; intro Hlast; eauto with code. Qed.

Local Lemma code_steps_strip : forall t a b,
  code_parallel t a -> code_steps t b ->
  exists c, code_steps a c /\ code_parallel b c.
Proof.
  intros t a b Ha Hb. revert a Ha. induction Hb; intros a Ha.
  - exists a; auto with code.
  - destruct (code_parallel_diamond Ha H) as (d & Had & Hyd).
    destruct (IHHb _ Hyd) as (e & Hde & Hze). exists e; eauto with code.
Qed.

Local Lemma code_steps_confluent : forall t a b,
  code_steps t a -> code_steps t b ->
  exists c, code_steps a c /\ code_steps b c.
Proof.
  intros t a b Ha; revert b; induction Ha; intros b Hb.
  - exists b; auto with code.
  - destruct (code_steps_strip H Hb) as (d & Hyd & Hbd).
    destruct (IHHa _ Hyd) as (e & Hze & Hde). exists e; eauto with code.
Qed.

Local Lemma code_eq_refl : forall a, code_eq a a.
Proof. unfold code_eq; eauto with code. Qed.
Local Lemma code_eq_sym : forall a b, code_eq a b -> code_eq b a.
Proof. unfold code_eq; firstorder. Qed.
Local Lemma code_eq_trans : forall a b c,
  code_eq a b -> code_eq b c -> code_eq a c.
Proof.
  intros a b c (d & Had & Hbd) (e & Hbe & Hce).
  destruct (code_steps_confluent Hbd Hbe) as (f & Hdf & Hef).
  exists f; eauto using code_steps_trans.
Qed.
Local Lemma code_eq_parallel : forall a b, code_parallel a b -> code_eq a b.
Proof. intros; exists b; eauto with code. Qed.
Local Hint Resolve code_eq_refl code_eq_parallel : code.

Local Lemma code_steps_lam : forall a b, code_steps a b ->
  code_steps (cl a) (cl b).
Proof. intros a b H; induction H; eauto with code. Qed.

Local Lemma code_steps_app : forall a a' b b',
  code_steps a a' -> code_steps b b' -> code_steps (ca a b) (ca a' b').
Proof.
  intros a a' b b' Ha Hb. induction Ha.
  - induction Hb; eauto with code.
  - eauto with code.
Qed.

Local Lemma code_eq_lam : forall a b, code_eq a b -> code_eq (cl a) (cl b).
Proof. intros a b (c & Hac & Hbc); exists (cl c); auto using code_steps_lam. Qed.

Local Lemma code_eq_app : forall a a' b b',
  code_eq a a' -> code_eq b b' -> code_eq (ca a b) (ca a' b').
Proof.
  intros a a' b b' (c & Hac & Hac') (d & Hbd & Hbd').
  exists (ca c d); auto using code_steps_app.
Qed.

Local Lemma code_eq_rename : forall a b,
  code_eq a b -> forall f, code_eq (rename_code f a) (rename_code f b).
Proof.
  assert (H : forall a b, code_steps a b -> forall f,
    code_steps (rename_code f a) (rename_code f b)).
  { intros a b H; induction H; eauto using code_parallel_rename with code. }
  intros a b (c & Hac & Hbc) f. exists (rename_code f c); auto.
Qed.

Local Lemma code_eq_beta : forall b a, code_eq (ca (cl b) a) (apply_body b a).
Proof. auto with code. Qed.
Local Hint Resolve code_eq_lam code_eq_app code_eq_rename code_eq_beta : code.

(* A constant and its left-associated arguments survive every reduction.
   This gives both discrimination and injectivity for type constructors. *)
Fixpoint spine (c : consistency_constant) (args : list code) : code :=
  match args with
  | nil => cc c
  | a :: rest => ca (spine c rest) a
  end.

Local Lemma code_parallel_spine : forall args c u,
  code_parallel (spine c args) u ->
  exists args', u = spine c args' /\ Forall2 code_parallel args args'.
Proof.
  induction args as [|a args IH]; intros c u H; simpl in H.
  - inversion H; subst. exists nil; auto.
  - remember (spine c args) as f eqn:Ef in H.
    inversion H; subst.
    + match goal with
      | Hp : code_parallel (spine c args) _ |- _ =>
          destruct (IH _ _ Hp) as (args' & -> & Hargs)
      end.
      eexists (_ :: args'); split; [reflexivity|constructor; assumption].
    + destruct args; discriminate.
Qed.

Local Lemma code_steps_spine : forall t u, code_steps t u ->
  forall c args, t = spine c args ->
  exists args', u = spine c args' /\ Forall2 code_steps args args'.
Proof.
  intros t u H; induction H; intros c args ->.
  - exists args; split; auto. induction args; auto with code.
  - destruct (code_parallel_spine args c H) as (args' & Heq & Hpar).
    destruct (IHclos_refl_trans_1n _ _ Heq) as (args'' & -> & Hmulti).
    exists args''; split; auto.
    clear IHclos_refl_trans_1n H0 Heq H. revert args'' Hmulti. induction Hpar; intros args'' Hmulti;
      inversion Hmulti; subst; eauto with code.
Qed.

Local Lemma spine_inj : forall args args' c c',
  spine c args = spine c' args' -> c = c' /\ args = args'.
Proof.
  induction args as [|a args IH]; intros [|a' args'] c c' H; simpl in H;
    try discriminate.
  - now inversion H.
  - injection H as Hf Ha. destruct (IH _ _ _ Hf) as (-> & ->). now subst.
Qed.

Local Lemma code_eq_spine : forall c c' args args',
  code_eq (spine c args) (spine c' args') ->
  c = c' /\ Forall2 code_eq args args'.
Proof.
  intros c c' args args' (u & H1 & H2).
  destruct (code_steps_spine H1 c args Logic.eq_refl) as (xs & E & R).
  destruct (code_steps_spine H2 c' args' Logic.eq_refl) as (ys & E' & R').
  rewrite E in E'. destruct (spine_inj xs ys c c' E') as (-> & <-).
  split; auto. clear H1 H2 E E'. revert args' R'. induction R; intros args' R';
    inversion R'; subst; constructor; eauto. now exists y.
Qed.

Local Lemma code_steps_lam_inv : forall t u, code_steps t u ->
  forall b, t = cl b -> exists b', u = cl b' /\ code_steps b b'.
Proof.
  intros t u H; induction H; intros b ->.
  - exists b; auto with code.
  - inversion H; subst. destruct (IHclos_refl_trans_1n _ Logic.eq_refl) as (out & -> & Hb').
    exists out; eauto with code.
Qed.

Local Lemma code_eq_lam_inv : forall a b,
  code_eq (cl a) (cl b) -> code_eq a b.
Proof.
  intros a b (c & Hac & Hbc).
  destruct (code_steps_lam_inv Hac Logic.eq_refl) as (a' & -> & Ha').
  destruct (code_steps_lam_inv Hbc Logic.eq_refl) as (b' & E & Hb').
  injection E as ->. now exists b'.
Qed.

Local Lemma code_eq_apply_body : forall b b' a a',
  code_eq b b' -> code_eq a a' -> code_eq (apply_body b a) (apply_body b' a').
Proof.
  intros. eapply code_eq_trans; [apply code_eq_sym, code_eq_beta|].
  eapply code_eq_trans with (b := ca (cl b') a');
    [apply code_eq_app; auto with code|apply code_eq_beta].
Qed.

(* Numeric scoping also applies to unopened bodies. *)
Local Fixpoint scoped (k : nat) (a : tm) : Prop :=
  match a with
  | a_Var_b n => (n < k)%nat
  | a_Pi _ a b | a_Abs _ a b | a_WSigma _ a b | a_SSigma _ a b
  | a_LetPair _ a b => scoped k a /\ scoped (S k) b
  | a_App a _ b | a_WPair a _ b | a_SPair a _ b | a_Sum a b =>
      scoped k a /\ scoped k b
  | a_Case _ a b c => scoped k a /\ scoped k b /\ scoped k c
  | a_Inj1 a | a_Inj2 a | a_Proj1 _ a | a_Proj2 _ a => scoped k a
  | _ => True
  end.

Local Lemma scoped_mono : forall a k j,
  scoped k a -> (k <= j)%nat -> scoped j a.
Proof.
  intro a; induction a; simpl; intros; intuition eauto with arith.
Qed.

Local Lemma scoped_open_rec : forall b k a,
  scoped (S k) b -> scoped k a -> scoped k (open_tm_wrt_tm_rec k a b).
Proof.
  intro b; induction b; simpl; intros k a Hb Ha;
    try solve [intuition eauto using scoped_mono with arith].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto; try lia.
Qed.

Local Lemma scoped_open_inv : forall b k a,
  scoped k (open_tm_wrt_tm_rec k a b) -> scoped (S k) b.
Proof.
  intro b; induction b; simpl; intros k a H;
    try solve [intuition eauto].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl in *; lia.
Qed.

Local Lemma lc_scoped : forall a, lc_tm a -> scoped 0 a.
Proof.
  intros a H; induction H; simpl; auto.
  all: split; auto; eapply scoped_open_inv with (a := a_Var_f (fresh nil));
    unfold open_tm_wrt_tm in *; auto.
Qed.

Local Fixpoint tm_size (a : tm) : nat :=
  match a with
  | a_Pi _ a b | a_Abs _ a b | a_WSigma _ a b | a_SSigma _ a b
  | a_App a _ b | a_WPair a _ b | a_SPair a _ b | a_Sum a b
  | a_LetPair _ a b => S (tm_size a + tm_size b)
  | a_Case _ a b c => S (tm_size a + tm_size b + tm_size c)
  | a_Inj1 a | a_Inj2 a | a_Proj1 _ a | a_Proj2 _ a => S (tm_size a)
  | _ => 0
  end.

Local Lemma tm_size_open_var : forall b k x,
  tm_size (open_tm_wrt_tm_rec k (a_Var_f x) b) = tm_size b.
Proof.
  intro b; induction b; intros k z; simpl; try now rewrite ?IHb, ?IHb1, ?IHb2, ?IHb3.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Local Lemma scoped_lc : forall a, scoped 0 a -> lc_tm a.
Proof.
  assert (H : forall n a, (tm_size a < n)%nat -> scoped 0 a -> lc_tm a).
  { induction n as [|n IH]; intros a Hn Ha; [lia|].
    destruct a; simpl in *; try lia; try solve [constructor].
    all: constructor; intuition idtac;
      first [eapply IH; [simpl in *; lia|assumption]
            |intros z; eapply IH;
               [unfold open_tm_wrt_tm; rewrite tm_size_open_var; lia
               |apply scoped_open_rec; simpl; auto]]. }
  intros a Ha; apply (H (S (tm_size a)) a); [lia|assumption].
Qed.

Local Lemma scoped_cofinite : forall b (L : atoms),
  (forall x, x `notin` L -> scoped 0 (open_tm_wrt_tm b (a_Var_f x))) ->
  scoped 1 b.
Proof.
  intros b L H; pick fresh x for L.
  apply (@scoped_open_inv b 0 (a_Var_f x)), H; assumption.
Qed.

Local Lemma scoped_cofinite_pair : forall b1 b2 (L : atoms),
  (forall x, x `notin` L ->
     scoped 0 (open_tm_wrt_tm b1 (a_Var_f x)) /\
     scoped 0 (open_tm_wrt_tm b2 (a_Var_f x))) ->
  scoped 1 b1 /\ scoped 1 b2.
Proof.
  intros b1 b2 L H; pick fresh x for L.
  specialize (H x ltac:(assumption)) as [H1 H2].
  split; eapply scoped_open_inv; eassumption.
Qed.

Scheme grade_ind_mut := Induction for Grade Sort Prop
  with cgrade_ind_mut := Induction for CGrade Sort Prop.
Scheme defeq_ind_mut := Induction for DefEq Sort Prop
  with cdefeq_ind_mut := Induction for CDefEq Sort Prop.

Local Lemma grade_scoped : forall P g a, Grade P g a -> scoped 0 a.
Proof.
  apply (grade_ind_mut (fun (_ : econtext) (_ : grade) a (_ : Grade _ _ a) => scoped 0 a)
    (fun (_ : econtext) (_ _ : grade) a (_ : CGrade _ _ _ a) => scoped 0 a));
    simpl; intros; intuition eauto using lc_scoped.
  all: eapply scoped_cofinite; eassumption.
Qed.

Local Lemma defeq_scoped : forall P g a b, DefEq P g a b ->
  scoped 0 a /\ scoped 0 b.
Proof.
  apply (defeq_ind_mut (fun _ _ a b _ => scoped 0 a /\ scoped 0 b)
    (fun _ _ _ a b _ => scoped 0 a /\ scoped 0 b));
    simpl; intros; intuition eauto using lc_scoped, grade_scoped, scoped_open_rec.
  all: multimatch goal with
  | H : _ |- _ => destruct (@scoped_cofinite_pair _ _ _ H)
  end.
  all: intuition eauto using scoped_open_rec, lc_scoped.
Qed.

(* The runtime forms use Church pairs and injections. Type forms instead
   retain their constants, so conversion can recover their components. *)
Local Definition dummy := cc ct_dummy.
Local Definition pair_code a b :=
  ca (ca (cl (cl (cl (ca (ca (cv 0) (cv 2)) (cv 1))))) a) b.
Local Definition left_code a := ca (cl (cl (cl (ca (cv 1) (cv 2))))) a.
Local Definition right_code a := ca (cl (cl (cl (ca (cv 0) (cv 2))))) a.
Local Definition first_code a := ca a (cl (cl (cv 1))).
Local Definition second_code a := ca a (cl (cl (cv 0))).
Local Definition visible (g q : grade) (a : code) :=
  if q <=? g then a else dummy.
Local Definition shift_env {X : Type} (env : X -> code) :=
  fun x => rename_code S (env x).

Local Fixpoint translate (g : grade) (F : atom -> code)
    (B : nat -> code) (a : tm) : code :=
  let tr := translate g F B in
  let body b := cl (translate g (shift_env F) (lift_code B) b) in
  match a with
  | a_TyUnit => cc ct_unit
  | a_TmUnit => dummy
  | a_Type s => cc (ct_type s)
  | a_Var_b n => B n
  | a_Var_f x => F x
  | a_Pi q a b => spine (ct_pi q) (body b :: tr a :: nil)
  | a_WSigma q a b => spine (ct_wsigma q) (body b :: tr a :: nil)
  | a_SSigma q a b => spine (ct_ssigma q) (body b :: tr a :: nil)
  | a_Sum a b => spine ct_sum (tr b :: tr a :: nil)
  | a_Abs _ _ b => body b
  | a_App a q b => ca (tr a) (visible g q (tr b))
  | a_WPair a q b | a_SPair a q b => pair_code (visible g q (tr a)) (tr b)
  | a_LetPair _ a b => ca (tr a) (body b)
  | a_Proj1 _ a => first_code (tr a)
  | a_Proj2 _ a => second_code (tr a)
  | a_Inj1 a => left_code (tr a)
  | a_Inj2 a => right_code (tr a)
  | a_Case _ a b c => ca (ca (tr a) (tr b)) (tr c)
  end.

Local Ltac split_code_equalities :=
  repeat first
    [ solve [reflexivity]
    | match goal with
      | |- ca _ _ = ca _ _ => f_equal
      | |- cl _ = cl _ => f_equal
      end ].

Local Lemma translate_ext : forall a g F F' B B',
  (forall x, x `in` fv_tm_tm a -> F x = F' x) ->
  (forall n, B n = B' n) ->
  translate g F B a = translate g F' B' a.
Proof.
  intro a; induction a; simpl; intros g F F' B B' HF HB;
    unfold visible, pair_code, first_code, second_code, left_code, right_code;
    try destruct (psi <=? g); try reflexivity;
    try solve [apply HB | apply HF; fsetdec].
  all: split_code_equalities;
    first [apply IHa | apply IHa1 | apply IHa2 | apply IHa3].
  all: unfold shift_env, lift_code; intros; try destruct n; simpl;
    try rewrite HB; auto; try solve [rewrite HF; [reflexivity|fsetdec]].
Qed.

Local Lemma translate_bound_ext : forall a g F B B' k,
  scoped k a -> (forall n, (n < k)%nat -> B n = B' n) ->
  translate g F B a = translate g F B' a.
Proof.
  intro a; induction a; simpl; intros g F B B' k Hs HB;
    unfold visible, pair_code, first_code, second_code, left_code, right_code;
    try destruct (psi <=? g); try reflexivity; try solve [auto].
  all: split_code_equalities;
    first [eapply IHa | eapply IHa1 | eapply IHa2 | eapply IHa3].
  all: intuition eauto.
  all: destruct n; simpl; try reflexivity; rewrite HB; auto with arith.
Qed.

Local Lemma translate_subst : forall a g F B f,
  subst_code f (translate g F B a) =
  translate g (fun x => subst_code f (F x)) (fun n => subst_code f (B n)) a.
Proof.
  intro a; induction a; intros g F B f; cbn [translate spine];
    unfold pair_code, left_code, right_code, first_code, second_code, visible, dummy;
    try destruct (psi <=? g);
    cbn [subst_code lift_code push rename_code];
    try rewrite IHa; try rewrite IHa1; try rewrite IHa2; try rewrite IHa3;
    try reflexivity.
  all: split_code_equalities;
    apply translate_ext; unfold shift_env, lift_code; intros;
    try destruct n; simpl; try reflexivity;
    now rewrite subst_rename_code, rename_subst_code.
Qed.

Local Lemma translate_shift : forall a g F B,
  rename_code S (translate g F B a) =
  translate g (shift_env F) (shift_env B) a.
Proof.
  intros. rewrite <- (subst_code_id (rename_code S _)), subst_rename_code.
  rewrite translate_subst. apply translate_ext; intros;
    rewrite <- subst_rename_code; apply subst_code_id.
Qed.

Local Lemma translate_apply : forall b g F B v,
  apply_body (translate g (shift_env F) (lift_code B) b) v =
  translate g F (push v B) b.
Proof.
  intros. unfold apply_body. rewrite translate_subst.
  apply translate_ext; unfold shift_env; intros; try destruct n;
    simpl; auto using subst_code_unshift.
Qed.

Local Definition insert_code k (v : code) (B : nat -> code) n :=
  match lt_eq_lt_dec n k with
  | inleft (left _) => B n
  | inleft (right _) => v
  | inright _ => B (n - 1)
  end.

Local Lemma lift_insert_code : forall k v B n,
  lift_code (insert_code k v B) n =
  insert_code (S k) (rename_code S v) (lift_code B) n.
Proof.
  intros k v B [|n]; unfold insert_code, lift_code, push.
  - destruct (lt_eq_lt_dec 0 (S k)) as [[?|?]|?]; auto; lia.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?];
      destruct (lt_eq_lt_dec (S n) (S k)) as [[?|?]|?];
      try lia; try reflexivity.
    destruct n; [lia|simpl; now rewrite Nat.sub_0_r].
Qed.

Local Lemma insert_code_zero : forall v B n,
  insert_code 0 v B n = push v B n.
Proof.
  intros v B [|n]; unfold insert_code, push;
    destruct lt_eq_lt_dec as [[?|?]|?]; simpl; try lia; auto.
  now rewrite Nat.sub_0_r.
Qed.

Local Lemma translate_open_rec : forall b k a g F B,
  scoped 0 a ->
  translate g F B (open_tm_wrt_tm_rec k a b) =
  translate g F (insert_code k (translate g F B a) B) b.
Proof.
  intro b; induction b; intros k a g F B Ha; cbn [open_tm_wrt_tm_rec translate spine];
    try solve [unfold insert_code; destruct lt_eq_lt_dec as [[?|?]|?]; reflexivity];
    try (rewrite IHb by assumption);
    try (rewrite IHb1 by assumption);
    try (rewrite IHb2 by assumption);
    try (rewrite IHb3 by assumption);
    try reflexivity.
  all: unfold visible, pair_code, first_code, second_code, left_code, right_code;
    try destruct (psi <=? g); split_code_equalities.
  all: apply translate_ext; intros; [reflexivity|].
  all: assert (Hshift : translate g (shift_env F) (lift_code B) a =
                       rename_code S (translate g F B a)).
  all: try solve [rewrite translate_shift; apply translate_bound_ext with (k := 0); auto; lia].
  all: now rewrite Hshift, lift_insert_code.
Qed.

Local Lemma translate_open : forall b a g F B,
  scoped 0 a ->
  translate g F B (open_tm_wrt_tm b a) =
  translate g F (push (translate g F B a) B) b.
Proof.
  intros. unfold open_tm_wrt_tm. rewrite translate_open_rec by assumption.
  apply translate_ext; auto using insert_code_zero.
Qed.

Local Definition update_env (F : atom -> code) x v y :=
  if eq_var y x then v else F y.

Local Lemma translate_open_fresh : forall b g F B x v,
  x `notin` fv_tm_tm b ->
  translate g (update_env F x v) B (open_tm_wrt_tm b (a_Var_f x)) =
  translate g F (push v B) b.
Proof.
  intros. rewrite translate_open by exact I.
  simpl. unfold update_env. destruct (eq_var x x); [|contradiction].
  apply translate_ext; intros; auto.
  destruct (eq_var x0 x); subst; auto; contradiction.
Qed.

Local Definition related (P : econtext) (g : grade) (F F' : atom -> code) :=
  forall x q, binds x q P -> q <= g -> code_eq (F x) (F' x).

Local Definition meaning (P : econtext) g a b :=
  forall F F' B, related P g F F' ->
  code_eq (translate g F B a) (translate g F' B b).

Local Lemma related_refl : forall P g F, related P g F F.
Proof. unfold related; auto with code. Qed.

Local Lemma related_sym : forall P g F F', related P g F F' -> related P g F' F.
Proof. unfold related; intros; apply code_eq_sym; eauto. Qed.

Local Lemma related_shift : forall P g F F',
  related P g F F' -> related P g (shift_env F) (shift_env F').
Proof. unfold related, shift_env; intros; apply code_eq_rename; eauto. Qed.

Local Lemma related_update : forall P g q F F' x v v',
  x `notin` dom P -> related P g F F' -> (q <= g -> code_eq v v') ->
  related ((x, q) :: P) g (update_env F x v) (update_env F' x v').
Proof.
  unfold related, update_env. intros P g q F F' x v v' Hx HF Hv y r Hy Hr.
  apply binds_cons_1 in Hy as [[-> ->]|Hy].
  - destruct (eq_var x x); auto; contradiction.
  - destruct (eq_var y x) as [->|Hne].
    + exfalso. apply Hx. eauto using binds_In.
    + eapply HF; eassumption.
Qed.

Local Lemma body_meaning : forall P g q L b b',
  (forall x, x `notin` L ->
    meaning ((x, q) :: P) g (open_tm_wrt_tm b (a_Var_f x))
                            (open_tm_wrt_tm b' (a_Var_f x))) ->
  forall F F' B v v', related P g F F' ->
  (q <= g -> code_eq v v') ->
  code_eq (translate g F (push v B) b) (translate g F' (push v' B) b').
Proof.
  intros P g q L b b' H F F' B v v' HF Hv.
  pick fresh x for (L `union` dom P `union` fv_tm_tm b `union` fv_tm_tm b').
  specialize (H x ltac:(solve_notin) (update_env F x v) (update_env F' x v') B).
  rewrite !translate_open_fresh in H by solve_notin.
  apply H. eapply related_update; eauto.
Qed.

Local Lemma lambda_meaning : forall P g q L b b',
  (forall x, x `notin` L ->
    meaning ((x, q) :: P) g (open_tm_wrt_tm b (a_Var_f x))
                            (open_tm_wrt_tm b' (a_Var_f x))) ->
  forall F F' B, related P g F F' ->
  code_eq (cl (translate g (shift_env F) (lift_code B) b))
          (cl (translate g (shift_env F') (lift_code B) b')).
Proof.
  intros P g q L b b' Hb F F' B HF.
  apply code_eq_lam.
  eapply body_meaning with (q := q);
    [exact Hb|apply related_shift; exact HF|auto with code].
Qed.

Local Lemma visible_eq : forall g q a b, (q <= g -> code_eq a b) ->
  code_eq (visible g q a) (visible g q b).
Proof.
  unfold visible, is_true. intros g q a b H.
  destruct (q <=? g); simpl in *; auto with code.
Qed.

Local Ltac code_congruence :=
  unfold pair_code, first_code, second_code, left_code, right_code;
  repeat first [solve [apply code_eq_refl] | apply code_eq_app | apply visible_eq].

Local Lemma grade_meaning : forall P g a, Grade P g a -> meaning P g a a.
Proof.
  apply (grade_ind_mut (fun P g a _ => meaning P g a a)
    (fun P g q a _ => q <= g -> meaning P g a a)).
  all: unfold meaning; intros; cbn [translate spine].
  all: try solve [contradiction | eapply H; eassumption].
  all: code_congruence; intros.
  all: try solve [eauto].
  all: first [solve [eapply lambda_meaning with (q := psi) (L := L) (P := P); eassumption]
             |solve [eapply lambda_meaning with (q := psi0) (L := L) (P := P); eassumption]].
Qed.

Local Lemma subst_lift_shift : forall f a,
  subst_code (lift_code f) (rename_code S a) = rename_code S (subst_code f a).
Proof. intros; now rewrite subst_rename_code, rename_subst_code. Qed.

Local Lemma apply_body_unshift : forall a t, apply_body (rename_code S t) a = t.
Proof. exact subst_code_unshift. Qed.

Local Ltac beta_on_code :=
  first [apply code_eq_beta | apply code_eq_app; [beta_on_code | apply code_eq_refl]].

Local Ltac reduce_code :=
  eapply code_eq_trans; [solve [beta_on_code]|];
  cbn [apply_body subst_code lift_code push rename_code];
  repeat rewrite subst_lift_shift;
  repeat rewrite subst_code_unshift;
  repeat rewrite apply_body_unshift.

Local Lemma pair_code_elim : forall a b f,
  code_eq (ca (pair_code a b) f) (ca (ca f a) b).
Proof.
  intros; unfold pair_code; reduce_code; reduce_code; reduce_code; apply code_eq_refl.
Qed.

Local Lemma first_code_pair : forall a b,
  code_eq (first_code (pair_code a b)) a.
Proof.
  intros; unfold first_code. eapply code_eq_trans; [apply pair_code_elim|].
  reduce_code; reduce_code; apply code_eq_refl.
Qed.

Local Lemma second_code_pair : forall a b,
  code_eq (second_code (pair_code a b)) b.
Proof.
  intros; unfold second_code. eapply code_eq_trans; [apply pair_code_elim|].
  reduce_code; reduce_code; apply code_eq_refl.
Qed.

Local Lemma left_code_elim : forall a l r,
  code_eq (ca (ca (left_code a) l) r) (ca l a).
Proof.
  intros; unfold left_code; reduce_code; reduce_code; reduce_code; apply code_eq_refl.
Qed.

Local Lemma right_code_elim : forall a l r,
  code_eq (ca (ca (right_code a) l) r) (ca r a).
Proof.
  intros; unfold right_code; reduce_code; reduce_code; reduce_code; apply code_eq_refl.
Qed.

Local Lemma visible_leq : forall g q a, q <= g -> visible g q a = a.
Proof. unfold visible, is_true; intros; now rewrite H. Qed.

Local Lemma visible_bot : forall g a, visible g q_Bot a = a.
Proof.
  intros; apply visible_leq, leq_meet. rewrite meet_comm. apply meet_Bot_r.
Qed.

(* A graded body accepts arbitrary different arguments at an invisible
   grade. This also applies to the first component of a weak pair. *)
Local Lemma grade_body_argument : forall P g q L b F B v v',
  (forall x, x `notin` L ->
    Grade ((x, q) :: P) g (open_tm_wrt_tm b (a_Var_f x))) ->
  (q <= g -> code_eq v v') ->
  code_eq (translate g F (push v B) b) (translate g F (push v' B) b).
Proof.
  intros. eapply body_meaning with (q := q) (L := L);
    eauto using grade_meaning, related_refl.
Qed.

Local Lemma visible_argument : forall g q v, q <= g -> code_eq (visible g q v) v.
Proof. intros; rewrite visible_leq by assumption; apply code_eq_refl. Qed.

Local Lemma translate_beta : forall P g q L b a F B,
  (forall x, x `notin` L -> Grade ((x, q) :: P) g
    (open_tm_wrt_tm b (a_Var_f x))) ->
  lc_tm a ->
  code_eq
    (ca (cl (translate g (shift_env F) (lift_code B) b))
      (visible g q (translate g F B a)))
    (translate g F B (open_tm_wrt_tm b a)).
Proof.
  intros. eapply code_eq_trans; [apply code_eq_beta|].
  rewrite translate_apply, translate_open by auto using lc_scoped.
  eapply grade_body_argument; eauto using visible_argument.
Qed.

Local Lemma step_meaning : forall a b, Step a b ->
  forall P g F B, Grade P g a ->
  code_eq (translate g F B a) (translate g F B b).
Proof.
  intros a b H; induction H; intros P g F B HG; cbn [translate].
  - inversion HG; subst. apply code_eq_app; eauto with code.
  - inversion HG; subst.
    match goal with
    | Habs : Grade _ _ (a_Abs _ _ _) |- _ => inversion Habs; subst
    end.
    eapply translate_beta with (P := P) (L := L); eassumption.
  - inversion HG; subst. apply code_eq_app; auto with code.
    apply code_eq_app; eauto with code.
  - inversion HG; subst. rewrite visible_leq by assumption. apply left_code_elim.
  - inversion HG; subst. rewrite visible_leq by assumption. apply right_code_elim.
  - inversion HG; subst. unfold first_code. apply code_eq_app; eauto with code.
  - inversion HG; subst. unfold second_code. apply code_eq_app; eauto with code.
  - inversion HG; subst. rewrite visible_leq by assumption. apply first_code_pair.
  - apply second_code_pair.
  - inversion HG; subst. apply code_eq_app; eauto with code.
  - inversion HG; subst. rewrite visible_bot.
    eapply code_eq_trans; [apply pair_code_elim|].
    apply code_eq_app; [eapply translate_beta with (P := P) (L := L); eassumption|apply code_eq_refl].
Qed.

Local Lemma code_eq_binary : forall c d a b a' b',
  code_eq (ca (ca (cc c) a) b) (ca (ca (cc d) a') b') ->
  c = d /\ code_eq a a' /\ code_eq b b'.
Proof.
  intros c d a b a' b' H.
  destruct (code_eq_spine c d (b :: a :: nil) (b' :: a' :: nil) H) as [Htag Hargs].
  inversion Hargs as [|u v xs ys Hsecond Hrest]; subst.
  inversion Hrest; subst; auto.
Qed.

Local Lemma code_eq_open : forall g b a b' a' F F' B,
  scoped 0 a -> scoped 0 a' ->
  code_eq (cl (translate g (shift_env F) (lift_code B) b))
          (cl (translate g (shift_env F') (lift_code B) b')) ->
  code_eq (translate g F B a) (translate g F' B a') ->
  code_eq (translate g F B (open_tm_wrt_tm b a))
          (translate g F' B (open_tm_wrt_tm b' a')).
Proof.
  intros. rewrite !translate_open by assumption. rewrite <- !translate_apply.
  apply code_eq_apply_body; auto using code_eq_lam_inv.
Qed.

Local Lemma defeq_meaning : forall P g a b, DefEq P g a b -> meaning P g a b.
Proof.
  apply (defeq_ind_mut (fun P g a b _ => meaning P g a b)
    (fun P g q a b _ => q <= g -> meaning P g a b)).
  all: unfold meaning; intros.
  all: try solve [contradiction | apply code_eq_refl].
  { exact (grade_meaning g B H). }
  { eapply code_eq_trans; [apply H; eassumption|apply H0, related_refl]. }
  { apply code_eq_sym, H, related_sym; assumption. }
  { eapply code_eq_trans; [eapply step_meaning; eassumption|].
    eapply grade_meaning; eassumption. }
  all: cbn [translate spine]; code_congruence; intros.
  all: try solve [eauto].
  all: try solve
    [eapply lambda_meaning with (q := psi) (L := L) (P := P); eassumption
    |eapply lambda_meaning with (q := psi0) (L := L) (P := P); eassumption].
  (* Injectivity is valid because conversion preserves constant spines. *)
  1-8: pose proof (H F F' B ltac:(assumption)) as Hpair.
  1-8: cbn [translate spine] in Hpair.
  1-8: apply code_eq_binary in Hpair as (_ & Hfirst & Hsecond).
  all: try assumption.
  1-3: apply code_eq_open; try assumption; try solve [eauto using grade_scoped].
  1,2,4,5: destruct (defeq_scoped d0); assumption.
  { eapply grade_meaning; eassumption. }
  (* An invisible variable imposes no condition on the two arguments. *)
  rewrite !translate_open by auto using lc_scoped.
  eapply body_meaning with (P := P) (q := psi) (L := L);
    [eassumption|assumption|contradiction].
Qed.

Local Lemma value_type_dec : forall a, lc_tm a -> {ValueType a} + {~ ValueType a}.
Proof.
  intros a Ha; destruct a;
    first [left; inversion Ha; subst; constructor; assumption
          |right; inversion 1].
Qed.

Local Definition type_tag (a : tm) : consistency_constant :=
  match a with
  | a_Type s => ct_type s
  | a_TyUnit => ct_unit
  | a_Pi q _ _ => ct_pi q
  | a_WSigma q _ _ => ct_wsigma q
  | a_SSigma q _ _ => ct_ssigma q
  | a_Sum _ _ => ct_sum
  | _ => ct_dummy
  end.

Local Lemma translated_value_spine : forall a, ValueType a ->
  forall g F B, exists args, translate g F B a = spine (type_tag a) args.
Proof.
  intros a Ha; destruct Ha; intros g F E;
    cbn [type_tag translate]; first [exists nil; reflexivity | eexists; reflexivity].
Qed.

Local Lemma matching_value_types : forall a b,
  ValueType a -> ValueType b -> type_tag a = type_tag b -> Consistent a b.
Proof.
  intros a b Ha Hb. destruct Ha; destruct Hb; simpl;
    intros Htag; try discriminate; inversion Htag; subst; constructor; assumption.
Qed.

Theorem DefEq_Consistent : forall S D A B, DefEq S D A B -> Consistent A B.
Proof.
  intros S D A B Heq.
  destruct (defeq_scoped Heq) as [HA HB].
  apply scoped_lc in HA, HB.
  destruct (value_type_dec HA) as [HVA|HVA]; [|now apply Consistent_a_Step_R].
  destruct (value_type_dec HB) as [HVB|HVB]; [|now apply Consistent_a_Step_L].
  apply matching_value_types; try assumption.
  pose (F := fun _ : atom => dummy).
  pose proof (defeq_meaning Heq cv (@related_refl S D F)) as Hcode.
  destruct (translated_value_spine HVA D F cv) as [args HAcode].
  destruct (translated_value_spine HVB D F cv) as [args' HBcode].
  rewrite HAcode, HBcode in Hcode.
  exact (proj1 (code_eq_spine _ _ _ _ Hcode)).
Qed.
