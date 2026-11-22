Set Implicit Arguments.

Require Import LibExtra AbstractSyntax TypingMode GeneralTyping.

Require Import OperationalSemantics ConfigTyping MethodCall.
Require Import HeapUpdate InertContext HeapCorrespondence Coq.Arith.Arith.
Require Import RecordTypes Indep.
Require Import ConfigNotations.
Require Import ConfigVarkinds.
Require Import EnvCorrespondence.
Require Import TFree.
Require Import Equivalence.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.

(* ------------------------------------------------------------------ *)
(* Structural facts about how a single reduction step affects the heap *)
(* ------------------------------------------------------------------ *)

Definition changes_at_most (S S' : heap) (y : var) : Prop :=
  forall z v, z <> y -> binds z v S -> binds z v S'.

Lemma red_changes_at_most :
  forall c c', red c c' ->
    exists y, changes_at_most (config_heap c) (config_heap c') y.
Proof.
  intros c c' Hred. destruct Hred.
  - (* red_read *) exists wObj. intros z v Hne Hb. exact Hb.
  - (* red_write *) exists yObj. intros z v Hne Hb.
    unfold heap_update in H. destruct H as (_ & _ & _ & Hunch & _).
    apply Hunch; assumption.
  - (* red_call *) exists wObj. intros z v Hne Hb. exact Hb.
  - (* red_apply *) exists wFun. intros z v Hne Hb. exact Hb.
  - (* red_let_fun *) exists y. intros z v Hne Hb.
    apply binds_concat_left. { exact Hb. }
    rewrite dom_single. apply notin_singleton_l. exact Hne.
  - (* red_let_obj *) exists y. intros z v Hne Hb.
    apply binds_concat_left. { exact Hb. }
    rewrite dom_single. apply notin_singleton_l. exact Hne.
  - (* red_let_var *) exists x. intros z v Hne Hb. exact Hb.
  - (* red_let_push *) exists (var_gen (\{} : vars)). intros z v Hne Hb. exact Hb.
Qed.

Lemma binds_in_dom : forall (S : heap) z v,
  binds z v S -> z \in dom S.
Proof.
  intros S z v H. exact (@get_some_inv item z v S H).
Qed.

Lemma binds_env_in_dom : forall (e:renv) (w y:var),
  binds w y e -> w \in dom e.
Proof. intros e w y H. exact (@get_some_inv var w y e H). Qed.

(* Eliminating a closedness hypothesis: opening at any depth is the
   identity. *)
Lemma closed_open_rec : forall (A:Set) `{Openable A} (a:A),
  closed a -> forall (n:nat) (x:var), open_rec n x a = a.
Proof. intros A H a Hc n x. exact (Hc n x). Qed.

Lemma closed_open : forall (A:Set) `{Openable A} (a:A),
  closed a -> forall (x:var), open x a = a.
Proof. intros A H a Hc x. exact (Hc 0 x). Qed.

(* Sealing-invariance at depth [k] implies that opening at any depth at least
   [k] is the identity.  This relates the two "closedness" styles used by the
   syntax classes: [sealed] is stability under [seal], [closed] under [open]. *)
Lemma seal_open_avar : forall (a:avar) (k m:nat) (u x:var),
  k <= m -> seal_rec k u a = a -> open_rec m x a = a.
Proof.
  intros a k m u x Hle H. destruct a as [i | y]; simpl in *.
  - destruct (classicT (k <= i)) as [E | E].
    + discriminate H.
    + assert (Hi : i < k) by lia.
      destruct (classicT (m = i)) as [E2 | E2].
      * exfalso. lia.
      * reflexivity.
  - reflexivity.
Qed.

Fixpoint seal_open_typ (T:typ) {struct T} :
  forall (k m:nat) (u x:var), k <= m -> seal_rec_typ k u T = T -> open_rec_typ m x T = T
with seal_open_dec (D:dec) {struct D} :
  forall (k m:nat) (u x:var), k <= m -> seal_rec_dec k u D = D -> open_rec_dec m x D = D.
Proof.
  - destruct T as [| | D | T1 T2 | T1 T2 | av1 L av2 | T | T1 T2 |];
      simpl; intros k m u x Hle H; try reflexivity.
    + (* typ_rcd *) injection H as HD.
      rewrite (seal_open_dec D k m u x Hle HD). reflexivity.
    + (* typ_and *) injection H as H1 H2.
      rewrite (seal_open_typ T1 k m u x Hle H1),
              (seal_open_typ T2 k m u x Hle H2). reflexivity.
    + (* typ_or *) injection H as H1 H2.
      rewrite (seal_open_typ T1 k m u x Hle H1),
              (seal_open_typ T2 k m u x Hle H2). reflexivity.
    + (* typ_sel *) injection H as H1 H2.
      rewrite (@seal_open_avar av1 k m u x Hle H1),
              (@seal_open_avar av2 k m u x Hle H2). reflexivity.
    + (* typ_bnd *) injection H as H1.
      rewrite (seal_open_typ T (S k) (S m) u x ltac:(lia) H1). reflexivity.
    + (* typ_fun *) injection H as H1 H2.
      rewrite (seal_open_typ T1 k m u x Hle H1),
              (seal_open_typ T2 (S k) (S m) u x ltac:(lia) H2). reflexivity.
  - destruct D as [L t t0 | L t t0 | m0 t t0 t1]; simpl; intros k m u x Hle H.
    + (* dec_typ *) injection H as H1 H2.
      rewrite (seal_open_typ t (S k) (S m) u x ltac:(lia) H1),
              (seal_open_typ t0 (S k) (S m) u x ltac:(lia) H2). reflexivity.
    + (* dec_fld *) injection H as H1 H2.
      rewrite (seal_open_typ t k m u x Hle H1),
              (seal_open_typ t0 k m u x Hle H2). reflexivity.
    + (* dec_met *) injection H as H1 H2 H3.
      rewrite (seal_open_typ t (S k) (S m) u x ltac:(lia) H1),
              (seal_open_typ t0 k m u x Hle H2),
              (seal_open_typ t1 (S (S k)) (S (S m)) u x ltac:(lia) H3). reflexivity.
Qed.

Lemma seal_closed_typ : forall (T:typ),
  (forall x, seal_rec 0 x T = T) -> closed T.
Proof.
  intros T H n x. change (open_rec_typ n x T = T).
  apply (@seal_open_typ T 0 n x x); [lia | apply H].
Qed.

(* A sealed context binds only closed types. *)
Lemma sealed_ctx_binds_closed : forall (G:ctx) (v:var) (T:typ),
  sealed G -> ctx_binds v T G -> closed T.
Proof.
  intros G v T Hs Hb. induction Hb.
  - unfold sealed in Hs.
    apply seal_closed_typ. intro x.
    pose proof (Hs x) as E. cbn [ctx_seal_rec] in E.
    injection E as _ Ht. exact Ht.
  - unfold sealed in Hs.
    apply IHHb. intro x.
    pose proof (Hs x) as E. cbn [ctx_seal_rec] in E.
    injection E as HG _. exact HG.
  - unfold sealed in Hs.
    apply IHHb. intro x.
    pose proof (Hs x) as E. cbn [ctx_seal_rec] in E.
    injection E as HG. exact HG.
Qed.

(* The closedness of an object-reference type splits: the record part is
   stable under opening at depth at least two, and the refcap part under
   opening at any depth. *)
Lemma closed_objref_parts : forall (U Sref:typ),
  closed (typ_objref U Sref) ->
  (forall (n:nat) (x:var), open_rec (S (S n)) x U = U) /\ (forall (n:nat) (x:var), open_rec n x Sref = Sref).
Proof.
  intros U Sref H. split.
  - intros n x. pose proof (H (S n) x) as E.
    cbn [open_rec_typ] in E.
    injection E as E1 E2. exact E1.
  - intros n x. pose proof (H n x) as E.
    cbn [open_rec_typ] in E.
    injection E as E1 E2. exact E2.
Qed.

(* Consequence for a sealed context: the record part and refcap part of every
   object-reference binding have the same stability. *)
Lemma sealed_binds_objref_open_U : forall (G:ctx) (v:var) (U Sref:typ),
  sealed G -> ctx_binds v (typ_objref U Sref) G ->
  forall (n:nat) (x:var), open_rec (S (S n)) x U = U.
Proof.
  intros G v U Sref Hs Hb n x.
  exact (proj1 (closed_objref_parts (sealed_ctx_binds_closed Hs Hb)) n x).
Qed.

Lemma sealed_binds_objref_open_S : forall (G:ctx) (v:var) (U Sref:typ),
  sealed G -> ctx_binds v (typ_objref U Sref) G ->
  forall (n:nat) (x:var), open_rec n x Sref = Sref.
Proof.
  intros G v U Sref Hs Hb n x.
  exact (proj2 (closed_objref_parts (sealed_ctx_binds_closed Hs Hb)) n x).
Qed.

(* A closed object item has a locally closed definition list, and every
   definition found in it is stable under opening at any depth. *)
Lemma item_closed_defs : forall (ds:defs) (n:nat) (x:var),
  closed (item_obj ds) -> open_rec n x ds = ds.
Proof.
  intros ds n x H. pose proof (closed_open_rec H n x) as E.
  simpl in E. injection E as E'. exact E'.
Qed.

Lemma closed_defs_parts : forall (ds:defs) (n:nat) (x:var),
  (forall k y, open_rec k y ds = ds) ->
  forall d, defs_has ds d -> open_rec_def n x d = d.
Proof.
  intros ds. induction ds as [| ds0 IH d0]; intros n x Hc d Hhas.
  - unfold defs_has in Hhas. cbn in Hhas. discriminate Hhas.
  - assert (Hcons : open_rec_defs n x (defs_cons ds0 d0) = defs_cons ds0 d0)
      by exact (Hc n x).
    cbn [open_rec_defs] in Hcons.
    injection Hcons as Hds0 Hd0.
    unfold defs_has in Hhas. cbn in Hhas.
    destruct (classicT (label_of d0 = label_of d)) as [Heq | Hneq].
    + injection Hhas as Hd. subst d. exact Hd0.
    + apply IH.
      * intros k y.
        pose proof (Hc k y) as Hk. cbn [open_rec_defs] in Hk.
        injection Hk as Hk1 Hk2. exact Hk1.
      * unfold defs_has. exact Hhas.
Qed.

(* Consequence for heap method bodies: a stored body is stable under opening
   at depth at least two; only the receiver (depth 1) and parameter (depth 0)
   can be substituted by [red_call]. *)
Lemma closed_heap_body_depth : forall (ds:defs) (m:met_label) (t:trm),
  closed (item_obj ds) -> defs_has ds (def_met m t) ->
  forall (n:nat) (x:var), open_rec (S (S n)) x t = t.
Proof.
  intros ds m t Hc Hhas n x.
  pose proof (@item_closed_defs ds n x Hc) as Hds.
  pose proof (@closed_defs_parts ds n x (fun k y => @item_closed_defs ds k y Hc)
                (def_met m t) Hhas) as Hdef.
  cbn [open_rec_def] in Hdef. injection Hdef as Ht. exact Ht.
Qed.

(* Reduction never removes heap locations or environment keys: allocations
   add fresh keys, writes preserve the heap domain, and environment extension
   only adds keys. *)
Lemma red_heap_dom_mono : forall (c c':config),
  c ↦ c' ->
  forall z, z \in dom (config_heap c) -> z \in dom (config_heap c').
Proof.
  intros c c' Hred. destruct Hred; simpl; intros z Hz.
  - exact Hz.
  - unfold heap_update in H. destruct H as (? & ? & Hdom & ? & ?).
    rewrite <- Hdom. exact Hz.
  - exact Hz.
  - exact Hz.
  - rewrite dom_push. rewrite in_union. right. exact Hz.
  - rewrite dom_push. rewrite in_union. right. exact Hz.
  - exact Hz.
  - exact Hz.
Qed.

Lemma red_env_dom_mono : forall (c c':config),
  c ↦ c' ->
  forall z, z \in dom (config_env c) -> z \in dom (config_env c').
Proof.
  intros c c' Hred. destruct Hred; simpl; intros z Hz.
  - rewrite dom_push. rewrite in_union. right. exact Hz.
  - exact Hz.
  - exact Hz.
  - exact Hz.
  - rewrite dom_push. rewrite in_union. right. exact Hz.
  - rewrite dom_push. rewrite in_union. right. exact Hz.
  - exact Hz.
  - exact Hz.
Qed.

Lemma red_closure_heap_dom_mono : forall (c1 c2:config) (k:nat),
  c1 ⊣k↦* c2 ->
  forall z, z \in dom (config_heap c1) -> z \in dom (config_heap c2).
Proof.
  intros c1 c2 k Hcl.
  induction Hcl as [C | C1 C2 C3 n Hcln IH Hred]; intros z Hz.
  - exact Hz.
  - eapply red_heap_dom_mono; [ exact Hred | apply IH; exact Hz ].
Qed.

Lemma red_closure_env_dom_mono : forall (c1 c2:config) (k:nat),
  c1 ⊣k↦* c2 ->
  forall z, z \in dom (config_env c1) -> z \in dom (config_env c2).
Proof.
  intros c1 c2 k Hcl.
  induction Hcl as [C | C1 C2 C3 n Hcln IH Hred]; intros z Hz.
  - exact Hz.
  - eapply red_env_dom_mono; [ exact Hred | apply IH; exact Hz ].
Qed.

Lemma red_closure_inv : forall c1 k c4,
  red_closure c1 k c4 ->
  (k = 0 /\ c4 = c1) \/
  (exists n c2, k = S n /\ red_closure c1 n c2 /\ red c2 c4).
Proof.
  intros c1 k c4 H. destruct H.
  - left. auto.
  - right. exists n, C2. auto.
Qed.

(* Split off the first step of a non-empty reduction sequence. *)
Lemma red_closure_first : forall (c1:config) (n:nat) (c4:config),
  red_closure c1 n c4 ->
  forall k, n = S k -> exists c2, red c1 c2 /\ red_closure c2 k c4.
Proof.
  intros c1 n c4 H. induction H as [C | C1 C2 C3 m Hcl Hstep IH]; intros k Hk.
  - discriminate Hk.
  - injection Hk as Hk. subst k.
    destruct m as [| m'].
    + inversion Hcl; subst. exists C3. split; [exact IH | apply red_refl].
    + pose proof (Hstep m' eq_refl) as [c2 [Hred Hcl2]].
      exists c2. split; [exact Hred |].
      eapply red_trans; [exact Hcl2 | exact IH].
Qed.

(* The shape of the (unique possible) step from a configuration whose term is
   a call: the call step exposes the receiver's heap location, its object
   definitions, the method body, and the resulting opened-body configuration. *)
Lemma red_step_call_inv : forall (c1 c2:config) (w1:var) (m:met_label) (w2:var),
  c1 ↦ c2 ->
  config_trm c1 = trm_call (avar_f w1) m (avar_f w2) ->
  exists yObj ds t fs Sigma e Lv,
    c1 = (trm_call (avar_f w1) m (avar_f w2) ; fs ; Sigma ; e ; Lv) /\
    binds yObj (item_obj ds) Sigma /\
    defs_has ds (def_met m t) /\
    binds w1 yObj e /\
    c2 = (open_met w2 w1 t ; fs ; Sigma ; e ; fv_config c1).
Proof.
  intros c1 c2 w1 m w2 Hred Htrm.
  inversion Hred; subst.
  - exfalso. discriminate Htrm.
  - exfalso. discriminate Htrm.
  - injection Htrm as Ha1 Hmmet Ha2. subst.
    eexists _, _, _, _, _, _, _. repeat split; try reflexivity; try eassumption.
  - exfalso. discriminate Htrm.
  - exfalso. discriminate Htrm.
  - exfalso. discriminate Htrm.
  - exfalso. discriminate Htrm.
  - exfalso. discriminate Htrm.
Qed.

(* A call step changes neither the heap, the environment, nor the stack:
   it only replaces the call term by the opened method body. *)
Lemma red_step_call_same : forall (c1 c2:config) (w1:var) (m:met_label) (w2:var),
  c1 ↦ c2 ->
  config_trm c1 = trm_call (avar_f w1) m (avar_f w2) ->
  config_heap c2 = config_heap c1 /\
  config_env c2 = config_env c1 /\
  config_stack c2 = config_stack c1.
Proof.
  intros c1 c2 w1 m w2 Hred Htrm.
  destruct (red_step_call_inv Hred Htrm)
    as (yObj & ds & t & fs & Sigma & e & Lv & Hc1 & _ & _ & _ & Hc2).
  rewrite Hc1, Hc2. simpl. repeat split; reflexivity.
Qed.

Lemma fresh_fv_config_dom : forall (y:var) (c:config),
  y \notin fv_config c -> y \notin (dom (config_heap c)).
Proof.
  intros y [t s S e Lv] H. simpl in H.
  apply notin_union_r in H. destruct H as [Ht H].
  apply notin_union_r in H. destruct H as [Hs H].
  apply notin_union_r in H. destruct H as [Hheap H].
  simpl in Hheap. apply notin_union_r in Hheap. destruct Hheap as [Hdom _].
  exact Hdom.
Qed.

(* Reduction preserves heap well-formedness (distinct location keys): writes
   preserve the domain, allocations push a fresh key. *)
Lemma red_ok_heap : forall (c c':config),
  c ↦ c' -> ok (config_heap c) -> ok (config_heap c').
Proof.
  intros c c' Hred Hok. destruct Hred; simpl in *.
  - exact Hok.
  - unfold heap_update in H. destruct H as (? & Hok' & ? & ? & ?). exact Hok'.
  - exact Hok.
  - exact Hok.
  - apply ok_push.
    + exact Hok.
    + simpl in H. destruct H as [Hy _].
      exact (fresh_fv_config_dom
               (trm_lit (lit_fun T t1) t2 ; fs ; Sigma ; e ; Lv) Hy).
  - apply ok_push.
    + exact Hok.
    + simpl in H. destruct H as [Hy _].
      exact (fresh_fv_config_dom
               (trm_lit (lit_obj T ds) t ; fs ; Sigma ; e ; Lv) Hy).
  - exact Hok.
  - exact Hok.
Qed.

Lemma red_closure_ok_heap : forall (c1 c2:config) (k:nat),
  c1 ⊣k↦* c2 -> ok (config_heap c1) -> ok (config_heap c2).
Proof.
  intros c1 c2 k Hcl.
  induction Hcl as [C | C1 C2 C3 n Hcln IH Hred]; intro Hok.
  - exact Hok.
  - eapply red_ok_heap; [ exact Hred | apply IH; exact Hok ].
Qed.

(* The free variables of a configuration only grow along reduction: each
   step stores the previous free-variable set in [Lv]. *)
Lemma fv_config_mono_red : forall (c c':config),
  c ↦ c' -> fv_config c \c fv_config c'.
Proof.
  intros c c' Hred x Hx. destruct Hred; simpl.
  all: try (do 4 (rewrite in_union; right)); exact Hx.
Qed.

Lemma fv_config_mono_closure : forall (c1 c2:config) (k:nat),
  c1 ⊣k↦* c2 -> fv_config c1 \c fv_config c2.
Proof.
  intros c1 c2 k Hcl.
  induction Hcl as [C | C1 C2 C3 n Hcln IH Hred].
  - intros x Hx. exact Hx.
  - intros x Hx. exact (@fv_config_mono_red C2 C3 Hred x (IH x Hx)).
Qed.


Lemma fresh_fv_config_env_dom : forall (y:var) (c:config),
  y \notin fv_config c -> y \notin dom (config_env c).
Proof.
  intros y [t st S e Lv] H. simpl in H.
  apply notin_union_r in H. destruct H as [Ht H].
  apply notin_union_r in H. destruct H as [Hs H].
  apply notin_union_r in H. destruct H as [Hheap H].
  apply notin_union_r in H. destruct H as [Hrenv _].
  apply notin_union_r in Hrenv. destruct Hrenv as [Hdom _].
  exact Hdom.
Qed.

Lemma notin_dom_neq : forall (y z:var) (S:heap),
  z \in dom S -> y \notin dom S -> z <> y.
Proof. intros y z S Hz Hy E. subst. apply Hy. assumption. Qed.

Lemma red_nonwrite_subheap : forall (c c':config),
  c ↦ c' ->
  (forall S0, subheap_unchanged S0 (config_heap c) ->
             subheap_unchanged S0 (config_heap c')) \/
  (exists (Sigma Sigma':heap) (yObj:var) (a:fld_label) (yArg:var),
      config_heap c = Sigma /\ config_heap c' = Sigma' /\
      heap_update Sigma yObj a yArg Sigma').
Proof.
  intros c c' Hred. induction Hred.
  - left. intros S0 Hsub. simpl in *. exact Hsub.
  - right. simpl. exists Sigma, Sigma', yObj, m, yArg. auto.
  - left. intros S0 Hsub. simpl in *. exact Hsub.
  - left. intros S0 Hsub. simpl in *. exact Hsub.
  - left. intros S0 Hsub. simpl.
    intros z itm Hb.
    apply binds_push_neq.
    + apply Hsub; assumption.
    + apply notin_dom_neq with (S:=Sigma).
      * apply get_some_inv with (v:=itm). apply binds_get. apply Hsub; exact Hb.
      * simpl in H. destruct H as [Hy _].
        pose proof (fresh_fv_config_dom
          (trm_lit (lit_fun T t1) t2 ; fs ; Sigma ; e ; Lv) Hy) as Hd.
        simpl in Hd. exact Hd.
  - left. intros S0 Hsub. simpl.
    intros z itm Hb.
    apply binds_push_neq.
    + apply Hsub; assumption.
    + apply notin_dom_neq with (S:=Sigma).
      * apply get_some_inv with (v:=itm). apply binds_get. apply Hsub; exact Hb.
      * simpl in H. destruct H as [Hy _].
        pose proof (fresh_fv_config_dom
          (trm_lit (lit_obj T ds) t ; fs ; Sigma ; e ; Lv) Hy) as Hd.
        simpl in Hd. exact Hd.
  - left. intros S0 Hsub. simpl in *. exact Hsub.
  - left. intros S0 Hsub. simpl in *. exact Hsub.
Qed.

(* A step preserves the initial heap provided it is not a write to a
   location of the initial heap. *)
Definition SefStep (c1 : config) : Prop :=
  forall j c2 c3,
    red_closure c1 j c2 ->
    (forall c3', ~ frame_end_in c1 j c3') ->
    red c2 c3 ->
    subheap_unchanged (config_heap c1) (config_heap c2) ->
    subheap_unchanged (config_heap c1) (config_heap c3).

Lemma subheap_unchanged_refl : forall (S:heap), subheap_unchanged S S.
Proof. intros S z v H; exact H. Qed.

Lemma subheap_unchanged_trans : forall (S1 S2 S3:heap),
  subheap_unchanged S1 S2 -> subheap_unchanged S2 S3 ->
  subheap_unchanged S1 S3.
Proof. intros S1 S2 S3 H12 H23 z v H. apply H23. apply H12. exact H. Qed.

(* Pushing a fresh location preserves all pre-existing heap bindings. *)
Lemma subheap_unchanged_push : forall (S:heap) (y:var) (itm:item),
  y \notin dom S -> subheap_unchanged S (S & y ~ itm).
Proof.
  intros S y itm Hy z v Hz.
  apply binds_push_neq.
  - exact Hz.
  - intro E. apply Hy. rewrite <- E. exact (binds_in_dom Hz).
Qed.

Lemma heap_update_preserves_others : forall (S S':heap) (x:var) (a:fld_label) (y:var),
  heap_update S x a y S' ->
  forall z v, z <> x -> binds z v S -> binds z v S'.
Proof.
  intros S S' x a y [Hok [Hok' [Hdom [Hunch _]]]] z v Hne Hb.
  apply Hunch; assumption.
Qed.

Lemma inert_typ_not_nocap : forall (typing_mode:Mode) (T:typ) vk,
  inert_typ (typing_mode:=typing_mode) T vk -> T <> typ_nocap.
Proof. intros typing_mode T vk H. inversion H; subst; discriminate. Qed.

Lemma inert_binds_not_nocap : forall (typing_mode:Mode) (G:ctx) v T,
  inert (typing_mode:=typing_mode) G -> ctx_binds v T G -> T <> typ_nocap.
Proof.
  intros typing_mode G v T Hi Hb. induction Hb.
  - inversion Hi; subst. eapply inert_typ_not_nocap; eassumption.
  - inversion Hi; subst. apply IHHb; assumption.
  - inversion Hi.
Qed.

(* In the modes satisfying the target's hypotheses, functions are excluded,
   hence inert types are necessarily object types. *)
Lemma mode_sef_mut_no_fun : forall (m:mode),
  mode_has_sef m -> mode_has_mutability m -> mode_has_fun m -> False.
Proof. intros m Hs Hm Hf. destruct m; simpl in *; discriminate. Qed.

Lemma inert_typ_obj_only : forall (typing_mode:Mode) (T:typ) (vk:varkind),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  inert_typ T vk ->
  exists U S, T = typ_objref U S.
Proof.
  intros typing_mode T vk Hs Hm Hi.
  inversion Hi; subst.
  - exfalso. eapply mode_sef_mut_no_fun; eassumption.
  - eexists. eexists. reflexivity.
Qed.

Lemma mode_mut_refcaps : forall (m:mode),
  mode_has_mutability m -> mode_refcaps' m = mode_refcaps_mutability.
Proof. intros m Hm. destruct m; simpl in *; discriminate || reflexivity. Qed.

(* In the relevant modes every inert binding is either a location or a
   reference variable (the function branch is impossible). *)
Lemma inert_typ_vk_loc_ref : forall (typing_mode:Mode) (T:typ) (vk:varkind),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  inert_typ T vk ->
  vk = v_loc \/ vk = v_ref.
Proof.
  intros typing_mode T vk Hs Hm Hi.
  inversion Hi; subst.
  - exfalso. eapply mode_sef_mut_no_fun; eassumption.
  - pose proof (mode_mut_refcaps typing_mode Hm) as Hr.
    unfold refcap_inert_type in H0.
    rewrite Hr in H0. simpl in H0.
    inversion H0; subst; auto.
Qed.

(* Full shape of inert types and of the bindings of an inert context in the
   target's modes: an object type with a record part [U], a refcap part [S],
   both well formed and independent. *)
Lemma inert_typ_obj_shape : forall (typing_mode:Mode) (T:typ) (vk:varkind),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  inert_typ T vk ->
  exists U S, T = typ_objref U S /\ record_type U /\
              refcap_inert_type S vk /\ typ_indep_b 0 U.
Proof.
  intros typing_mode T vk Hs Hm Hi.
  inversion Hi; subst.
  - exfalso. eapply mode_sef_mut_no_fun; eassumption.
  - eexists. eexists. repeat split; eassumption.
Qed.

Lemma inert_binds_obj_shape : forall (typing_mode:Mode) (G:ctx) (x:var) (T:typ),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  inert G -> ctx_binds x T G ->
  exists U S vk, T = typ_objref U S /\ record_type U /\
                refcap_inert_type S vk /\ typ_indep_b 0 U.
Proof.
  intros typing_mode G x T Hs Hm Hi Hb. revert Hi. induction Hb; intros Hi.
  - inversion Hi; subst.
    destruct (inert_typ_obj_shape Hs Hm H5) as (U & S & Heq & Hrec & Href & Hind).
    exists U, S, vk. repeat split; assumption.
  - inversion Hi; subst. apply IHHb; assumption.
  - inversion Hi.
Qed.

(* In a mutability mode the refcap component of an inert binding is a mut
   marker: [typ_mut_marker typ_bot] for locations, [typ_mut_marker Tbnd] for
   reference variables. *)
Lemma refcap_inert_type_mut_shape : forall (typing_mode:Mode) (S:typ) (vk:varkind),
  mode_has_mutability typing_mode ->
  refcap_inert_type (typing_mode:=typing_mode) S vk ->
  (vk = v_loc /\ S = typ_mut_marker typ_bot) \/
  (exists Tbnd, vk = v_ref /\ S = typ_mut_marker Tbnd).
Proof.
  intros typing_mode S vk Hm Href.
  unfold refcap_inert_type in Href.
  rewrite (mode_mut_refcaps typing_mode Hm) in Href.
  simpl in Href.
  inversion Href; subst; auto.
  right. eauto.
Qed.

(* [typ_nocap] can never be capability-bounded: none of the constructors of
   [cap_bnd] has [typ_nocap] as its source type.  This is used when
   inspecting the viewpoint adaptation performed by field reads. *)
Lemma no_capbnd_nocap :
  forall (typing_mode:Mode) (C:typ_refcap_label) (G:ctx) (Go:objctx) (e:renv) (T:typ),
    ~ (G §§ Go ⁏ e ⊢ typ_nocap ∶cpb⟦C⟧ T).
Proof. intros. intro H. inversion H. Qed.

(* Every binding of an inert context carries an inert type. *)
Lemma inert_binds_inert_type :
  forall (typing_mode:Mode) (G:ctx) (x:var) (T:typ),
    inert G -> ctx_binds x T G -> inert_type T.
Proof.
  intros typing_mode G x T Hi Hb. revert Hi. induction Hb; intros Hi.
  - inversion Hi; subst. eexists. eassumption.
  - inversion Hi; subst. apply IHHb. assumption.
  - inversion Hi.
Qed.

Lemma heap_prefix_subheap : forall (S1 S1' S2:heap),
  S2 = concat S1' S1 ->
  (forall x, x \in dom S1 -> x \notin dom S1') ->
  subheap_unchanged S1 S2.
Proof.
  intros S1 S1' S2 Heq Hdis x v Hx.
  rewrite Heq. unfold binds in *.
  rewrite get_concat.
  destruct (get x S1) as [w|] eqn:E.
  - injection Hx as <-. reflexivity.
  - discriminate Hx.
Qed.

(* Distribution of substitution over the classical conditional, used by
   the (missing) substitution/open commutation metatheory. *)
Lemma subst_if_avar : forall (x y:var) (P:Prop) (a b:avar),
  subst_var x y (If P then a else b) = If P then subst_var x y a else subst_var x y b.
Proof. intros; destruct (classicT P); cbn; reflexivity. Qed.

Lemma subst_if_typ : forall (x y:var) (P:Prop) (A B:typ),
  subst_var x y (If P then A else B) = If P then subst_var x y A else subst_var x y B.
Proof. intros; destruct (classicT P); cbn; reflexivity. Qed.

(* Simultaneous substitution of a free variable commutes with opening at a
   bound variable (the stripped [SubstOpenCommut] instances for the syntax). *)
Lemma subst_open_commut_avar : forall (x y z:var) (a:avar) (n:nat),
  subst_var x y (open_rec n z a) = open_rec n (subst_var x y z) (subst_var x y a).
Proof.
  intros x y z a n. destruct a as [i | w]; simpl.
  - destruct (classicT (n = i)) as [Heq | Hneq]; simpl.
    + subst i. simpl. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma subst_open_commut_typ_dec :
  (forall (T:typ) (x y z:var) (n:nat),
     subst_var x y (open_rec n z T) = open_rec n (subst_var x y z) (subst_var x y T)) /\
  (forall (D:dec) (x y z:var) (n:nat),
     subst_var x y (open_rec n z D) = open_rec n (subst_var x y z) (subst_var x y D)).
Proof.
  apply typ_mutind; intros; simpl; try reflexivity;
    try (f_equal; eauto using subst_open_commut_avar).
Qed.

Lemma subst_open_commut_trm_defs :
  (forall (t:trm) (x y z:var) (n:nat),
     subst_var x y (open_rec n z t) = open_rec n (subst_var x y z) (subst_var x y t)) /\
  (forall (l:lit) (x y z:var) (n:nat),
     subst_var x y (open_rec n z l) = open_rec n (subst_var x y z) (subst_var x y l)) /\
  (forall (d:def) (x y z:var) (n:nat),
     subst_var x y (open_rec n z d) = open_rec n (subst_var x y z) (subst_var x y d)) /\
  (forall (ds:defs) (x y z:var) (n:nat),
     subst_var x y (open_rec n z ds) = open_rec n (subst_var x y z) (subst_var x y ds)).
Proof.
  apply trm_mutind; intros; simpl; try reflexivity;
    try (f_equal; eauto using subst_open_commut_avar,
                                       (proj1 subst_open_commut_typ_dec),
                                       (proj2 subst_open_commut_typ_dec)).
Qed.

(* Reconstructed [SubstId] instances: substituting a variable for itself is
   the identity on the syntax. *)
Lemma subst_id_var : forall (x y:var), subst_var x x y = y.
Proof.
  intros x y. unfold subst_var, VarSubstVar. simpl.
  destruct (classicT (y = x)) as [Heq | Hneq]; simpl; congruence.
Qed.

Lemma subst_id_avar : forall (x:var) (a:avar), subst_var x x a = a.
Proof.
  intros x a. destruct a as [i | w]; unfold subst_var, AvarSubstVar; simpl.
  - reflexivity.
  - destruct (classicT (w = x)) as [Heq | Hneq]; simpl; congruence.
Qed.

Lemma subst_id_typ_dec :
  (forall (T:typ) (x:var), subst_var x x T = T) /\
  (forall (D:dec) (x:var), subst_var x x D = D).
Proof.
  apply typ_mutind; intros; unfold subst_var; simpl; try reflexivity;
    try (f_equal; eauto using subst_id_var, subst_id_avar).
Qed.

Lemma subst_id_trm_defs :
  (forall (t:trm) (x:var), subst_var x x t = t) /\
  (forall (l:lit) (x:var), subst_var x x l = l) /\
  (forall (d:def) (x:var), subst_var x x d = d) /\
  (forall (ds:defs) (x:var), subst_var x x ds = ds).
Proof.
  apply trm_mutind; intros; unfold subst_var; simpl; try reflexivity;
    try (f_equal; eauto using subst_id_var, subst_id_avar,
                                       (proj1 subst_id_typ_dec),
                                       (proj2 subst_id_typ_dec)).
Qed.

(* Reconstructed [OpenTwice] instances (with the underlying avar equations). *)
Lemma open_avar_b : forall (n:nat) (x:var) (i:nat),
  open_rec n x (avar_b i) = If n = i then avar_f x else avar_b i.
Proof. intros. reflexivity. Qed.

Lemma open_avar_f : forall (n:nat) (x w:var),
  open_rec n x (avar_f w) = avar_f w.
Proof. intros. reflexivity. Qed.

Lemma open_twice_avar : forall (n:nat) (x y:var) (a:avar),
  open_rec n y (open_rec n x a) = open_rec n x a.
Proof.
  intros n x y a. destruct a as [i | w].
  - rewrite !open_avar_b.
    destruct (classicT (n = i)) as [Heq | Hneq].
    + rewrite open_avar_f. reflexivity.
    + rewrite open_avar_b. rewrite (@If_r avar (n = i) (avar_f y) (avar_b i) Hneq).
      reflexivity.
  - rewrite open_avar_f. rewrite open_avar_f. reflexivity.
Qed.

Lemma open_twice_typ_dec :
  (forall (T:typ) (n:nat) (x y:var), open_rec n y (open_rec n x T) = open_rec n x T) /\
  (forall (D:dec) (n:nat) (x y:var), open_rec n y (open_rec n x D) = open_rec n x D).
Proof.
  apply typ_mutind; intros; simpl; try reflexivity;
    try (f_equal; eauto using open_twice_avar).
Qed.

Lemma open_twice_trm_defs :
  (forall (t:trm) (n:nat) (x y:var), open_rec n y (open_rec n x t) = open_rec n x t) /\
  (forall (l:lit) (n:nat) (x y:var), open_rec n y (open_rec n x l) = open_rec n x l) /\
  (forall (d:def) (n:nat) (x y:var), open_rec n y (open_rec n x d) = open_rec n x d) /\
  (forall (ds:defs) (n:nat) (x y:var), open_rec n y (open_rec n x ds) = open_rec n x ds).
Proof.
  apply trm_mutind; intros; simpl; try reflexivity;
    try (f_equal; eauto using open_twice_avar,
                                       (proj1 open_twice_typ_dec),
                                       (proj2 open_twice_typ_dec)).
Qed.

(* Reconstructed [OpenCommut] instances. *)
Lemma open_commut_avar : forall (m n:nat) (x y:var) (a:avar),
  m <> n -> open_rec m x (open_rec n y a) = open_rec n y (open_rec m x a).
Proof.
  intros m n x y a Hmn. destruct a as [i | w].
  - rewrite !open_avar_b.
    destruct (classicT (n = i)) as [Hni | Hni];
      destruct (classicT (m = i)) as [Hmi | Hmi].
    + exfalso. apply Hmn. congruence.
    + rewrite open_avar_f. rewrite open_avar_b.
      rewrite (@If_l avar (n = i) (avar_f y) (avar_b i) Hni). reflexivity.
    + rewrite open_avar_b. rewrite (@If_l avar (m = i) (avar_f x) (avar_b i) Hmi).
      rewrite open_avar_f. reflexivity.
    + rewrite open_avar_b. rewrite (@If_r avar (m = i) (avar_f x) (avar_b i) Hmi).
      rewrite open_avar_b. rewrite (@If_r avar (n = i) (avar_f y) (avar_b i) Hni).
      reflexivity.
  - rewrite open_avar_f. rewrite open_avar_f. reflexivity.
Qed.

Lemma neq_S : forall (m n:nat), m <> n -> S m <> S n.
Proof. intros m n H E. apply H. injection E. auto. Qed.

Lemma open_commut_typ_dec :
  (forall (T:typ) (m n:nat) (x y:var),
     m <> n -> open_rec m x (open_rec n y T) = open_rec n y (open_rec m x T)) /\
  (forall (D:dec) (m n:nat) (x y:var),
     m <> n -> open_rec m x (open_rec n y D) = open_rec n y (open_rec m x D)).
Proof.
  apply typ_mutind; intros; simpl; try reflexivity;
    try (f_equal; eauto using open_commut_avar, neq_S).
Qed.

Lemma open_commut_trm_defs :
  (forall (t:trm) (m n:nat) (x y:var),
     m <> n -> open_rec m x (open_rec n y t) = open_rec n y (open_rec m x t)) /\
  (forall (l:lit) (m n:nat) (x y:var),
     m <> n -> open_rec m x (open_rec n y l) = open_rec n y (open_rec m x l)) /\
  (forall (d:def) (m n:nat) (x y:var),
     m <> n -> open_rec m x (open_rec n y d) = open_rec n y (open_rec m x d)) /\
  (forall (ds:defs) (m n:nat) (x y:var),
     m <> n -> open_rec m x (open_rec n y ds) = open_rec n y (open_rec m x ds)).
Proof.
  apply trm_mutind; intros; simpl; try reflexivity;
    try (f_equal; eauto using open_commut_avar, neq_S,
                                       (proj1 open_commut_typ_dec),
                                       (proj2 open_commut_typ_dec)).
Qed.

(* Reconstructed [SubstFresh] instances. *)
Lemma subst_fresh_avar : forall (x y:var) (a:avar),
  x \notin fv a -> subst_var x y a = a.
Proof.
  intros x y a H. destruct a as [i | w].
  - unfold subst_var, AvarSubstVar. simpl. reflexivity.
  - simpl in H. apply notin_singleton_r in H.
    unfold subst_var, AvarSubstVar. simpl.
    destruct (classicT (w = x)) as [Heq | Hneq]; simpl; congruence.
Qed.

Lemma subst_fresh_var : forall (x y z:var),
  x \notin fv z -> subst_var x y z = z.
Proof.
  intros x y z H. simpl in H. apply notin_singleton_r in H.
  unfold subst_var, VarSubstVar. simpl.
  destruct (classicT (z = x)) as [Heq | Hneq]; simpl; congruence.
Qed.

Lemma subst_fresh_typ_dec :
  (forall (T:typ) (x y:var), x \notin fv T -> subst_var x y T = T) /\
  (forall (D:dec) (x y:var), x \notin fv D -> subst_var x y D = D).
Proof.
  apply typ_mutind; intros; simpl in *; try reflexivity;
    try (repeat match goal with H : ?x \notin (?A \u ?B) |- _ =>
                 let H1 := fresh in apply notin_union_r in H; destruct H as [H H1] end);
    try (f_equal; eauto using subst_fresh_avar, subst_fresh_var).
Qed.

Lemma subst_fresh_trm_defs :
  (forall (t:trm) (x y:var), x \notin fv t -> subst_var x y t = t) /\
  (forall (l:lit) (x y:var), x \notin fv l -> subst_var x y l = l) /\
  (forall (d:def) (x y:var), x \notin fv d -> subst_var x y d = d) /\
  (forall (ds:defs) (x y:var), x \notin fv ds -> subst_var x y ds = ds).
Proof.
  apply trm_mutind; intros; simpl in *; try reflexivity;
    try (repeat match goal with H : ?x \notin (?A \u ?B) |- _ =>
                 let H1 := fresh in apply notin_union_r in H; destruct H as [H H1] end);
    try (f_equal; eauto using subst_fresh_avar, subst_fresh_var,
                                       (proj1 subst_fresh_typ_dec),
                                       (proj2 subst_fresh_typ_dec)).
Qed.

(* First [FvOpenCases] instances (vars/avars). *)
Lemma fv_open_var : forall (n:nat) (x y:var),
  fv (open_rec n x y) = fv y \/ fv (open_rec n x y) = \{x} \u fv y.
Proof. intros. left. reflexivity. Qed.

Lemma fv_open_avar : forall (n:nat) (x:var) (a:avar),
  fv (open_rec n x a) = fv a \/ fv (open_rec n x a) = \{x} \u fv a.
Proof.
  intros n x a. destruct a as [i | w].
  - rewrite open_avar_b.
    destruct (classicT (n = i)) as [Heq | Hneq].
    + right. simpl. rewrite union_empty_r. reflexivity.
    + left. reflexivity.
  - rewrite open_avar_f. left. reflexivity.
Qed.

Lemma heap_update_at_key : forall (S S':heap) (x:var) (a:fld_label) (y:var),
  heap_update S x a y S' ->
  exists ds ds', binds x (item_obj ds) S /\
                defs_update ds a y ds' /\
                binds x (item_obj ds') S'.
Proof.
  intros S S' x a y [_ [_ [_ [_ [ds [ds' [H1 [H2 H3]]]]]]]].
  exists ds, ds'. auto.
Qed.

Lemma heap_update_ok_l : forall (S S':heap) (x:var) (a:fld_label) (y:var),
  heap_update S x a y S' -> ok S.
Proof. intros S S' x a y [H _]. exact H. Qed.

Lemma heap_update_ok_r : forall (S S':heap) (x:var) (a:fld_label) (y:var),
  heap_update S x a y S' -> ok S'.
Proof. intros S S' x a y [_ [H _]]. exact H. Qed.

Lemma heap_update_dom : forall (S S':heap) (x:var) (a:fld_label) (y:var),
  heap_update S x a y S' -> dom S = dom S'.
Proof. intros S S' x a y [_ [_ [H _]]]. exact H. Qed.

Lemma heap_update_changes_at_most : forall (S S':heap) (x:var) (a:fld_label) (y:var),
  heap_update S x a y S' -> changes_at_most S S' x.
Proof.
  intros S S' x a y Hup z v Hne Hb.
  eapply heap_update_preserves_others; [ exact Hup | exact Hne | exact Hb ].
Qed.

(* A write at a location outside [H] preserves every binding of [H]. *)
Lemma heap_update_preserves_heap : forall (H S S':heap) (x:var) (a:fld_label)
                                          (y:var),
  x \notin dom H -> subheap_unchanged H S -> heap_update S x a y S' ->
  subheap_unchanged H S'.
Proof.
  intros H S S' x a y Hx Hsub Hup z v Hz.
  assert (Hne : z <> x).
  { intro E. apply Hx. rewrite <- E. exact (@get_some_inv item z v H Hz). }
  eapply heap_update_preserves_others; [ exact Hup | exact Hne | apply Hsub; exact Hz ].
Qed.

(* Definition-list lookup leaves the head alone when its label differs. *)
Lemma get_def_cons_neq : forall (l:label) (ds:defs) (d:def),
  label_of d <> l -> get_def l (defs_cons ds d) = get_def l ds.
Proof.
  intros l ds d H. cbn [get_def].
  destruct (classicT (label_of d = l)) as [E | E].
  - exfalso. apply H. exact E.
  - reflexivity.
Qed.

Lemma get_def_cons_eq : forall (l:label) (ds:defs) (d:def),
  label_of d = l -> get_def l (defs_cons ds d) = Some d.
Proof.
  intros l ds d H. cbn [get_def].
  destruct (classicT (label_of d = l)) as [E | E].
  - reflexivity.
  - exfalso. apply E. exact H.
Qed.

(* A write only updates a field definition, so every method definition of the
   object stays present: writes never change the code of a heap object. *)
Lemma defs_update_preserves_met : forall (ds ds':defs) (a:fld_label) (x:var)
                                          (m:met_label) (t:trm),
  defs_update ds a x ds' ->
  defs_has ds (def_met m t) ->
  defs_has ds' (def_met m t).
Proof.
  intros ds ds' a x m t Hu. induction Hu; intros Hhas.
  - (* defs_update_var *) unfold defs_has in *.
    change (get_def (label_met m) (defs_cons ds (def_fld a t0)) =
            Some (def_met m t)) in Hhas.
    change (get_def (label_met m) (defs_cons ds (def_fld a (avar_f x))) =
            Some (def_met m t)).
    assert (Hneq : label_of (def_fld a t0) <> label_met m) by discriminate.
    rewrite (@get_def_cons_neq (label_met m) ds (def_fld a t0) Hneq) in Hhas.
    assert (Hneq' : label_of (def_fld a (avar_f x)) <> label_met m) by discriminate.
    rewrite (@get_def_cons_neq (label_met m) ds (def_fld a (avar_f x)) Hneq').
    exact Hhas.
  - (* defs_update_push *) unfold defs_has in *.
    change (get_def (label_met m) (defs_cons ds d) =
            Some (def_met m t)) in Hhas.
    change (get_def (label_met m) (defs_cons ds' d) =
            Some (def_met m t)).
    destruct (classicT (label_of d = label_met m)) as [Heq | Hneq].
    + rewrite (@get_def_cons_eq (label_met m) ds d Heq) in Hhas.
      rewrite (@get_def_cons_eq (label_met m) ds' d Heq).
      exact Hhas.
    + rewrite (@get_def_cons_neq (label_met m) ds d Hneq) in Hhas.
      rewrite (@get_def_cons_neq (label_met m) ds' d Hneq).
      apply IHHu. exact Hhas.
Qed.

(* A write preserves the presence of every label in the object's definition
   list (the definition stored at a label may change value, but the label
   remains). *)
Lemma defs_update_get_def_some : forall (ds ds':defs) (a:fld_label) (x:var)
                                        (l:label),
  defs_update ds a x ds' ->
  (exists d, get_def l ds = Some d) ->
  (exists d, get_def l ds' = Some d).
Proof.
  intros ds ds' a x l Hu.
  induction Hu as [ds0 a0 t0 x0 | ds0 d0 a0 x0 ds0' Hu0 Hlab];
    intros [dd Hd].
  - (* var *)
    destruct (classicT (label_fld a0 = l)) as [Heq | Hneq].
    + exists (def_fld a0 (avar_f x0)).
      assert (Hl : label_of (def_fld a0 (avar_f x0)) = l)
        by (change (label_fld a0 = l); exact Heq).
      rewrite (@get_def_cons_eq l ds0 (def_fld a0 (avar_f x0)) Hl).
      reflexivity.
    + assert (Hn1 : label_of (def_fld a0 t0) <> l)
        by (change (label_fld a0 <> l); exact Hneq).
      assert (Hn2 : label_of (def_fld a0 (avar_f x0)) <> l)
        by (change (label_fld a0 <> l); exact Hneq).
      rewrite (@get_def_cons_neq l ds0 (def_fld a0 t0) Hn1) in Hd.
      rewrite (@get_def_cons_neq l ds0 (def_fld a0 (avar_f x0)) Hn2).
      exists dd. exact Hd.
  - (* push *)
    destruct (classicT (label_of d0 = l)) as [Heq | Hneq].
    + rewrite (@get_def_cons_eq l ds0 d0 Heq) in Hd.
      injection Hd as Hdd. subst d0.
      exists dd.
      rewrite (@get_def_cons_eq l ds0' dd Heq). reflexivity.
    + rewrite (@get_def_cons_neq l ds0 d0 Hneq) in Hd.
      rewrite (@get_def_cons_neq l ds0' d0 Hneq).
      match goal with
      | IH : (exists d, get_def l ds0 = Some d) -> _ |- _ =>
          destruct (IH (ex_intro _ dd Hd)) as [d' Hd']
      end.
      exists d'. exact Hd'.
Qed.

(* The single semantic obligation: during a pure call, before its frame
   ends, no write step can target a location of the initial heap. *)
Definition SefWrite (c1 : config) : Prop :=
  forall j c2 c3 Sigma Sigma' yObj a yArg,
    red_closure c1 j c2 ->
    (forall c3', ~ frame_end_in c1 j c3') ->
    red c2 c3 ->
    config_heap c2 = Sigma ->
    config_heap c3 = Sigma' ->
    heap_update Sigma yObj a yArg Sigma' ->
    yObj \notin dom (config_heap c1).

(* A step whose term is not a write preserves every binding of the current
   heap (reads/calls/let-var/let-push keep it; fresh allocations only add a
   location). *)
Lemma red_nonwrite_step_subheap : forall (c c':config),
  c ↦ c' ->
  (forall (wx:var) (a:fld_label) (wy:var),
     config_trm c <> trm_write (avar_f wx) a (avar_f wy)) ->
  subheap_unchanged (config_heap c) (config_heap c').
Proof.
  intros c c' Hred Hnw. destruct Hred; simpl in *.
  - apply subheap_unchanged_refl.
  - exfalso. apply (Hnw wObj m wArg). reflexivity.
  - apply subheap_unchanged_refl.
  - apply subheap_unchanged_refl.
  - apply subheap_unchanged_push.
    simpl in H. destruct H as [Hy _].
    exact (fresh_fv_config_dom (trm_lit (lit_fun T t1) t2 ; fs ; Sigma ; e ; Lv) Hy).
  - apply subheap_unchanged_push.
    simpl in H. destruct H as [Hy _].
    exact (fresh_fv_config_dom (trm_lit (lit_obj T ds) t ; fs ; Sigma ; e ; Lv) Hy).
  - apply subheap_unchanged_refl.
  - apply subheap_unchanged_refl.
Qed.

Lemma SefStep_of_write :
  forall c1, SefWrite c1 ->
  forall j c2 c3,
    red_closure c1 j c2 ->
    (forall c3', ~ frame_end_in c1 j c3') ->
    red c2 c3 ->
    subheap_unchanged (config_heap c1) (config_heap c2) ->
    subheap_unchanged (config_heap c1) (config_heap c3).
Proof.
  intros c1 Hw j c2 c3 Hcl Hnofe Hstep Hsub.
  destruct (red_nonwrite_subheap Hstep)
    as [Hnw | [Sigma [Sigma' [yObj [a [yArg [Heq1 [Heq2 Hup]]]]]]]].
  - apply Hnw. exact Hsub.
  - (* the step is a write *)
    assert (Hy : yObj \notin dom (config_heap c1)).
    { eapply Hw; eauto. }
    intros z v Hz.
    unfold heap_update in Hup. destruct Hup as (_ & _ & _ & Hunch & _).
    assert (Hne : z <> yObj).
    { intro Heq. apply Hy. rewrite <- Heq.
      exact (@get_some_inv item z v (config_heap c1) Hz). }
    assert (Hz2 : binds z v Sigma).
    { rewrite <- Heq1. exact (Hsub z v Hz). }
    pose proof (Hunch z v Hne Hz2) as Hz3.
    rewrite Heq2. exact Hz3.
Qed.

Lemma no_frame_end_heap_sub : forall c1 c4 k,
  red_closure c1 k c4 ->
  (forall j c3, j < k -> ~ frame_end_in c1 j c3) ->
  SefStep c1 ->
  subheap_unchanged (config_heap c1) (config_heap c4).
Proof.
  intros c1 c4 k Hcl. revert c4 Hcl.
  induction k as [| n IH]; intros c4 Hcl Hnofe Hstep.
  - destruct (red_closure_inv Hcl) as [H0 | Hex].
    + destruct H0 as [E ->]. intros z v Hz. exact Hz.
    + destruct Hex as [m [c2 [E _]]]. discriminate E.
  - destruct (red_closure_inv Hcl) as [H0 | Hex].
    + destruct H0 as [E _]. discriminate E.
    + destruct Hex as [m [c2 [E [Hcln Hred]]]].
      injection E as Hnm. subst m.
      assert (Hsub2 : subheap_unchanged (config_heap c1) (config_heap c2)).
      { apply (IH c2 Hcln).
        - intros j c3 Hj Hfe. apply (Hnofe j c3).
          + lia.
          + exact Hfe.
        - exact Hstep. }
      eapply Hstep.
      * exact Hcln.
      * intros c3' Hfe. exact (Hnofe n c3' (Nat.lt_succ_diag_r n) Hfe).
      * exact Hred.
      * exact Hsub2.
Qed.

Lemma SefG_I_reduce :
  forall c1 c4 k,
    red_closure c1 k c4 ->
    SefStep c1 ->
    (exists j c3, frame_end_in c1 j c3 /\ j < k) \/
    subheap_unchanged (config_heap c1) (config_heap c4).
Proof.
  intros c1 c4 k Hcl Hstep.
  destruct (classic (exists j c3, frame_end_in c1 j c3 /\ j < k)) as [Hfe | Hno].
  - left. exact Hfe.
  - right. apply no_frame_end_heap_sub with (k:=k); auto.
    intros j c3 Hj Hfe. apply Hno. exists j, c3. split; assumption.
Qed.

(* Packaging of the reduction: the target's conclusion follows from the
   single semantic obligation [SefWrite] (no write step before the call frame
   ends targets a location of the initial heap). *)
Lemma SefG_I_of_SefWrite :
  forall (c1 c4:config) (k:nat),
    red_closure c1 k c4 ->
    SefWrite c1 ->
    (exists j c3, frame_end_in c1 j c3 /\ j < k) \/
    subheap_unchanged (config_heap c1) (config_heap c4).
Proof.
  intros c1 c4 k Hcl Hw.
  apply (@SefG_I_reduce c1 c4 k Hcl).
  exact (@SefStep_of_write c1 Hw).
Qed.

(* A run in which every heap-changing step targets a location outside H. *)
Inductive red_closure_fresh_writes (H : heap) : config -> nat -> config -> Prop :=
| rcfw_refl c :
    red_closure_fresh_writes H c 0 c
| rcfw_step c1 c2 c3 n y :
    red_closure_fresh_writes H c1 n c2 ->
    red c2 c3 ->
    changes_at_most (config_heap c2) (config_heap c3) y ->
    y \notin dom H ->
    red_closure_fresh_writes H c1 (S n) c3.

Lemma rcfw_preserves :
  forall H c1 k c4,
    subheap_unchanged H (config_heap c1) ->
    red_closure_fresh_writes H c1 k c4 ->
    subheap_unchanged H (config_heap c4).
Proof.
  intros H c1 k c4 Hsub Hcl. induction Hcl as [c | c1 c2 c3 n y Hcl IH Hred Hch Hy].
  - exact Hsub.
  - intros z v Hz.
    apply Hch.
    + intro Heq. apply Hy. rewrite <- Heq. exact (@get_some_inv item z v H Hz).
    + apply IH. { exact Hsub. } exact Hz.
Qed.

Lemma subheap_unchanged_of_fresh_writes :
  forall c1 c4 k,
    red_closure_fresh_writes (config_heap c1) c1 k c4 ->
    subheap_unchanged (config_heap c1) (config_heap c4).
Proof.
  intros c1 c4 k Hcl.
  eapply rcfw_preserves. 2: exact Hcl.
  intros z v Hz. exact Hz.
Qed.

(* Reduction only ever adds fresh environment bindings (the binders
   introduced by read/let allocation are fresh for the whole configuration),
   so every pre-existing environment binding survives every step. *)
Lemma red_preserves_env_binds : forall (c c':config),
  c ↦ c' ->
  forall w y, binds w y (config_env c) -> binds w y (config_env c').
Proof.
  intros c c' Hred. induction Hred.
  - (* red_read *)
    intros w y Hb. simpl. simpl in H. destruct H as [Hfresh _].
    apply binds_push_neq.
    + exact Hb.
    + intro E.
      assert (Hd : wVal \notin dom e).
      { apply notin_union_r in Hfresh. destruct Hfresh as [_ Hfresh].
        apply notin_union_r in Hfresh. destruct Hfresh as [_ Hfresh].
        apply notin_union_r in Hfresh. destruct Hfresh as [_ Hfresh].
        apply notin_union_r in Hfresh. destruct Hfresh as [Hrenv _].
        apply notin_union_r in Hrenv. destruct Hrenv as [Hdom _].
        exact Hdom. }
      apply Hd. rewrite <- E.
      exact (@get_some_inv var w y (config_env (trm_read (avar_f wObj) m ; fs ; Sigma ; e ; Lv)) Hb).
  - (* red_write *) intros w y Hb. simpl. exact Hb.
  - (* red_call *) intros w y Hb. simpl. exact Hb.
  - (* red_apply *) intros w y Hb. simpl. exact Hb.
  - (* red_let_fun *)
    intros w' y' Hb. simpl. simpl in H. destruct H as [Hy H]. destruct H as [Hw _]. simpl in Hw.
    apply binds_push_neq.
    + exact Hb.
    + intro E.
      assert (Hd : w \notin dom e).
      { apply notin_union_r in Hw. destruct Hw as [Hw _].
        apply notin_union_r in Hw. destruct Hw as [_ Hw].
        apply notin_union_r in Hw. destruct Hw as [_ Hw].
        apply notin_union_r in Hw. destruct Hw as [_ Hw].
        apply notin_union_r in Hw. destruct Hw as [Hrenv _].
        apply notin_union_r in Hrenv. destruct Hrenv as [Hdom _].
        exact Hdom. }
      apply Hd. rewrite <- E.
      exact (@get_some_inv var w' y' (config_env (trm_lit (lit_fun T t1) t2 ; fs ; Sigma ; e ; Lv)) Hb).
  - (* red_let_obj *)
    intros w' y' Hb. simpl. simpl in H. destruct H as [Hy H]. destruct H as [Hw _]. simpl in Hw.
    apply binds_push_neq.
    + exact Hb.
    + intro E.
      assert (Hd : w \notin dom e).
      { apply notin_union_r in Hw. destruct Hw as [Hw _].
        apply notin_union_r in Hw. destruct Hw as [_ Hw].
        apply notin_union_r in Hw. destruct Hw as [_ Hw].
        apply notin_union_r in Hw. destruct Hw as [_ Hw].
        apply notin_union_r in Hw. destruct Hw as [Hrenv _].
        apply notin_union_r in Hrenv. destruct Hrenv as [Hdom _].
        exact Hdom. }
      apply Hd. rewrite <- E.
      exact (@get_some_inv var w' y' (config_env (trm_lit (lit_obj T ds) t ; fs ; Sigma ; e ; Lv)) Hb).
  - (* red_let_var *) intros w y Hb. simpl. exact Hb.
  - (* red_let_push *) intros w y Hb. simpl. exact Hb.
Qed.

Lemma red_closure_preserves_env_binds :
  forall (c1:config) (k:nat) (c4:config),
    red_closure c1 k c4 ->
    forall w y, binds w y (config_env c1) -> binds w y (config_env c4).
Proof.
  intros c1 k c4 H. induction H as [C | C1 C2 C3 n Hcl Hstep IH].
  - intros w y Hb. exact Hb.
  - intros w y Hb. apply (red_preserves_env_binds IH). apply Hstep. exact Hb.
Qed.

(* Projection laws: subtyping into an intersection and out of a union. *)
Lemma subtyp_and_elim : forall (typing_mode:Mode) (G:ctx) (e:renv) (S T U:typ),
  G ⁏ e ⊢ S <: typ_and T U ->
  (G ⁏ e ⊢ S <: T) /\ (G ⁏ e ⊢ S <: U).
Proof.
  intros. split.
  - eapply subtyp_trans; [exact H | apply subtyp_and11].
  - eapply subtyp_trans; [exact H | apply subtyp_and12].
Qed.

Lemma subtyp_or_elim : forall (typing_mode:Mode) (G:ctx) (e:renv) (S U T:typ),
  G ⁏ e ⊢ typ_or S U <: T ->
  (G ⁏ e ⊢ S <: T) /\ (G ⁏ e ⊢ U <: T).
Proof.
  intros. split.
  - eapply subtyp_trans; [apply subtyp_or11 | exact H].
  - eapply subtyp_trans; [apply subtyp_or12 | exact H].
Qed.

(* The strip component produced by incapacitation is a supertype of the
   source type.  Hence capability reachability of the strip transfers back to
   the field type. *)
Lemma incap_strip_super : forall (typing_mode:Mode) (G:ctx) (Go:objctx) (e:renv)
                                 (T Tstrip:typ),
  @ty_incap typing_mode G Go e T Tstrip ->
  @subtyp typing_mode G objctx_empty e T Tstrip.
Proof.
  intros typing_mode G Go e T Tstrip H.
  dependent induction H.
  - apply subtyp_refl.
  - apply subtyp_bot.
  - apply subtyp_refl.
  - apply subtyp_top.
  - apply subtyp_refl.
  - apply subtyp_refl.
  - match goal with
    | HTy : (_ ⁏ _ ⊢ ?x ∶ typ_rcd (dec_typ ?B ?S ?T0)),
      IHx : (@subtyp _ _ _ _ (open ?y ?T0) ?Tp) |- _ =>
        eapply subtyp_trans; [eapply subtyp_sel1; exact HTy | exact IHx]
    end.
  - apply subtyp_refl.
  - apply subtyp_and2.
    + eapply subtyp_trans; [apply subtyp_and11 | eassumption].
    + eapply subtyp_trans; [apply subtyp_and12 | eassumption].
  - apply subtyp_or2.
    + eapply subtyp_trans; [eassumption | apply subtyp_or11].
    + eapply subtyp_trans; [eassumption | apply subtyp_or12].
  - apply subtyp_refl.
  - apply subtyp_refl.
Qed.

(* A syntactic under-approximation of "T can be viewed as a write capability":
   the least relation reaching [typ_mut_marker typ_bot] backwards along the
   subtyping rules.  If [T] is not in this relation, no type assignment can
   turn it into a writable reference by subtyping alone. *)
Inductive MutReach (typing_mode:Mode) : ctx -> renv -> typ -> Prop :=
| mr_mut G e :
    MutReach typing_mode G e (typ_mut_marker typ_bot)
| mr_and_l G e T U :
    MutReach typing_mode G e T ->
    MutReach typing_mode G e (typ_and T U)
| mr_and_r G e T U :
    MutReach typing_mode G e U ->
    MutReach typing_mode G e (typ_and T U)
| mr_or_l G e T U :
    MutReach typing_mode G e (typ_or T U) ->
    MutReach typing_mode G e T
| mr_or_r G e T U :
    MutReach typing_mode G e (typ_or T U) ->
    MutReach typing_mode G e U
| mr_or_intro G e T U :
    MutReach typing_mode G e T ->
    MutReach typing_mode G e U ->
    MutReach typing_mode G e (typ_or T U)
| mr_sub G e S T :
    (G ⁏ e ⊢ S <: T) ->
    MutReach typing_mode G e T ->
    MutReach typing_mode G e S
| mr_sel1 G e x (A:typ_label) S T y :
    (G ⁏ e ⊢ x ∶ typ_rcd (dec_typ A S T)) ->
    MutReach typing_mode G e (open y T) ->
    MutReach typing_mode G e (typ_sel (avar_f x) A (avar_f y))
| mr_sel2 G e x (A:typ_label) S T y :
    (G ⁏ e ⊢ x ∶ typ_rcd (dec_typ A S T)) ->
    MutReach typing_mode G e (typ_sel (avar_f x) A (avar_f y)) ->
    MutReach typing_mode G e (open y S).

Lemma MutReach_sound : forall (typing_mode:Mode) (G:ctx) (e:renv) (T:typ),
  MutReach typing_mode G e T ->
  G ⁏ e ⊢ T <: typ_mut_marker typ_bot.
Proof.
  intros typing_mode G e T H. induction H.
  - apply subtyp_refl.
  - eapply subtyp_trans; [apply subtyp_and11 | exact IHMutReach].
  - eapply subtyp_trans; [apply subtyp_and12 | exact IHMutReach].
  - eapply subtyp_trans; [apply subtyp_or11 | exact IHMutReach].
  - eapply subtyp_trans; [apply subtyp_or12 | exact IHMutReach].
  - apply subtyp_or2; assumption.
  - eapply subtyp_trans; [exact H | exact IHMutReach].
  - eapply subtyp_trans; [eapply subtyp_sel1; exact H | exact IHMutReach].
  - eapply subtyp_trans; [eapply subtyp_sel2; exact H | exact IHMutReach].
Qed.

(* [typ_nocap] reaching a write capability propagates to it: every supertype
   of [typ_nocap] is writable-reachable only if [typ_nocap] itself is. *)
Lemma MutReach_nocap_of_super :
  forall (typing_mode:Mode) (G:ctx) (e:renv) (T:typ),
    (G ⁏ e ⊢ typ_nocap <: T) ->
    MutReach typing_mode G e T ->
    MutReach typing_mode G e typ_nocap.
Proof.
  intros typing_mode G e T Hsub Hmr.
  eapply mr_sub; eassumption.
Qed.

Lemma not_MutReach_super_of_not_MutReach_nocap :
  forall (typing_mode:Mode) (G:ctx) (e:renv) (T:typ),
    ~ MutReach typing_mode G e typ_nocap ->
    (G ⁏ e ⊢ typ_nocap <: T) ->
    ~ MutReach typing_mode G e T.
Proof.
  intros typing_mode G e T Hn Hsub Hmr.
  apply Hn. eapply mr_sub; eassumption.
Qed.

(* The reachability relation is exact: it coincides with subtyping to the
   write capability.  So the remaining capability obligation is precisely
   nonderivability of [typ_nocap <: typ_mut_marker typ_bot] in the relevant
   inert/call context. *)
Lemma MutReach_sub_iff : forall (typing_mode:Mode) (G:ctx) (e:renv) (T:typ),
  MutReach typing_mode G e T <-> (G ⁏ e ⊢ T <: typ_mut_marker typ_bot).
Proof.
  intros. split.
  - apply MutReach_sound.
  - intro Hsub. eapply mr_sub; [exact Hsub | apply mr_mut].
Qed.

(* Union types reach the write capability exactly when both components do. *)
Lemma MutReach_or : forall (typing_mode:Mode) (G:ctx) (e:renv) (S U:typ),
  MutReach typing_mode G e (typ_or S U) <->
  (MutReach typing_mode G e S /\ MutReach typing_mode G e U).
Proof.
  intros. split.
  - intro H. rewrite MutReach_sub_iff in H.
    apply subtyp_or_elim in H. destruct H as [HS HU].
    split; rewrite MutReach_sub_iff; assumption.
  - intros [HS HU]. rewrite MutReach_sub_iff.
    apply subtyp_or2; rewrite <- MutReach_sub_iff; assumption.
Qed.

Lemma MutReach_sub : forall (typing_mode:Mode) (G:ctx) (e:renv) (S T:typ),
  (G ⁏ e ⊢ S <: T) -> MutReach typing_mode G e T -> MutReach typing_mode G e S.
Proof. intros. eapply mr_sub; eassumption. Qed.

Lemma MutReach_and_l : forall (typing_mode:Mode) (G:ctx) (e:renv) (T U:typ),
  MutReach typing_mode G e T -> MutReach typing_mode G e (typ_and T U).
Proof. intros. apply mr_and_l. assumption. Qed.

Lemma MutReach_and_r : forall (typing_mode:Mode) (G:ctx) (e:renv) (T U:typ),
  MutReach typing_mode G e U -> MutReach typing_mode G e (typ_and T U).
Proof. intros. apply mr_and_r. assumption. Qed.

(* Visibility has no case for [ctx_hide]: variables underneath a hidden
   context can never be shown visible.  In visibility modes this keeps a
   method body from naming ambient heap references in term position.
   (Selector typing uses [ty_var], which does *not* require visibility, so
   type-level uses of hidden references still need the separate inertness
   analysis.) *)
Lemma no_ctx_vis_hide : forall (G:ctx) (x:var),
  ~ ctx_vis (ctx_hide G) x.
Proof. intros. intro H. inversion H. Qed.

(* Consequently, in visibility modes no typed term can consist of a bare
   variable bound underneath a hidden context. *)
Lemma no_ty_trm_var_hide : forall (typing_mode:Mode) (G0:ctx) (Go:objctx)
                                  (e:renv) (x:var) (T:typ),
  mode_has_visibility typing_mode ->
  ~ (@ty_trm typing_mode (ctx_hide G0) Go e (trm_var (avar_f x)) T).
Proof.
  intros typing_mode G0 Go e x T Hvis Hty.
  dependent induction Hty.
  - exact (no_ctx_vis_hide (G:=G0) (x:=x) (H Hvis)).
  - exact (IHHty G0 x Hvis eq_refl eq_refl).
Qed.

(* General form: in a visibility mode, a variable that is not visible is not
   the subject of any term typing. *)
Lemma no_ty_trm_var_of_not_vis :
  forall (typing_mode:Mode) (G:ctx) (Go:objctx) (e:renv) (x:var) (T:typ),
    mode_has_visibility typing_mode ->
    ~ ctx_vis G x ->
    ~ (@ty_trm typing_mode G Go e (trm_var (avar_f x)) T).
Proof.
  intros typing_mode G Go e x T Hvis Hnvis Hty.
  dependent induction Hty.
  - exact (Hnvis (H Hvis)).
  - exact (IHHty x Hvis Hnvis eq_refl).
Qed.

(* Inversion of visibility at a context push. *)
Lemma ctx_vis_ctx_push_inv :
  forall (G:ctx) (v:var) (vk:varkind) (t:typ) (x:var),
    ctx_vis (ctx_push G v vk t) x ->
    x = v \/ (x <> v /\ ctx_vis G x).
Proof. intros. inversion H; subst; auto. Qed.

(* Hidden bindings stay invisible under any local context concatenated above
   the hidden context, provided the variable is not bound by the locals. *)
Lemma ctx_vis_hide_above : forall (Delta:ctx) (G0:ctx) (x:var),
  x §# Delta ->
  ~ ctx_vis ((ctx_hide G0) §& Delta) x.
Proof.
  intros Delta. induction Delta as [| Delta' IH v vk t | Delta' IH | Delta' IH];
    intros G0 x Hnin Hv.
  - simpl in Hv. exact (no_ctx_vis_hide (G:=G0) (x:=x) Hv).
  - simpl in Hv, Hnin.
    apply notin_union_r in Hnin. destruct Hnin as [Hnv HnDelta].
    apply ctx_vis_ctx_push_inv in Hv. destruct Hv as [Heq | [Hneq Hvis]].
    + rewrite <- Heq in Hnv. exact (Hnv (in_singleton_self x)).
    + apply (IH G0 x HnDelta Hvis).
  - simpl in Hv. inversion Hv.
  - simpl in Hv. inversion Hv.
Qed.

(* In a visibility-hiding mode, [vis_hide] is [ctx_hide]. *)
Lemma vis_hide_hide : forall (typing_mode:Mode),
  mode_visibility' typing_mode = mode_visibility_hide_method ->
  forall (G:ctx),
  (match mode_visibility' typing_mode with
   | mode_visibility_all => G
   | mode_visibility_hide_method => ctx_hide G
   end) = ctx_hide G.
Proof. intros typing_mode H G. rewrite H. reflexivity. Qed.

(* The only visible variables of a method body context are its parameter and
   its receiver: the ambient context (and an object literal's self variable)
   sit underneath the [ctx_hide] and can never be shown visible.  This is what
   restricts the run-time term variables of a heap method body to [xz], [xc]
   and the locals bound inside the body. *)
Lemma ctx_obj_met_vis_inv : forall (typing_mode:Mode) (G:ctx) (Go:objctx)
                                   (xz:var) (TZ:typ) (xc:var) (TC:typ) (v:var),
  mode_visibility' typing_mode = mode_visibility_hide_method ->
  ctx_vis (ctx_obj_met typing_mode G Go xz TZ xc TC) v ->
  v = xz \/ v = xc.
Proof.
  intros typing_mode G Go xz TZ xc TC v Hvis H.
  unfold ctx_obj_met in H.
  destruct Go; simpl in H.
  - rewrite (@vis_hide_hide typing_mode Hvis G) in H.
    apply ctx_vis_ctx_push_inv in H. destruct H as [-> | [_ H]].
    + auto.
    + apply ctx_vis_ctx_push_inv in H. destruct H as [-> | [_ H2]].
      * auto.
      * exfalso. exact (no_ctx_vis_hide H2).
  - rewrite (@vis_hide_hide typing_mode Hvis (G § x / v_self ~ open x T)) in H.
    apply ctx_vis_ctx_push_inv in H. destruct H as [-> | [_ H]].
    + auto.
    + apply ctx_vis_ctx_push_inv in H. destruct H as [-> | [_ H2]].
      * auto.
      * exfalso. exact (no_ctx_vis_hide H2).
  - rewrite (@vis_hide_hide typing_mode Hvis G) in H.
    apply ctx_vis_ctx_push_inv in H. destruct H as [-> | [_ H]].
    + auto.
    + apply ctx_vis_ctx_push_inv in H. destruct H as [-> | [_ H2]].
      * auto.
      * exfalso. exact (no_ctx_vis_hide H2).
Qed.

(* In the target's modes, related reference/location types share their record
   part; the reference's refcap is [mut_marker Tbnd], the location's is
   [mut_marker typ_bot]. *)
Lemma ctx_binds_k_after_ctx_binds : forall (G1 G2:ctx) (v:var) (vk:varkind) (t:typ),
  ctx_binds_k_after v vk t G1 G2 -> ctx_binds v t G1.
Proof.
  intros G1 G2 v vk t H. induction H.
  - apply ctx_binds_e.
  - apply ctx_binds_n; assumption.
Qed.

(* In an ok context, a variable has at most one binding type. *)
Lemma ctx_binds_unique : forall (G:ctx) (x:var) (T1 T2:typ),
  ctx_ok G -> ctx_binds x T1 G -> ctx_binds x T2 G -> T1 = T2.
Proof.
  intros G. induction G as [| G0 IH v vk t | G0 IH | G0 IH];
    intros x T1 T2 Hokb Hb1 Hb2.
  - inversion Hb1.
  - inversion Hokb; subst.
    inversion Hb1; subst; inversion Hb2; subst;
      try reflexivity; try congruence;
      try (match goal with
           | Hok0 : ctx_ok G0, B1 : ctx_binds x ?A G0, B2 : ctx_binds x ?B G0
             |- ?A = ?B => exact (IH x A B Hok0 B1 B2)
           end).
  - inversion Hb1.
  - inversion Hokb; subst. inversion Hb1; subst. inversion Hb2; subst.
    apply (IH x T1 T2); assumption.
Qed.

(* A bound variable lies in the context domain. *)
Lemma ctx_binds_dom : forall (G:ctx) (v:var) (t:typ),
  ctx_binds v t G -> v \in ctx_dom G.
Proof.
  intros G v t H. induction H.
  - simpl. rewrite in_union, in_singleton. left; reflexivity.
  - simpl. rewrite in_union. right; assumption.
  - simpl. assumption.
Qed.

(* Membership in [ctx_kdom] is exactly the [ctx_k] judgement, for a context
   that only grows by pushes (in particular an inert context): the two
   definitions are the extensional and structural views of the same
   variable-kind information. *)
Lemma in_ctx_kdom_iff : forall (G:ctx) (v:var) (vk:varkind),
  ctx_weakens G -> ctx_ok G ->
  (v \in ctx_kdom vk G <-> ctx_k G v vk).
Proof.
  intros G v vk Hw. induction Hw as [| G0 v2 vk2 t0 Hw0 IHHw]; intro Hok.
  - split.
    + intro H. rewrite in_empty in H. destruct H.
    + intros (t' & G2 & Hb). inversion Hb.
  - inversion Hok as [| ? ? ? ? HokG Hnotin | ? HokS | ? HokH]; subst.
    split.
    + intro H. cbn [ctx_kdom] in H.
      destruct (classicT (vk = vk2)) as [Heq | Hneq].
      * rewrite in_union in H. rewrite in_singleton in H.
        destruct H as [Hv | Hk].
        -- subst v. subst vk2. exists t0. exists G0. apply ctx_binds_k_e.
        -- apply (proj1 (IHHw HokG)) in Hk. destruct Hk as (t' & G2 & Hb).
           exists t', G2. apply ctx_binds_k_n.
           ++ intro E. subst v. apply Hnotin.
              exact (@ctx_binds_dom G0 v2 t'
                       (@ctx_binds_k_after_ctx_binds G0 G2 v2 vk t' Hb)).
           ++ exact Hb.
      * apply (proj1 (IHHw HokG)) in H. destruct H as (t' & G2 & Hb).
        exists t', G2. apply ctx_binds_k_n.
        -- intro E. subst v. apply Hnotin.
           exact (@ctx_binds_dom G0 v2 t'
                    (@ctx_binds_k_after_ctx_binds G0 G2 v2 vk t' Hb)).
        -- exact Hb.
    + intros (t' & G2 & Hb). inversion Hb as [| ? ? ? ? ? ? Hne Haft]; subst.
      * cbn [ctx_kdom].
        match goal with |- _ \in If ?P then _ else _ =>
          destruct (classicT P) as [Heq | Hneq] end.
        -- rewrite in_union, in_singleton. left; reflexivity.
        -- exfalso. apply Hneq. reflexivity.
      * cbn [ctx_kdom].
        assert (HkG : ctx_k G0 v vk) by (exists t', G2; assumption).
        apply (proj2 (IHHw HokG)) in HkG.
        destruct (classicT (vk = vk2)) as [Heq | Hneq].
        -- rewrite in_union. right. exact HkG.
        -- exact HkG.
Qed.

(* The closure of a variable's binding type under the variable typing rules:
   everything a variable can be typed at is obtained from its binding type by
   subtyping, conjunction, recursive introduction/elimination and the
   mutability-top rule.  This makes the "what can this variable be viewed as"
   analysis a concrete inductive object. *)
Inductive Der (typing_mode:Mode) (G:ctx) (e:renv) (x:var) : typ -> typ -> Prop :=
| der_refl T :
    Der typing_mode G e x T T
| der_sub T U V :
    Der typing_mode G e x T U ->
    @subtyp typing_mode G objctx_empty e U V ->
    Der typing_mode G e x T V
| der_and T U V :
    Der typing_mode G e x T U ->
    Der typing_mode G e x T V ->
    Der typing_mode G e x T (typ_and U V)
| der_rec_intro T U :
    Der typing_mode G e x T (open x U) ->
    typ_indep_b 0 U ->
    ((mode_has_incap typing_mode) ->
      @ty_incap typing_mode G objctx_empty e (open x U) (open x U)) ->
    Der typing_mode G e x T (typ_bnd U)
| der_rec_elim T U :
    Der typing_mode G e x T (typ_bnd U) ->
    typ_indep_b 0 U ->
    Der typing_mode G e x T (open x U)
| der_mut_top T U :
    mode_has_mutability typing_mode ->
    Der typing_mode G e x T U ->
    Der typing_mode G e x T (typ_mut_marker typ_top).

(* Every variable typing factors through the variable's unique context
   binding: it is an element of the [Der] closure of that binding. *)
Lemma ty_var_Der : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var) (T:typ),
  @ty_var typing_mode G objctx_empty e x T ->
  forall T0, ctx_binds x T0 G -> ctx_ok G ->
  @Der typing_mode G e x T0 T.
Proof.
  intros typing_mode G e x T H.
  dependent induction H; intros T0 Hb Hok.
  - (* ty_var_var *) eapply der_sub.
    + apply der_refl.
    + match goal with
      | Hc : ctx_binds x T G |- _ =>
          assert (E : T = T0) by (eapply ctx_binds_unique; eassumption);
          subst T; apply subtyp_refl
      end.
  - (* ty_rec_intro *) eapply der_rec_intro.
    + match goal with
      | IH : objctx_empty = objctx_empty ->
             forall T0 : typ, ctx_binds x T0 G -> ctx_ok G ->
             Der typing_mode G e x T0 (open x ?U) |- _ =>
          eapply IH; [ reflexivity | eassumption | eassumption ]
      end.
    + eassumption.
    + eassumption.
  - (* ty_rec_elim *) eapply der_rec_elim.
    + match goal with
      | IH : objctx_empty = objctx_empty ->
             forall T0 : typ, ctx_binds x T0 G -> ctx_ok G ->
             Der typing_mode G e x T0 (typ_bnd ?U) |- _ =>
          eapply IH; [ reflexivity | eassumption | eassumption ]
      end.
    + eassumption.
  - (* ty_var_and *) eapply der_and.
    + match goal with
      | IH : objctx_empty = objctx_empty ->
             forall T0 : typ, ctx_binds x T0 G -> ctx_ok G ->
             Der typing_mode G e x T0 ?U |- _ =>
          eapply IH; [ reflexivity | eassumption | eassumption ]
      end.
    + match goal with
      | IH : objctx_empty = objctx_empty ->
             forall T0 : typ, ctx_binds x T0 G -> ctx_ok G ->
             Der typing_mode G e x T0 ?U |- _ =>
          eapply IH; [ reflexivity | eassumption | eassumption ]
      end.
  - (* ty_var_sub *) eapply der_sub.
    + match goal with
      | IH : objctx_empty = objctx_empty ->
             forall T0 : typ, ctx_binds x T0 G -> ctx_ok G ->
             Der typing_mode G e x T0 ?U |- _ =>
          eapply IH; [ reflexivity | eassumption | eassumption ]
      end.
    + eassumption.
  - (* ty_var_mut_top *) eapply der_mut_top.
    + eassumption.
    + match goal with
      | IH : objctx_empty = objctx_empty ->
             forall T0 : typ, ctx_binds x T0 G -> ctx_ok G ->
             Der typing_mode G e x T0 ?U |- _ =>
          eapply IH; [ reflexivity | eassumption | eassumption ]
      end.
Qed.

(* Converse direction: [Der] is sound for variable typing.  Together with
   [ty_var_Der] this makes [Der] an exact characterisation of the types a
   variable can be viewed at, given its (unique) context binding. *)
Lemma Der_ty_var : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                          (T0 T:typ),
  @Der typing_mode G e x T0 T ->
  ctx_binds x T0 G ->
  @ty_var typing_mode G objctx_empty e x T.
Proof.
  intros typing_mode G e x T0 T H. induction H; intro Hb.
  - apply ty_var_var. exact Hb.
  - eapply ty_var_sub; [ apply IHDer; exact Hb | eassumption ].
  - eapply ty_var_and; [ apply IHDer1; exact Hb | apply IHDer2; exact Hb ].
  - eapply ty_rec_intro.
    + apply IHDer; exact Hb.
    + eassumption.
    + eassumption.
  - eapply ty_rec_elim; [ apply IHDer; exact Hb | eassumption ].
  - eapply ty_var_mut_top; [ eassumption | apply IHDer; exact Hb ].
Qed.

(* Exact characterisation of the views of a variable. *)
Lemma ty_var_Der_iff : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                              (T0 T:typ),
  ctx_binds x T0 G -> ctx_ok G ->
  (@ty_var typing_mode G objctx_empty e x T <->
   @Der typing_mode G e x T0 T).
Proof.
  intros typing_mode G e x T0 T Hb Hok. split.
  - intro H. eapply ty_var_Der; eassumption.
  - intro H. eapply Der_ty_var; eassumption.
Qed.

(* Elimination of a conjunction view: any conjunct view is itself derivable
   (via subtyping [subtyp_and11]/[subtyp_and12] and the exactness of [Der]). *)
Lemma Der_and_inv : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                           (T0 A B:typ),
  ctx_binds x T0 G -> ctx_ok G ->
  @Der typing_mode G e x T0 (typ_and A B) ->
  @Der typing_mode G e x T0 A /\ @Der typing_mode G e x T0 B.
Proof.
  intros typing_mode G e x T0 A B Hb Hok Hd. split.
  - eapply ty_var_Der.
    + eapply ty_var_sub.
      * eapply Der_ty_var; eassumption.
      * apply subtyp_and11.
    + exact Hb.
    + exact Hok.
  - eapply ty_var_Der.
    + eapply ty_var_sub.
      * eapply Der_ty_var; eassumption.
      * apply subtyp_and12.
    + exact Hb.
    + exact Hok.
Qed.

(* The leaves of the [Der] closure of an inert object-reference binding:
   the recursive record part (opened at the variable) and the refcap part. *)
Lemma Der_inert_open : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                              (U S:typ),
  typ_indep_b 0 U ->
  @Der typing_mode G e x (typ_objref U S) (open x U).
Proof.
  intros typing_mode G e x U S Hi. eapply der_rec_elim.
  - eapply der_sub.
    + apply der_refl.
    + apply subtyp_and11.
  - exact Hi.
Qed.

Lemma Der_inert_refcap : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                                (U S:typ),
  @Der typing_mode G e x (typ_objref U S) S.
Proof.
  intros. eapply der_sub.
  - apply der_refl.
  - apply subtyp_and12.
Qed.

(* The [Der] closure is closed under supertyping and the mutability-top rule. *)
Lemma Der_sub_view : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                            (T0 T U:typ),
  @Der typing_mode G e x T0 T ->
  @subtyp typing_mode G objctx_empty e T U ->
  @Der typing_mode G e x T0 U.
Proof. intros. eapply der_sub; eassumption. Qed.

Lemma Der_mut_top_intro : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                                 (T0 T:typ),
  mode_has_mutability typing_mode ->
  @Der typing_mode G e x T0 T ->
  @Der typing_mode G e x T0 (typ_mut_marker typ_top).
Proof. intros. eapply der_mut_top; eassumption. Qed.

Lemma Der_and_intro : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                             (T0 A B:typ),
  @Der typing_mode G e x T0 A ->
  @Der typing_mode G e x T0 B ->
  @Der typing_mode G e x T0 (typ_and A B).
Proof. intros. eapply der_and; eassumption. Qed.

Lemma Der_rec_elim_view : forall (typing_mode:Mode) (G:ctx) (e:renv) (x:var)
                                 (T0 U:typ),
  @Der typing_mode G e x T0 (typ_bnd U) ->
  typ_indep_b 0 U ->
  @Der typing_mode G e x T0 (open x U).
Proof. intros. eapply der_rec_elim; eassumption. Qed.

Lemma typ_refcap_corr_mut_iff : forall (typing_mode:Mode) (Tw Ty:typ),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  ((match mode_refcap_corr' typing_mode with
    | mode_refcap_corr_same => Ty = Tw
    | mode_refcap_corr_ref_mutability =>
        exists Tbnd, Tw = typ_mut_marker Tbnd /\ Ty = typ_mut_marker typ_bot
    end) <->
   (exists Tbnd, Tw = typ_mut_marker Tbnd /\ Ty = typ_mut_marker typ_bot)).
Proof.
  intros typing_mode Tw Ty Hs Hm.
  destruct typing_mode; simpl in *; try discriminate; simpl; tauto.
Qed.

Lemma typ_corr_objref_inv : forall (typing_mode:Mode) (Tw Ty:typ),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  @typ_corr typing_mode Tw Ty ->
  exists U S S', Tw = typ_objref U S /\ Ty = typ_objref U S' /\
    (exists Tbnd, S = typ_mut_marker Tbnd) /\ S' = typ_mut_marker typ_bot.
Proof.
  intros typing_mode Tw Ty Hs Hm Hcorr.
  inversion Hcorr; subst.
  - match goal with
    | Hrc : context [mode_refcap_corr' typing_mode] |- _ =>
        apply (proj1 (typ_refcap_corr_mut_iff typing_mode _ _ Hs Hm)) in Hrc;
        destruct Hrc as (Tbnd & HS & HU)
    end.
    eexists T, S, U.
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- exists Tbnd. assumption.
        -- assumption.
  - exfalso. eapply mode_sef_mut_no_fun; eassumption.
Qed.

(* Mode equations for the capability machinery in the target's modes. *)
Lemma mode_sef_mut_incap : forall (m:mode),
  mode_has_sef m -> mode_has_mutability m -> mode_incap' m = mode_incap_nocap.
Proof. intros m Hs Hm. destruct m; simpl in *; discriminate || reflexivity. Qed.

Lemma mode_sef_mut_ty_inv : forall (m:mode),
  mode_has_sef m -> mode_has_mutability m -> mode_ty_inv' m = mode_ty_inv_layered.
Proof. intros m Hs Hm. destruct m; simpl in *; discriminate || reflexivity. Qed.

(* The four possible modes split into the subtype and complement groups, so
   the two mode-specific top/nocap rules can be handled by cases. *)
Lemma mode_top_nm_cases : forall (m:mode),
  mode_has_sef m -> mode_has_mutability m ->
  mode_top_nm' m = mode_top_nm_subtype \/ mode_top_nm' m = mode_top_nm_complement.
Proof.
  intros m Hs Hm. destruct m; simpl in *; try discriminate;
    try (left; reflexivity); try (right; reflexivity).
Qed.

Lemma mode_mut_top_cases : forall (m:mode),
  mode_has_sef m -> mode_has_mutability m ->
  (mode_mut_top' m = mode_mut_top_subtype \/
   mode_mut_top' m = mode_mut_top_none).
Proof.
  intros m Hs Hm. destruct m; simpl in *; try discriminate;
    try (left; reflexivity); try (right; reflexivity).
Qed.

(* In the target's modes there are no functions, so function literals and
   applications can never be typed.  This eliminates the [red_apply] and
   [red_let_fun] cases from the runtime argument. *)
Lemma no_ty_lit_fun_sef : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                 (S:typ) (t1:trm) (T:typ),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  ~ (@ty_lit typing_mode G objctx_empty e (lit_fun S t1) T).
Proof.
  intros typing_mode G e S t1 T Hs Hm H.
  dependent induction H.
  exfalso. eapply mode_sef_mut_no_fun; eassumption.
Qed.

Lemma no_ty_trm_apply_sef : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                   (wx wz:var) (T:typ),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  ~ (@ty_trm typing_mode G objctx_empty e (trm_apply (avar_f wx) (avar_f wz)) T).
Proof.
  intros typing_mode G e wx wz T Hs Hm H.
  dependent induction H.
  - exfalso. eapply mode_sef_mut_no_fun; eassumption.
  - match goal with
    | IHgen : forall (w1 w2:var), _ -> _ -> _ -> _ -> _ |- _ =>
      exact (IHgen wx wz Hs Hm eq_refl eq_refl)
    end.
Qed.

Lemma no_ty_trm_lit_fun_sef : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                      (S:typ) (t1 t2:trm) (T:typ),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  ~ (@ty_trm typing_mode G objctx_empty e (trm_lit (lit_fun S t1) t2) T).
Proof.
  intros typing_mode G e S t1 t2 T Hs Hm H.
  dependent induction H.
  - exfalso. eapply no_ty_lit_fun_sef; eassumption.
  - match goal with
    | IHgen : forall (S0:typ) (t3 t4:trm), _ -> _ -> _ -> _ -> _ |- _ =>
      exact (IHgen S t1 t2 Hs Hm eq_refl eq_refl)
    end.
Qed.

(* Inversion of the typing of a call term: it exposes the method's capability,
   argument and result types, the receiver/argument typings, the capability
   check, and the result subtyping (the possible [ty_trm_sub] wrapper). *)
Lemma ty_trm_call_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                               (w1:var) (m:met_label) (w2:var) (T:typ),
  @ty_trm typing_mode G objctx_empty e (trm_call (avar_f w1) m (avar_f w2)) T ->
  exists TC TZ TR T',
    T' = open_met w2 w1 TR /\
    (G ⁏ e ⊢ w1 ∶ typ_rcd (dec_met m TC TZ TR)) /\
    (G ⁏ e ⊢ w2 ∶ TZ) /\
    (mode_has_sef typing_mode -> typ_indep_b 0 TC) /\
    (G ⁏ e ⊢ w1 ∶ open w2 TC) /\
    (G ⁏ e ⊢ T' <: T).
Proof.
  intros typing_mode G e w1 m w2 T H.
  dependent induction H.
  - eexists _, _, _, (open_met w2 w1 _).
    repeat split; try reflexivity; try eassumption; try apply subtyp_refl.
  - match goal with
    | IHgen : forall (w3:var) (m0:met_label) (w4:var), _ -> _ -> _ |- _ =>
      destruct (IHgen w1 m w2 eq_refl eq_refl)
        as (TC & TZ & TR & T' & Heq & Hw1 & Hw2 & Hse & Hcap & Hsub)
    end.
    exists TC, TZ, TR, T'.
    repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

(* In the target's modes viewpoint adaptation is the mutability variant and
   splits into an incapacitation and a capability bound of the field type. *)
Lemma mode_sef_mut_viewpoint : forall (m:mode),
  mode_has_sef m -> mode_has_mutability m ->
  mode_viewpoint_adaptation' m = mode_viewpoint_adapt_mutability.
Proof. intros m Hs Hm. destruct m; simpl in *; discriminate || reflexivity. Qed.

Lemma viewpoint_adapt_mut_inv : forall (typing_mode:Mode) (x:var) (G:ctx) (Go:objctx)
                                       (e:renv) (Tf Tr:typ),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  @viewpoint_adapt typing_mode x G Go e Tf Tr ->
  exists Tstrip Tcap,
    (G §§ Go ⁏ e ⊢ Tf ∶icp Tstrip) /\
    (G §§ Go ⁏ e ⊢ Tf ∶cpb⟦typ_refcap_mutability⟧ Tcap) /\
    Tr = typ_and Tstrip (typ_cap_adapt typ_refcap_mutability x Tcap).
Proof.
  intros typing_mode x G Go e Tf Tr Hs Hm Hvw.
  pose proof (mode_sef_mut_viewpoint typing_mode Hs Hm) as Hmv.
  unfold viewpoint_adapt in Hvw.
  rewrite Hmv in Hvw. simpl in Hvw.
  inversion Hvw; subst.
  eexists _, _. repeat split; try eassumption; reflexivity.
Qed.

(* Inversion of a variable term's typing: exposure of the variable typing,
   visibility, and result subtyping. *)
Lemma ty_trm_var_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                              (x:var) (T:typ),
  @ty_trm typing_mode G objctx_empty e (trm_var (avar_f x)) T ->
  exists T0,
    (G ⁏ e ⊢ x ∶ T0) /\ vis_var typing_mode G x /\ (G ⁏ e ⊢ T0 <: T).
Proof.
  intros typing_mode G e x T H.
  dependent induction H.
  - eexists _. repeat split; try eassumption; apply subtyp_refl.
  - match goal with
    | IHgen : forall (w:var), _ -> _ -> _ |- _ =>
      destruct (IHgen x eq_refl eq_refl) as (T0 & Hty & Hvis & Hsub)
    end.
    exists T0. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

(* Inversion of the typing of a read term: it exposes the receiver's field
   record, the viewpoint adaptation used, and the result subtyping. *)
Lemma ty_trm_read_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                               (wx:var) (a:fld_label) (T:typ),
  @ty_trm typing_mode G objctx_empty e (trm_read (avar_f wx) a) T ->
  exists S Tf T0,
    (G ⁏ e ⊢ wx ∶ typ_rcd (dec_fld a S Tf)) /\
    @viewpoint_adapt typing_mode wx G objctx_empty e Tf T0 /\
    (G ⁏ e ⊢ T0 <: T).
Proof.
  intros typing_mode G e wx a T H.
  dependent induction H.
  - eexists _, _, _. repeat split; try eassumption; try apply subtyp_refl.
  - match goal with
    | IHgen : forall (w:var) (a0:fld_label), _ -> _ -> _ |- _ =>
      destruct (IHgen wx a eq_refl eq_refl)
        as (S & Tf & T0 & Hwx & Hvw & Hsub)
    end.
    exists S, Tf, T0. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

(* Inversion of the typing of a write term: it exposes the field type, the
   written value's typing, the mutability requirement, and the result
   subtyping. *)
Lemma ty_trm_write_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                (wx:var) (a:fld_label) (wy:var) (T:typ),
  @ty_trm typing_mode G objctx_empty e (trm_write (avar_f wx) a (avar_f wy)) T ->
  exists S Tf T',
    T' = Tf /\
    (G ⁏ e ⊢ wx ∶ typ_rcd (dec_fld a S Tf)) /\
    (G ⁏ e ⊢ wy ∶ S) /\
    mut_var_writeable typing_mode G e wx /\
    (G ⁏ e ⊢ T' <: T).
Proof.
  intros typing_mode G e wx a wy T H.
  dependent induction H.
  - eexists _, _, _. repeat split; try reflexivity; try eassumption; try apply subtyp_refl.
  - match goal with
    | IHgen : forall (w3:var) (a0:fld_label) (w4:var), _ -> _ -> _ |- _ =>
      destruct (IHgen wx a wy eq_refl eq_refl)
        as (S & Tf & T' & Heq & Hwx & Hwy & Hmut & Hsub)
    end.
    exists S, Tf, T'.
    repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

(* In the target's modes a write's target is typed at the write capability. *)
Lemma ty_trm_write_target_mut : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                       (wx:var) (a:fld_label) (wy:var) (T:typ),
  mode_has_mutability typing_mode ->
  @ty_trm typing_mode G objctx_empty e (trm_write (avar_f wx) a (avar_f wy)) T ->
  exists S Tf,
    (G ⁏ e ⊢ wx ∶ typ_rcd (dec_fld a S Tf)) /\
    (G ⁏ e ⊢ wy ∶ S) /\
    (G ⁏ e ⊢ wx ∶ typ_mut_marker typ_bot).
Proof.
  intros typing_mode G e wx a wy T Hmut H.
  destruct (ty_trm_write_inv H) as (S & Tf & T' & Heq & Hwx & Hwy & Hmw & Hsub).
  exists S, Tf. split; [exact Hwx | split; [exact Hwy | apply Hmw; exact Hmut]].
Qed.

(* Inversions of let and literal term typings, exposing the bound value's
   type and the continuation typing. *)
Lemma ty_trm_let_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                              (s u:trm) (T:typ),
  @ty_trm typing_mode G objctx_empty e (trm_let s u) T ->
  exists S L T',
    (G ⁏ e ⊢ T' <: T) /\
    (G ⁏ e ⊢ s ∶ S) /\
    (forall x, x \notin L ->
      @ty_trm typing_mode (G § x / v_let ~ S) objctx_empty e (open x u) T').
Proof.
  intros typing_mode G e s u T H.
  dependent induction H.
  - eexists _, _, _. repeat split; try eassumption; try apply subtyp_refl.
  - match goal with
    | IHgen : forall (s0 u0:trm), _ -> _ -> _ |- _ =>
      destruct (IHgen s u eq_refl eq_refl) as (S & L & T' & Hsub & Hs & Hu)
    end.
    exists S, L, T'. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Lemma ty_trm_lit_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                              (l:lit) (u:trm) (T:typ),
  @ty_trm typing_mode G objctx_empty e (trm_lit l u) T ->
  exists S L T',
    (G ⁏ e ⊢ T' <: T) /\
    (G ⁏ e ⊢ l ∶ S) /\
    (forall x, x \notin L ->
      @ty_trm typing_mode (G § x / v_let ~ S) objctx_empty e (open x u) T').
Proof.
  intros typing_mode G e l u T H.
  dependent induction H.
  - eexists _, _, _. repeat split; try eassumption; try apply subtyp_refl.
  - match goal with
    | IHgen : forall (l0:lit) (u0:trm), _ -> _ -> _ |- _ =>
      destruct (IHgen l u eq_refl eq_refl) as (S & L & T' & Hsub & Hl & Hu)
    end.
    exists S, L, T'. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

(* Inversion of a field-definition typing: the stored location is visible and
   typed at the field type. *)
Lemma ty_def_fld_inv : forall (typing_mode:Mode) (G:ctx) (Go:objctx) (e:renv)
                              (a:fld_label) (t:var) (D:dec),
  @ty_def typing_mode G Go e (def_fld a (avar_f t)) D ->
  exists T,
    D = dec_fld a T T /\
    vis_var typing_mode (G §§& Go) t /\
    ((G §§& Go) ⁏ e ⊢ t ∶ T).
Proof.
  intros typing_mode G Go e a t D H.
  inversion H; subst.
  eexists. split; [reflexivity | split; eassumption].
Qed.

(* The type of a fresh object literal in the target's modes: a recursive
   record together with the mutable refcap. *)
Lemma typ_objlit_mut : forall (typing_mode:Mode) (T:typ),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  typ_objlit typing_mode T = typ_and (typ_bnd T) (typ_mut_marker typ_bot).
Proof.
  intros typing_mode T Hs Hm.
  destruct typing_mode; simpl in *; try discriminate; reflexivity.
Qed.

(* Inversion of an object-literal typing. *)
Lemma ty_lit_obj_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                              (T:typ) (ds:defs) (U:typ),
  @ty_lit typing_mode G objctx_empty e (lit_obj T ds) U ->
  U = typ_objlit typing_mode T /\
  (exists L, (forall x, x \notin L ->
      G §§ (objctx_lit x T) ⁏ e ⊢ (open x ds) ∶ (open x T)) /\
    typ_indep_b 0 T).
Proof.
  intros typing_mode G e T ds U H.
  inversion H; subst.
  split.
  - reflexivity.
  - eexists. split; eassumption.
Qed.

(* Basic decompositions of record membership. *)
Lemma record_has_rcd : forall (D D':dec), record_has (typ_rcd D) D' -> D = D'.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma record_has_and_inv : forall (T U:typ) (D:dec),
  record_has (typ_and T U) D -> record_has T D \/ record_has U D.
Proof. intros. inversion H; subst; auto. Qed.

(* A nullary type is equivalent only to itself.  This is the [tyq] case of
   the subtyping analysis behind the capability model. *)
Lemma tyq_nulary_gen : forall (e:renv) (a b:typ),
  tyq_typ e a b -> typ_nulary a -> b = a.
Proof.
  intros e a b H. induction H; intros Ha.
  - reflexivity.
  - destruct H; inversion Ha.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
  - inversion Ha.
Qed.

Lemma tyq_nocap : forall (e:renv) (T:typ),
  tyq_typ e typ_nocap T -> T = typ_nocap.
Proof. intros e T H. apply (tyq_nulary_gen H typ_nulary_nocap). Qed.

Lemma tyq_top : forall (e:renv) (T:typ),
  tyq_typ e typ_top T -> T = typ_top.
Proof. intros e T H. apply (tyq_nulary_gen H typ_nulary_top). Qed.

Lemma tyq_bot : forall (e:renv) (T:typ),
  tyq_typ e typ_bot T -> T = typ_bot.
Proof. intros e T H. apply (tyq_nulary_gen H typ_nulary_bot). Qed.

(* Right-side version: the type equivalent to a nullary type on the right is
   that nullary type itself. *)
(* Opening cannot turn a type into a nullary one. *)
Lemma open_bot_eq : forall (x:var) (T:typ), open x T = typ_bot -> T = typ_bot.
Proof.
  intros x T H. destruct T; simpl in *; try discriminate; reflexivity.
Qed.

Lemma tyq_bot_r : forall (e:renv) (a b:typ),
  tyq_typ e a b -> b = typ_bot -> a = typ_bot.
Proof.
  intros e a b H. induction H; intros Hb.
  - exact Hb.
  - destruct H; discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
Qed.

(* Last-rule analysis of [T <: typ_bot]: only bottom, the impossible/reflexive
   and equivalence cases, a transitivity step, a disjunction/intersection
   shape, or a selector can occur. *)
Lemma subtyp_bot_cases : forall (typing_mode:Mode) (G:ctx) (e:renv) (T:typ),
  @subtyp typing_mode G objctx_empty e T typ_bot ->
  T = typ_bot \/
  (exists X, @subtyp typing_mode G objctx_empty e T X /\
             @subtyp typing_mode G objctx_empty e X typ_bot) \/
  (exists S U, T = typ_or S U) \/
  (exists S U, T = typ_and S U) \/
  (exists x (A:typ_label) y, T = typ_sel (avar_f x) A (avar_f y)).
Proof.
  intros typing_mode G e T H.
  inversion H; subst; try discriminate;
    try (left; reflexivity);
    try (right; left; eexists; split; eassumption);
    try (right; right; left; eexists; eexists; reflexivity);
    try (right; right; right; left; eexists; eexists; reflexivity);
    try (right; right; right; right; eexists; eexists; eexists; reflexivity).
  - left. eapply tyq_bot_r.
    + eassumption.
    + reflexivity.
Qed.

(* Right-side version of [tyq_mutmarker_gen]: the type equivalent to the
   write capability on the right is that marker itself. *)
Lemma tyq_mutmarker_r_gen : forall (x0:var) (e:renv) (a b:typ),
  tyq_typ e a b -> b = typ_mut_marker typ_bot ->
  a = typ_mut_marker typ_bot.
Proof.
  intros x0 e a b H. induction H; intros Hb.
  - exact Hb.
  - destruct H; discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
  - injection Hb as HB Ht21 Ht22. subst B t21 t22.
    assert (H11 : t11 = typ_bot).
    { apply open_bot_eq with (x:=x0).
      exact (tyq_bot_r (H x0) eq_refl). }
    assert (H12 : t12 = typ_bot).
    { apply open_bot_eq with (x:=x0).
      exact (tyq_bot_r (H1 x0) eq_refl). }
    subst t11 t12. reflexivity.
  - discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
  - discriminate Hb.
Qed.

(* Last-rule analysis of [T <: typ_mut_marker typ_bot]: bottom, the marker
   itself, a transitivity step, a disjunction/intersection, a refcap record or
   a selector. *)
Lemma subtyp_mutbot_cases : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                   (x0:var) (T:typ),
  @subtyp typing_mode G objctx_empty e T (typ_mut_marker typ_bot) ->
  T = typ_mut_marker typ_bot \/
  T = typ_bot \/
  (exists X, @subtyp typing_mode G objctx_empty e T X /\
             @subtyp typing_mode G objctx_empty e X (typ_mut_marker typ_bot)) \/
  (exists S U, T = typ_or S U) \/
  (exists S U, T = typ_and S U) \/
  (exists (A:typ_label) S T', T = typ_rcd (dec_typ A S T')) \/
  (exists x (A:typ_label) y, T = typ_sel (avar_f x) A (avar_f y)).
Proof.
  intros typing_mode G e x0 T H.
  inversion H; subst; try discriminate;
    try (left; reflexivity);
    try (right; left; reflexivity);
    try (right; right; left; eexists; split; eassumption);
    try (right; right; right; left; eexists; eexists; reflexivity);
    try (right; right; right; right; left; eexists; eexists; reflexivity);
    try (right; right; right; right; right; left; eexists; eexists; eexists; reflexivity);
    try (right; right; right; right; right; right; eexists; eexists; eexists; reflexivity).
  - left. eapply (@tyq_mutmarker_r_gen x0 e T (typ_mut_marker typ_bot)).
    + eassumption.
    + reflexivity.
Qed.

(* The [tyq] case at the write capability: the only type equivalent to
   [typ_mut_marker typ_bot] is that marker itself. *)
Lemma tyq_mutmarker_gen : forall (x0:var) (e:renv) (a b:typ),
  tyq_typ e a b -> a = typ_mut_marker typ_bot ->
  b = typ_mut_marker typ_bot.
Proof.
  intros x0 e a b H. induction H; intros Ha.
  - exact Ha.
  - destruct H; discriminate Ha.
  - discriminate Ha.
  - discriminate Ha.
  - injection Ha as HB Ht11 Ht12. subst B t11 t12.
    assert (H21 : t21 = typ_bot).
    { apply open_bot_eq with (x:=x0).
      exact (tyq_nulary_gen (H x0) typ_nulary_bot). }
    assert (H22 : t22 = typ_bot).
    { apply open_bot_eq with (x:=x0).
      exact (tyq_nulary_gen (H1 x0) typ_nulary_bot). }
    subst t21 t22. reflexivity.
  - discriminate Ha.
  - discriminate Ha.
  - discriminate Ha.
  - discriminate Ha.
Qed.

(* Root analysis of the write-capability subtype: a derivation of
   [typ_nocap <: typ_mut_marker typ_bot] can only be a transitivity step
   through an intermediate type, or an equivalence step (impossible). *)
Lemma subtyp_nocap_mutbot_trans : forall (typing_mode:Mode) (G:ctx) (e:renv),
  @subtyp typing_mode G objctx_empty e typ_nocap (typ_mut_marker typ_bot) ->
  exists X,
    @subtyp typing_mode G objctx_empty e typ_nocap X /\
    @subtyp typing_mode G objctx_empty e X (typ_mut_marker typ_bot).
Proof.
  intros typing_mode G e H.
  inversion H; subst; try discriminate.
  - (* trans *) eexists _. split; eassumption.
  - (* tyq *) exfalso.
    pose proof (@tyq_nocap e (typ_mut_marker typ_bot) H0) as E.
    discriminate E.
Qed.

(* Important correction: the subtype [typ_nocap <: typ_mut_marker typ_bot] is
   *not* refutable without assumptions on the context.  A context binding a
   variable [x] to the conjunction of two same-label type members (one with
   lower bound [typ_nocap], one with upper bound [typ_bot]) lets [x] be viewed
   at both records; the selector rules then chain [typ_nocap <: sel x A y] and
   [sel x A y <: typ_bot].  Such a context is not inert, so the target's
   [inert G] is essential: the capability argument must be context-relative
   and exploit inertness (record members of a [record_type] have equal bounds
   or lower bound [typ_bot]), never a context-free "safe type" predicate. *)
Lemma subtyp_nocap_mutbot_ctx : forall (typing_mode:Mode) (x y:var)
                                      (A:typ_label),
  @subtyp typing_mode
    (x / v_ref ~ typ_and (typ_rcd (dec_typ A typ_nocap typ_top))
                         (typ_rcd (dec_typ A typ_bot typ_bot)))
    objctx_empty renv_empty typ_nocap (typ_mut_marker typ_bot).
Proof.
  intros typing_mode x y A.
  set (r1 := typ_rcd (dec_typ A typ_nocap typ_top)).
  set (r2 := typ_rcd (dec_typ A typ_bot typ_bot)).
  set (G := x / v_ref ~ typ_and r1 r2).
  assert (HxT : @ty_var typing_mode G objctx_empty renv_empty x (typ_and r1 r2)).
  { apply (@ty_var_var typing_mode G renv_empty x (typ_and r1 r2)).
    apply ctx_binds_e. }
  assert (Hx1 : @ty_var typing_mode G objctx_empty renv_empty x r1).
  { eapply ty_var_sub.
    - exact HxT.
    - apply subtyp_and11. }
  assert (Hx2 : @ty_var typing_mode G objctx_empty renv_empty x r2).
  { eapply ty_var_sub.
    - exact HxT.
    - apply subtyp_and12. }
  assert (Hsel2 : @subtyp typing_mode G objctx_empty renv_empty typ_nocap
                    (typ_sel (avar_f x) A (avar_f y))).
  { apply (@subtyp_sel2 typing_mode G renv_empty x A y typ_nocap typ_top).
    unfold r1. exact Hx1. }
  assert (Hsel1 : @subtyp typing_mode G objctx_empty renv_empty
                    (typ_sel (avar_f x) A (avar_f y)) typ_bot).
  { apply (@subtyp_sel1 typing_mode G renv_empty x A y typ_bot typ_bot).
    unfold r2. exact Hx2. }
  eapply subtyp_trans; [ exact Hsel2 | ].
  eapply subtyp_trans; [ exact Hsel1 | apply subtyp_bot ].
Qed.

(* Every declaration occurring in a record type has its label in the type's
   label set (the basic ingredient of record-label uniqueness). *)
Lemma record_has_label : forall (T:typ) (ls:fset label),
  record_typ T ls -> forall (dd:dec), record_has T dd -> label_of dd \in ls.
Proof.
  intros T ls Hrt. induction Hrt; intros dd Hhas.
  - inversion Hhas; subst. apply in_singleton_self.
  - inversion Hhas; subst.
    + rewrite in_union. left. apply IHHrt. assumption.
    + rewrite in_union. right.
      match goal with H5 : record_has (typ_rcd _) dd |- _ => inversion H5; subst end.
      subst. apply in_singleton_self.
Qed.

(* A record type has at most one declaration per label. *)
Lemma record_has_dec_unique : forall (T:typ) (ls:fset label),
  record_typ T ls -> forall D1 D2,
    record_has T D1 -> record_has T D2 ->
    label_of D1 = label_of D2 -> D1 = D2.
Proof.
  intros T ls Hrt.
  induction Hrt as [D l Hdec Hl | T0 ls0 D0 l Hrt0 IH Hdec0 Hl Hnotin];
    intros D1 D2 H1 H2 Hlab.
  - (* rt_one *) subst l. apply record_has_rcd in H1. apply record_has_rcd in H2.
    subst; reflexivity.
  - (* rt_cons *) subst l.
    apply record_has_and_inv in H1. apply record_has_and_inv in H2.
    destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
    + exact (IH D1 D2 H1 H2 Hlab).
    + rewrite <- (record_has_rcd H2) in Hlab.
      exfalso.
      pose proof (@record_has_label T0 ls0 Hrt0 D1 H1) as Hin.
      rewrite Hlab in Hin.
      apply Hnotin. exact Hin.
    + rewrite <- (record_has_rcd H1) in Hlab.
      exfalso.
      pose proof (@record_has_label T0 ls0 Hrt0 D2 H2) as Hin.
      rewrite <- Hlab in Hin.
      apply Hnotin. exact Hin.
    + rewrite <- (record_has_rcd H1). rewrite <- (record_has_rcd H2).
      reflexivity.
Qed.

(* A type member of a record type has equal bounds, or lower bound [typ_bot].
   This is the structural fact that makes inert contexts block the
   two-incompatible-views construction of [subtyp_nocap_mutbot_ctx]. *)
Lemma record_dec_typ_shape : forall (A:typ_label) (S T:typ),
  record_dec (dec_typ A S T) -> S = T \/ S = typ_bot.
Proof. intros A S T H. inversion H; subst; auto. Qed.

(* Type members of record types carry normal labels only, so a typed record
   can never contain a refcap-labelled type member.  This is what forces the
   refcap views of an inert-bound variable to come from its refcap component
   rather than from a record member. *)
Lemma record_dec_typ_normal : forall (A:typ_label) (S T:typ),
  record_dec (dec_typ A S T) -> exists A0, A = typ_label_normal A0.
Proof. intros A S T H. inversion H; subst; eexists; reflexivity. Qed.

Lemma record_dec_typ_refcap_false : forall (C:typ_refcap_label) (S T:typ),
  record_dec (dec_typ (typ_label_refcap C) S T) -> False.
Proof.
  intros C S T H. destruct (record_dec_typ_normal H) as [A0 HA].
  discriminate HA.
Qed.

Lemma record_has_dec : forall (T:typ) (ls:fset label),
  record_typ T ls -> forall D, record_has T D -> record_dec D.
Proof.
  intros T ls Hrt.
  induction Hrt as [D l Hdec Hl | T0 ls0 D l Hrt0 IH Hdec Hl Hnotin];
    intros D' Hhas.
  - apply record_has_rcd in Hhas. subst D'. exact Hdec.
  - apply record_has_and_inv in Hhas. destruct Hhas as [Hhas | Hhas].
    + apply IH; exact Hhas.
    + apply record_has_rcd in Hhas. subst D'. exact Hdec.
Qed.

Lemma record_typ_no_refcap : forall (T:typ) (ls:fset label)
                                    (C:typ_refcap_label) (S T':typ),
  record_typ T ls -> record_has T (dec_typ (typ_label_refcap C) S T') -> False.
Proof.
  intros T ls C S T' Hrt Hhas.
  pose proof (record_has_dec Hrt Hhas) as Hdec.
  exact (record_dec_typ_refcap_false Hdec).
Qed.

(* Record structure is stable under opening: labels, record declarations,
   record types and record membership all commute with [open_rec]. *)
Lemma label_of_open_dec : forall (n:nat) (x:var) (D:dec),
  label_of (open_rec_dec n x D) = label_of D.
Proof. intros. destruct D; reflexivity. Qed.

Lemma record_dec_open : forall (n:nat) (x:var) (D:dec),
  record_dec D -> record_dec (open_rec_dec n x D).
Proof.
  intros n x D H. destruct H.
  - cbn [open_rec_dec]. apply rd_typ.
  - cbn [open_rec_dec]. apply rd_typb.
  - cbn [open_rec_dec]. apply rd_fld.
  - cbn [open_rec_dec]. apply rd_met.
Qed.

Lemma record_typ_open : forall (T:typ) (ls:fset label),
  record_typ T ls -> forall (n:nat) (x:var), record_typ (open_rec n x T) ls.
Proof.
  intros T ls Hrt.
  induction Hrt as [D l Hdec Hl | T0 ls0 D l Hrt0 IH Hdec Hl Hnotin];
    intros n x.
  - change (record_typ (typ_rcd (open_rec_dec n x D)) (singleton l)).
    apply rt_one.
    + apply record_dec_open. exact Hdec.
    + rewrite (label_of_open_dec n x D). exact Hl.
  - change (record_typ
              (typ_and (open_rec n x T0) (typ_rcd (open_rec_dec n x D)))
              (union ls0 (singleton l))).
    apply rt_cons.
    + apply IH.
    + apply record_dec_open. exact Hdec.
    + rewrite (label_of_open_dec n x D). exact Hl.
    + exact Hnotin.
Qed.

Lemma record_type_open : forall (T:typ),
  record_type T -> forall (n:nat) (x:var), record_type (open_rec n x T).
Proof.
  intros T [ls H] n x. exists ls. apply record_typ_open. exact H.
Qed.

Lemma record_has_open : forall (T:typ) (D:dec) (n:nat) (x:var),
  record_has T D -> record_has (open_rec n x T) (open_rec_dec n x D).
Proof.
  intros T D n x H. induction H.
  - cbn [open_rec_typ]. apply rh_one.
  - cbn [open_rec_typ]. apply rh_andl. exact IHrecord_has.
  - cbn [open_rec_typ]. apply rh_andr. exact IHrecord_has.
Qed.

(* Membership in a record type yields subtyping to that record. *)
Lemma record_has_subtyp : forall (typing_mode:Mode) (G:ctx) (e:renv) (T:typ) (D:dec),
  record_has T D -> G ⁏ e ⊢ T <: typ_rcd D.
Proof.
  intros typing_mode G e T D H. induction H.
  - apply subtyp_refl.
  - eapply subtyp_trans; [apply subtyp_and11 | exact IHrecord_has].
  - eapply subtyp_trans; [apply subtyp_and12 | exact IHrecord_has].
Qed.

(* The definition found by [defs_has] is typed, and its declaration is a
   record component of the whole definition-list type. *)
Lemma ty_defs_has_met : forall (typing_mode:Mode) (G:ctx) (Go:objctx) (e:renv)
                               (ds:defs) (T:typ) (m:met_label) (t:trm),
  @ty_defs typing_mode G Go e ds T ->
  defs_has ds (def_met m t) ->
  exists D, @ty_def typing_mode G Go e (def_met m t) D /\ record_has T D.
Proof.
  intros typing_mode G Go e ds T m t Hds. induction Hds; intros Hhas.
  - unfold defs_has in Hhas. cbn in Hhas.
    destruct (classicT (label_of d = label_met m)) as [Heq | Hneq]; cbn in Hhas.
    + injection Hhas as Hd. subst d.
      exists D. split; [exact H | apply rh_one].
    + discriminate Hhas.
  - unfold defs_has in Hhas. cbn in Hhas.
    destruct (classicT (label_of d = label_met m)) as [Heq | Hneq]; cbn in Hhas.
    + injection Hhas as Hd. subst d.
      exists D. split; [exact H0 | apply rh_andr; apply rh_one].
    + destruct (IHHds Hhas) as (D' & Hdef' & Hrh).
      exists D'. split; [exact Hdef' | apply rh_andl; exact Hrh].
Qed.

(* The method found by [defs_has] in a kind-correct definition list has all
   its free (term/type) variables of reference kind. *)
Lemma defs_varkinds_has_met : forall (G:ctx) (ds:defs) (m:met_label) (t:trm),
  defs_varkinds G ds ->
  defs_has ds (def_met m t) ->
  all_tfree_k G t v_ref.
Proof.
  intros G ds m t Hvk. induction Hvk; intros Hhas.
  - unfold defs_has in Hhas. cbn in Hhas. discriminate Hhas.
  - unfold defs_has in Hhas. cbn in Hhas.
    destruct (classicT (label_of d = label_met m)) as [Heq | Hneq]; cbn in Hhas.
    + injection Hhas as Hd. subst d.
      match goal with Hdv : def_varkinds G (def_met m t) |- _ =>
        inversion Hdv; subst; assumption end.
    + apply IHHvk. unfold defs_has. assumption.
Qed.

(* The field found by [defs_has] in a kind-correct definition list stores a
   location variable.  This is the dynamic-provenance counterpart of
   [defs_varkinds_has_met]: a heap field never stores a reference variable, so
   reading it can only produce a location, which is not a key of the
   environment and hence can never be the target of a write step. *)
Lemma defs_varkinds_has_fld : forall (G:ctx) (ds:defs) (a:fld_label) (v:var),
  defs_varkinds G ds ->
  defs_has ds (def_fld a (avar_f v)) ->
  ctx_k G v v_loc.
Proof.
  intros G ds a v Hvk. induction Hvk; intros Hhas.
  - unfold defs_has in Hhas. cbn in Hhas. discriminate Hhas.
  - unfold defs_has in Hhas. cbn in Hhas.
    destruct (classicT (label_of d = label_fld a)) as [Heq | Hneq]; cbn in Hhas.
    + injection Hhas as Hd. subst d.
      match goal with Hdv : def_varkinds G (def_fld a (avar_f v)) |- _ =>
        inversion Hdv; subst; assumption end.
    + apply IHHvk. unfold defs_has. assumption.
Qed.

(* Any definition found in a well-typed definition list is itself typed. *)
Lemma ty_defs_has_def : forall (typing_mode:Mode) (G:ctx) (Go:objctx) (e:renv)
                               (ds:defs) (T:typ),
  @ty_defs typing_mode G Go e ds T ->
  forall (dd:def), defs_has ds dd -> exists D, @ty_def typing_mode G Go e dd D.
Proof.
  intros typing_mode G Go e ds T Hds. induction Hds; intros dd Hhas.
  - unfold defs_has in Hhas. cbn in Hhas.
    destruct (classicT (label_of d = label_of dd)) as [Heq | Hneq]; cbn in Hhas.
    + injection Hhas as Hdd. subst dd. exists D. assumption.
    + discriminate Hhas.
  - unfold defs_has in Hhas. cbn in Hhas.
    destruct (classicT (label_of d = label_of dd)) as [Heq | Hneq]; cbn in Hhas.
    + injection Hhas as Hdd. subst dd. exists D. assumption.
    + apply IHHds. unfold defs_has. assumption.
Qed.

(* Inversion of a method-definition typing: it exposes the capability,
   argument and result types, and the typing of the opened body in the
   method context. *)
Lemma ty_def_met_inv : forall (typing_mode:Mode) (G:ctx) (Go:objctx) (e:renv)
                              (m:met_label) (t:trm) (D:dec),
  @ty_def typing_mode G Go e (def_met m t) D ->
  exists L TC TZ TR,
    D = dec_met m TC TZ TR /\
    (forall xz, xz \notin L -> forall xc, xc <> xz -> xc \notin L ->
       ctx_obj_met typing_mode G Go xz TZ xc TC ⁏ e ⊢ open_met xz xc t ∶ open_met xz xc TR).
Proof.
  intros typing_mode G Go e m t D H.
  inversion H; subst.
  eexists _, _, _, _. split; [reflexivity | eassumption].
Qed.

(* Inversion of the typing of an object heap item: the stored definitions are
   typed against the record part [U] of the location's context type. *)
Lemma ty_item_s_obj : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap)
                             (x:var) (ds:defs),
  @ty_item_s typing_mode G e s x ->
  binds x (item_obj ds) s ->
  exists U S,
    ctx_binds x (typ_objref U S) G /\
    (G §§ (objctx_heap x U) ⁏ e ⊢ ds ∶ open x U) /\
    defs_varkinds G ds.
Proof.
  intros typing_mode G e s x ds Hi Hb.
  inversion Hi; subst.
  - exfalso.
    match goal with
    | Hf : binds x (item_fun ?t) s |- _ =>
        pose proof (binds_get Hf) as E1;
        pose proof (binds_get Hb) as E2;
        rewrite E2 in E1; discriminate E1
    end.
  - match goal with
    | Hb0 : binds x (item_obj ?ds0) s,
      Hctx : ctx_binds x (typ_objref ?U ?S) G,
      Hds : (_ §§ objctx_heap x ?U ⁏ _ ⊢ ?ds0 ∶ _),
      Hvk : defs_varkinds G ?ds0 |- _ =>
        assert (Heqds : ds0 = ds) by
          (pose proof (binds_get Hb0) as E1;
           pose proof (binds_get Hb) as E2; congruence);
        subst ds0;
        exists U, S; repeat split; assumption
    end.
Qed.

(* Projections of the heap correspondence. *)
Lemma heap_correspond_ctx_ok : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap),
  @heap_correspond typing_mode G e s -> ctx_ok G.
Proof. intros. destruct H as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8). exact h1. Qed.

Lemma heap_correspond_ok_s : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap),
  @heap_correspond typing_mode G e s -> ok s.
Proof. intros. destruct H as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8). exact h3. Qed.

Lemma heap_correspond_ok_e : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap),
  @heap_correspond typing_mode G e s -> ok e.
Proof. intros. destruct H as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8). exact h4. Qed.

Lemma heap_correspond_kdom_loc : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap),
  @heap_correspond typing_mode G e s -> ctx_kdom v_loc G = dom s.
Proof. intros. destruct H as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8). exact h5. Qed.

Lemma heap_correspond_kdom_ref : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap),
  @heap_correspond typing_mode G e s -> ctx_kdom v_ref G = dom e.
Proof. intros. destruct H as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8). exact h6. Qed.

Lemma heap_correspond_renv : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap),
  @heap_correspond typing_mode G e s -> @renv_corr typing_mode G e.
Proof. intros. destruct H as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8). exact h7. Qed.

Lemma heap_correspond_item : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap),
  @heap_correspond typing_mode G e s ->
  forall x, x \in dom s -> @ty_item_s typing_mode G e s x.
Proof. intros. destruct H as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8). apply h8. assumption. Qed.

(* Consequently every field of a corresponding heap item stores a location. *)
Lemma heap_item_field_loc : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap)
                                  (y:var) (ds:defs) (a:fld_label) (v:var),
  @heap_correspond typing_mode G e s ->
  binds y (item_obj ds) s ->
  defs_has ds (def_fld a (avar_f v)) ->
  ctx_k G v v_loc.
Proof.
  intros typing_mode G e s y ds a v Hcorr Hb Hhas.
  pose proof (@heap_correspond_item typing_mode G e s Hcorr y
                (binds_in_dom Hb)) as Hi.
  destruct (@ty_item_s_obj typing_mode G e s y ds Hi Hb)
    as (U & S & Hcb & Hds & Hvk).
  eapply defs_varkinds_has_fld; eassumption.
Qed.

(* Environment keys are reference-kind context bindings, and heap locations
   are location-kind context bindings.  These are the two directions of the
   [ctx_kdom] characterisation used to identify variables at run time. *)
Lemma heap_correspond_binds_ref : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                         (s:heap) (w:var) (y:var),
  @heap_correspond typing_mode G e s ->
  binds w y e ->
  ctx_k G w v_ref.
Proof.
  intros typing_mode G e s w y Hcorr Hb.
  destruct Hcorr as (Hok & Hwk & _ & _ & _ & Hkref & _ & _).
  apply (proj1 (@in_ctx_kdom_iff G w v_ref Hwk Hok)).
  rewrite Hkref. exact (@get_some_inv var w y e Hb).
Qed.

Lemma heap_correspond_binds_loc : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                         (s:heap) (y:var) (itm:item),
  @heap_correspond typing_mode G e s ->
  binds y itm s ->
  ctx_k G y v_loc.
Proof.
  intros typing_mode G e s y itm Hcorr Hb.
  destruct Hcorr as (Hok & Hwk & _ & _ & Hkloc & _ & _ & _).
  apply (proj1 (@in_ctx_kdom_iff G y v_loc Hwk Hok)).
  rewrite Hkloc. exact (@get_some_inv item y itm s Hb).
Qed.

(* Every environment binding of a corresponding environment is represented in
   the context by a reference-kind binding for the variable and a
   location-kind binding for its target, with corresponding record parts (the
   [typ_corr] relation).  This is the static view of a run-time reference. *)
Lemma renv_corr_binds_k : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                 (w:var) (y:var),
  @renv_corr typing_mode G e ->
  binds w y e ->
  exists G2 G3 Tw Ty,
    ctx_binds_k_after w v_ref Tw G G2 /\
    ctx_binds_k_after y v_loc Ty G2 G3 /\
    @typ_corr typing_mode Tw Ty.
Proof.
  intros typing_mode G e w y H.
  induction H as [G1
                | G1 G2 G3 e0 w0 y0 Tw Ty Href Hloc Hcorr Hrenv IH];
    intro Hb.
  - (* empty *) unfold binds in Hb. rewrite get_empty in Hb. discriminate Hb.
  - (* ref *) destruct (classicT (w = w0)) as [Heq | Hneq].
    + subst w.
      assert (Hy : y = y0).
      { pose proof (binds_get Hb) as E. rewrite get_push in E.
        destruct (classicT (w0 = w0)) as [H2 | H2].
        - injection E as Hy0. symmetry. exact Hy0.
        - exfalso. apply H2. reflexivity. }
      subst y.
      exists G2, G3, Tw, Ty. repeat split; assumption.
    + assert (Hb0 : binds w y e0).
      { pose proof (binds_get Hb) as E. rewrite get_push in E.
        destruct (classicT (w = w0)) as [H2 | H2].
        - exfalso. apply Hneq. exact H2.
        - unfold binds. exact E. }
      destruct (IH Hb0) as (G2' & G3' & Tw' & Ty' & Hr & Hl & Hc).
      exists G2', G3', Tw', Ty'. repeat split; assumption.
Qed.

Lemma heap_correspond_binds_corr : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                         (s:heap) (w:var) (y:var),
  @heap_correspond typing_mode G e s ->
  binds w y e ->
  exists G2 G3 Tw Ty,
    ctx_binds_k_after w v_ref Tw G G2 /\
    ctx_binds_k_after y v_loc Ty G2 G3 /\
    @typ_corr typing_mode Tw Ty.
Proof.
  intros typing_mode G e s w y Hcorr Hb.
  eapply renv_corr_binds_k.
  - eapply heap_correspond_renv. eassumption.
  - exact Hb.
Qed.

(* In the target's modes (with an inert context) no heap location can hold a
   function item: the fun-item typing would require a function-typed context
   binding, impossible for an inert context. *)
Lemma no_item_fun : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap)
                           (x:var) (t:trm),
  mode_has_sef typing_mode -> mode_has_mutability typing_mode ->
  inert G -> @heap_correspond typing_mode G e s ->
  binds x (item_fun t) s -> False.
Proof.
  intros typing_mode G e s x t Hs Hm Hi Hcorr Hb.
  destruct Hcorr as (Hok & Hweak & Hoks & Hoke & Hkd1 & Hkd2 & Hrenv & Hitem).
  pose proof (Hitem x (binds_in_dom Hb)) as Hiitem.
  inversion Hiitem; subst.
  - match goal with
    | Hcb : ctx_binds x (typ_fun ?S ?T) G |- _ =>
        destruct (@inert_binds_obj_shape typing_mode G x (typ_fun S T) Hs Hm Hi Hcb)
          as (U & S' & vk & Heq & _)
    end.
    discriminate Heq.
  - match goal with
    | Hb2 : binds x (item_obj ?ds) s |- _ =>
        pose proof (binds_get Hb) as E1;
        pose proof (binds_get Hb2) as E2;
        rewrite E2 in E1; discriminate E1
    end.
Qed.

(* End-to-end extraction of a heap method body: from the heap correspondence,
   the receiver's object binding and the method lookup, obtain the object's
   record part [U], the method declaration as a component of [open x U], the
   subtyping of [open x U] to that declaration, and the body typing. *)
Lemma heap_method_body : forall (typing_mode:Mode) (G:ctx) (e:renv) (s:heap)
                                (x:var) (ds:defs) (m:met_label) (t:trm),
  @heap_correspond typing_mode G e s ->
  binds x (item_obj ds) s ->
  defs_has ds (def_met m t) ->
  exists U S L TC TZ TR,
    ctx_binds x (typ_objref U S) G /\
    record_has (open x U) (dec_met m TC TZ TR) /\
    (@subtyp typing_mode G objctx_empty e (open x U) (typ_rcd (dec_met m TC TZ TR))) /\
    (forall xz, xz \notin L -> forall xc, xc <> xz -> xc \notin L ->
       ctx_obj_met typing_mode G (objctx_heap x U) xz TZ xc TC ⁏ e
         ⊢ open_met xz xc t ∶ open_met xz xc TR).
Proof.
  intros typing_mode G e s x ds m t Hcorr Hb Hhas.
  destruct Hcorr as (Hok & Hweak & Hoks & Hoke & Hkd1 & Hkd2 & Hrenv & Hitem).
  pose proof (Hitem x (binds_in_dom Hb)) as Hi.
  destruct (@ty_item_s_obj typing_mode G e s x ds Hi Hb)
    as (U & S & Hcb & Hds & Hvk).
  destruct (@ty_defs_has_met typing_mode G (objctx_heap x U) e ds (open x U) m t Hds Hhas)
    as (D & Hdef & Hrh).
  pose proof (@record_has_subtyp typing_mode G e (open x U) D Hrh) as Hsub.
  destruct (@ty_def_met_inv typing_mode G (objctx_heap x U) e m t D Hdef)
    as (L & TC & TZ & TR & HD & Hbody).
  subst D.
  exists U, S, L, TC, TZ, TR. repeat split; try eassumption.
Qed.

(* Projections of a configuration typing, used to extract the static data
   of the initial configuration in the target. *)
Lemma ty_config_inert : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  ty_config G c T -> inert G.
Proof. intros. inversion H. assumption. Qed.

Lemma ty_config_heap_correspond : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  ty_config G c T -> heap_correspond G (config_env c) (config_heap c).
Proof. intros. inversion H. simpl. assumption. Qed.

Lemma ty_config_term : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  ty_config G c T ->
  exists T0, G ⁏ (config_env c) ⊢ config_trm c ∶ T0.
Proof. intros. inversion H. eexists. simpl. eassumption. Qed.

Lemma ty_config_stack : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  ty_config G c T ->
  exists T0 U0, ty_stack G (config_env c) T0 (config_stack c) U0.
Proof. intros. inversion H. eexists. eexists. simpl. eassumption. Qed.

Lemma ty_config_closed_config : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  ty_config G c T -> config_closed c.
Proof. intros. inversion H. assumption. Qed.

Lemma ty_config_closed_trm : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  @ty_config typing_mode G c T -> closed (config_trm c).
Proof.
  intros typing_mode G c T H. destruct c as [t s Sigma e Lv].
  pose proof (ty_config_closed_config H) as Hc. simpl in Hc.
  inversion Hc; subst. simpl. assumption.
Qed.

Lemma ty_config_closed_stack : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  @ty_config typing_mode G c T -> closed (config_stack c).
Proof.
  intros typing_mode G c T H. destruct c as [t s Sigma e Lv].
  pose proof (ty_config_closed_config H) as Hc. simpl in Hc.
  inversion Hc; subst. simpl. assumption.
Qed.

Lemma ty_config_heap_closed : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  @ty_config typing_mode G c T -> heap_closed (config_heap c).
Proof.
  intros typing_mode G c T H. destruct c as [t s Sigma e Lv].
  pose proof (ty_config_closed_config H) as Hc. simpl in Hc.
  inversion Hc; subst. simpl. assumption.
Qed.

Lemma ty_config_sealed_G : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  ty_config G c T -> sealed G.
Proof. intros. inversion H. assumption. Qed.

Lemma ty_config_has_null : forall (typing_mode:Mode) (G:ctx) (c:config) (T:typ),
  ty_config G c T -> has_null (config_fv c).
Proof. intros. inversion H. simpl. assumption. Qed.

(* The "nothing fresh in the configuration" hypothesis, projected: the
   context domain, the context's free type variables, and the type of the
   stack are all among the configuration's free variables. *)
Lemma ty_config_ctx_dom_sub : forall (typing_mode:Mode) (G:ctx) (c:config)
                                     (T:typ),
  @ty_config typing_mode G c T -> ctx_dom G \c fv_config c.
Proof.
  intros typing_mode G c T H. inversion H; subst.
  match goal with Hnf : (subset (ctx_dom G) ?X /\ _) /\ _ |- _ =>
    destruct Hnf as [[Hdom HfvG] HfvU] end.
  exact Hdom.
Qed.

Lemma ty_config_ctx_fv_sub : forall (typing_mode:Mode) (G:ctx) (c:config)
                                    (T:typ),
  @ty_config typing_mode G c T -> fv G \c fv_config c.
Proof.
  intros typing_mode G c T H. inversion H; subst.
  match goal with Hnf : (subset (ctx_dom G) ?X /\ _) /\ _ |- _ =>
    destruct Hnf as [[Hdom HfvG] HfvU] end.
  exact HfvG.
Qed.

Lemma ty_config_U_fv_sub : forall (typing_mode:Mode) (G:ctx) (c:config)
                                  (T:typ),
  @ty_config typing_mode G c T -> fv T \c fv_config c.
Proof.
  intros typing_mode G c T H. inversion H; subst.
  match goal with Hnf : (subset (ctx_dom G) ?X /\ _) /\ _ |- _ =>
    destruct Hnf as [[Hdom HfvG] HfvU] end.
  exact HfvU.
Qed.

(* Inversions of stack typings used at the let-reduction steps. *)
Lemma ty_stack_nil_inv : forall (typing_mode:Mode) (G:ctx) (e:renv) (T U:typ),
  @ty_stack typing_mode G e T stack_nil U ->
  G ⁏ e ⊢ T <: U.
Proof. intros. inversion H. assumption. Qed.

Lemma ty_stack_let_inv : forall (typing_mode:Mode) (G:ctx) (e:renv)
                                (S:typ) (t:trm) (s:stack) (U:typ),
  @ty_stack typing_mode G e S (stack_cons (frame_let t) s) U ->
  exists T L,
    @ty_stack typing_mode G e T s U /\
    (forall x, x \notin L ->
      @ty_trm typing_mode (G § x / v_let ~ S) objctx_empty e (open x t) T).
Proof.
  intros typing_mode G e S t s U H.
  inversion H; subst.
  eexists _, _. split; eassumption.
Qed.

(* The target-shaped statement for the one-step case, proved from the call
   step analysis: a single call step preserves the heap. *)
Lemma SefG_I_k1 :
  forall (typing_mode : Mode) (w1 : var) (m : met_label) (w2 : var)
         (TZv : typ) (c1 : config) (G : ctx) (c4 : config),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  config_trm c1 = trm_call (avar_f w1) m (avar_f w2) ->
  (G ⁏ (config_env c1) ⊢ w1 ∶ typ_rcd (dec_met m typ_nocap TZv typ_top) /\
   G ⁏ (config_env c1) ⊢ w2 ∶ TZv /\
   G ⁏ (config_env c1) ⊢ typ_nocap <: TZv) ->
  (exists T1, ty_config G c1 T1) ->
  c1 ⊣1↦* c4 ->
  (exists j c3, frame_end_in c1 j c3 /\ j < 1) \/
  subheap_unchanged (config_heap c1) (config_heap c4).
Proof.
  intros typing_mode w1 m w2 TZv c1 G c4 Hs Hm Htrm H4 H5 Hcl.
  destruct (red_closure_inv Hcl) as [[Hk _] | (n & c2 & Hk & Hcl2 & Hred)].
  - discriminate Hk.
  - injection Hk as Hn. subst n.
    inversion Hcl2; subst.
    right.
    destruct (red_step_call_same Hred Htrm) as (Hh & _ & _).
    rewrite Hh. apply subheap_unchanged_refl.
Qed.

(* The target-shaped statement for two steps when the second step is not a
   write: the call step preserves the heap, and the non-write step preserves
   all pre-existing bindings. *)
Lemma SefG_I_k2_nonwrite :
  forall (typing_mode : Mode) (w1 : var) (m : met_label) (w2 : var)
         (TZv : typ) (c1 : config) (G : ctx) (c2 c4 : config),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  config_trm c1 = trm_call (avar_f w1) m (avar_f w2) ->
  (G ⁏ (config_env c1) ⊢ w1 ∶ typ_rcd (dec_met m typ_nocap TZv typ_top) /\
   G ⁏ (config_env c1) ⊢ w2 ∶ TZv /\
   G ⁏ (config_env c1) ⊢ typ_nocap <: TZv) ->
  (exists T1, ty_config G c1 T1) ->
  c1 ⊣1↦* c2 ->
  c2 ↦ c4 ->
  (forall (wx:var) (a:fld_label) (wy:var),
     config_trm c2 <> trm_write (avar_f wx) a (avar_f wy)) ->
  (exists j c3, frame_end_in c1 j c3 /\ j < 2) \/
  subheap_unchanged (config_heap c1) (config_heap c4).
Proof.
  intros typing_mode w1 m w2 TZv c1 G c2 c4 Hs Hm Htrm H4 H5 Hcl1 Hstep Hnw.
  destruct (red_closure_inv Hcl1) as [[Hk _] | (n & c2' & Hk & Hcl2 & Hred)].
  - discriminate Hk.
  - injection Hk as Hn. subst n.
    inversion Hcl2; subst.
    right.
    destruct (red_step_call_same Hred Htrm) as (Hh & _ & _).
    pose proof (red_nonwrite_step_subheap Hstep Hnw) as Hsub.
    rewrite Hh in Hsub.
    exact Hsub.
Qed.

(* ------------------------------------------------------------------ *)
(* Target                                                              *)
(*                                                                     *)
(* The target is reduced by [SefG_I_reduce] to [SefStep c1], and by     *)
(* [SefStep_of_write] to [SefWrite c1]: every write reachable before    *)
(* the call frame ends must target a location outside                *)
(* [dom (config_heap c1)].                                             *)
(*                                                                     *)
(* Verified static ingredients:                                          *)
(*  * [ty_trm_call_inv]/[ty_trm_write_inv]/[ty_trm_read_inv]/            *)
(*    [ty_trm_let_inv]/[ty_trm_lit_inv]/[ty_trm_var_inv]: complete        *)
(*    constructor inversions; [no_ty_trm_apply_sef],                     *)
(*    [no_ty_trm_lit_fun_sef]: no functions in the target's modes.       *)
(*  * [red_step_call_inv], [red_step_call_same]: the call step exposes    *)
(*    the receiver location, object definitions and body, and changes    *)
(*    neither heap, environment nor stack.                               *)
(*  * [ty_config_*]: the static data of the initial configuration.       *)
(*  * [heap_method_body]: a heap method body and the subtyping            *)
(*    [open x U <: typ_rcd (dec_met m TC TZ TR)] of its declaration.      *)
(*  * [inert_binds_obj_shape], [refcap_inert_type_mut_shape],             *)
(*    [typ_corr_objref_inv]: canonical shapes of inert bindings and of    *)
(*    reference/location correspondences (shared record part [U]).        *)
(*  * [MutReach] with [MutReach_sub_iff]: exactness of write-capability   *)
(*    reachability, plus [incap_strip_super], [viewpoint_adapt_mut_inv],  *)
(*    [subtyp_and_elim], [subtyp_or_elim], [MutReach_or].                 *)
(*  * [mode_*_cases]: mode-group splits for the mode-specific rules.      *)
(*                                                                     *)
(* Remaining obligations, both stripped from the supplied files:         *)
(*  (1) capability side: a context-relative model showing that under the *)
(*      inert ambient context [typ_nocap] does not reach                     *)
(*      [typ_mut_marker typ_bot], and that typing/viewpoint adaptation   *)
(*      preserves this for variables that point at pre-existing          *)
(*      locations.  The selector rules make this context-dependent; a    *)
(*      context-free colouring is impossible (a variable may be typed    *)
(*      with either a [nocap] bound or a [mut] upper view);             *)
(*  (2) runtime side: renaming/substitution and weakening for [ty_var],  *)
(*      [ty_trm], [subtyp], [ty_incap], [ty_capbnd] (the syntax-class   *)
(*      instances were stripped), configuration subject reduction for    *)
(*      [red], and heap-item typing preservation under [heap_update].    *)
(*                                                                     *)
(* Correction (verified formal fact): a context-free "no write capability"  *)
(* predicate cannot be used.  [subtyp_nocap_mutbot_ctx] proves that in a   *)
(* context binding one variable to the conjunction of two same-label type  *)
(* members (lower bound [typ_nocap] in one, upper bound [typ_bot] in the   *)
(* other) the subtype [typ_nocap <: typ_mut_marker typ_bot] IS derivable,  *)
(* through the two selector rules.  So the capability analysis must be     *)
(* *context-relative*, and the target's [inert G] is what rules this out:  *)
(* in an inert context every binding is [typ_objref U S] with [U] a        *)
(* [record_type] whose type members have equal bounds or lower bound       *)
(* [typ_bot] (rd_typ/rd_typb), so no single variable can be viewed at two  *)
(* incompatible same-label type-member records unless a strictly smaller   *)
(* instance of the same subtype obligation is already available.  The      *)
(* expected proof is therefore a mutual induction over the goal types      *)
(* [typ_bot] / [typ_mut_marker typ_bot] (with [typ_top] for the [top <:    *)
(* typ_bot] branch), using inertness at the selector steps and the         *)
(* [record_type] bound structure; it is not a model of arbitrary contexts. *)
(*                                                                     *)
(* Sharper analysis of the capability side (why a naive argument fails  *)
(* and what the model must establish).  Two "universal coercion" routes  *)
(* would trivialise a writable view if they were available:              *)
(*   * [subtyp_nocap_bnd] followed by [ty_rec_elim] turns any variable  *)
(*     typed [typ_nocap] into a value of any closed type [T] (with      *)
(*     [typ_indep_b 0 T]);                                              *)
(*   * [subtyp_bot] followed by [ty_var_sub] does the same for a        *)
(*     variable typed [typ_bot] (or, in the complement modes, typed     *)
(*     [typ_and typ_nocap (typ_mut_marker typ_bot)], see                 *)
(*     [subtyp_nocap_mut_bot]).                                         *)
(* Consequently a receiver at capability [typ_nocap] could write to its  *)
(* own (pre-existing) location.  The hypotheses of the target rule this  *)
(* out only indirectly: from [ty_config] the initial call is typed with  *)
(* a capability type [TC]; the call premise [w1 ∶ open w2 TC] together  *)
(* with [heap_correspond] forces [TC] to be derivable from the inert     *)
(* binding of [w1], while the subtyping in H4 forces                     *)
(* [typ_nocap <: open x TC].  The derivability requirement excludes      *)
(* [TC = typ_nocap] (a context/all-tfree/inertness induction: no type   *)
(* assignment from an inert binding can be [typ_nocap]), and the         *)
(* [ty_rec_intro] side condition ([T ∶icp T], see [ty_incap], where     *)
(* refcap records such as [typ_mut_marker _] only satisfy [∶icp typ_top]) *)
(* excludes every self-incapacitated wrapper whose elimination would     *)
(* expose [typ_mut_marker typ_bot].  The same argument applies to the    *)
(* argument type and, recursively, to the parameter/receiver types of    *)
(* every callee body in the heap.                                       *)
(*                                                                     *)
(* What is missing is therefore not this case analysis but its           *)
(* mechanisation together with the freshness bookkeeping: a static type  *)
(* alone does not distinguish a writable capability on a *fresh* object  *)
(* ([typ_objlit] contains [typ_mut_marker typ_bot]) from one on a        *)
(* pre-existing location, so the runtime invariant must pair heap        *)
(* provenance with the typing derivation, and that invariant has to be   *)
(* preserved by every reduction step (the item-(2) metatheory).          *)
(*                                                                     *)
(* Two operational facts refine that bookkeeping.  First, [red_read]     *)
(* does *not* preserve location provenance: it binds the fresh reference *)
(* name [wVal] to the stored variable [yVal], which may be a location of *)
(* the initial heap.  So a freshly named variable can denote an old       *)
(* location; freshness of the variable is therefore useless as a guard,  *)
(* and the adapted type returned by the read is the only protection.     *)
(* Second, in a configuration satisfying [heap_correspond], a stored     *)
(* field value is a *location* variable, not a reference                *)
(* ([defs_varkinds_has_fld]/[heap_item_field_loc]), so such a value is  *)
(* not a key of the environment and can never itself be the target of a  *)
(* [red_write] step; the danger is exactly the fresh reference name      *)
(* introduced by [red_read].                                            *)
(*                                                                     *)
(* Formal obstruction recorded for the continuation: the remaining      *)
(* inert-context capability fact is an infinite-descent statement.  At   *)
(* each root/selector step a derivation of [nocap <: bot] (or            *)
(* [nocap <: typ_mut_marker typ_bot]) reduces to a *strictly smaller*    *)
(* derivation of the same statement, because the two incompatible        *)
(* same-label views of one inert-bound variable must come from the same  *)
(* [record_dec], whose bounds are equal or have lower bound [typ_bot]    *)
(* ([record_has_dec_unique], [record_dec_typ_shape]).  Mechanising the   *)
(* descent is blocked by two Coq-level facts: [subtyp]/[ty_var] live in  *)
(* [Prop] and cannot be eliminated into [nat] (no derivation-size        *)
(* function), and an accessibility predicate does not suffice because    *)
(* the transitivity rotation [trans (trans d1 d2a) d2b] preserves the    *)
(* total derivation size, so no auxiliary pair measure decreases.  A     *)
(* stratified syntactic model of the mutual [ty_var]/[subtyp]/           *)
(* [ty_incap] system (the original development's machinery) is the       *)
(* viable route.                                                        *)
(*                                                                     *)
(* The sources contain only declarations (no typing instances or lemmas) *)
(* and the compiled objects match those stripped sources, so the         *)
(* remaining declarations cannot be derived from what is supplied       *)
(* without the metatheory above; proof escapes remain disallowed.        *)
(* ------------------------------------------------------------------ *)

Theorem SefG_I :
  forall (typing_mode : Mode) (w1 : var) (m : met_label) (w2 : var)
         (TZv : typ) (c1 : config) (G : ctx) (c4 : config) (k : nat),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  config_trm c1 = trm_call (avar_f w1) m (avar_f w2) ->
  (G ⁏ (config_env c1) ⊢ w1 ∶ typ_rcd (dec_met m typ_nocap TZv typ_top) /\
   G ⁏ (config_env c1) ⊢ w2 ∶ TZv /\
   G ⁏ (config_env c1) ⊢ typ_nocap <: TZv) ->
  (exists T1, ty_config G c1 T1) ->
  c1 ⊣k↦* c4 ->
  (exists j c3, frame_end_in c1 j c3 /\ j < k) \/
  subheap_unchanged (config_heap c1) (config_heap c4).
