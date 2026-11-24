Require Import syntax_ott.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Relation_Operators.

Require Import Operators_Properties.

Local Lemma eqe2_weaken_assumptions : forall D H A B,
  eqe2 D H A B -> forall K, incl H K -> eqe2 D K A B.
Proof.
  intros D H A B Heq.
  induction Heq; intros K Hsub; eauto using eqe2.
  apply e2_arrfix; [apply IHHeq1 | apply IHHeq2];
    (intros p [Hp | Hp]; [now left | right; now apply Hsub]).
Qed.

Local Lemma TypCast_soundness_context : forall D E A B c,
  TypCast D E A B c -> eqe2 D (List.map snd E) A B.
Proof.
  intros D E A B c Hcast.
  induction Hcast; eauto using eqe2.
  - apply e2_arrfix; (eapply eqe2_weaken_assumptions;
      [eassumption | intros p Hp; now right]).
  - apply e2_assump; auto.
    change (In (snd (cx, (A, B))) (List.map snd E)).
    now apply in_map.
  - destruct (atom_fresh L) as [x Hx].
    apply e2_arrfix; [apply (H0 x Hx) | apply (H2 x Hx)].
Qed.

Theorem TypCast_soundness: forall D A B c,
  TypCast D nil A B c ->
  eqe2 D nil A B.
Proof.
  intros D A B c Hcast.
  exact (TypCast_soundness_context _ _ _ _ _ Hcast).
Qed.

(* Cast derivations with unnamed assumptions. *)
Inductive cast_derivable (D : tctx) : actx -> typ -> typ -> Prop :=
| cast_assumption : forall K A B,
    In (A, B) K -> WFT D A -> WFT D B -> cast_derivable D K A B
| cast_identity : forall K A,
    WFT D A -> cast_derivable D K A A
| cast_unfold : forall K A,
    WFT D (t_mu A) -> cast_derivable D K (t_mu A) (unfold_mu A)
| cast_fold : forall K A,
    WFT D (t_mu A) -> cast_derivable D K (unfold_mu A) (t_mu A)
| cast_sequence : forall K A B C,
    cast_derivable D K A B -> cast_derivable D K B C -> cast_derivable D K A C
| cast_fix : forall K A1 A2 B1 B2,
    cast_derivable D ((t_arrow A1 A2, t_arrow B1 B2) :: K) A1 B1 ->
    cast_derivable D ((t_arrow A1 A2, t_arrow B1 B2) :: K) A2 B2 ->
    cast_derivable D K (t_arrow A1 A2) (t_arrow B1 B2).

Local Lemma cast_derivable_weaken : forall D K A B,
  cast_derivable D K A B -> forall K', incl K K' -> cast_derivable D K' A B.
Proof.
  intros D K A B Hcast.
  induction Hcast; intros K' Hsub.
  - apply cast_assumption; auto.
  - now apply cast_identity.
  - now apply cast_unfold.
  - now apply cast_fold.
  - eapply cast_sequence; [apply IHHcast1 | apply IHHcast2]; exact Hsub.
  - apply cast_fix; [apply IHHcast1 | apply IHHcast2];
      (intros p [Hp | Hp]; [now left | right; now apply Hsub]).
Qed.

Local Lemma cast_derivable_subst : forall D K A B,
  cast_derivable D K A B -> forall K',
  (forall U V, In (U, V) K -> WFT D U -> WFT D V -> cast_derivable D K' U V) ->
  cast_derivable D K' A B.
Proof.
  intros D K A B Hcast.
  induction Hcast; intros K' Hsubst.
  - now apply Hsubst.
  - now apply cast_identity.
  - now apply cast_unfold.
  - now apply cast_fold.
  - eapply cast_sequence; [apply IHHcast1 | apply IHHcast2]; exact Hsubst.
  - apply cast_fix; [apply IHHcast1 | apply IHHcast2];
      (intros U V [Hhead | Htail] HU HV;
       [apply cast_assumption; [now left | exact HU | exact HV] |
        eapply cast_derivable_weaken; [now apply Hsubst | intros p Hp; now right]]).
Qed.

(* Bind the reverse pair inside the forward binder, then substitute that cast
   for the reverse assumption in the forward components. *)
Local Lemma cast_derivable_fix_direction : forall D K A1 A2 B1 B2,
  let P := (t_arrow A1 A2, t_arrow B1 B2) in
  let Q := (t_arrow B1 B2, t_arrow A1 A2) in
  cast_derivable D (P :: Q :: K) A1 B1 ->
  cast_derivable D (P :: Q :: K) A2 B2 ->
  cast_derivable D (P :: Q :: K) B1 A1 ->
  cast_derivable D (P :: Q :: K) B2 A2 ->
  cast_derivable D K (t_arrow A1 A2) (t_arrow B1 B2).
Proof.
  intros D K A1 A2 B1 B2 P Q Hdom Hcod Hdom_rev Hcod_rev.
  assert (Hreverse : cast_derivable D (P :: K) (t_arrow B1 B2) (t_arrow A1 A2)).
  { apply cast_fix;
      (eapply cast_derivable_weaken; [eassumption | intros p; simpl; tauto]). }
  apply cast_fix;
    (eapply cast_derivable_subst; [eassumption | intros U V Hp HU HV]);
    (change (In (U, V) (P :: Q :: K)) in Hp;
     destruct Hp as [Hp | [Hp | Hp]];
     [apply cast_assumption; [now left | exact HU | exact HV] |
      unfold Q in Hp; injection Hp as <- <-; exact Hreverse |
      apply cast_assumption; [now right | exact HU | exact HV]]).
Qed.

Local Lemma eqe2_cast_derivable : forall D H A B,
  eqe2 D H A B -> forall K,
  (forall U V, In (U, V) H -> In (U, V) K /\ In (V, U) K) ->
  cast_derivable D K A B /\ cast_derivable D K B A.
Proof.
  intros D H A B Heq.
  induction Heq; intros K Hsub.
  - destruct (Hsub A B H0); split; now apply cast_assumption.
  - split; now apply cast_identity.
  - destruct (IHHeq1 K Hsub) as [HAB HBA].
    destruct (IHHeq2 K Hsub) as [HBC HCB].
    split; eauto using cast_sequence.
  - destruct (IHHeq K Hsub); auto.
  - split; [now apply cast_unfold | now apply cast_fold].
  - set (P := (t_arrow A1 A2, t_arrow B1 B2)).
    set (Q := (t_arrow B1 B2, t_arrow A1 A2)).
    assert (Hsub' : forall U V, In (U, V) (P :: H) ->
        In (U, V) (P :: Q :: K) /\ In (V, U) (P :: Q :: K)).
    { intros U V [Hp | Hp].
      - unfold P in Hp; injection Hp as <- <-.
        split; [now left | right; now left].
      - destruct (Hsub U V Hp); split; right; now right. }
    destruct (IHHeq1 _ Hsub') as [Hdom Hdom_rev].
    destruct (IHHeq2 _ Hsub') as [Hcod Hcod_rev].
    split.
    + now apply cast_derivable_fix_direction.
    + apply cast_derivable_fix_direction;
        (eapply cast_derivable_weaken; [eassumption | intros p; simpl; tauto]).
Qed.

(* Interpret indices outside the local binders using the named context. *)
Local Fixpoint name_cast (E : cctx) (depth : nat) (c : castop) : castop :=
  match c with
  | c_var_b i =>
      if lt_dec i depth then c_var_b i else
      match nth_error E (i - depth) with
      | Some (x, _) => c_var_f x
      | None => c_id
      end
  | c_arrow c1 c2 => c_arrow (name_cast E depth c1) (name_cast E depth c2)
  | c_seq c1 c2 => c_seq (name_cast E depth c1) (name_cast E depth c2)
  | c_fixc c => c_fixc (name_cast E (S depth) c)
  | _ => c
  end.

Local Lemma name_cast_open : forall c E depth x p,
  open_castop_wrt_castop_rec depth (c_var_f x) (name_cast E (S depth) c) =
  name_cast ((x, p) :: E) depth c.
Proof.
  induction c; intros E depth x p; simpl; try reflexivity.
  - destruct (lt_dec n (S depth)), (lt_dec n depth); try lia.
    + simpl; destruct (lt_eq_lt_dec n depth) as [[Hlt | Heq] | Hgt];
        try lia; reflexivity.
    + replace n with depth in * by lia.
      rewrite Nat.sub_diag; simpl.
      destruct (lt_eq_lt_dec depth depth) as [[Hlt | Heq] | Hgt];
        try lia; reflexivity.
    + replace (n - depth) with (S (n - S depth)) by lia.
      cbn [nth_error].
      destruct (nth_error E (n - S depth)) as [[y q] |]; reflexivity.
  - now rewrite (IHc1 E depth x p), (IHc2 E depth x p).
  - now rewrite (IHc1 E depth x p), (IHc2 E depth x p).
  - now rewrite (IHc E (S depth) x p).
Qed.

(* A single index-based witness works for every assignment of fresh names. *)
Local Lemma cast_derivable_TypCast : forall D K A B,
  cast_derivable D K A B -> exists c, forall E,
  List.map snd E = K -> uniq E -> TypCast D E A B (name_cast E 0 c).
Proof.
  intros D K A B Hcast.
  induction Hcast.
  - destruct (In_nth_error _ _ H) as [i Hi].
    exists (c_var_b i); intros E HE Huniq.
    rewrite <- HE, nth_error_map in Hi.
    simpl; destruct (lt_dec i 0) as [Hlt | Hnlt]; [lia |].
    rewrite Nat.sub_0_r.
    destruct (nth_error E i) as [[x [U V]] |] eqn:Hentry; simpl in Hi;
      [injection Hi as <- <- | discriminate].
    apply TCast_var; eauto using nth_error_In.
  - exists c_id; intros; simpl; now apply TCast_id.
  - exists (c_unfold (t_mu A)); intros; simpl; now apply TCast_unfold.
  - exists (c_fold (t_mu A)); intros; simpl; now apply TCast_fold.
  - destruct IHHcast1 as [c1 Hc1], IHHcast2 as [c2 Hc2].
    exists (c_seq c1 c2); intros; simpl.
    eapply TCast_seq; [now apply Hc1 | now apply Hc2].
  - destruct IHHcast1 as [c1 Hc1], IHHcast2 as [c2 Hc2].
    exists (c_fixc (c_arrow c1 c2)); intros E HE Huniq; simpl.
    apply TCast_fix with (L := dom E); intros x Hx;
      unfold open_castop_wrt_castop;
      rewrite (name_cast_open _ E 0 x (t_arrow A1 A2, t_arrow B1 B2));
      [apply Hc1 | apply Hc2]; (now simpl; rewrite HE) || now constructor.
Qed.

Theorem TypCast_completeness: forall D A B,
  eqe2 D nil A B ->
  exists c, TypCast D nil A B c.
Proof.
  intros D A B Heq.
  assert (Hcast : cast_derivable D nil A B).
  { apply (eqe2_cast_derivable _ _ _ _ Heq nil).
    intros U V H; inversion H. }
  destruct (cast_derivable_TypCast _ _ _ _ Hcast) as [c Hc].
  exists (name_cast nil 0 c); apply Hc; [reflexivity | constructor].
Qed.
