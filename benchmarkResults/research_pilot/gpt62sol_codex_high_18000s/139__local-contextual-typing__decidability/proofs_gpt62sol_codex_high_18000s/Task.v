Require Import Syntax Algo.
From Stdlib Require Import List Bool Arith Lia.
Local Notation "'one' x" := (cons x nil) (at level 10, x at next level).

Fixpoint find_tm (G : Env) (x : nat) : option Typ :=
  match G with
  | TmCons E A => match x with 0 => Some A | S y => find_tm E y end
  | TyCons E | ExCons E | ExTyCons E _ =>
      option_map (fun A => ty_shift A 0) (find_tm E x)
  | _ => None
  end.

Fixpoint find_ty (G : Env) (x : nat) : bool :=
  match G with
  | TmCons E _ | SepCons E => find_ty E x
  | TyCons E => match x with 0 => true | S y => find_ty E y end
  | ExCons E | ExTyCons E _ =>
      match x with 0 => false | S y => find_ty E y end
  | EnvEmpty => false
  end.

Fixpoint find_ex (G : Env) (x : nat) : bool :=
  match G with
  | TmCons E _ | SepCons E => find_ex E x
  | ExCons E => match x with 0 => true | S y => find_ex E y end
  | TyCons E | ExTyCons E _ =>
      match x with 0 => false | S y => find_ex E y end
  | EnvEmpty => false
  end.

Fixpoint find_exty (G : Env) (x : nat) : option Typ :=
  match G with
  | TmCons E _ => find_exty E x
  | ExTyCons E A =>
      match x with
      | 0 => Some (ty_shift A 0)
      | S y => option_map (fun B => ty_shift B 0) (find_exty E y)
      end
  | TyCons E | ExCons E =>
      match x with
      | 0 => None
      | S y => option_map (fun B => ty_shift B 0) (find_exty E y)
      end
  | _ => None
  end.

Definition is_some {X} (a : option X) : bool :=
  match a with Some _ => true | None => false end.

Lemma option_map_some {X Y} (f : X -> Y) o y :
  option_map f o = Some y <-> exists x, o = Some x /\ f x = y.
Proof.
  destruct o; simpl; split; intros H; try discriminate.
  - injection H as H. eauto.
  - destruct H as (? & H & <-). now inversion H.
  - destruct H as (? & H & _). discriminate.
Qed.

Lemma is_some_spec {X} (o : option X) :
  is_some o = true <-> exists x, o = Some x.
Proof. destruct o; simpl; split; eauto; try discriminate. intros [? H]; discriminate. Qed.

Lemma find_tm_spec G x A : find_tm G x = Some A <-> lookupTm G x A.
Proof.
  revert x A. induction G; intros x B; destruct x; simpl;
    try rewrite option_map_some; try setoid_rewrite IHG;
    split; intros H; try discriminate; try solve [inversion H];
    try solve [inversion H; subst; eauto using lookupTm];
    try solve [destruct H as (? & ? & <-); eauto using lookupTm].
Qed.

Lemma find_ty_spec G x : find_ty G x = true <-> lookupTy G x.
Proof.
  revert x. induction G; intros []; simpl; try rewrite IHG;
    split; intros H; try discriminate; solve [eauto using lookupTy | inversion H; auto].
Qed.

Lemma find_ex_spec G x : find_ex G x = true <-> lookupEx G x.
Proof.
  revert x. induction G; intros []; simpl; try rewrite IHG;
    split; intros H; try discriminate; solve [eauto using lookupEx | inversion H; auto].
Qed.

Lemma find_exty_spec G x A : find_exty G x = Some A <-> lookupExTy G x A.
Proof.
  revert x A. induction G; intros x B; destruct x; simpl;
    try rewrite option_map_some; try setoid_rewrite IHG;
    split; intros H; try discriminate; try solve [inversion H];
    try solve [inversion H; subst; eauto using lookupExTy];
    try solve [destruct H as (? & ? & <-); eauto using lookupExTy].
Qed.

Lemma find_exty_present G x : is_some (find_exty G x) = true <-> lookupExTy' G x.
Proof.
  revert x. induction G; intros []; simpl;
    try match goal with
        | |- is_some (option_map _ ?o) = true <-> _ =>
            replace (is_some (option_map (fun B => ty_shift B 0) o))
              with (is_some o) by now destruct o
        end;
    try rewrite IHG; split; intros H; try discriminate;
    solve [eauto using lookupExTy' | inversion H; auto].
Qed.

Fixpoint regular_typ (G : Env) (A : Typ) : bool :=
  match A with
  | Int => true
  | TVar x => find_ty G x
  | Arr A B => regular_typ G A && regular_typ G B
  | All A => regular_typ (TyCons G) A
  end.

Fixpoint regular_tm_env (G : Env) : bool :=
  match G with
  | EnvEmpty => true
  | TyCons E | ExCons E => regular_tm_env E
  | TmCons E A | ExTyCons E A => regular_tm_env E && regular_typ E A
  | SepCons _ => false
  end.

Fixpoint regular_sub_env (G : Env) : bool :=
  match G with
  | SepCons E => regular_tm_env E
  | TyCons E | ExCons E => regular_sub_env E
  | ExTyCons E A => regular_sub_env E && regular_typ E A
  | _ => false
  end.

Fixpoint open_typ (G : Env) (A : Typ) : bool :=
  match A with
  | Int => false
  | TVar x => find_ex G x
  | Arr A B => open_typ G A || open_typ G B
  | All A => open_typ (TyCons G) A
  end.

Fixpoint closed_typ (G : Env) (A : Typ) : bool :=
  match A with
  | Int => true
  | TVar x => find_ty G x || is_some (find_exty G x)
  | Arr A B => closed_typ G A && closed_typ G B
  | All A => closed_typ (TyCons G) A
  end.

Lemma regular_typ_spec G A : regular_typ G A = true <-> RegularTyp G A.
Proof.
  revert G. induction A; intros G; simpl;
    rewrite ?andb_true_iff, ?find_ty_spec, ?IHA, ?IHA1, ?IHA2;
    split; intros H; try match type of H with _ /\ _ => destruct H as [H1 H2] end;
    solve [eauto using RegularTyp | inversion H; auto].
Qed.

Lemma regular_tm_env_spec G : regular_tm_env G = true <-> TRegular G.
Proof.
  induction G; simpl; rewrite ?andb_true_iff, ?regular_typ_spec, ?IHG;
    split; intros H; try discriminate; try match type of H with _ /\ _ => destruct H as [H1 H2] end;
    solve [eauto using TRegular | inversion H; auto].
Qed.

Lemma regular_sub_env_spec G : regular_sub_env G = true <-> SRegular G.
Proof.
  induction G; simpl; rewrite ?andb_true_iff, ?regular_typ_spec, ?regular_tm_env_spec, ?IHG;
    split; intros H; try discriminate; try match type of H with _ /\ _ => destruct H as [H1 H2] end;
    solve [eauto using SRegular | inversion H; auto].
Qed.

Lemma open_typ_spec G A : open_typ G A = true <-> open G A.
Proof.
  revert G. induction A; intros G; simpl;
    rewrite ?orb_true_iff, ?find_ex_spec, ?IHA, ?IHA1, ?IHA2;
    split; intros H; try discriminate; try match type of H with _ \/ _ => destruct H as [H|H] end;
    solve [eauto using open | inversion H; auto].
Qed.

Lemma closed_typ_spec G A : closed_typ G A = true <-> close G A.
Proof.
  revert G. induction A; intros G; simpl;
    rewrite ?orb_true_iff, ?andb_true_iff, ?find_ty_spec, ?find_exty_present,
      ?IHA, ?IHA1, ?IHA2;
    split; intros H; try discriminate; try match type of H with _ \/ _ => destruct H as [H|H] end; try match type of H with _ /\ _ => destruct H as [H1 H2] end;
    solve [eauto using close | inversion H; auto].
Qed.

Fixpoint unshift (A : Typ) (k : nat) : option Typ :=
  match A with
  | Int => Some Int
  | TVar x =>
      match Nat.compare x k with
      | Lt => Some (TVar x)
      | Eq => None
      | Gt => Some (TVar (Nat.pred x))
      end
  | Arr A B =>
      match unshift A k with
      | Some C => option_map (Arr C) (unshift B k)
      | None => None
      end
  | All A => option_map All (unshift A (S k))
  end.

Lemma unshift_correct A k B : unshift A k = Some B <-> A = ty_shift B k.
Proof.
  revert k B. induction A; intros k B; destruct B; simpl;
    try solve [split; intros H; inversion H; auto];
    try solve [destruct (n ?= k); split; discriminate];
    try solve [destruct (unshift A1 k), (unshift A2 k); split; discriminate];
    try solve [destruct (unshift A (S k)); split; discriminate].
  - destruct (n ?= k) eqn:E; unfold punchIn;
      destruct (k <=? n0) eqn:F;
      (apply Nat.compare_eq in E || apply Nat.compare_lt_iff in E ||
       apply Nat.compare_gt_iff in E);
      (apply Nat.leb_le in F || apply Nat.leb_gt in F);
      split; intro H; try discriminate; try (injection H as H); try lia;
      repeat f_equal; lia.
  - split.
    + destruct (unshift A1 k) eqn:E, (unshift A2 k) eqn:F;
        simpl; intro H; try discriminate.
      injection H as <- <-. apply IHA1 in E. apply IHA2 in F. now subst.
    + intro H. injection H as E F.
      apply <- IHA1 in E. apply <- IHA2 in F. now rewrite E, F.
  - rewrite option_map_some. split.
    + intros (C & H & E). injection E as <-. now apply IHA in H; subst.
    + intros H. injection H as H. exists B. now rewrite IHA.
Qed.

Fixpoint install (G : Env) (x : nat) (A : Typ) : option Env :=
  match G with
  | ExCons E =>
      match unshift A 0 with
      | None => None
      | Some B =>
          match x with
          | 0 => if regular_typ E B && regular_sub_env E
                 then Some (ExTyCons E B) else None
          | S y => option_map ExCons (install E y B)
          end
      end
  | TyCons E =>
      match x with
      | S y => match unshift A 0 with
               | Some B => option_map TyCons (install E y B)
               | None => None
               end
      | 0 => None
      end
  | ExTyCons E C =>
      match x with
      | S y => match unshift A 0 with
               | Some B => if regular_typ E C then
                             option_map (fun F => ExTyCons F C) (install E y B)
                           else None
               | None => None
               end
      | 0 => None
      end
  | _ => None
  end.

Lemma install_spec G x A F : install G x A = Some F <-> substEnv A x G F.
Proof.
  split.
  - revert x A F. induction G; intros [] A F; simpl; try discriminate;
      destruct (unshift A 0) as [B|] eqn:U; try discriminate;
      apply unshift_correct in U; subst A.
    + destruct (regular_typ G B && regular_sub_env G) eqn:R; try discriminate.
      apply andb_true_iff in R as [R S].
      apply regular_typ_spec in R. apply regular_sub_env_spec in S.
      intros H. injection H as <-. now apply se_ExZ.
    + rewrite option_map_some. intros (E & H & <-). eauto using se_ExS.
    + rewrite option_map_some. intros (E & H & <-). eauto using se_TyS.
    + destruct (regular_typ G t) eqn:R; try discriminate.
      apply regular_typ_spec in R.
      rewrite option_map_some. intros (E & H & <-). eauto using se_ExTyS.
  - intro H. induction H; subst; simpl;
      rewrite (proj2 (unshift_correct (ty_shift A 0) 0 A) eq_refl);
      rewrite ?IHsubstEnv;
      try match goal with
      | R : RegularTyp _ _ |- _ => rewrite (proj2 (regular_typ_spec _ _) R)
      end;
      try match goal with
      | R : SRegular _ |- _ => rewrite (proj2 (regular_sub_env_spec _) R)
      end;
      reflexivity.
Qed.

Definition list_option {X} (o : option X) : list X :=
  match o with Some x => (one x) | None => nil end.

Definition guard {X} (b : bool) (xs : list X) : list X :=
  if b then xs else nil.

Lemma in_list_option {X} (x : X) o :
  In x (list_option o) <-> o = Some x.
Proof. destruct o; simpl; intuition congruence. Qed.

Lemma in_guard {X} (x : X) b xs :
  In x (guard b xs) <-> b = true /\ In x xs.
Proof. destruct b; simpl; intuition discriminate. Qed.

Lemma in_one {X} (x y : X) : In y (one x) <-> y = x.
Proof. simpl; intuition congruence. Qed.

Definition typ_eq_dec (A B : Typ) : {A = B} + {A <> B}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Definition env_eq_dec (G F : Env) : {G = F} + {G <> F}.
Proof. decide equality; apply typ_eq_dec. Defined.

Definition type_eqb (A B : Typ) : bool := if typ_eq_dec A B then true else false.
Definition env_eqb (G F : Env) : bool := if env_eq_dec G F then true else false.

Lemma type_eqb_spec A B : type_eqb A B = true <-> A = B.
Proof. unfold type_eqb. destruct (typ_eq_dec A B); intuition discriminate. Qed.

Lemma env_eqb_spec G F : env_eqb G F = true <-> G = F.
Proof. unfold env_eqb. destruct (env_eq_dec G F); intuition discriminate. Qed.

Definition from_binder (G : Env) : list Env :=
  match G with TyCons F => (one F) | _ => nil end.

Lemma in_from_binder G F : In F (from_binder G) <-> G = TyCons F.
Proof. destruct G; simpl; intuition congruence. Qed.

Definition sub_var_outputs G x B : list Env :=
  list_option (install G x B) ++
  (flat_map (fun C => guard (regular_sub_env G && type_eqb C B) (one G))
            (list_option (find_exty G x))) ++
  (match B with
   | TVar y => guard (regular_sub_env G && find_ty G x && Nat.eqb x y) (one G)
   | _ => nil
   end).

Lemma sub_var_outputs_spec G x B F :
  In F (sub_var_outputs G x B) <->
  substEnv B x G F \/
  (SRegular G /\ lookupExTy G x B /\ F = G) \/
  (SRegular G /\ lookupTy G x /\ B = TVar x /\ F = G).
Proof.
  unfold sub_var_outputs. rewrite !in_app_iff, in_list_option, install_spec,
    in_flat_map.
  setoid_rewrite in_guard. setoid_rewrite andb_true_iff.
  setoid_rewrite regular_sub_env_spec. setoid_rewrite type_eqb_spec.
  setoid_rewrite in_list_option. setoid_rewrite find_exty_spec.
  setoid_rewrite in_one.
  assert (forall C, (exists T, lookupExTy G x T /\
           (SRegular G /\ T = C) /\ F = G) <->
           SRegular G /\ lookupExTy G x C /\ F = G) as H.
  { intro C. split; [intros (T & L & (R & ->) & E) | intros (R & L & E)]; eauto. }
  rewrite H. destruct B; simpl; try (intuition discriminate).
  rewrite in_guard, !andb_true_iff, regular_sub_env_spec, find_ty_spec,
    Nat.eqb_eq, in_one.
  intuition congruence.
Qed.

(* The type on which recursion proceeds is on the side selected by polarity. *)
Fixpoint sub_outputs (G : Env) (A : Typ) (p : Polar) (B : Typ) {struct A}
    : list Env :=
  match A with
  | Int => match B with Int => guard (regular_sub_env G) (one G) | _ => nil end
  | TVar x => sub_var_outputs G x B
  | Arr A1 A2 =>
      match B with
      | Arr B1 B2 =>
          flat_map (fun F => sub_outputs F A2 p B2)
                   (sub_outputs G A1 (neg p) B1)
      | _ => nil
      end
  | All A1 =>
      match B with
      | All B1 => flat_map from_binder (sub_outputs (TyCons G) A1 p B1)
      | _ => nil
      end
  end.

Definition oriented_sub G A p B F :=
  match p with Pos => sub G A Pos B F | Neg => sub G B Neg A F end.

Lemma sub_outputs_spec G A p B F :
  In F (sub_outputs G A p B) <-> oriented_sub G A p B F.
Proof.
  revert G p B F. induction A; intros G [] B F; destruct B;
    cbn [oriented_sub sub_outputs neg].
  all: try solve [split; [contradiction | intro H; inversion H]].
  all: try solve [rewrite in_guard, regular_sub_env_spec, in_one;
                  split; [intros [R ->]; apply s_int; exact R |
                          intro H; inversion H; auto]].
  all: try solve [rewrite sub_var_outputs_spec; split;
                  [intros [H | [(R & H & ->) | (R & H & -> & ->)]];
                   eauto using sub
                  | intro H; inversion H; subst; intuition]].
  all: try solve [rewrite in_flat_map; setoid_rewrite IHA1; setoid_rewrite IHA2;
                  cbn [oriented_sub]; split;
                  [intros (E & H1 & H2); eauto using s_arr |
                   intro H; inversion H; subst; eauto]].
  all: rewrite in_flat_map; setoid_rewrite IHA; setoid_rewrite in_from_binder;
       cbn [oriented_sub].
  all: split; [intros (E & H & ->); eauto using s_all |
               intro H; inversion H; subst; eauto].
Qed.

Lemma sub_candidates_spec G A p B F :
  In F (match p with
        | Pos => sub_outputs G A Pos B
        | Neg => sub_outputs G B Neg A
        end) <-> sub G A p B F.
Proof. destruct p; apply sub_outputs_spec. Qed.

(* Keep every candidate until the enclosing rule has checked its premises. *)
Lemma decide_outputs {X : Set} (P : X -> Prop) (xs : list X) :
  (forall x, In x xs <-> P x) ->
  {x | P x} + {~ exists x, P x}.
Proof.
  intros H. destruct xs as [|x xs].
  - right. intros [x E]. now apply H in E.
  - left. exists x. apply H. now left.
Defined.

Theorem dec_sub : forall Δ A p B,
  {Ω | sub Δ A p B Ω} + {~ exists Ω, sub Δ A p B Ω}.
Proof.
  intros G A p B.
  eapply decide_outputs. intro F. apply sub_candidates_spec.
Defined.

Fixpoint ground_outputs (G : Env) (A : Typ) : list Typ :=
  match A with
  | Int => (one Int)
  | TVar x => list_option (find_exty G x) ++ guard (find_ty G x) (one (TVar x))
  | Arr A B =>
      flat_map (fun C => map (Arr C) (ground_outputs G B)) (ground_outputs G A)
  | All A => map All (ground_outputs (TyCons G) A)
  end.

Lemma ground_outputs_spec G A B : In B (ground_outputs G A) <-> grd_typ G A B.
Proof.
  revert G B. induction A; intros G C; cbn [ground_outputs].
  - rewrite in_one. split; [intros ->; constructor | intro H; now inversion H].
  - rewrite in_app_iff, in_list_option, find_exty_spec, in_guard, find_ty_spec, in_one.
    split; [intros [H | (H & ->)]; now constructor | intro H; inversion H; auto].
  - rewrite in_flat_map. setoid_rewrite in_map_iff.
    setoid_rewrite IHA1. setoid_rewrite IHA2.
    split; [intros (B & H & (D & <- & J)); now constructor |
            intro H; inversion H; subst; eauto].
  - rewrite in_map_iff. setoid_rewrite IHA.
    split; [intros (B & <- & H); now constructor | intro H; inversion H; eauto].
Qed.

Fixpoint term_size (e : Trm) : nat :=
  match e with
  | Lit _ | Var _ => 1
  | Lam e | Ann e _ | TLam e | TApp e _ => 2 + term_size e
  | App e f => 2 + term_size e + term_size f
  end.

Fixpoint context_size (K : Context) : nat :=
  match K with
  | CtxEmpty => 0
  | CtxTyp _ => 1
  | CtxTrm e K => 1 + term_size e + context_size K
  | CtxTApp _ K => 1 + context_size K
  end.

Lemma term_size_pos e : 0 < term_size e.
Proof. destruct e; simpl; lia. Qed.

Lemma term_shift_size e k : term_size (tm_shift e k) = term_size e.
Proof. revert k; induction e; intro k; simpl; now rewrite ?IHe, ?IHe1, ?IHe2. Qed.

Lemma type_shift_term_size e k : term_size (ty_shift_tm e k) = term_size e.
Proof. revert k; induction e; intro k; simpl; now rewrite ?IHe, ?IHe1, ?IHe2. Qed.

Lemma term_shift_context_size K k : context_size (tm_shift_ctx K k) = context_size K.
Proof. induction K; simpl; now rewrite ?IHK, ?term_shift_size. Qed.

Lemma type_shift_context_size K k : context_size (ty_shift_ctx K k) = context_size K.
Proof. induction K; simpl; now rewrite ?IHK, ?type_shift_term_size. Qed.

Definition extend_weights (w : nat -> nat) (a : nat) (x : nat) : nat :=
  match x with 0 => a | S y => w y end.

Fixpoint type_weight (w : nat -> nat) (A : Typ) : nat :=
  match A with
  | Int => 1
  | TVar x => w x
  | Arr A B => 1 + type_weight w A + type_weight w B
  | All A => 1 + type_weight (extend_weights w 1) A
  end.

(* A solved variable weighs more than its solution in the tail environment.
   Lifting under a binder preserves the weight of a shifted type. *)
Fixpoint env_weights (G : Env) : nat -> nat :=
  match G with
  | EnvEmpty => fun _ => 1
  | TmCons E _ | SepCons E => env_weights E
  | TyCons E | ExCons E => extend_weights (env_weights E) 1
  | ExTyCons E A => extend_weights (env_weights E) (S (type_weight (env_weights E) A))
  end.

Lemma type_weight_shift A k w v :
  (forall x, v (punchIn k x) = w x) ->
  type_weight v (ty_shift A k) = type_weight w A.
Proof.
  revert k w v. induction A; intros k w v H; simpl.
  - reflexivity.
  - apply H.
  - now rewrite (IHA1 k w v H), (IHA2 k w v H).
  - f_equal. apply IHA. intros [|x].
    + reflexivity.
    + unfold punchIn in *. simpl. specialize (H x). now destruct (k <=? x).
Qed.

Lemma type_weight_shift_zero A w a :
  type_weight (extend_weights w a) (ty_shift A 0) = type_weight w A.
Proof. apply type_weight_shift. reflexivity. Qed.

Lemma lookup_exty_weight G x A :
  lookupExTy G x A -> type_weight (env_weights G) A < env_weights G x.
Proof.
  intros H. induction H; cbn [env_weights extend_weights];
    rewrite ?type_weight_shift_zero; lia.
Qed.

Inductive query : Set :=
| QTy : Env -> Context -> Trm -> query
| QSub : Env -> Typ -> Context -> query
| QInf : Env -> Context -> query.

Definition output (q : query) : Set :=
  match q with QSub _ _ _ => (Env * Typ)%type | _ => Typ end.

Definition valid (q : query) : output q -> Prop :=
  match q as r return output r -> Prop with
  | QTy G K e => ty G K e
  | QSub G A K => fun v => sub_ctx G A K (fst v) (snd v)
  | QInf G K => infs G K
  end.

(* Doubling the syntax size leaves room for contextual subtyping to call
   inference on the same context while still decreasing the primary measure. *)
Definition primary (q : query) : nat :=
  match q with
  | QTy _ K e => 2 * (term_size e + context_size K)
  | QSub _ _ K => 1 + 2 * context_size K
  | QInf _ K => 2 * context_size K
  end.

Definition secondary (q : query) : nat :=
  match q with QSub G A _ => type_weight (env_weights G) A | _ => 0 end.

Definition answers := forall q, list (output q).

Definition on_arrow {X} (f : Typ -> Typ -> list X) (A : Typ) : list X :=
  match A with Arr B C => f B C | _ => nil end.

Definition on_all {X} (f : Typ -> list X) (A : Typ) : list X :=
  match A with All B => f B | _ => nil end.

Lemma in_on_arrow {X} (x : X) f A :
  In x (on_arrow f A) <-> exists B C, A = Arr B C /\ In x (f B C).
Proof.
  destruct A; simpl; split; [contradiction | intros (? & ? & H & _); discriminate |
      contradiction | intros (? & ? & H & _); discriminate | eauto |
      intros (? & ? & H & J); injection H as <- <-; exact J |
      contradiction | intros (? & ? & H & _); discriminate].
Qed.

Lemma in_on_all {X} (x : X) f A :
  In x (on_all f A) <-> exists B, A = All B /\ In x (f B).
Proof.
  destruct A; simpl; split; try contradiction; try solve [intros (? & H & _); discriminate].
  - eauto.
  - intros (? & H & J). injection H as <-. exact J.
Qed.

Definition generic (e : Trm) : bool :=
  match e with Lit _ | Var _ | Ann _ _ | TLam _ => true | _ => false end.

Definition nonempty (K : Context) : bool :=
  match K with CtxEmpty => false | _ => true end.

Lemma generic_spec e : generic e = true <-> GenericConsumer e.
Proof. destruct e; simpl; intuition discriminate. Qed.

Lemma nonempty_spec K : nonempty K = true <-> NonEmpty K.
Proof. destruct K; simpl; split; intro H; try discriminate; try constructor; inversion H. Qed.

Definition has_output {X} (xs : list X) : bool :=
  match xs with nil => false | _ :: _ => true end.

Lemma has_output_spec {X} (xs : list X) :
  has_output xs = true <-> exists x, In x xs.
Proof. destruct xs as [|x xs]; simpl; split; eauto; try discriminate. intros [? H]; contradiction. Qed.

Definition consumer_outputs (smaller : answers) (G : Env) (K : Context) (e : Trm) :
    list Typ :=
  guard (nonempty K && generic e)
    (flat_map (fun A =>
       flat_map (fun v => guard (env_eqb (fst v) (SepCons G)) (one (snd v)))
                (smaller (QSub (SepCons G) A K)))
       (smaller (QTy G CtxEmpty e))).

Definition type_step (smaller : answers) (G : Env) (K : Context) (e : Trm) :
    list Typ :=
  (match e with
   | App f a => flat_map (on_arrow (fun _ B => one B)) (smaller (QTy G (CtxTrm a K) f))
   | TApp f A =>
       flat_map (on_all (fun B => one (subst B 0 A))) (smaller (QTy G (CtxTApp A K) f))
   | Lit _ => match K with
              | CtxEmpty => guard (regular_tm_env G) (one Int)
              | _ => nil
              end
   | Var x => match K with
              | CtxEmpty => guard (regular_tm_env G) (list_option (find_tm G x))
              | _ => nil
              end
   | Ann f A => match K with
                | CtxEmpty => guard (has_output (smaller (QTy G (CtxTyp A) f))) (one A)
                | _ => nil
                end
   | Lam f =>
       match K with
       | CtxTyp A =>
           on_arrow (fun B C => map (Arr B) (smaller (QTy (TmCons G B) (CtxTyp C) f))) A
       | CtxTrm a K =>
           flat_map (fun A => map (Arr A) (smaller (QTy (TmCons G A) (tm_shift_ctx K 0) f)))
                    (smaller (QTy G CtxEmpty a))
       | _ => nil
       end
   | TLam f =>
       match K with
       | CtxEmpty => map All (smaller (QTy (TyCons G) CtxEmpty f))
       | CtxTyp A =>
           on_all (fun B => guard (has_output (smaller (QTy (TyCons G) (CtxTyp B) f)))
                                   (one (All B))) A
       | _ => nil
       end
   end) ++
  consumer_outputs smaller G K e.


Definition infer_step (smaller : answers) (G : Env) (K : Context) : list Typ :=
  match K with
  | CtxTyp A => guard (regular_tm_env G && regular_typ G A) (one A)
  | CtxTrm e K =>
      flat_map (fun A => map (Arr A) (smaller (QInf G K))) (smaller (QTy G CtxEmpty e))
  | _ => nil
  end.

Definition strip_explicit (B : Typ) (v : Env * Typ) : list (Env * Typ) :=
  match fst v with
  | ExTyCons F C => guard (type_eqb B C) (one (pair F (All (snd v))))
  | _ => nil
  end.

Definition is_arrow (A : Typ) : bool :=
  match A with Arr _ _ => true | _ => false end.

Definition is_all (A : Typ) : bool :=
  match A with All _ => true | _ => false end.

Definition unshift_arrow (A : Typ) : list Typ :=
  filter is_arrow (list_option (unshift A 0)).

Definition strip_ex_arrow (F : Env) (A : Typ) : list (Env * Typ) :=
  match F with
  | ExCons G | ExTyCons G _ => map (pair G) (unshift_arrow A)
  | _ => nil
  end.

Definition solved_var_outputs (same : answers) (G : Env) (x : nat)
    (K : Context) (shape : Typ -> bool) : list (Env * Typ) :=
  flat_map (fun A =>
    flat_map (fun v => guard (env_eqb (fst v) G && shape (snd v)) (one v))
             (same (QSub G A K)))
    (list_option (find_exty G x)).

Definition ctx_step (smaller same : answers) (G : Env) (A : Typ) (K : Context) :
    list (Env * Typ) :=
  match K with
  | CtxEmpty =>
      guard (regular_sub_env G && closed_typ G A)
        (map (pair G) (ground_outputs G A))
  | CtxTyp B => map (fun F => pair F B) (sub_outputs G A Pos B)
  | CtxTApp B K' =>
      match A with
      | All C =>
          flat_map (strip_explicit B)
                   (smaller (QSub (ExTyCons G B) C (ty_shift_ctx K' 0)))
      | TVar x => solved_var_outputs same G x K is_all
      | _ => nil
      end
  | CtxTrm e K' =>
      match A with
      | Int => nil
      | TVar x =>
          solved_var_outputs same G x K is_arrow ++
          flat_map (fun B => map (fun F => pair F B) (list_option (install G x B)))
                   (smaller (QInf G K))
      | Arr B C =>
          guard (closed_typ G B)
            (flat_map (fun D =>
               guard (has_output (smaller (QTy (rm_sep G) (CtxTyp D) e)))
                 (map (fun v => pair (fst v) (Arr D (snd v))) (smaller (QSub G C K'))))
               (ground_outputs G B)) ++
          guard (open_typ G B)
            (flat_map (fun D =>
               flat_map (fun F =>
                 map (fun v => pair (fst v) (Arr D (snd v))) (smaller (QSub F C K')))
                 (sub_outputs G B Neg D))
               (smaller (QTy (rm_sep G) CtxEmpty e)))
      | All B =>
          flat_map (fun v => strip_ex_arrow (fst v) (snd v))
                   (same (QSub (ExCons G) B (CtxTrm (ty_shift_tm e 0) (ty_shift_ctx K' 0))))
      end
  end.

Definition step (smaller same : answers) (q : query) : list (output q) :=
  match q as r return list (output r) with
  | QTy G K e => type_step smaller G K e
  | QSub G A K => ctx_step smaller same G A K
  | QInf G K => infer_step smaller G K
  end.

Definition smaller_correct (f : answers) (q : query) :=
  forall r, primary r < primary q -> forall v, In v (f r) <-> valid r v.

Definition same_correct (f : answers) (q : query) :=
  forall r, primary r = primary q -> secondary r < secondary q ->
    forall v, In v (f r) <-> valid r v.

Lemma nonempty_size K : NonEmpty K -> 0 < context_size K.
Proof. intro H. destruct H; simpl; lia. Qed.

Local Ltac solve_primary :=
  cbn [primary term_size context_size];
  rewrite ?term_shift_context_size, ?type_shift_context_size, ?type_shift_term_size;
  repeat match goal with
  | H : NonEmpty ?K |- _ =>
      let P := fresh in pose proof (nonempty_size K H) as P; clear H
  end;
  repeat match goal with
  | |- context [term_size ?e] =>
      match goal with
      | _ : 0 < term_size e |- _ => fail 1
      | _ => let P := fresh in pose proof (term_size_pos e) as P
      end
  end;
  lia.

Local Ltac normalize_in :=
  repeat first [
    setoid_rewrite in_app_iff | setoid_rewrite in_guard | setoid_rewrite andb_true_iff |
    setoid_rewrite in_flat_map | setoid_rewrite in_map_iff | setoid_rewrite in_one |
    setoid_rewrite in_list_option | setoid_rewrite find_tm_spec | setoid_rewrite find_exty_spec |
    setoid_rewrite install_spec | setoid_rewrite regular_tm_env_spec |
    setoid_rewrite regular_sub_env_spec | setoid_rewrite regular_typ_spec |
    setoid_rewrite closed_typ_spec | setoid_rewrite open_typ_spec | setoid_rewrite ground_outputs_spec |
    setoid_rewrite env_eqb_spec | setoid_rewrite type_eqb_spec | setoid_rewrite has_output_spec |
    setoid_rewrite nonempty_spec | setoid_rewrite generic_spec |
    setoid_rewrite in_on_arrow | setoid_rewrite in_on_all
  ].

Local Tactic Notation "normalize_in" "in" hyp(H) :=
  revert H; normalize_in; intro H.

Local Ltac read_smaller L H :=
  lazymatch type of H with
  | In _ (_ ?q) => apply (L q) in H; [cbn [valid fst snd] in H | solve_primary]
  end.

Local Ltac write_smaller L :=
  lazymatch goal with
  | |- In _ (_ ?q) => apply (L q); [solve_primary | cbn [valid fst snd]; eassumption]
  end.

Lemma consumer_outputs_spec smaller G K e B :
  smaller_correct smaller (QTy G K e) ->
  In B (consumer_outputs smaller G K e) <->
  exists A, NonEmpty K /\ GenericConsumer e /\
            ty G CtxEmpty e A /\ sub_ctx (SepCons G) A K (SepCons G) B.
Proof.
  intro L. unfold consumer_outputs. normalize_in.
  split.
  - intros ((N & C) & A & T & v & S & H).
    normalize_in in H.
    destruct H as (E & ->). destruct v as [F D]. simpl in *; subst F.
    read_smaller L T.
    read_smaller L S.
    eauto.
  - intros (A & N & C & T & S).
    split; [auto |].
    exists A. split.
    + write_smaller L.
    + exists (pair (SepCons G) B). split.
      * write_smaller L.
      * normalize_in. auto.
Qed.

Lemma type_step_spec smaller G K e B :
  smaller_correct smaller (QTy G K e) ->
  In B (type_step smaller G K e) <-> ty G K e B.
Proof.
  intro L. unfold type_step. rewrite in_app_iff, consumer_outputs_spec by exact L.
  split.
  - intros [H | (A & N & C & T & S)]; [|eauto using ty_sub].
    destruct e; [destruct K | destruct K | destruct K | | destruct K | destruct K | ];
      cbn beta iota in H; try solve [contradiction].
    all: normalize_in in H.
    + destruct H as (R & ->). now apply ty_lit.
    + destruct H as (R & T). now apply ty_var.
    + destruct H as (A & C & -> & D & <- & T).
      read_smaller L T. now apply ty_lam1.
    + destruct H as (A & T & C & <- & U).
      read_smaller L T. read_smaller L U. now apply ty_lam2.
    + destruct H as (T & H & A & C & -> & ->).
      read_smaller L H. eauto using ty_app.
    + destruct H as ((C & T) & ->).
      read_smaller L T. eauto using ty_ann.
    + destruct H as (C & <- & T).
      read_smaller L T. now apply ty_tabs.
    + destruct H as (A & -> & (C & T) & ->).
      read_smaller L T. eauto using ty_tabs_ty.
    + destruct H as (T & H & C & -> & ->).
      read_smaller L H. eauto using ty_tapp.
  - intro H. inversion H; subst.
    all: try solve [right; eauto 8].
    all: left; cbn beta iota; normalize_in.
    + auto.
    + auto.
    + split; [eexists; write_smaller L | reflexivity].
    + eexists. split; [write_smaller L | do 2 eexists; auto].
    + eexists. split; [reflexivity | write_smaller L].
    + eexists. split; [write_smaller L |].
      eexists. split; [reflexivity | write_smaller L].
    + eexists. split; [reflexivity | write_smaller L].
    + eexists. split; [write_smaller L | eexists; auto].
    + split; [eexists; write_smaller L | reflexivity].
Qed.

Lemma infer_step_spec smaller G K B :
  smaller_correct smaller (QInf G K) ->
  In B (infer_step smaller G K) <-> infs G K B.
Proof.
  intro L. destruct K; unfold infer_step; normalize_in.
  - split; [contradiction | intro H; inversion H].
  - split; [intros ((R & T) & ->); now apply infs_z | intro H; inversion H; auto].
  - split.
    + intros (A & T & C & <- & I).
      read_smaller L T. read_smaller L I. now apply infs_s.
    + intro H. inversion H; subst.
      eexists. split; [write_smaller L |].
      eexists. split; [reflexivity | write_smaller L].
  - split; [contradiction | intro H; inversion H].
Qed.

Lemma in_unshift_arrow A T :
  In T (unshift_arrow A) <->
  exists C D, T = Arr C D /\ A = Arr (ty_shift C 0) (ty_shift D 0).
Proof.
  unfold unshift_arrow. rewrite filter_In, in_list_option, unshift_correct.
  destruct T; cbn [is_arrow ty_shift]; split;
    try solve [intros (? & ? & H & _); discriminate | intros (? & H); discriminate].
  - intros [H _]. eauto.
  - intros (? & ? & H & J). injection H as <- <-. auto.
Qed.

Lemma in_strip_ex_arrow E A F T :
  In (pair F T) (strip_ex_arrow E A) <->
  (E = ExCons F \/ (exists B, E = ExTyCons F B)) /\
  (exists C D, T = Arr C D /\ A = Arr (ty_shift C 0) (ty_shift D 0)).
Proof.
  destruct E; cbn [strip_ex_arrow]; try setoid_rewrite in_map_iff;
    try setoid_rewrite in_unshift_arrow; split;
    try solve [contradiction | intros ([H | (? & H)] & _); discriminate].
  - intros (D & H & J). inversion H; subst. auto.
  - intros ([H | (? & H)] & J); try discriminate. inversion H; subst. eauto.
  - intros (D & H & J). inversion H; subst. eauto.
  - intros ([H | (? & H)] & J); try discriminate. inversion H; subst. eauto.
Qed.

Lemma in_strip_explicit B v F T :
  In (pair F T) (strip_explicit B v) <->
  fst v = ExTyCons F B /\ T = All (snd v).
Proof.
  destruct v as [E A]. destruct E; cbn [strip_explicit fst snd]; normalize_in;
    split; try solve [contradiction | intros [H _]; discriminate].
  - intros [H J]. inversion J; subst. auto.
  - intros [H J]. inversion H; subst. auto.
Qed.

Local Ltac solve_secondary :=
  cbn [secondary]; first [solve [eapply lookup_exty_weight; eassumption] |
                          cbn [type_weight env_weights]; lia].

Local Ltac read_same S H :=
  lazymatch type of H with
  | In _ (_ ?q) => apply (S q) in H;
      [cbn [valid fst snd] in H | solve_primary | solve_secondary]
  end.

Local Ltac write_same S :=
  lazymatch goal with
  | |- In _ (_ ?q) => apply (S q);
      [solve_primary | solve_secondary | cbn [valid fst snd]; eassumption]
  end.

Lemma solved_var_outputs_spec same G x K F T shape :
  same_correct same (QSub G (TVar x) K) ->
  In (pair F T) (solved_var_outputs same G x K shape) <->
  F = G /\ shape T = true /\
  exists A, lookupExTy G x A /\ sub_ctx G A K G T.
Proof.
  intro S. unfold solved_var_outputs. normalize_in.
  split.
  - intros (A & H & v & M & (E & D) & J).
    inversion J; subst. cbn [fst snd] in *.
    read_same S M. eauto.
  - intros (-> & D & A & H & M).
    exists A. split; [exact H |].
    exists (pair G T). split; [write_same S |].
    cbn [fst snd]. auto.
Qed.

Lemma ctx_step_spec smaller same G A K F T :
  smaller_correct smaller (QSub G A K) ->
  same_correct same (QSub G A K) ->
  In (pair F T) (ctx_step smaller same G A K) <-> sub_ctx G A K F T.
Proof.
  intros L S. destruct K as [|B|e K|B K].
  - cbn [ctx_step]. normalize_in. split.
    + intros ((R & C) & D & E & H). inversion E; subst. now apply s_empty.
    + intro H. inversion H; subst. eauto.
  - cbn [ctx_step]. normalize_in. setoid_rewrite sub_outputs_spec. cbn [oriented_sub].
    split.
    + intros (E & J & H). inversion J; subst. now apply s_typ.
    + intro H. inversion H; subst. eauto.
  - destruct A as [|x|A B|A]; cbn [ctx_step].
    + split; [contradiction | intro H; inversion H].
    + rewrite in_app_iff, solved_var_outputs_spec by exact S. normalize_in.
      split.
      * intros [(-> & D & C & H & I) | (C & H & E & J & M)].
        -- destruct T; cbn [is_arrow] in D; try discriminate.
           eauto using s_svar_trm.
        -- inversion J; subst. read_smaller L H. eauto using s_evar_infers.
      * intro H. inversion H; subst.
        -- left. split; [reflexivity |]. split; [reflexivity | eauto].
        -- right. eexists. split; [write_smaller L | eauto].
    + normalize_in. setoid_rewrite sub_outputs_spec. cbn [oriented_sub].
      split.
      * intros [(C & D & H & (U & V) & [E R] & W & J) |
                (O & D & V & E & P & [I R] & J & M)].
        -- cbn [fst snd] in W. inversion W; subst.
           read_smaller L V. read_smaller L J. eauto using s_trm_c.
        -- cbn [fst snd] in J. inversion J; subst.
           read_smaller L V. read_smaller L M. eauto using s_trm_o.
      * intro H. inversion H; subst.
        -- left. split; [assumption |].
           eexists. split; [eassumption |].
           split; [eexists; write_smaller L |].
           eexists (pair F D). split; [reflexivity | write_smaller L].
        -- right. split; [assumption |].
           eexists. split; [write_smaller L |].
           eexists. split; [eassumption |].
           eexists (pair F D). split; [reflexivity | write_smaller L].
    + normalize_in. setoid_rewrite in_strip_ex_arrow. split.
      * intros ([E R] & M & J & C & D & -> & N). cbn [fst snd] in J, N.
        subst R. destruct J as [-> | (B & ->)];
          read_same S M; eauto using s_alll, s_alll_no.
      * intro H. inversion H; subst.
        -- eexists (pair (ExTyCons F B) (Arr (ty_shift C 0) (ty_shift D 0))).
           split; [write_same S | cbn [fst snd]; eauto 8].
        -- eexists (pair (ExCons F) (Arr (ty_shift C 0) (ty_shift D 0))).
           split; [write_same S | cbn [fst snd]; eauto 8].
  - destruct A as [|x|A C|A]; cbn [ctx_step].
    + split; [contradiction | intro H; inversion H].
    + rewrite solved_var_outputs_spec by exact S. split.
      * intros (-> & D & C & H & I). destruct T; cbn [is_all] in D; try discriminate.
        eauto using s_svar_tapp.
      * intro H. inversion H; subst. split; [reflexivity |].
        split; [reflexivity | eauto].
    + split; [contradiction | intro H; inversion H].
    + normalize_in. setoid_rewrite in_strip_explicit. split.
      * intros ([E R] & M & J & N). cbn [fst snd] in J, N. subst E T.
        read_smaller L M. now apply s_tapp.
      * intro H. inversion H; subst.
        eexists (pair (ExTyCons F B) C). split; [write_smaller L | auto].
Qed.

Lemma step_spec smaller same q :
  smaller_correct smaller q ->
  same_correct same q ->
  forall v, In v (step smaller same q) <-> valid q v.
Proof.
  destruct q; cbn [step valid output]; intros L S v.
  - now apply type_step_spec.
  - destruct v. now apply ctx_step_spec.
  - now apply infer_step_spec.
Qed.

(* Calls that consume syntax restart the type bound. Calls at the same
   syntax size descend through a universal type or follow a solved variable. *)
Fixpoint run_secondary (smaller : answers) (fuel : nat) : answers :=
  match fuel with
  | 0 => fun _ => nil
  | S fuel' => step smaller (run_secondary smaller fuel')
  end.

Fixpoint run_primary (fuel : nat) : answers :=
  match fuel with
  | 0 => fun _ => nil
  | S fuel' =>
      fun q => run_secondary (run_primary fuel') (S (secondary q)) q
  end.

Lemma run_secondary_spec p smaller fuel :
  (forall q, primary q < p -> forall v, In v (smaller q) <-> valid q v) ->
  forall q, primary q <= p -> secondary q < fuel ->
  forall v, In v (run_secondary smaller fuel q) <-> valid q v.
Proof.
  intros L. induction fuel as [|fuel IH]; intros q P S v; [lia |].
  cbn [run_secondary]. apply step_spec.
  - intros r R. apply L. lia.
  - intros r R T. apply IH; lia.
Qed.

Lemma run_primary_spec fuel :
  forall q, primary q < fuel ->
  forall v, In v (run_primary fuel q) <-> valid q v.
Proof.
  induction fuel as [|fuel IH]; intros q P v; [lia |].
  cbn [run_primary]. apply (run_secondary_spec fuel); auto; lia.
Qed.

Theorem dec_ty : forall Γ Σ e,
  {A | ty Γ Σ e A} + {~ exists A, ty Γ Σ e A}.
Proof.
  intros G K e. set (q := QTy G K e).
  apply (decide_outputs (valid q) (run_primary (S (primary q)) q)).
  apply run_primary_spec. lia.
Defined.
