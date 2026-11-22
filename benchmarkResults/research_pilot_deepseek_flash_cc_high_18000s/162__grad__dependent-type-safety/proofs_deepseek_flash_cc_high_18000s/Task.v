Require Import ssreflect.

Require Import Coq.Classes.EquivDec.

Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.

Require Import Stdlib.Init.Sumbool.

Require Import Coq.Program.Equality.

Require Import Coq.Classes.RelationClasses.

Require Import dqtt_ott.

Require Export beta.
From Stdlib Require Import Lia.
From Coq Require Import Logic.ProofIrrelevance.
Local Open Scope usage_scope.


(* ===== inlined from Merged.v ===== *)
(* ---------- projections ---------- *)
Definition gnames (G:context) : list atom := List.map (fun p => fst p) G.
Definition gsorts (G:context) : list sort := List.map (fun p => snd (snd p)) G.
Definition gusages (G:context) : list usage := List.map (fun p => fst (snd p)) G.
Definition dnames (D:D) : list atom := List.map (fun p => fst p) D.
Definition dssorts (D:D) : list sort := List.map (fun p => snd p) D.

(* sort/context substitution *)
Definition sort_subst (b:tm) (x:tmvar) (s:sort) : sort :=
  match s with Tm A => Tm (subst_tm_tm b x A) end.
Definition Dsubst (b:tm) (x:tmvar) (D0:D) : D := map (sort_subst b x) D0.
Definition val_subst (b:tm) (x:tmvar) (p: usage*sort) : usage*sort :=
  (fst p, sort_subst b x (snd p)).
Definition Gsubst (b:tm) (x:tmvar) (G:context) : context := map (val_subst b x) G.

(* ---------- shape relations ---------- *)
Inductive ctx_shape : context -> context -> Prop :=
| csh_nil : ctx_shape nil nil
| csh_cons : forall x q1 q2 A G1 G2, ctx_shape G1 G2 ->
    ctx_shape ((x,(q1,A))::G1) ((x,(q2,A))::G2).

Inductive shapeDG : D -> context -> Prop :=
| sh_nil : shapeDG nil nil
| sh_cons : forall x q A D0 G, shapeDG D0 G ->
    shapeDG ((x,Tm A)::D0) ((x,(q,Tm A))::G).

Lemma csh_length : forall G1 G2, ctx_shape G1 G2 -> length G1 = length G2.
Proof. intros G1 G2 H. induction H; simpl; auto. Qed.
Lemma sh_length_l : forall D0 G, shapeDG D0 G -> length D0 = length G.
Proof. intros D0 G H. induction H; simpl; auto. Qed.
Lemma csh_sym : forall G1 G2, ctx_shape G1 G2 -> ctx_shape G2 G1.
Proof. intros G1 G2 H. induction H; econstructor; auto. Qed.
Lemma csh_names : forall G1 G2, ctx_shape G1 G2 -> gnames G1 = gnames G2.
Proof. intros G1 G2 H. induction H; simpl; auto. rewrite IHctx_shape. reflexivity. Qed.
Lemma csh_sorts : forall G1 G2, ctx_shape G1 G2 -> gsorts G1 = gsorts G2.
Proof. intros G1 G2 H. induction H; simpl; auto. rewrite IHctx_shape. reflexivity. Qed.
Lemma sh_names : forall D0 G, shapeDG D0 G -> dnames D0 = gnames G.
Proof. intros D0 G H. induction H; simpl; auto. rewrite IHshapeDG. reflexivity. Qed.
Lemma sh_sorts : forall D0 G, shapeDG D0 G -> dssorts D0 = gsorts G.
Proof. intros D0 G H. induction H; simpl; auto. rewrite IHshapeDG. reflexivity. Qed.
Lemma sh_sym : forall D0 G1 G2, shapeDG D0 G1 -> shapeDG D0 G2 -> ctx_shape G1 G2.
Proof.
  intros D0. induction D0 as [|[x A] D0 IH]; intros G1 G2 H1 H2.
  - inversion H1. inversion H2. constructor.
  - destruct A as [A]. inversion H1; subst. inversion H2; subst.
    econstructor. apply IH; assumption.
Qed.

(* ---------- basic ctx_plus / ctx_mul ---------- *)
Lemma ctx_plus_nil_l : forall (G:context), ctx_plus nil G = nil.
Proof. intros [| [x [q A]] G]; reflexivity. Qed.
Lemma ctx_plus_nil_r : forall (G:context), ctx_plus G nil = nil.
Proof. intros [| [x [q A]] G]; reflexivity. Qed.
Lemma ctx_mul_nil : forall (q:usage), ctx_mul q (nil:context) = nil.
Proof. reflexivity. Qed.
Lemma ctx_mul_cons : forall (q:usage) (x:atom) (q1:usage) (A:sort) (G:context),
  ctx_mul q ((x,(q1,A))::G) = (x,(q*q1,A))::ctx_mul q G.
Proof. reflexivity. Qed.
Lemma ctx_plus_cons : forall (x:atom) (q1:usage) (A:sort) (G1:context) (y:atom) (q2:usage) (B:sort) (G2:context),
  ctx_plus ((x,(q1,A))::G1) ((y,(q2,B))::G2) = (x,(q1+q2,A))::ctx_plus G1 G2.
Proof. reflexivity. Qed.

Lemma ctx_plus_nil_eq : forall (G1 G2:context), ctx_plus G1 G2 = nil -> G1 = nil \/ G2 = nil.
Proof. intros G1 G2. destruct G1 as [|[x [q A]] G1]; destruct G2 as [|[y [q2 B]] G2]; simpl; auto. intros H; discriminate. Qed.

Lemma ctx_plus_not_nil : forall (G1 G2:context), G1 <> nil -> G2 <> nil -> ctx_plus G1 G2 <> nil.
Proof. intros G1 G2. destruct G1 as [|[x [q A]] G1]; destruct G2 as [|[y [q2 B]] G2]; simpl; intros H1 H2; try discriminate; try contradiction. Qed.

Lemma ctx_mul_app : forall (q:usage) (G1 G2:context), ctx_mul q (G1++G2) = ctx_mul q G1 ++ ctx_mul q G2.
Proof.
  intros q G1. induction G1 as [| [x [q1 A]] G1 IH]; intros G2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma ctx_mul_ctx_plus : forall (q:usage) (G1 G2:context),
  ctx_mul q (ctx_plus G1 G2) = ctx_plus (ctx_mul q G1) (ctx_mul q G2).
Proof.
  intros q G1. induction G1 as [| [x [q1 A]] G1 IH]; intros G2.
  - destruct G2 as [|[y [q2 B]] G2]; simpl; reflexivity.
  - destruct G2 as [|[y [q2 B]] G2]; simpl.
    + reflexivity.
    + rewrite distr_r. rewrite IH. reflexivity.
Qed.

Lemma ctx_mul_ctx_mul : forall (q1 q2:usage) (G:context),
  ctx_mul q1 (ctx_mul q2 G) = ctx_mul (q1*q2) G.
Proof.
  intros q1 q2 G. induction G as [| [x [q A]] G IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite qmul_assoc. reflexivity.
Qed.

Lemma ctx_plus_app : forall (G1 G2 G3 G4:context),
  length G1 = length G3 ->
  ctx_plus (G1++G2) (G3++G4) = ctx_plus G1 G3 ++ ctx_plus G2 G4.
Proof.
  intros G1. induction G1 as [| [x [q1 A]] G1 IH]; intros G2 G3 G4 Hlen.
  - destruct G3; [|discriminate]. simpl. reflexivity.
  - destruct G3 as [| [y [q3 B]] G3]; [discriminate|]. simpl in Hlen. injection Hlen as Hlen.
    simpl. rewrite IH; auto.
Qed.

Lemma ctx_plus_comm_shape : forall (G1 G2:context),
  ctx_shape G1 G2 -> ctx_plus G1 G2 = ctx_plus G2 G1.
Proof.
  intros G1 G2 H. induction H; simpl.
  - reflexivity.
  - rewrite qplus_comm. rewrite IHctx_shape. reflexivity.
Qed.

(* names/sorts of operations *)
Lemma gnames_app : forall (G1 G2:context), gnames (G1++G2) = gnames G1 ++ gnames G2.
Proof. intros. unfold gnames. apply List.map_app. Qed.
Lemma gsorts_app : forall (G1 G2:context), gsorts (G1++G2) = gsorts G1 ++ gsorts G2.
Proof. intros. unfold gsorts. apply List.map_app. Qed.
Lemma gusages_app : forall (G1 G2:context), gusages (G1++G2) = gusages G1 ++ gusages G2.
Proof. intros. unfold gusages. apply List.map_app. Qed.
Lemma gnames_cons : forall (x:atom) (q:usage) (A:sort) (G:context), gnames ((x,(q,A))::G) = x :: gnames G.
Proof. reflexivity. Qed.
Lemma gsorts_cons : forall (x:atom) (q:usage) (A:sort) (G:context), gsorts ((x,(q,A))::G) = A :: gsorts G.
Proof. reflexivity. Qed.
Lemma gnames_ctx_mul : forall (q:usage) (G:context), gnames (ctx_mul q G) = gnames G.
Proof.
  intros q G. induction G as [| [x [q1 A]] G IH]; simpl.
  - reflexivity. - simpl. rewrite IH. reflexivity.
Qed.
Lemma gsorts_ctx_mul : forall (q:usage) (G:context), gsorts (ctx_mul q G) = gsorts G.
Proof.
  intros q G. induction G as [| [x [q1 A]] G IH]; simpl.
  - reflexivity. - simpl. rewrite IH. reflexivity.
Qed.
Lemma gnames_ctx_plus_shape : forall G1 G2, ctx_shape G1 G2 -> gnames (ctx_plus G1 G2) = gnames G1.
Proof.
  intros G1 G2 H. induction H; simpl. reflexivity.
  rewrite IHctx_shape. reflexivity.
Qed.
Lemma gsorts_ctx_plus_shape : forall G1 G2, ctx_shape G1 G2 -> gsorts (ctx_plus G1 G2) = gsorts G1.
Proof. intros G1 G2 H. induction H; simpl. reflexivity. rewrite IHctx_shape. reflexivity. Qed.

Lemma gnames_subst : forall (b:tm) (x:tmvar) (G:context), gnames (Gsubst b x G) = gnames G.
Proof. intros. unfold Gsubst, gnames. induction G as [|[y [q A]] G IH]; simpl; auto. rewrite IH; auto. Qed.
Lemma gsorts_subst : forall (b:tm) (x:tmvar) (G:context), gsorts (Gsubst b x G) = List.map (sort_subst b x) (gsorts G).
Proof. intros b x G. unfold gsorts, Gsubst. induction G as [|[y [q A]] G IH]; simpl; auto. rewrite IH; auto. Qed.
Lemma dnames_Dsubst : forall (b:tm) (x:tmvar) (D0:D), dnames (Dsubst b x D0) = dnames D0.
Proof. intros. unfold Dsubst, dnames. induction D0 as [|[y A] D0 IH]; simpl; auto. rewrite IH; auto. Qed.
Lemma dssorts_Dsubst : forall (b:tm) (x:tmvar) (D0:D), dssorts (Dsubst b x D0) = List.map (sort_subst b x) (dssorts D0).
Proof. intros b x D0. unfold dssorts, Dsubst. induction D0 as [|[y A] D0 IH]; simpl; auto. rewrite IH; auto. Qed.
Lemma length_Gsubst : forall (b:tm) (x:tmvar) (G:context), length (Gsubst b x G) = length G.
Proof. intros. unfold Gsubst. rewrite map_length. reflexivity. Qed.
Lemma length_Dsubst : forall (b:tm) (x:tmvar) (D0:D), length (Dsubst b x D0) = length D0.
Proof. intros. unfold Dsubst. rewrite map_length. reflexivity. Qed.

(* sort substitution on contexts commutes with shape *)
Lemma sh_Dsubst : forall b x D0 G, shapeDG D0 G -> shapeDG (Dsubst b x D0) (Gsubst b x G).
Proof.
  intros b x D0. induction D0 as [|[y A] D0 IH]; intros G H.
  - inversion H. constructor.
  - destruct A as [A0]. inversion H as [| y' q' A' D0' G' Hsh]; subst.
    unfold Dsubst, Gsubst. simpl.
    change (shapeDG ((y, Tm (subst_tm_tm b x A0)) :: map (sort_subst b x) D0)
                   ((y, (q', Tm (subst_tm_tm b x A0))) :: map (val_subst b x) G')).
    constructor. apply IH. assumption.
Qed.



Lemma le_SS : forall k k', Nat.le k k' -> Nat.le (S k) (S k').
Proof. intros; lia. Qed.

Fixpoint cl (k:nat) (t:tm) : Prop :=
  match t with
  | a_TyUnit => True
  | a_TmUnit => True
  | a_letunitB a b B => cl k a /\ cl k b /\ cl k B
  | a_Pi q A B => cl k A /\ cl (S k) B
  | a_Lam q A a => cl k A /\ cl (S k) a
  | a_App a b => cl k a /\ cl k b
  | a_Box q A => cl k A
  | a_LetBoxB a b B => cl k a /\ cl (S k) b /\ cl k B
  | a_Type => True
  | a_Var_b n => n < k
  | a_Var_f x => True
  | a_box q a => cl k a
  | a_Let a b => cl k a /\ cl (S k) b
  | a_Sum A1 A2 => cl k A1 /\ cl k A2
  | a_Inj1 a => cl k a
  | a_Inj2 a => cl k a
  | a_Case q a b1 b2 B => cl k a /\ cl k b1 /\ cl k b2 /\ cl k B
  | a_Sigma q A B => cl k A /\ cl (S k) B
  | a_Tensor a b => cl k a /\ cl k b
  | a_Spread a b B => cl k a /\ cl (S k) b /\ cl k B
  end.

Ltac useih :=
  match goal with
  | IH : forall (k0 k1:nat), Nat.le k0 k1 -> cl k0 ?x -> cl k1 ?x,
    Hx : cl ?k0 ?x
    |- cl ?kk ?x =>
       apply (IH k0 kk); [ lia | exact Hx ]
  end.

Lemma cl_mono : forall (u:tm) k k', Nat.le k k' -> cl k u -> cl k' u.
Proof.
  intros u. induction u; intros k k' Hle H; simpl in *; try tauto.
  all: try (destruct H as [? [? [? ?]]]).
  all: try (destruct H as [? [? ?]]).
  all: try (destruct H as [? ?]).
  all: try (repeat (first [ split | useih | assumption | lia ])).
Qed.


Lemma cl_open_rec_eq : forall (t:tm) k u, cl k t -> open_tm_wrt_tm_rec k u t = t.
Proof.
  intros t. induction t as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n | x
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros k u Hc; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct Hc as [Ha [Hb HB]]. f_equal; [apply (IHa k u Ha)|apply (IHb k u Hb)|apply (IHB k u HB)].
  - destruct Hc as [HA HB]. f_equal; [apply (IHA k u HA)|apply (IHB (S k) u HB)].
  - destruct Hc as [HA Ha]. f_equal; [apply (IHA k u HA)|apply (IHa (S k) u Ha)].
  - destruct Hc as [Ha Hb]. f_equal; [apply (IHa k u Ha)|apply (IHb k u Hb)].
  - f_equal; apply (IHA k u Hc).
  - destruct Hc as [Ha [Hb HB]]. f_equal; [apply (IHa k u Ha)|apply (IHb (S k) u Hb)|apply (IHB k u HB)].
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; try lia; try reflexivity.
  - reflexivity.
  - f_equal; apply (IHa k u Hc).
  - destruct Hc as [Ha Hb]. f_equal; [apply (IHa k u Ha)|apply (IHb (S k) u Hb)].
  - destruct Hc as [H1 H2]. f_equal; [apply (IHA1 k u H1)|apply (IHA2 k u H2)].
  - f_equal; apply (IHa k u Hc).
  - f_equal; apply (IHa k u Hc).
  - destruct Hc as [Ha [Hb1 [Hb2 HB]]]. f_equal; [apply (IHa k u Ha)|apply (IHb1 k u Hb1)|apply (IHb2 k u Hb2)|apply (IHB k u HB)].
  - destruct Hc as [HA HB]. f_equal; [apply (IHA k u HA)|apply (IHB (S k) u HB)].
  - destruct Hc as [Ha Hb]. f_equal; [apply (IHa k u Ha)|apply (IHb k u Hb)].
  - destruct Hc as [Ha [Hb HB]]. f_equal; [apply (IHa k u Ha)|apply (IHb (S k) u Hb)|apply (IHB k u HB)].
Qed.

Lemma cl_open_fwd : forall (t:tm) K, cl (S K) t -> forall u, cl 0 u -> cl K (open_tm_wrt_tm_rec K u t).
Proof.
  intros t. induction t as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n | x
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros K Hc u Hu; simpl in *.
  - exact I.
  - exact I.
  - destruct Hc as [Ha [Hb HB]]. repeat split.
    + apply (IHa K Ha u Hu).
    + apply (IHb K Hb u Hu).
    + apply (IHB K HB u Hu).
  - destruct Hc as [HA HB]. split.
    + apply (IHA K HA u Hu).
    + apply (IHB (S K) HB u Hu).
  - destruct Hc as [HA Ha]. split.
    + apply (IHA K HA u Hu).
    + apply (IHa (S K) Ha u Hu).
  - destruct Hc as [Ha Hb]. split; [apply (IHa K Ha u Hu)|apply (IHb K Hb u Hu)].
  - apply (IHA K Hc u Hu).
  - destruct Hc as [Ha [Hb HB]]. repeat split.
    + apply (IHa K Ha u Hu).
    + apply (IHb (S K) Hb u Hu).
    + apply (IHB K HB u Hu).
  - exact I.
  - destruct (lt_eq_lt_dec n K) as [[Hlt|Heq]|Hgt]; simpl in *.
    + lia.
    + exact (cl_mono u 0%nat K (Nat.le_0_l K) Hu).
    + lia.
  - exact I.
  - apply (IHa K Hc u Hu).
  - destruct Hc as [Ha Hb]. split.
    + apply (IHa K Ha u Hu).
    + apply (IHb (S K) Hb u Hu).
  - destruct Hc as [H1 H2]. split; [apply (IHA1 K H1 u Hu)|apply (IHA2 K H2 u Hu)].
  - apply (IHa K Hc u Hu).
  - apply (IHa K Hc u Hu).
  - destruct Hc as [Ha [Hb1 [Hb2 HB]]]. repeat split.
    + apply (IHa K Ha u Hu).
    + apply (IHb1 K Hb1 u Hu).
    + apply (IHb2 K Hb2 u Hu).
    + apply (IHB K HB u Hu).
  - destruct Hc as [HA HB]. split.
    + apply (IHA K HA u Hu).
    + apply (IHB (S K) HB u Hu).
  - destruct Hc as [Ha Hb]. split; [apply (IHa K Ha u Hu)|apply (IHb K Hb u Hu)].
  - destruct Hc as [Ha [Hb HB]]. repeat split.
    + apply (IHa K Ha u Hu).
    + apply (IHb (S K) Hb u Hu).
    + apply (IHB K HB u Hu).
Qed.

Lemma cl_open_bwd : forall (t:tm) K x, cl K (open_tm_wrt_tm_rec K (a_Var_f x) t) -> cl (S K) t.
Proof.
  intros t. induction t as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n | x0
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros K x Hc; simpl in *.
  - exact I.
  - exact I.
  - destruct Hc as [Ha [Hb HB]]. repeat split.
    + apply (IHa K x Ha).
    + apply (IHb K x Hb).
    + apply (IHB K x HB).
  - destruct Hc as [HA HB]. split.
    + apply (IHA K x HA).
    + apply (IHB (S K) x HB).
  - destruct Hc as [HA Ha]. split.
    + apply (IHA K x HA).
    + apply (IHa (S K) x Ha).
  - destruct Hc as [Ha Hb]. split; [apply (IHa K x Ha)|apply (IHb K x Hb)].
  - apply (IHA K x Hc).
  - destruct Hc as [Ha [Hb HB]]. repeat split.
    + apply (IHa K x Ha).
    + apply (IHb (S K) x Hb).
    + apply (IHB K x HB).
  - exact I.
  - destruct (lt_eq_lt_dec n K) as [[Hlt|Heq]|Hgt]; simpl in *.
    + lia.
    + lia.
    + lia.
  - exact I.
  - apply (IHa K x Hc).
  - destruct Hc as [Ha Hb]. split.
    + apply (IHa K x Ha).
    + apply (IHb (S K) x Hb).
  - destruct Hc as [H1 H2]. split; [apply (IHA1 K x H1)|apply (IHA2 K x H2)].
  - apply (IHa K x Hc).
  - apply (IHa K x Hc).
  - destruct Hc as [Ha [Hb1 [Hb2 HB]]]. repeat split.
    + apply (IHa K x Ha).
    + apply (IHb1 K x Hb1).
    + apply (IHb2 K x Hb2).
    + apply (IHB K x HB).
  - destruct Hc as [HA HB]. split.
    + apply (IHA K x HA).
    + apply (IHB (S K) x HB).
  - destruct Hc as [Ha Hb]. split; [apply (IHa K x Ha)|apply (IHb K x Hb)].
  - destruct Hc as [Ha [Hb HB]]. repeat split.
    + apply (IHa K x Ha).
    + apply (IHb (S K) x Hb).
    + apply (IHB K x HB).
Qed.

Lemma body_cl_1 : forall (b:tm),
  (forall x:atom, cl 0 (open_tm_wrt_tm b (a_Var_f x))) -> cl 1 b.
Proof.
  intros b H. destruct (atom_fresh_for_list nil) as [y _].
  apply (cl_open_bwd b 0 y). apply H.
Qed.

Lemma lc_cl : forall (t:tm), lc_tm t -> cl 0 t.
Proof.
  intros t H. induction H; simpl.
  all: try exact I.
  all: try (repeat split).
  all: try (apply body_cl_1; auto).
  all: auto.
Qed.

Fixpoint size_tm (t:tm) : nat :=
  match t with
  | a_TyUnit => 1
  | a_TmUnit => 1
  | a_letunitB a b B => 1 + size_tm a + size_tm b + size_tm B
  | a_Pi q A B => 1 + size_tm A + size_tm B
  | a_Lam q A a => 1 + size_tm A + size_tm a
  | a_App a b => 1 + size_tm a + size_tm b
  | a_Box q A => 1 + size_tm A
  | a_LetBoxB a b B => 1 + size_tm a + size_tm b + size_tm B
  | a_Type => 1
  | a_Var_b n => 1
  | a_Var_f x => 1
  | a_box q a => 1 + size_tm a
  | a_Let a b => 1 + size_tm a + size_tm b
  | a_Sum A1 A2 => 1 + size_tm A1 + size_tm A2
  | a_Inj1 a => 1 + size_tm a
  | a_Inj2 a => 1 + size_tm a
  | a_Case q a b1 b2 B => 1 + size_tm a + size_tm b1 + size_tm b2 + size_tm B
  | a_Sigma q A B => 1 + size_tm A + size_tm B
  | a_Tensor a b => 1 + size_tm a + size_tm b
  | a_Spread a b B => 1 + size_tm a + size_tm b + size_tm B
  end.

Ltac vbsize :=
  match goal with
  | |- context [lt_eq_lt_dec ?m ?kk] =>
      destruct (lt_eq_lt_dec m kk) as [[H1|H2]|H3]; simpl; reflexivity
  end.

Lemma size_open_var : forall (t:tm) k x, size_tm (open_tm_wrt_tm_rec k (a_Var_f x) t) = size_tm t.
Proof.
  intros t. induction t as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n0 | y
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros k x; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHa; rewrite IHb; rewrite IHB; reflexivity.
  - rewrite IHA; rewrite IHB; reflexivity.
  - rewrite IHA; rewrite IHa; reflexivity.
  - rewrite IHa; rewrite IHb; reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHa; rewrite IHb; rewrite IHB; reflexivity.
  - reflexivity.
  - vbsize.
  - reflexivity.
  - rewrite IHa; reflexivity.
  - rewrite IHa; rewrite IHb; reflexivity.
  - rewrite IHA1; rewrite IHA2; reflexivity.
  - rewrite IHa; reflexivity.
  - rewrite IHa; reflexivity.
  - rewrite IHa; rewrite IHb1; rewrite IHb2; rewrite IHB; reflexivity.
  - rewrite IHA; rewrite IHB; reflexivity.
  - rewrite IHa; rewrite IHb; reflexivity.
  - rewrite IHa; rewrite IHb; rewrite IHB; reflexivity.
Qed.


Lemma cl_lc_aux : forall n (t:tm), Nat.le (size_tm t) n -> cl 0 t -> lc_tm t.
Proof.
  induction n as [| n IH]; intros t Hle Hc.
  - destruct t; simpl in Hle; lia.
  - destruct t as [| | a b B | q A B | q A a | a b | q A | a b B | | n0 | x | q a | a b | A1 A2 | a | a | q a b1 b2 B0 | q A B | a b | a b B];
      simpl in *.
    + constructor.
    + constructor.
    + destruct Hc as [Ha [Hb HB]]. constructor.
      * apply (IH a); [simpl in Hle; lia | exact Ha].
      * apply (IH b); [simpl in Hle; lia | exact Hb].
      * apply (IH B); [simpl in Hle; lia | exact HB].
    + destruct Hc as [HA HB]. constructor.
      * apply (IH A); [simpl in Hle; lia | exact HA].
      * intros y. apply (IH (open_tm_wrt_tm B (a_Var_f y))).
        -- rewrite size_open_var. simpl in Hle. lia.
        -- apply (cl_open_fwd B 0 HB (a_Var_f y)). exact I.
    + destruct Hc as [HA Ha]. constructor.
      * apply (IH A); [simpl in Hle; lia | exact HA].
      * intros y. apply (IH (open_tm_wrt_tm a (a_Var_f y))).
        -- rewrite size_open_var. simpl in Hle. lia.
        -- apply (cl_open_fwd a 0 Ha (a_Var_f y)). exact I.
    + destruct Hc as [Ha Hb]. constructor.
      * apply (IH a); [simpl in Hle; lia | exact Ha].
      * apply (IH b); [simpl in Hle; lia | exact Hb].
    + constructor. apply (IH A); [simpl in Hle; lia | exact Hc].
    + destruct Hc as [Ha [Hb HB]]. constructor.
      * apply (IH a); [simpl in Hle; lia | exact Ha].
      * intros y. apply (IH (open_tm_wrt_tm b (a_Var_f y))).
        -- rewrite size_open_var. simpl in Hle. lia.
        -- apply (cl_open_fwd b 0 Hb (a_Var_f y)). exact I.
      * apply (IH B); [simpl in Hle; lia | exact HB].
    + constructor.
    + simpl in Hc. lia.
    + constructor.
    + constructor. apply (IH a); [simpl in Hle; lia | exact Hc].
    + destruct Hc as [Ha Hb]. constructor.
      * apply (IH a); [simpl in Hle; lia | exact Ha].
      * intros y. apply (IH (open_tm_wrt_tm b (a_Var_f y))).
        -- rewrite size_open_var. simpl in Hle. lia.
        -- apply (cl_open_fwd b 0 Hb (a_Var_f y)). exact I.
    + destruct Hc as [H1 H2]. constructor.
      * apply (IH A1); [simpl in Hle; lia | exact H1].
      * apply (IH A2); [simpl in Hle; lia | exact H2].
    + constructor. apply (IH a); [simpl in Hle; lia | exact Hc].
    + constructor. apply (IH a); [simpl in Hle; lia | exact Hc].
    + destruct Hc as [Ha [Hb1 [Hb2 HB]]]. constructor.
      * apply (IH a); [simpl in Hle; lia | exact Ha].
      * apply (IH b1); [simpl in Hle; lia | exact Hb1].
      * apply (IH b2); [simpl in Hle; lia | exact Hb2].
      * apply (IH B0); [simpl in Hle; lia | exact HB].
    + destruct Hc as [HA HB]. constructor.
      * apply (IH A); [simpl in Hle; lia | exact HA].
      * intros y. apply (IH (open_tm_wrt_tm B (a_Var_f y))).
        -- rewrite size_open_var. simpl in Hle. lia.
        -- apply (cl_open_fwd B 0 HB (a_Var_f y)). exact I.
    + destruct Hc as [Ha Hb]. constructor.
      * apply (IH a); [simpl in Hle; lia | exact Ha].
      * apply (IH b); [simpl in Hle; lia | exact Hb].
    + destruct Hc as [Ha [Hb HB]]. constructor.
      * apply (IH a); [simpl in Hle; lia | exact Ha].
      * intros y. apply (IH (open_tm_wrt_tm b (a_Var_f y))).
        -- rewrite size_open_var. simpl in Hle. lia.
        -- apply (cl_open_fwd b 0 Hb (a_Var_f y)). exact I.
      * apply (IH B); [simpl in Hle; lia | exact HB].
Qed.

Lemma cl_lc : forall (t:tm), cl 0 t -> lc_tm t.
Proof.
  intros t Hc. apply (cl_lc_aux (size_tm t) t); [lia | exact Hc].
Qed.

Lemma shapeDG_mul : forall (D:D) (G:context) (q:usage), shapeDG D G -> shapeDG D (ctx_mul q G).
Proof.
  intros D. induction D as [|[x A] D IH]; intros G q H.
  - inversion H. simpl. constructor.
  - destruct A as [A]. inversion H as [| xx qq AA DD GG Hsh]; subst. simpl.
    constructor. apply IH. assumption.
Qed.

Lemma shapeDG_plus : forall (D:D) (G1 G2:context), shapeDG D G1 -> shapeDG D G2 -> shapeDG D (ctx_plus G1 G2).
Proof.
  intros D. induction D as [|[x A] D IH]; intros G1 G2 H1 H2.
  - inversion H1. inversion H2. simpl. constructor.
  - destruct A as [A]. inversion H1 as [| x1 q1 A1 D1 G1' Hsh1]; subst.
    inversion H2 as [| x2 q2 A2 D2 G2' Hsh2]; subst.
    simpl. constructor. apply (IH G1' G2'); assumption.
Qed.

Lemma shapeDG_cons_inv : forall (x:atom) (A:tm) (D:D) (G:context),
  shapeDG ((x,Tm A)::D) G -> exists q G', G = (x,(q,Tm A))::G' /\ shapeDG D G'.
Proof.
  intros x A D G H. inversion H as [| xx qq AA DD GG Hsh]; subst.
  exists qq, GG. split; [reflexivity | assumption].
Qed.


Lemma ctx_sub_shape : forall (D0:D) (G1 G2:context), ctx_sub D0 G1 G2 -> shapeDG D0 G1 -> shapeDG D0 G2.
Proof.
  intros D0 G1 G2 H. induction H; intros Hsh.
  - constructor.
  - inversion Hsh as [| xx qq AA DD GG Hsh']; subst.
    simpl. constructor. apply IHctx_sub. assumption.
Qed.

Lemma shapeDG_binder_inv : forall (L:atoms) (A:tm) (r:usage) (D0:D) (G:context),
  (forall x:atom, x \notin L -> shapeDG (x ~ Tm A ++ D0) (x ~ (r, Tm A) ++ G)) -> shapeDG D0 G.
Proof.
  intros L A r D0 G H.
  pick fresh x for L.
  assert (Hx : x \notin L) by assumption.
  pose proof (H x Hx) as Hsh.
  apply shapeDG_cons_inv in Hsh.
  destruct Hsh as [q [G' [Heq Hrest]]].
  inversion Heq; subst; exact Hrest.
Qed.

Lemma shapeDG_binder_inv2 : forall (L:atoms) (A:tm) (r:usage) (D0:D) (G:context),
  (forall x:atom, x \notin L -> forall y:atom, y \notin L \u {{x}} -> shapeDG (x ~ Tm A ++ D0) (x ~ (r, Tm A) ++ G)) -> shapeDG D0 G.
Proof.
  intros L A r D0 G H.
  pick fresh x for L.
  assert (Hx : x \notin L) by assumption.
  pose proof (H x Hx) as Hxy.
  pick fresh y for (L \u {{x}}).
  assert (Hy : y \notin L \u {{x}}) by assumption.
  pose proof (Hxy y Hy) as Hsh.
  apply shapeDG_cons_inv in Hsh.
  destruct Hsh as [q [G' [Heq Hrest]]].
  inversion Heq; subst; exact Hrest.
Qed.

Ltac align_binder :=
  match goal with
  | IHf : forall (x:atom), x \notin ?L -> shapeDG (x ~ Tm ?A ++ ?D) (x ~ (?r, Tm ?A) ++ ?G)
    |- shapeDG ?D ?G =>
      exact (shapeDG_binder_inv L A r D G IHf)
  end.

Ltac align_binder2 :=
  match goal with
  | IHf : forall (x:atom), x \notin ?L -> forall (y:atom), y \notin _ -> shapeDG (x ~ Tm ?A ++ ?D) (x ~ (?r, Tm ?A) ++ ?G)
    |- shapeDG ?D ?G =>
      exact (shapeDG_binder_inv2 L A r D G IHf)
  end.

Ltac align_sub :=
  match goal with
  | Hs : ctx_sub ?D ?G1 ?G2, H : shapeDG ?D ?G1 |- shapeDG ?D ?G2 =>
      exact (ctx_sub_shape D G1 G2 Hs H)
  end.

Ltac align_mul :=
  match goal with |- shapeDG ?D (ctx_mul ?q ?G) => apply shapeDG_mul end.

Ltac align_plus :=
  match goal with |- shapeDG ?D (ctx_plus ?G1 ?G2) => apply shapeDG_plus end.

Ltac align_assum :=
  match goal with H : shapeDG _ _ |- shapeDG _ _ => exact H end.

Ltac align_base :=
  match goal with |- shapeDG nil nil => constructor end.

Ltac align_cons :=
  match goal with
  | |- shapeDG ((?x, Tm ?A) :: ?D) ((?x, (?q, Tm ?A)) :: ?G) => constructor
  end.

Lemma typing_align : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> shapeDG D0 G.
Proof.
  intros D0 G a A H. induction H; simpl.
  all: try align_base.
  all: try align_cons.
  all: try align_mul.
  all: try align_plus.
  all: try align_assum.
  all: try align_binder.
  all: try align_binder2.
  all: try align_sub.
  all: try align_base.
  all: try align_cons.
  all: try align_mul.
  all: try align_plus.
  all: try align_assum.
  all: try align_binder.
  all: try align_binder2.
  all: try align_cons.
  all: try align_mul.
  all: try align_plus.
  all: try align_assum.
Qed.

Lemma body_cl_1_fst : forall (L:atoms) (b:tm) (P:atom -> Prop),
  (forall x:atom, x \notin L -> cl 0 (open_tm_wrt_tm b (a_Var_f x)) /\ P x) -> cl 1 b.
Proof.
  intros L b P H. pick fresh x for L.
  assert (Hx : x \notin L) by assumption.
  apply (cl_open_bwd b 0 x). exact (proj1 (H x Hx)).
Qed.

Lemma body_cl_1_snd : forall (L:atoms) (b:tm) (P:atom -> Prop),
  (forall x:atom, x \notin L -> P x /\ cl 0 (open_tm_wrt_tm b (a_Var_f x))) -> cl 1 b.
Proof.
  intros L b P H. pick fresh x for L.
  assert (Hx : x \notin L) by assumption.
  apply (cl_open_bwd b 0 x). exact (proj2 (H x Hx)).
Qed.

Lemma body_cl_1_fst2 : forall (L:atoms) (b:tm) (P:atom -> atom -> Prop),
  (forall x:atom, x \notin L -> forall y:atom, y \notin L \u {{x}} -> cl 0 (open_tm_wrt_tm b (a_Var_f x)) /\ P x y) -> cl 1 b.
Proof.
  intros L b P H. pick fresh x for L.
  assert (Hx : x \notin L) by assumption.
  pose proof (H x Hx) as Hy.
  pick fresh y for (L \u {{x}}).
  assert (Hyy : y \notin L \u {{x}}) by assumption.
  apply (cl_open_bwd b 0 x). exact (proj1 (Hy y Hyy)).
Qed.

Ltac cl_body :=
  match goal with
  | |- cl 1 ?b =>
      first [
        (match goal with
         | H : forall x, x \notin ?L -> cl 0 (open_tm_wrt_tm ?b (a_Var_f x)) /\ cl 0 a_Type |- _ =>
             exact (body_cl_1_fst L b (fun x => cl 0 a_Type) H)
         end)
      | (match goal with
         | H : forall x, x \notin ?L -> cl 0 (open_tm_wrt_tm ?b (a_Var_f x)) /\ cl 0 (open_tm_wrt_tm ?C (a_Var_f x)) |- _ =>
             exact (body_cl_1_fst L b (fun x => cl 0 (open_tm_wrt_tm C (a_Var_f x))) H)
         end)
      | (match goal with
         | H : forall x, x \notin ?L -> cl 0 (open_tm_wrt_tm ?C (a_Var_f x)) /\ cl 0 (open_tm_wrt_tm ?b (a_Var_f x)) |- _ =>
             exact (body_cl_1_snd L b (fun x => cl 0 (open_tm_wrt_tm C (a_Var_f x))) H)
         end)
      | (match goal with
         | H : forall x, x \notin ?L -> cl 0 (open_tm_wrt_tm ?b (a_Var_f x)) /\ cl 0 (open_tm_wrt_tm ?C (a_box ?q0 (a_Var_f x))) |- _ =>
             exact (body_cl_1_fst L b (fun x => cl 0 (open_tm_wrt_tm C (a_box q0 (a_Var_f x)))) H)
         end)
      | (match goal with
         | H : forall x, x \notin ?L -> forall y, y \notin ?L2 -> cl 0 (open_tm_wrt_tm ?b (a_Var_f x)) /\ cl 0 (a_Pi ?qq ?AA ?BB) |- _ =>
             exact (body_cl_1_fst2 L b (fun x y => cl 0 (a_Pi qq AA BB)) H)
         end)
      ]
  end.

Ltac cl_open :=
  match goal with
  | |- cl 0 (open_tm_wrt_tm ?B ?b) =>
      let HB := fresh "HB" in
      first [
        (match goal with H : cl 1 B |- _ => pose proof H as HB end)
      | (match goal with H : forall x, x \notin ?L -> cl 0 (open_tm_wrt_tm B (a_Var_f x)) /\ cl 0 a_Type |- _ =>
             pose proof (body_cl_1_fst L B (fun x => cl 0 a_Type) H) as HB end)
      | (match goal with H : forall x, x \notin ?L -> cl 0 (open_tm_wrt_tm B (a_Var_f x)) /\ cl 0 (open_tm_wrt_tm ?C (a_Var_f x)) |- _ =>
             pose proof (body_cl_1_fst L B (fun x => cl 0 (open_tm_wrt_tm C (a_Var_f x))) H) as HB end)
      | (match goal with H : forall x, x \notin ?L -> cl 0 (open_tm_wrt_tm B (a_Var_f x)) /\ cl 0 (open_tm_wrt_tm ?C (a_box ?q0 (a_Var_f x))) |- _ =>
             pose proof (body_cl_1_fst L B (fun x => cl 0 (open_tm_wrt_tm C (a_box q0 (a_Var_f x)))) H) as HB end)
      | (match goal with H : forall x, x \notin ?L -> forall y, y \notin ?L2 -> cl 0 (open_tm_wrt_tm B (a_Var_f x)) /\ cl 0 (a_Pi ?qq ?AA ?BB) |- _ =>
             pose proof (body_cl_1_fst2 L B (fun x y => cl 0 (a_Pi qq AA BB)) H) as HB end)
      ];
      let Hb := fresh "Hb" in
      (match goal with H : cl 0 b |- _ => pose proof H as Hb end);
      exact (cl_open_fwd B 0 HB b Hb)
  end.

Ltac cl_split :=
  match goal with |- _ /\ _ => split end.

Ltac cl_destr :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac cl_unfold :=
  match goal with
  | H : cl ?k (a_Box ?q ?A) |- _ => simpl in H
  | H : cl ?k (a_Sum ?A1 ?A2) |- _ => simpl in H
  | H : cl ?k (a_Sigma ?q ?A ?B) |- _ => simpl in H
  | H : cl ?k (a_Pi ?q ?A ?B) |- _ => simpl in H
  end.

Ltac cl_proj :=
  first [
    match goal with H : cl 0 ?x /\ _ |- cl 0 ?x => exact (proj1 H) end
  | match goal with H : _ /\ cl 0 ?x |- cl 0 ?x => exact (proj2 H) end
  | match goal with H : cl 1 ?x /\ _ |- cl 1 ?x => exact (proj1 H) end
  | match goal with H : _ /\ cl 1 ?x |- cl 1 ?x => exact (proj2 H) end
  | match goal with H : cl 0 ?x |- cl 0 ?x => exact H end
  | match goal with H : cl 1 ?x |- cl 1 ?x => exact H end
  ].

Lemma typing_cl : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> cl 0 a /\ cl 0 A.
Proof.
  intros D0 G a A H. induction H; simpl.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: try cl_destr. all: try cl_unfold. all: try cl_split. all: try cl_proj. all: try cl_body. all: try cl_open. all: try assumption. all: try exact I.
  all: match goal with |- ?G => idtac "CL_REM:" G end.
Qed.

Ltac fv_done :=
  first [ assumption
        | match goal with
          | |- ?z \in Metatheory.union ?X ?Y =>
              first [ (apply union_iff; left; fv_done) | (apply union_iff; right; fv_done) ]
          end ].

Ltac fv_destr :=
  match goal with
  | H : ?z \in Metatheory.union ?X ?Y |- _ => apply union_iff in H; destruct H as [H|H]
  end.

Ltac fv_apply_at IH kk c :=
  match goal with
  | Hx : ?zz \in fv_tm_tm _ |- _ => apply (IH kk c) in Hx
  end.

Lemma fv_open_sup_gen : forall (u:tm) k c, fv_tm_tm u [<=] fv_tm_tm (open_tm_wrt_tm_rec k c u).
Proof.
  intros u. induction u as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n0 | y
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros k c z Hz; simpl in *.
  - repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb k c). all: try (fv_apply_at IHB k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: try (fv_apply_at IHB (S k) c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: try (fv_apply_at IHa (S k) c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb (S k) c). all: try (fv_apply_at IHB k c). all: try fv_done.
  - repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (exfalso; exact (proj1 (empty_iff z) Hz)).
  - repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb (S k) c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA1 k c). all: try (fv_apply_at IHA2 k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb1 k c). all: try (fv_apply_at IHb2 k c). all: try (fv_apply_at IHB k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: try (fv_apply_at IHB (S k) c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb k c). all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb (S k) c). all: try (fv_apply_at IHB k c). all: try fv_done.
Qed.

Lemma fv_open_sub_gen : forall (u:tm) k c z,
  z \in fv_tm_tm (open_tm_wrt_tm_rec k c u) -> z \in Metatheory.union (fv_tm_tm u) (fv_tm_tm c).
Proof.
  intros u. induction u as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n0 | y
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros k c z Hz; simpl in *.
  - exfalso; exact (proj1 (empty_iff z) Hz).
  - exfalso; exact (proj1 (empty_iff z) Hz).
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb k c). all: try (fv_apply_at IHB k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: try (fv_apply_at IHB (S k) c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: try (fv_apply_at IHa (S k) c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb (S k) c). all: try (fv_apply_at IHB k c). all: repeat fv_destr. all: try fv_done.
  - exfalso; exact (proj1 (empty_iff z) Hz).
  - destruct (lt_eq_lt_dec n0 k) as [[Hlt|Heq]|Hgt]; simpl in *;
      try (exfalso; exact (proj1 (empty_iff z) Hz));
      try fv_done.
  - fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb (S k) c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA1 k c). all: try (fv_apply_at IHA2 k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb1 k c). all: try (fv_apply_at IHb2 k c). all: try (fv_apply_at IHB k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHA k c). all: try (fv_apply_at IHB (S k) c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb k c). all: repeat fv_destr. all: try fv_done.
  - repeat fv_destr. all: try (fv_apply_at IHa k c). all: try (fv_apply_at IHb (S k) c). all: try (fv_apply_at IHB k c). all: repeat fv_destr. all: try fv_done.
Qed.

Lemma in_dom_cons : forall (z x:atom) (A:tm) (D0:D),
  z \in dom ((x,Tm A)::D0) <-> z = x \/ z \in dom D0.
Proof.
  intros. rewrite dom_cons. split; intros H.
  - apply union_iff in H. destruct H as [H|H].
    + left. apply singleton_iff in H. auto.
    + right; auto.
  - apply union_iff. destruct H as [->|H].
    + left. apply singleton_iff. reflexivity.
    + right; auto.
Qed.

Lemma in_dom_nil : forall (z:atom), z \in dom (nil:D) -> False.
Proof. intros z H. rewrite dom_nil in H. exact (proj1 (empty_iff z) H). Qed.

Lemma fv_body_dom : forall (L:atoms) (b:tm) (A:tm) (D0:D),
  (forall x:atom, x \notin L -> forall z, z \in fv_tm_tm (open_tm_wrt_tm b (a_Var_f x)) -> z \in dom (x ~ Tm A ++ D0)) ->
  forall z, z \in fv_tm_tm b -> z \in dom D0.
Proof.
  intros L b A D0 H z Hz.
  pick fresh x for (L \u fv_tm_tm b).
  assert (Hfresh : x \notin L \u fv_tm_tm b) by assumption.
  assert (Hxfv : x \notin fv_tm_tm b).
  { intro C. apply Hfresh. apply union_iff. right. exact C. }
  assert (HxL : x \notin L).
  { intro C. apply Hfresh. apply union_iff. left. exact C. }
  assert (Hzo : z \in fv_tm_tm (open_tm_wrt_tm b (a_Var_f x))).
  { apply (fv_open_sup_gen b 0 (a_Var_f x) z Hz). }
  pose proof (H x HxL z Hzo) as Hzd.
  destruct (proj1 (in_dom_cons z x A D0) Hzd) as [Heq | Hd].
  - subst. exfalso. apply Hxfv. exact Hz.
  - exact Hd.
Qed.

Ltac use_ih_dom :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?tt |- ?z \in dom ?D =>
      first [
        (match goal with
         | IH : (forall w, w \in fv_tm_tm tt -> w \in dom D) /\ _ |- _ => exact (proj1 IH z Hx)
         | IH : _ /\ (forall w, w \in fv_tm_tm tt -> w \in dom D) |- _ => exact (proj2 IH z Hx)
         end)
      | (match goal with
         | IH : forall x, x \notin ?L -> (forall w, w \in fv_tm_tm (open_tm_wrt_tm tt (a_Var_f x)) -> w \in dom (x ~ Tm ?A ++ D)) /\ _ |- _ =>
             exact (fv_body_dom L tt A D (fun x HxL => proj1 (IH x HxL)) z Hx)
         | IH : forall x, x \notin ?L -> _ /\ (forall w, w \in fv_tm_tm (open_tm_wrt_tm tt (a_Var_f x)) -> w \in dom (x ~ Tm ?A ++ D)) |- _ =>
             exact (fv_body_dom L tt A D (fun x HxL => proj2 (IH x HxL)) z Hx)
         end)
      ]
  end.

Ltac dom_weaken_add :=
  match goal with
  | Hx : ?z \in dom ?D |- ?z \in add ?x (dom D) =>
      exact (proj2 (add_iff (dom D) x z) (or_intror Hx))
  end.

Ltac dom_var_add :=
  match goal with
  | Hx : ?z \in singleton ?x |- ?z \in add ?x (dom ?D) =>
      apply singleton_iff in Hx;
      exact (proj2 (add_iff (dom D) x z) (or_introl Hx))
  end.

Ltac use_ih_dom_weaken_add :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?tt |- ?z \in add ?x (dom ?D) =>
      match goal with
      | IH : (forall w, w \in fv_tm_tm tt -> w \in dom D) /\ _ |- _ =>
          exact (proj2 (add_iff (dom D) x z) (or_intror (proj1 IH z Hx)))
      | IH : _ /\ (forall w, w \in fv_tm_tm tt -> w \in dom D) |- _ =>
          exact (proj2 (add_iff (dom D) x z) (or_intror (proj2 IH z Hx)))
      end
  end.

Ltac dom_weaken :=
  match goal with
  | Hx : ?z \in dom ?D |- ?z \in dom (?x ~ Tm ?A ++ D) =>
      apply (proj2 (in_dom_cons z x A D)); right; exact Hx
  end.

Ltac dom_var :=
  match goal with
  | Hx : ?z \in {{?x}} |- ?z \in dom (?x ~ Tm ?A ++ ?D) =>
      apply (proj2 (in_dom_cons z x A D)); left; apply singleton_iff in Hx; auto
  end.

Ltac use_ih_sum :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?A1 |- ?z \in dom ?D =>
      first [
        (match goal with
         | IH : (forall w, w \in fv_tm_tm (a_Sum A1 ?A2) -> w \in dom ?D2) |- _ =>
             exact (IH z (proj2 (union_iff (fv_tm_tm A1) (fv_tm_tm A2) z) (or_introl Hx)))
         end)
      | (match goal with
         | IH : (forall w, w \in fv_tm_tm (a_Sum ?A2 A1) -> w \in dom ?D2) |- _ =>
             exact (IH z (proj2 (union_iff (fv_tm_tm A2) (fv_tm_tm A1) z) (or_intror Hx)))
         end)
      ]
  end.

Lemma fv_body_dom2 : forall (L:atoms) (b:tm) (A:tm) (D0:D),
  (forall x:atom, x \notin L -> forall y:atom, y \notin L \u {{x}} ->
     forall z, z \in fv_tm_tm (open_tm_wrt_tm b (a_Var_f x)) -> z \in dom (x ~ Tm A ++ D0)) ->
  forall z, z \in fv_tm_tm b -> z \in dom D0.
Proof.
  intros L b A D0 H z Hz.
  pick fresh x for (L \u fv_tm_tm b).
  assert (Hfresh : x \notin L \u fv_tm_tm b) by assumption.
  assert (Hxfv : x \notin fv_tm_tm b).
  { intro C. apply Hfresh. apply union_iff. right. exact C. }
  assert (HxL : x \notin L).
  { intro C. apply Hfresh. apply union_iff. left. exact C. }
  pose proof (H x HxL) as Hxy.
  pick fresh y for (L \u {{x}}).
  assert (Hy : y \notin L \u {{x}}) by assumption.
  assert (Hzo : z \in fv_tm_tm (open_tm_wrt_tm b (a_Var_f x))).
  { apply (fv_open_sup_gen b 0 (a_Var_f x) z Hz). }
  pose proof (Hxy y Hy z Hzo) as Hzd.
  destruct (proj1 (in_dom_cons z x A D0) Hzd) as [Heq | Hd].
  - subst. exfalso. apply Hxfv. exact Hz.
  - exact Hd.
Qed.

Ltac use_ih_dom_binder2 :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?tt |- ?z \in dom ?D =>
      match goal with
      | IH : forall x, x \notin ?L -> forall y, y \notin ?L2 ->
               (forall w, w \in fv_tm_tm (open_tm_wrt_tm tt (a_Var_f x)) -> w \in dom (x ~ Tm ?A ++ D)) /\ _ |- _ =>
          exact (fv_body_dom2 L tt A D (fun x HxL y HyL => proj1 (IH x HxL y HyL)) z Hx)
      end
  end.

Ltac spread_solve :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?tt |- ?z \in dom ?D =>
      match goal with
      | IH : forall x, x \notin ?L -> forall y, y \notin ?L2 ->
               (forall w, w \in fv_tm_tm (open_tm_wrt_tm tt (a_Var_f x)) -> w \in dom (x ~ Tm ?A ++ D)) /\ _ |- _ =>
          eapply (fv_body_dom2 L tt A D);
          intros x HxL y HyL z0 Hzo;
          exact (proj1 (IH x HxL y HyL) z0 Hzo)
      end
  end.

Ltac spread2 :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?tt |- ?z \in dom ?D =>
      match goal with
      | IH : forall x, ?P -> forall y, ?Q -> ?R |- _ =>
          eapply (fv_body_dom2);
          intros x HxL y HyL z0 Hzo;
          exact (proj1 (IH x HxL y HyL) z0 Hzo)
      end
  end.

Ltac use_ih_dom2 :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?tt |- ?z \in dom ?D =>
      first [
        (match goal with
         | IH : (forall w, w \in fv_tm_tm tt -> w \in dom ?D2) /\ _ |- _ => exact (proj1 IH z Hx)
         | IH : _ /\ (forall w, w \in fv_tm_tm tt -> w \in dom ?D2) |- _ => exact (proj2 IH z Hx)
         | IH : (forall w, w \in fv_tm_tm tt -> w \in dom ?D2) |- _ => exact (IH z Hx)
         end)
      | (match goal with
         | IH : forall x, x \notin ?L -> (forall w, w \in fv_tm_tm (open_tm_wrt_tm tt (a_Var_f x)) -> w \in dom (x ~ Tm ?A ++ ?D2)) /\ _ |- _ =>
             exact (fv_body_dom L tt A D2 (fun x HxL => proj1 (IH x HxL)) z Hx)
         | IH : forall x, x \notin ?L -> _ /\ (forall w, w \in fv_tm_tm (open_tm_wrt_tm tt (a_Var_f x)) -> w \in dom (x ~ Tm ?A ++ ?D2)) |- _ =>
             exact (fv_body_dom L tt A D2 (fun x HxL => proj2 (IH x HxL)) z Hx)
         end)
      ]
  end.

Ltac use_ih_dom_weaken :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?tt |- ?z \in dom (?x ~ Tm ?A ++ ?D) =>
      match goal with
      | IH : (forall w, w \in fv_tm_tm tt -> w \in dom D) /\ _ |- _ =>
          exact (proj2 (in_dom_cons z x A D) (or_intror (proj1 IH z Hx)))
      | IH : _ /\ (forall w, w \in fv_tm_tm tt -> w \in dom D) |- _ =>
          exact (proj2 (in_dom_cons z x A D) (or_intror (proj2 IH z Hx)))
      end
  end.

Ltac use_ih_pi :=
  match goal with
  | Hx : ?z \in fv_tm_tm ?B |- ?z \in dom ?D =>
      match goal with
      | IH : _ /\ (forall w, w \in fv_tm_tm (a_Pi ?q ?A B) -> w \in dom D) |- _ =>
          exact (proj2 IH z (proj2 (union_iff (fv_tm_tm A) (fv_tm_tm B) z) (or_intror Hx)))
      | IH : (forall w, w \in fv_tm_tm (a_Pi ?q ?A B) -> w \in dom D) /\ _ |- _ =>
          exact (proj1 IH z (proj2 (union_iff (fv_tm_tm A) (fv_tm_tm B) z) (or_intror Hx)))
      end
  end.

Lemma typing_fv : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A ->
  (forall z, z \in fv_tm_tm a -> z \in dom D0) /\ (forall z, z \in fv_tm_tm A -> z \in dom D0).
Proof.
  intros D0 G a A H. induction H; simpl.
  all: try assumption.
  all: try (split; intros z Hz; repeat fv_destr).
  all: try use_ih_dom2.
  all: try dom_var_add.
  all: try dom_weaken_add.
  all: try use_ih_dom_weaken_add.
  all: try (exfalso; exact (proj1 (empty_iff z) Hz)).
  all: try (exfalso; apply (in_dom_nil z); assumption).
  all: try use_ih_pi.
  all: try (apply fv_open_sub_gen in Hz; repeat fv_destr).
  all: try use_ih_pi.
  all: try use_ih_dom.
  all: try dom_weaken_add.
  all: try use_ih_dom_weaken_add.
  all: try (exfalso; exact (proj1 (empty_iff z) Hz)).
  all: try use_ih_sum.
  all: try (intuition eauto).
  all: try (intuition auto).
  all: try use_ih_dom_binder2.
  all: try spread_solve.
  all: try spread2.
  all: try use_ih_sum.
  all: try use_ih_pi.
  all: try use_ih_dom2.
  all: try (match goal with
    | Hx : ?z \in fv_tm_tm ?bb |- ?z \in dom ?D =>
        eapply (fv_body_dom2); intros x HxL y HyL z0 Hzo;
        exact (proj1 (H2 x HxL y HyL) z0 Hzo)
    end).
  all: try (match goal with
    | Hx : ?z \in fv_tm_tm ?tt |- ?z \in dom ?D =>
        match goal with
        | IH : forall x, ?P -> forall y, ?Q -> ?R |- _ =>
            refine (fv_body_dom2 L tt _ D _ z Hx);
            intros x0 HxL y0 HyL z0 Hzo;
            exact (proj1 (IH x0 HxL y0 HyL) z0 Hzo)
        end
    end).
  all: match goal with |- ?G => idtac "TFV_REM:" G end.
Qed.

(* ---------- Gsubst / Dsubst algebra ---------- *)
Lemma Gsubst_nil : forall b x, Gsubst b x (nil:context) = nil.
Proof. reflexivity. Qed.
Lemma Gsubst_cons : forall b x (y:atom) (q:usage) (A:sort) (G:context),
  Gsubst b x ((y,(q,A))::G) = (y,(q, sort_subst b x A))::Gsubst b x G.
Proof. reflexivity. Qed.
Lemma Gsubst_app : forall b x (G1 G2:context), Gsubst b x (G1++G2) = Gsubst b x G1 ++ Gsubst b x G2.
Proof. intros. unfold Gsubst. apply map_app. Qed.
Lemma Dsubst_app : forall b x (D1 D2:D), Dsubst b x (D1++D2) = Dsubst b x D1 ++ Dsubst b x D2.
Proof. intros. unfold Dsubst. apply map_app. Qed.
Lemma Dsubst_nil : forall b x, Dsubst b x (nil:D) = nil.
Proof. reflexivity. Qed.

Lemma Gsubst_ctx_plus : forall b x (G1 G2:context),
  Gsubst b x (ctx_plus G1 G2) = ctx_plus (Gsubst b x G1) (Gsubst b x G2).
Proof.
  intros b x G1. induction G1 as [| [y [q A]] G1 IH]; intros G2.
  - destruct G2 as [|[z [q2 B]] G2]; reflexivity.
  - destruct G2 as [|[z [q2 B]] G2]; simpl.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma Gsubst_ctx_mul : forall b x q (G:context),
  Gsubst b x (ctx_mul q G) = ctx_mul q (Gsubst b x G).
Proof.
  intros b x q G. induction G as [| [y [q1 A]] G IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma Dsubst_cons : forall b x (y:atom) (A:sort) (D0:D),
  Dsubst b x ((y,A)::D0) = (y, sort_subst b x A) :: Dsubst b x D0.
Proof. reflexivity. Qed.

(* ---------- shape splitting ---------- *)
Lemma shape_split : forall (D0:D) (G:context), shapeDG D0 G ->
  forall (Dpre:D) (x:atom) (Ax:tm) (Dtail:D),
    D0 = Dpre ++ (x,Tm Ax) :: Dtail ->
    exists (Gpre:context) (q:usage) (Gtail:context),
      G = Gpre ++ (x,(q,Tm Ax)) :: Gtail /\ shapeDG Dpre Gpre /\ shapeDG Dtail Gtail.
Proof.
  intros D0 G Hsh. induction Hsh as [| x0 q0 A0 D0' G' Hsh' IH];
    intros Dpre x Ax Dtail Heq.
  - destruct Dpre; simpl in Heq; discriminate.
  - destruct Dpre as [| [p Ap] Dpre].
    + simpl in Heq. injection Heq as H1 H2 H3. subst x0. subst A0.
      exists nil, q0, G'. split; [reflexivity|]. split; [constructor|].
      subst D0'. assumption.
    + destruct Ap as [Ap]. simpl in Heq. injection Heq as H1 H2 H3. subst x0. subst A0.
      destruct (IH Dpre x Ax Dtail H3) as [Gpre [q [Gtail [HG [HS1 HS2]]]]].
      exists ((p,(q0,Tm Ap))::Gpre), q, Gtail. split.
      * rewrite HG. reflexivity.
      * split; [constructor; assumption | assumption].
Qed.

(* ---------- usage order helpers ---------- *)
Lemma ule_refl : forall a, a <= a.
Proof. intros. apply leb_le. apply qleb_refl. Qed.
Lemma ule_trans : forall a b c, a <= b -> b <= c -> a <= c.
Proof. intros a b c H1 H2. apply leb_le. apply (qleb_trans b a c); apply leb_le; assumption. Qed.
Lemma ule_add : forall a b c d, a <= b -> c <= d -> a + c <= b + d.
Proof.
  intros a b c d Hab Hcd.
  apply ule_trans with (b := b + c).
  - apply po_semiring1; assumption.
  - rewrite qplus_comm. rewrite (qplus_comm b d). apply po_semiring1; assumption.
Qed.
Lemma ule_mul_r : forall a b c, a <= b -> a * c <= b * c.
Proof. intros. apply po_semiring2; assumption. Qed.
Lemma ule_mul_l : forall a b c, a <= b -> c * a <= c * b.
Proof. intros. apply po_semiring3; assumption. Qed.

Lemma ctx_mul_1 : forall (G:context), ctx_mul 1 G = G.
Proof.
  intros G. induction G as [|[y [q A]] G IH]; simpl.
  - reflexivity.
  - rewrite qmul_1_l. rewrite IH. reflexivity.
Qed.
(* ---------- ctx_sub lemmas ---------- *)
Lemma ctx_sub_mul : forall (D0:D) (G1 G2:context), ctx_sub D0 G1 G2 ->
  forall q, ctx_sub D0 (ctx_mul q G1) (ctx_mul q G2).
Proof.
  intros D0 G1 G2 H. induction H; intros q; simpl.
  - constructor.
  - constructor.
    + apply ule_mul_l; assumption.
    + apply IHctx_sub.
    + assumption.
Qed.

Lemma ctx_sub_plus_mul : forall (D0:D) (G1 G2:context), ctx_sub D0 G1 G2 ->
  forall (H:context), shapeDG D0 H ->
  forall q1 q2, q1 <= q2 ->
  ctx_sub D0 (ctx_plus G1 (ctx_mul q1 H)) (ctx_plus G2 (ctx_mul q2 H)).
Proof.
  intros D0 G1 G2 Hsub. induction Hsub as [| D0' x a G1' q1' G2' q2' Hle Hsub' IH Hfresh];
    intros H Hsh q1 q2 Hq12.
  - destruct H as [|[y [qy Ay]] H]; simpl in Hsh.
    + simpl. constructor.
    + inversion Hsh.
  - destruct H as [|[y [qy Ay]] H]; simpl in Hsh.
    + inversion Hsh.
    + inversion Hsh as [| yy qq Ay' HH G'] ; subst.
      simpl. constructor.
      * apply ule_add; [assumption | apply ule_mul_r; assumption].
      * apply (IH H); assumption.
      * assumption.
Qed.

Lemma ctx_sub_decomp : forall (Dpre:D) (x:atom) (Ax:tm) (Dtail:D)
  (G1pre G1tail Gdpre Gdtail:context) (q1 q:usage),
  shapeDG Dpre G1pre -> shapeDG Dpre Gdpre ->
  shapeDG Dtail G1tail -> shapeDG Dtail Gdtail ->
  ctx_sub (Dpre ++ (x,Tm Ax) :: Dtail)
          (G1pre ++ (x,(q1,Tm Ax)) :: G1tail)
          (Gdpre ++ (x,(q,Tm Ax)) :: Gdtail) ->
  (q1 <= q) /\ ctx_sub Dpre G1pre Gdpre /\ ctx_sub Dtail G1tail Gdtail.
Proof.
  intros Dpre x Ax Dtail G1pre G1tail Gdpre Gdtail q1 q HS1 HS2 HS3 HS4 Hsub.
  remember (Dpre ++ (x,Tm Ax) :: Dtail) as D0 eqn:ED.
  remember (G1pre ++ (x,(q1,Tm Ax)) :: G1tail) as G1 eqn:EG1.
  remember (Gdpre ++ (x,(q,Tm Ax)) :: Gdtail) as Gd eqn:EGd.
  revert Dpre x Ax Dtail G1pre G1tail Gdpre Gdtail q1 q HS1 HS2 HS3 HS4 ED EG1 EGd.
  induction Hsub as [| Dc xc ac G1c q1c G2c q2c Hlec Hsubc IH Hfreshc];
    intros Dpre x Ax Dtail G1pre G1tail Gdpre Gdtail q1 q HS1 HS2 HS3 HS4 ED EG1 EGd.
  - destruct Dpre; simpl in ED; discriminate.
  - destruct Dpre as [|[p Ap] Dpre].
    + simpl in ED. inversion ED; subst.
      inversion HS1; subst. inversion HS2; subst.
      simpl in EG1. inversion EG1; subst.
      simpl in EGd. inversion EGd; subst.
      split; [exact Hlec|]. split; [constructor|exact Hsubc].
    + destruct Ap as [Ap]. simpl in ED. inversion ED; subst.
      inversion HS1 as [| y1 r1 A1 D1 Gs1 HS1']; subst.
      inversion HS2 as [| y2 r2 A2 D2 Gs2 HS2']; subst.
      simpl in EG1. inversion EG1; subst.
      simpl in EGd. inversion EGd; subst.
      assert (ED' : Dpre ++ (x,Tm Ax) :: Dtail = Dpre ++ (x,Tm Ax) :: Dtail) by reflexivity.
      assert (EG1' : Gs1 ++ (x,(q1,Tm Ax)) :: G1tail = Gs1 ++ (x,(q1,Tm Ax)) :: G1tail) by reflexivity.
      assert (EGd' : Gs2 ++ (x,(q,Tm Ax)) :: Gdtail = Gs2 ++ (x,(q,Tm Ax)) :: Gdtail) by reflexivity.
      destruct (IH Dpre x Ax Dtail Gs1 G1tail Gs2 Gdtail q1 q HS1' HS2' HS3 HS4
                  ED' EG1' EGd') as [Hq [Hs1 Hs2]].
      split; [exact Hq|]. split.
      * constructor; [exact Hlec | exact Hs1 | intro Hc; apply Hfreshc; rewrite dom_app; apply union_iff; left; exact Hc].
      * exact Hs2.
Qed.

Lemma ctx_plus_zero_one : forall (G1 G2:context),
  gnames G1 = gnames G2 -> gsorts G1 = gsorts G2 ->
  ctx_plus (ctx_mul 0 G1) (ctx_mul 1 G2) = G2.
Proof.
  intros G1. induction G1 as [|[y [q1 A1]] G1 IH]; intros G2 Hn Hs.
  - destruct G2 as [|[z [q2 A2]] G2]; simpl in Hn; [reflexivity|discriminate].
  - destruct G2 as [|[z [q2 A2]] G2].
    + simpl in Hn; discriminate.
    + simpl in Hn. simpl in Hs. injection Hn as Hn1 Hn2. injection Hs as Hs1 Hs2.
      subst z. subst A2.
      simpl. rewrite qmul_0_l. rewrite qmul_1_l. rewrite qplus_0_l.
      f_equal. apply (IH G2 Hn2 Hs2).
Qed.

(* ---------- environment well-formedness (types typable in their tails) ---------- *)
Definition env_wf (D0:D) : Prop :=
  forall (pre:D) (y:atom) (A:tm) (tail:D),
    D0 = pre ++ (y,Tm A) :: tail ->
    exists G', Typing tail G' A a_Type.

Lemma env_wf_nil : env_wf nil.
Proof.
  intros pre y A tail Heq. destruct pre; simpl in Heq; discriminate.
Qed.

Lemma env_wf_cons : forall (y:atom) (A:tm) (D0:D), env_wf D0 ->
  (exists G', Typing D0 G' A a_Type) -> env_wf ((y,Tm A)::D0).
Proof.
  intros y A D0 HW Hty pre z Az tail Heq.
  destruct pre as [| [p Ap] pre].
  - simpl in Heq. injection Heq as H1 H2 H3. subst z. subst Az. subst tail.
    exact Hty.
  - destruct Ap as [Ap]. simpl in Heq. injection Heq as H1 H2 H3. subst p. subst Ap.
    apply (HW pre z Az tail H3).
Qed.

Lemma typing_env_wf : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> env_wf D0.
Proof.
  intros D0 G a A H. induction H.
  - (* T_sub *) assumption.
  - (* T_type *) apply env_wf_nil.
  - (* T_var *) apply (env_wf_cons x A D5); [assumption|]. exists G; assumption.
  - (* T_weak *) apply (env_wf_cons x A D5); [assumption|]. exists G2; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply env_wf_nil.
  - apply env_wf_nil.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.


(* ---------- extra environment prefix (from T_weak peels) ---------- *)
Lemma in_dom_map_iff : forall (D0:D) (y:atom), y \in dom D0 <-> List.In y (List.map (fun p => fst p) D0).
Proof.
  intros D0. induction D0 as [|[x A] D0 IH]; intros y; simpl.
  - split; [intro H; exfalso; exact (proj1 (empty_iff y) H) | intro H; destruct H].
  - split; intros H.
    + apply add_iff in H. destruct H as [Heq|H].
      * left. exact Heq.
      * right. apply (proj1 (IH y)); assumption.
    + destruct H as [Heq|H].
      * apply add_iff. left. exact Heq.
      * apply add_iff. right. apply (proj2 (IH y)); assumption.
Qed.

Lemma in_dom_in_map : forall (D0:D) (y:atom),
  y \in dom D0 -> List.In y (List.map (fun p => fst p) D0).
Proof.
  intros D0. induction D0 as [|[x A] D0 IH]; intros y H; simpl in *.
  - exfalso. exact (proj1 (empty_iff y) H).
  - apply add_iff in H. destruct H as [Heq|H].
    + left. exact Heq.
    + right. apply IH. assumption.
Qed.

Lemma notin_dom_notin_map : forall (D0:D) (y:atom),
  y \notin dom D0 -> ~ List.In y (List.map (fun p => fst p) D0).
Proof.
  intros D0. induction D0 as [|[x A] D0 IH]; intros y Hnin Hin; simpl in Hin.
  - destruct Hin.
  - destruct Hin as [Heq|Hin].
    + subst y. apply Hnin. apply add_iff. left. reflexivity.
    + apply (IH y); [|exact Hin]. intro Hc. apply Hnin. apply add_iff. right. exact Hc.
Qed.

Definition De_ok (De:D) (D0:D) : Prop :=
  (forall y, y \in dom De -> y \notin dom D0) /\ List.NoDup (List.map (fun p => fst p) De).

Lemma De_ok_nil : forall (D0:D), De_ok nil D0.
Proof.
  intros. split.
  - intros y Hy. simpl in Hy. exfalso. exact (proj1 (empty_iff y) Hy).
  - simpl. constructor.
Qed.

Lemma De_ok_tail : forall (y:atom) (A:sort) (De:D) (D0:D), De_ok ((y,A)::De) D0 -> De_ok De D0.
Proof.
  intros y A De D0 [Hdis Hnd]. split.
  - intros z Hz. apply (Hdis z). apply add_iff. right. exact Hz.
  - simpl in Hnd. exact (proj2 (proj1 (NoDup_cons_iff y (List.map (fun p => fst p) De)) Hnd)).
Qed.

Lemma De_ok_cons : forall (y:atom) (A:sort) (De:D) (D0:D), De_ok De D0 ->
  y \notin dom De -> y \notin dom D0 -> De_ok ((y,A)::De) D0.
Proof.
  intros y A De D0 [Hdis Hnd] H1 H2. split.
  - intros z Hz. apply add_iff in Hz. destruct Hz as [Hz|Hz].
    + assert (Hzy : z = y) by exact (@Logic.eq_sym atom y z Hz).
      intro Hc. apply H2. rewrite Hzy in Hc. exact Hc.
    + apply Hdis; assumption.
  - simpl. apply NoDup_cons_iff. split.
    + exact (notin_dom_notin_map De y H1).
    + assumption.
Qed.

Lemma env_wf_tail : forall (y:atom) (A:tm) (D0:D), env_wf ((y,Tm A)::D0) -> env_wf D0.
Proof.
  intros y A D0 HW pre z Az tail Heq.
  apply (HW ((y,Tm A)::pre) z Az tail). simpl. rewrite Heq. reflexivity.
Qed.

Lemma env_wf_head : forall (y:atom) (A:tm) (De D0:D),
  env_wf ((y,Tm A) :: (De ++ D0)) -> exists G', Typing (De ++ D0) G' A a_Type.
Proof. intros. apply (H nil y A (De++D0)). reflexivity. Qed.

Lemma typing_add_zero_prefix : forall (De:D) (Ge:context) (D0:D) (G:context) (a B:tm),
  shapeDG De Ge -> De_ok De D0 -> env_wf (De ++ D0) -> Typing D0 G a B ->
  Typing (De ++ D0) (ctx_mul 0 Ge ++ G) a B.
Proof.
  intros De. induction De as [|[y A] De IH]; intros Ge D0 G a B Hsh Hok HW HT.
  - inversion Hsh; subst. simpl. exact HT.
  - destruct A as [A]. inversion Hsh as [| yy qq AA DD GG Hsh']; subst.
    destruct Hok as [Hdis Hnd].
    simpl. rewrite qmul_0_l.
    destruct (env_wf_head y A De D0 HW) as [G2 Hty2].
    apply (T_weak (De++D0) y A (ctx_mul 0 GG ++ G) a B G2).
    + (* freshness *)
      assert (HyD0 : y \notin dom D0).
      { intro Hc. apply (Hdis y); [apply add_iff; left; reflexivity | exact Hc]. }
      assert (HyDe : y \notin dom De).
      { intro Hc. exact ((proj1 (proj1 (NoDup_cons_iff y (List.map (fun p => fst p) De)) Hnd)) (in_dom_in_map De y Hc)). }
      intro Hc. rewrite dom_app in Hc. apply union_iff in Hc. destruct Hc as [Hc|Hc]; [exact (HyDe Hc)|exact (HyD0 Hc)].
    + apply (IH GG D0 G a B); [assumption | apply (De_ok_tail y (Tm A) De D0); split; assumption | apply (env_wf_tail y A (De++D0)); assumption | assumption].
    + exact Hty2.
Qed.

(* ---------- duplicate-free environments ---------- *)
Definition nodupD (D0:D) : Prop := List.NoDup (List.map (fun p => fst p) D0).

Lemma nodupD_nil : nodupD nil.
Proof. simpl. constructor. Qed.

Lemma nodupD_cons_inv : forall (y:atom) (A:sort) (D0:D), nodupD ((y,A)::D0) ->
  y \notin dom D0 /\ nodupD D0.
Proof.
  intros y A D0 H. simpl in H. apply NoDup_cons_iff in H. destruct H as [Hnin Hnd].
  split; [|exact Hnd].
  intro Hc. apply Hnin. exact (in_dom_in_map D0 y Hc).
Qed.

Lemma nodupD_cons : forall (y:atom) (A:sort) (D0:D), nodupD D0 ->
  y \notin dom D0 -> nodupD ((y,A)::D0).
Proof.
  intros y A D0 Hnd Hnin. simpl.
  apply (proj2 (NoDup_cons_iff y (List.map (fun p => fst p) D0))). split; [|exact Hnd].
  intro Hin. exact (notin_dom_notin_map D0 y Hnin Hin).
Qed.

Lemma nodupD_app_disj : forall (D1 D2:D) (y:atom), nodupD (D1++D2) ->
  y \in dom D1 -> y \notin dom D2.
Proof.
  intros D1. induction D1 as [|[x A] D1 IH]; intros D2 y Hnd Hy.
  - simpl in Hy. exfalso. exact (proj1 (empty_iff y) Hy).
  - simpl in Hnd. destruct (nodupD_cons_inv x A (D1++D2) Hnd) as [Hnotin Htail].
    simpl in Hy. apply add_iff in Hy. destruct Hy as [Heq|Hy].
    + intro Hc. apply Hnotin. rewrite Heq. rewrite dom_app. apply union_iff. right. exact Hc.
    + apply (IH D2 y Htail Hy).
Qed.

Lemma ctx_sub_refl_nodup : forall (D0:D) (G:context), shapeDG D0 G -> nodupD D0 -> ctx_sub D0 G G.
Proof.
  intros D0. induction D0 as [|[y A] D0 IH]; intros G Hsh Hnd.
  - inversion Hsh. constructor.
  - destruct A as [A]. inversion Hsh as [| y0 q0 A0 D0' G0 Hsh']; subst.
    destruct (nodupD_cons_inv y (Tm A) D0 Hnd) as [Hnin Htail].
    constructor.
    + apply ule_refl.
    + apply (IH G0 Hsh' Htail).
    + assumption.
Qed.

Lemma ctx_sub_mul_le : forall (D0:D) (H:context) (q1 q:usage),
  shapeDG D0 H -> nodupD D0 -> q1 <= q -> ctx_sub D0 (ctx_mul q1 H) (ctx_mul q H).
Proof.
  intros D0. induction D0 as [|[y A] D0 IH]; intros H q1 q Hsh Hnd Hle.
  - inversion Hsh. simpl. constructor.
  - destruct A as [A]. inversion Hsh as [| y0 q0 A0 D0' G0 Hsh']; subst.
    destruct (nodupD_cons_inv y (Tm A) D0 Hnd) as [Hnin Htail].
    simpl. constructor.
    + apply ule_mul_r; assumption.
    + apply (IH G0 q1 q Hsh' Htail Hle).
    + assumption.
Qed.

Lemma in_dom_Dsubst : forall (b:tm) (x:tmvar) (D0:D) (y:atom),
  y \in dom (Dsubst b x D0) <-> y \in dom D0.
Proof.
  intros b x D0 y.
  assert (Hmap : List.map (fun p => fst p) (Dsubst b x D0) = List.map (fun p => fst p) D0).
  { exact (dnames_Dsubst b x D0). }
  split; intro H.
  - apply (proj2 (in_dom_map_iff D0 y)). rewrite <- Hmap.
    apply (proj1 (in_dom_map_iff (Dsubst b x D0) y) H).
  - apply (proj2 (in_dom_map_iff (Dsubst b x D0) y)). rewrite Hmap.
    apply (proj1 (in_dom_map_iff D0 y) H).
Qed.

Lemma ctx_sub_Gsubst : forall (b:tm) (x:tmvar) (D0:D) (G1 G2:context),
  ctx_sub D0 G1 G2 -> ctx_sub (Dsubst b x D0) (Gsubst b x G1) (Gsubst b x G2).
Proof.
  intros b x D0 G1 G2 H.
  induction H as [| Dc xc ac G1c q1c G2c q2c Hle Hsub' IH Hfresh].
  - simpl. constructor.
  - simpl. constructor.
    + assumption.
    + assumption.
    + intro Hc. apply Hfresh. apply (proj1 (in_dom_Dsubst b x Dc xc)); exact Hc.
Qed.

Lemma ctx_sub_combine : forall (D1 D2:D) (G1 G1' G2 G2':context),
  nodupD (D1++D2) ->
  shapeDG D1 G1 -> shapeDG D1 G1' -> shapeDG D2 G2 -> shapeDG D2 G2' ->
  ctx_sub D1 G1 G1' -> ctx_sub D2 G2 G2' ->
  ctx_sub (D1++D2) (G1++G2) (G1'++G2').
Proof.
  intros D1. induction D1 as [|[y A] D1 IH]; intros D2 G1 G1' G2 G2' Hnd HS1 HS1' HS2 HS2' Hsub Hsub2.
  - inversion HS1. inversion HS1'. subst. simpl. exact Hsub2.
  - destruct A as [A].
    assert (HcI := nodupD_cons_inv y (Tm A) (D1++D2) Hnd). destruct HcI as [Hnin Hnd'].
    inversion HS1 as [| y1 q1 A1 D1a G1a HS1a]; subst.
    inversion HS1' as [| y1' q2 A1' D1a' G1a' HS1a']; subst.
    inversion Hsub as [| D0 y0 a0 G1c q1' G2c q2' Hle Hsub' Hfresh]; subst.
    simpl. constructor.
    + exact Hle.
    + apply (IH D2 G1a G1a' G2 G2' Hnd' HS1a HS1a' HS2 HS2' Hsub' Hsub2).
    + exact Hnin.
Qed.

(* ---------- substitution / opening commutation ---------- *)
Lemma subst_open_comm : forall (a:tm), lc_tm a ->
  forall (t:tm) (x:tmvar) (k:nat) (c:tm),
  subst_tm_tm a x (open_tm_wrt_tm_rec k c t) =
  open_tm_wrt_tm_rec k (subst_tm_tm a x c) (subst_tm_tm a x t).
Proof.
  intros a Hlc t. induction t; intros xv kv cv; simpl.
  all: try reflexivity.
  all: try (match goal with
            | |- context [lt_eq_lt_dec ?m ?kk] =>
                destruct (lt_eq_lt_dec m kk) as [[H1|H2]|H3]; simpl; reflexivity
            end).
  all: try (match goal with
            | |- context [eq_var ?y ?xx] =>
                destruct (eq_var y xx) as [Heq|Hneq]; simpl
            end).
  all: try (match goal with
            | H : lc_tm ?A, Heq : ?y = ?xx
              |- ?A = open_tm_wrt_tm_rec ?kk (subst_tm_tm ?A ?xx ?cc) ?A =>
                assert (Hclk : cl kk A) by (apply (cl_mono A 0 kk (Nat.le_0_l kk)); apply lc_cl; exact H);
                rewrite (cl_open_rec_eq A kk (subst_tm_tm A xx cc) Hclk); reflexivity
            end).
  all: try (f_equal;
            repeat match goal with
            | IH : forall (x0:tmvar) (k0:nat) (c0:tm),
                     subst_tm_tm ?A x0 (open_tm_wrt_tm_rec k0 c0 ?u) =
                     open_tm_wrt_tm_rec k0 (subst_tm_tm ?A x0 c0) (subst_tm_tm ?A x0 ?u)
              |- subst_tm_tm ?A ?xx (open_tm_wrt_tm_rec ?kk ?cc ?u) =
                 open_tm_wrt_tm_rec ?kk (subst_tm_tm ?A ?xx ?cc) (subst_tm_tm ?A ?xx ?u) =>
                exact (IH xx kk cc)
            end).
  all: match goal with |- ?G => idtac "SOC_REM:" G end.
Qed.

Lemma subst_fresh : forall (u:tm) (b:tm) (v:tmvar),
  v \notin fv_tm_tm u -> subst_tm_tm b v u = u.
Proof.
  intros u. induction u as
  [ | | x1 IH1 x2 IH2 x3 IH3
    | q A IHA B IHB
    | q A IHA x0 IHx
    | x1 IH1 x2 IH2
    | q A IHA
    | x1 IH1 x2 IH2 x3 IH3
    | | n | y
    | q x0 IHx
    | x1 IH1 x2 IH2
    | A1 IHA1 A2 IHA2
    | x0 IHx
    | x0 IHx
    | q x1 IH1 x2 IH2 x3 IH3 x4 IH4
    | q A IHA B IHB
    | x1 IH1 x2 IH2
    | x1 IH1 x2 IH2 x3 IH3 ]; intros b v Hfv; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IH1; fsetdec | apply IH2; fsetdec | apply IH3; fsetdec].
  - f_equal; [apply IHA; fsetdec | apply IHB; fsetdec].
  - f_equal; [apply IHA; fsetdec | apply IHx; fsetdec].
  - f_equal; [apply IH1; fsetdec | apply IH2; fsetdec].
  - f_equal; apply IHA; fsetdec.
  - f_equal; [apply IH1; fsetdec | apply IH2; fsetdec | apply IH3; fsetdec].
  - reflexivity.
  - reflexivity.
  - destruct (eq_var y v) as [Heq|Hneq].
    + exfalso. apply Hfv. rewrite Heq. apply singleton_iff. reflexivity.
    + reflexivity.
  - f_equal; apply IHx; fsetdec.
  - f_equal; [apply IH1; fsetdec | apply IH2; fsetdec].
  - f_equal; [apply IHA1; fsetdec | apply IHA2; fsetdec].
  - f_equal; apply IHx; fsetdec.
  - f_equal; apply IHx; fsetdec.
  - f_equal; [apply IH1; fsetdec | apply IH2; fsetdec | apply IH3; fsetdec | apply IH4; fsetdec].
  - f_equal; [apply IHA; fsetdec | apply IHB; fsetdec].
  - f_equal; [apply IH1; fsetdec | apply IH2; fsetdec].
  - f_equal; [apply IH1; fsetdec | apply IH2; fsetdec | apply IH3; fsetdec].
Qed.

Lemma subst_open_var : forall (b:tm) (x:tmvar) (y:tmvar) (body:tm), lc_tm b -> y <> x ->
  subst_tm_tm b x (open_tm_wrt_tm body (a_Var_f y)) =
  open_tm_wrt_tm (subst_tm_tm b x body) (a_Var_f y).
Proof.
  intros b x y body Hlc Hneq.
  rewrite (subst_open_comm b Hlc body x 0 (a_Var_f y)). simpl.
  destruct (eq_var y x) as [Heq|Hneq']; [|reflexivity].
  exfalso. exact (Hneq Heq).
Qed.

Lemma subst_open_self : forall (b:tm) (x:tmvar) (body:tm), lc_tm b ->
  x \notin fv_tm_tm body ->
  subst_tm_tm b x (open_tm_wrt_tm body (a_Var_f x)) = open_tm_wrt_tm body b.
Proof.
  intros b x body Hlc Hfv.
  rewrite (subst_open_comm b Hlc body x 0 (a_Var_f x)).
  rewrite (subst_fresh body b x Hfv).
  assert (Hvv : subst_tm_tm b x (a_Var_f x) = b).
  { simpl. destruct (eq_var x x) as [Heq|Hneq]; [reflexivity|].
    exfalso. exact (Hneq (@Logic.eq_refl atom x)). }
  rewrite Hvv. reflexivity.
Qed.



(* ---------- progress helpers ---------- *)
Lemma ctx_sub_nil_l : forall (G1 G2:context), ctx_sub (nil:D) G1 G2 -> G1 = nil /\ G2 = nil.
Proof.
  intros G1 G2 H. inversion H as [| D x a G1' q1 G2' q2 Hle Hsub Hfresh]; auto.
Qed.

Lemma typing_lc : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> lc_tm a.
Proof.
  intros. apply cl_lc. apply (proj1 (typing_cl D0 G a A H)).
Qed.

Lemma typing_lc_ty : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> lc_tm A.
Proof.
  intros. apply cl_lc. apply (proj2 (typing_cl D0 G a A H)).
Qed.

Ltac kill_val H :=
  inversion H; subst; try match goal with Ht : ty _ |- _ => inversion Ht end.

Ltac contra_pi :=
  match goal with
  | Hb : Beta ?Lt (a_Pi ?q ?A ?B) |- _ =>
      exfalso;
      assert (HvL : value Lt) by (apply val_ty; constructor);
      pose proof (Beta_consistent Lt (a_Pi q A B) Hb HvL (val_ty (a_Pi q A B) (ty_Pi q A B))) as Hc;
      inversion Hc
  end.

Lemma val_pi_inv_gen : forall (q:usage) (A B:tm) (D0:D) (G:context) (v T:tm),
  Typing D0 G v T -> D0 = nil -> value v -> Beta T (a_Pi q A B) ->
  exists q0 A0 a0, v = a_Lam q0 A0 a0.
Proof.
  intros q A B D0 G v T H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax G Hnotin H1 IH1
  | D5 x Ax G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A2 A1 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros ED Hval Hbeta.
  - (* T_sub *)
    exact (IH1 ED Hval Hbeta).
  - exfalso. assert (HvL : value a_Type) by (apply val_ty; constructor).
    pose proof (Beta_consistent a_Type (a_Pi q A B) Hbeta HvL (val_ty (a_Pi q A B) (ty_Pi q A B))) as Hc.
    inversion Hc.
  - simpl in ED. discriminate.
  - simpl in ED. discriminate.
  - contra_pi.
  - eexists qq, A1, a. reflexivity.
  - exfalso; kill_val Hval.
  - (* T_conv *)
    exact (IH1 ED Hval (B_Trans A1 (a_Pi q A B) B0 Hbconv Hbeta)).
  - contra_pi.
  - contra_pi.
  - exfalso; kill_val Hval.
  - contra_pi.
  - contra_pi.
  - exfalso; kill_val Hval.
  - contra_pi.
  - contra_pi.
  - contra_pi.
  - exfalso; kill_val Hval.
  - contra_pi.
  - contra_pi.
  - exfalso; kill_val Hval.
Qed.

Lemma val_pi_inv : forall (v:tm) (T:tm) (q:usage) (A B:tm),
  value v -> Typing nil nil v T -> Beta T (a_Pi q A B) ->
  exists q0 A0 a0, v = a_Lam q0 A0 a0.
Proof.
  intros v T q A B Hval H Hbeta.
  exact (val_pi_inv_gen q A B nil nil v T H (@Logic.eq_refl D nil) Hval Hbeta).
Qed.

Ltac contra_shape Tgt :=
  match goal with
  | Hb : Beta ?Lt Tgt |- _ =>
      exfalso;
      assert (HvL : value Lt) by (apply val_ty; constructor);
      assert (HvT : value Tgt) by (apply val_ty; constructor);
      pose proof (Beta_consistent Lt Tgt Hb HvL HvT) as Hc;
      inversion Hc
  end.

Lemma val_box_inv_gen : forall (qb:usage) (Ab:tm) (D0:D) (G:context) (v T:tm),
  Typing D0 G v T -> D0 = nil -> value v -> Beta T (a_Box qb Ab) ->
  exists q0 a0, v = a_box q0 a0.
Proof.
  intros qb Ab D0 G v T H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax G Hnotin H1 IH1
  | D5 x Ax G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A2 A1 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros ED Hval Hbeta.
  - exact (IH1 ED Hval Hbeta).
  - contra_shape (a_Box qb Ab).
  - simpl in ED. discriminate.
  - simpl in ED. discriminate.
  - contra_shape (a_Box qb Ab).
  - contra_shape (a_Box qb Ab).
  - exfalso; kill_val Hval.
  - exact (IH1 ED Hval (B_Trans A1 (a_Box qb Ab) B0 Hbconv Hbeta)).
  - contra_shape (a_Box qb Ab).
  - contra_shape (a_Box qb Ab).
  - exfalso; kill_val Hval.
  - contra_shape (a_Box qb Ab).
  - eexists qq, a. reflexivity.
  - exfalso; kill_val Hval.
  - contra_shape (a_Box qb Ab).
  - contra_shape (a_Box qb Ab).
  - contra_shape (a_Box qb Ab).
  - exfalso; kill_val Hval.
  - contra_shape (a_Box qb Ab).
  - contra_shape (a_Box qb Ab).
  - exfalso; kill_val Hval.
Qed.

Lemma val_sum_inv_gen : forall (As1 As2:tm) (D0:D) (G:context) (v T:tm),
  Typing D0 G v T -> D0 = nil -> value v -> Beta T (a_Sum As1 As2) ->
  exists a0, v = a_Inj1 a0 \/ v = a_Inj2 a0.
Proof.
  intros As1 As2 D0 G v T H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax G Hnotin H1 IH1
  | D5 x Ax G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A2 A1 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros ED Hval Hbeta.
  - exact (IH1 ED Hval Hbeta).
  - contra_shape (a_Sum As1 As2).
  - simpl in ED. discriminate.
  - simpl in ED. discriminate.
  - contra_shape (a_Sum As1 As2).
  - contra_shape (a_Sum As1 As2).
  - exfalso; kill_val Hval.
  - exact (IH1 ED Hval (B_Trans A1 (a_Sum As1 As2) B0 Hbconv Hbeta)).
  - contra_shape (a_Sum As1 As2).
  - contra_shape (a_Sum As1 As2).
  - exfalso; kill_val Hval.
  - contra_shape (a_Sum As1 As2).
  - contra_shape (a_Sum As1 As2).
  - exfalso; kill_val Hval.
  - contra_shape (a_Sum As1 As2).
  - exists a; left; reflexivity.
  - exists a; right; reflexivity.
  - exfalso; kill_val Hval.
  - contra_shape (a_Sum As1 As2).
  - contra_shape (a_Sum As1 As2).
  - exfalso; kill_val Hval.
Qed.

Lemma val_sum_inv : forall (v T:tm) (As1 As2:tm),
  value v -> Typing nil nil v T -> Beta T (a_Sum As1 As2) ->
  exists a0, v = a_Inj1 a0 \/ v = a_Inj2 a0.
Proof.
  intros v T As1 As2 Hval H Hbeta.
  exact (val_sum_inv_gen As1 As2 nil nil v T H (@Logic.eq_refl D nil) Hval Hbeta).
Qed.

Lemma val_sigma_inv_gen : forall (qs:usage) (As Bs:tm) (D0:D) (G:context) (v T:tm),
  Typing D0 G v T -> D0 = nil -> value v -> Beta T (a_Sigma qs As Bs) ->
  exists (q0:usage) (a0 b0:tm), v = a_Tensor a0 b0.
Proof.
  intros qs As Bs D0 G v T H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax G Hnotin H1 IH1
  | D5 x Ax G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A2 A1 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros ED Hval Hbeta.
  - exact (IH1 ED Hval Hbeta).
  - contra_shape (a_Sigma qs As Bs).
  - simpl in ED. discriminate.
  - simpl in ED. discriminate.
  - contra_shape (a_Sigma qs As Bs).
  - contra_shape (a_Sigma qs As Bs).
  - exfalso; kill_val Hval.
  - exact (IH1 ED Hval (B_Trans A1 (a_Sigma qs As Bs) B0 Hbconv Hbeta)).
  - contra_shape (a_Sigma qs As Bs).
  - contra_shape (a_Sigma qs As Bs).
  - exfalso; kill_val Hval.
  - contra_shape (a_Sigma qs As Bs).
  - contra_shape (a_Sigma qs As Bs).
  - exfalso; kill_val Hval.
  - contra_shape (a_Sigma qs As Bs).
  - contra_shape (a_Sigma qs As Bs).
  - contra_shape (a_Sigma qs As Bs).
  - exfalso; kill_val Hval.
  - contra_shape (a_Sigma qs As Bs).
  - exists qq, a, b; reflexivity.
  - exfalso; kill_val Hval.
Qed.

Lemma val_sigma_inv : forall (v T:tm) (qs:usage) (As Bs:tm),
  Typing nil nil v T -> value v -> Beta T (a_Sigma qs As Bs) ->
  exists (q0:usage) (a0 b0:tm), v = a_Tensor a0 b0.
Proof.
  intros v T qs As Bs H Hval Hbeta.
  exact (val_sigma_inv_gen qs As Bs nil nil v T H (@Logic.eq_refl D nil) Hval Hbeta).
Qed.

Lemma val_unit_inv_gen : forall (D0:D) (G:context) (v T:tm),
  Typing D0 G v T -> D0 = nil -> value v -> Beta T a_TyUnit ->
  v = a_TmUnit.
Proof.
  intros D0 G v T H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax G Hnotin H1 IH1
  | D5 x Ax G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A2 A1 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros ED Hval Hbeta.
  - exact (IH1 ED Hval Hbeta).
  - contra_shape a_TyUnit.
  - simpl in ED. discriminate.
  - simpl in ED. discriminate.
  - contra_shape a_TyUnit.
  - contra_shape a_TyUnit.
  - exfalso; kill_val Hval.
  - exact (IH1 ED Hval (B_Trans A1 a_TyUnit B0 Hbconv Hbeta)).
  - reflexivity.
  - contra_shape a_TyUnit.
  - exfalso; kill_val Hval.
  - contra_shape a_TyUnit.
  - contra_shape a_TyUnit.
  - exfalso; kill_val Hval.
  - contra_shape a_TyUnit.
  - contra_shape a_TyUnit.
  - contra_shape a_TyUnit.
  - exfalso; kill_val Hval.
  - contra_shape a_TyUnit.
  - contra_shape a_TyUnit.
  - exfalso; kill_val Hval.
Qed.

Lemma val_unit_inv : forall (v T:tm),
  Typing nil nil v T -> value v -> Beta T a_TyUnit ->
  v = a_TmUnit.
Proof.
  intros v T H Hval Hbeta.
  exact (val_unit_inv_gen nil nil v T H (@Logic.eq_refl D nil) Hval Hbeta).
Qed.

(* ---------- lc of open terms and lambda annotations ---------- *)

Lemma lc_open_all : forall (B:tm) (y:tmvar),
  lc_tm (open_tm_wrt_tm B (a_Var_f y)) ->
  forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x)).
Proof.
  intros B y H x.
  apply cl_lc.
  assert (Hcl : cl 0 (open_tm_wrt_tm B (a_Var_f y))) by (apply lc_cl; exact H).
  pose proof (cl_open_bwd B 0 y Hcl) as Hc1.
  apply (cl_open_fwd B 0 Hc1 (a_Var_f x)).
  exact I.
Qed.

Lemma lc_lam_from_body_ty : forall (q r:usage) (A B:tm) (L:vars) (D0:D) (G0:context),
  lc_tm A ->
  (forall y, y \notin L -> Typing ((y ~ Tm A) ++ D0) ((y ~ (r, Tm A)) ++ G0)
      (open_tm_wrt_tm B (a_Var_f y)) a_Type) ->
  lc_tm (a_Lam q A B).
Proof.
  intros q r A B L D0 G0 HA Hty.
  apply lc_a_Lam; [exact HA |].
  intro x.
  pick fresh y for L.
  assert (Hy : y \notin L) by assumption.
  apply (lc_open_all B y).
  exact (@typing_lc _ _ _ _ (Hty y Hy)).
Qed.

Lemma lc_lam_ann : forall (q:usage) (A a:tm), lc_tm (a_Lam q A a) -> lc_tm A.
Proof. intros q A a H. inversion H. assumption. Qed.

Lemma lc_box_arg : forall (q:usage) (A:tm), lc_tm (a_Box q A) -> lc_tm A.
Proof. intros q A H. inversion H. assumption. Qed.

Lemma lc_box_body : forall (q:usage) (a:tm), lc_tm (a_box q a) -> lc_tm a.
Proof. intros q a H. inversion H. assumption. Qed.

Lemma lc_inj1_arg : forall (a:tm), lc_tm (a_Inj1 a) -> lc_tm a.
Proof. intros a H. inversion H. assumption. Qed.

Lemma lc_inj2_arg : forall (a:tm), lc_tm (a_Inj2 a) -> lc_tm a.
Proof. intros a H. inversion H. assumption. Qed.

Lemma lc_tensor_fst : forall (a b:tm), lc_tm (a_Tensor a b) -> lc_tm a.
Proof. intros a b H. inversion H. assumption. Qed.

Lemma lc_tensor_snd : forall (a b:tm), lc_tm (a_Tensor a b) -> lc_tm b.
Proof. intros a b H. inversion H. assumption. Qed.

Lemma progress_gen : forall (D0:D) (G:context) (a A:tm),
  Typing D0 G a A -> D0 = nil -> value a \/ exists a', Step a a'.
Proof.
  intros D0 G a A H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax G Hnotin H1 IH1
  | D5 x Ax G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A2 A1 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros ED.
  - (* T_sub *) exact (IH1 ED).
  - (* T_type *) left. apply val_ty. constructor.
  - (* T_var *) exfalso. simpl in ED. discriminate.
  - (* T_weak *) exfalso. simpl in ED. discriminate.
  - (* T_pi *) left. apply val_ty. constructor.
  - (* T_lam *) left. apply val_lam.
  - (* T_app *)
    destruct (IH1 ED) as [Hva | [a' Hstep]].
    + right.
      destruct (val_pi_inv_gen qq A1 B1 D5 G1 a (a_Pi qq A1 B1) H1 ED Hva
                  (B_Refl (a_Pi qq A1 B1) ((@typing_lc_ty _ _ _ _ H1)))) as [q0 [A0 [a0 Heq]]].
      exists (open_tm_wrt_tm a0 b).
      rewrite Heq.
      assert (Hla : lc_tm (a_Lam q0 A0 a0)).
      { pose proof (@typing_lc _ _ _ _ H1) as Hlc. rewrite Heq in Hlc. exact Hlc. }
      apply S_Beta.
      * apply (lc_lam_ann q0 A0 a0 Hla).
      * exact Hla.
      * exact (@typing_lc _ _ _ _ H2).
    + right.
      exists (a_App a' b).
      apply S_AppCong.
      * exact (@typing_lc _ _ _ _ H2).
      * exact Hstep.
  - (* T_conv *) exact (IH1 ED).
  - (* T_unit *) left. apply val_unit.
  - (* T_Unit *) left. apply val_ty. constructor.
  - (* T_UnitE *)
    assert (HBlam : lc_tm (a_Lam r a_TyUnit B0)).
    { apply (lc_lam_from_body_ty r r a_TyUnit B0 L D5 G3); [apply lc_a_TyUnit | exact Hfun]. }
    destruct (IH1 ED) as [Hva | [a' Hstep]].
    + right.
      pose proof (val_unit_inv_gen D5 G1 a a_TyUnit H1 ED Hva
                    (B_Refl a_TyUnit ((@typing_lc_ty _ _ _ _ H1)))) as Hinv.
      exists b. rewrite Hinv.
      apply S_UnitBeta.
      * exact HBlam.
      * exact (@typing_lc _ _ _ _ H2).
    + right.
      exists (a_letunitB a' b (a_Lam r a_TyUnit B0)).
      apply S_UnitCong.
      * exact (@typing_lc _ _ _ _ H2).
      * exact HBlam.
      * exact Hstep.
  - (* T_Box *) left. apply val_ty. constructor.
  - (* T_box *) left. apply val_box.
  - (* T_letbox *)
    assert (HBlam : lc_tm (a_Lam r (a_Box qq A1) B1)).
    { apply (lc_lam_from_body_ty r r (a_Box qq A1) B1 L D5 G3);
        [exact ((@typing_lc_ty _ _ _ _ H1)) | exact Hfun3]. }
    assert (Hob : forall x, lc_tm (open_tm_wrt_tm b (a_Var_f x))).
    { pick fresh x0 for L.
      assert (Hx0 : x0 \notin L) by assumption.
      apply (lc_open_all b x0).
      exact (@typing_lc _ _ _ _ (Hfun2 x0 Hx0)). }
    assert (Hwhole : lc_tm (a_LetBoxB a b (a_Lam r (a_Box qq A1) B1))).
    { apply lc_a_LetBoxB.
      - exact (@typing_lc _ _ _ _ H1).
      - exact Hob.
      - exact HBlam. }
    destruct (IH1 ED) as [Hva | [a' Hstep]].
    + right.
      destruct (val_box_inv_gen qq A1 D5 G1 a (a_Box qq A1) H1 ED Hva
                  (B_Refl (a_Box qq A1) ((@typing_lc_ty _ _ _ _ H1)))) as [q0 [a0 Heq]].
      exists (open_tm_wrt_tm b a0).
      rewrite Heq.
      assert (Hla : lc_tm (a_box q0 a0)).
      { pose proof (@typing_lc _ _ _ _ H1) as Hlc. rewrite Heq in Hlc. exact Hlc. }
      assert (Hwhole' : lc_tm (a_LetBoxB (a_box q0 a0) b (a_Lam r (a_Box qq A1) B1))).
      { rewrite Heq in Hwhole. exact Hwhole. }
      apply S_BoxBeta.
      * exact Hwhole'.
      * exact HBlam.
      * apply (lc_box_body q0 a0 Hla).
    + right.
      exists (a_LetBoxB a' b (a_Lam r (a_Box qq A1) B1)).
      apply S_BoxCong.
      * exact Hwhole.
      * exact HBlam.
      * exact Hstep.
  - (* T_sum *) left. apply val_ty. constructor.
  - (* T_inj1 *) left. apply val_inj1.
  - (* T_inj2 *) left. apply val_inj2.
  - (* T_case *)
    assert (HBlam : lc_tm (a_Lam r (a_Sum A1 A2) B0)).
    { apply (lc_lam_from_body_ty r r (a_Sum A1 A2) B0 L D5 G3);
        [exact ((@typing_lc_ty _ _ _ _ H1)) | exact Hfun]. }
    destruct (IH1 ED) as [Hva | [a' Hstep]].
    + right.
      destruct (val_sum_inv_gen A1 A2 D5 G1 a (a_Sum A1 A2) H1 ED Hva
                  (B_Refl (a_Sum A1 A2) ((@typing_lc_ty _ _ _ _ H1)))) as [a0 [Heq | Heq]].
      * exists (a_App b1 a0). rewrite Heq.
        assert (Hla : lc_tm (a_Inj1 a0)).
        { pose proof (@typing_lc _ _ _ _ H1) as Hlc. rewrite Heq in Hlc. exact Hlc. }
        apply S_Case1Beta.
        -- exact (@typing_lc _ _ _ _ H4).
        -- exact HBlam.
        -- exact (@typing_lc _ _ _ _ H3).
        -- apply (lc_inj1_arg a0 Hla).
      * exists (a_App b2 a0). rewrite Heq.
        assert (Hla : lc_tm (a_Inj2 a0)).
        { pose proof (@typing_lc _ _ _ _ H1) as Hlc. rewrite Heq in Hlc. exact Hlc. }
        apply S_Case2Beta.
        -- exact (@typing_lc _ _ _ _ H3).
        -- exact HBlam.
        -- exact (@typing_lc _ _ _ _ H4).
        -- apply (lc_inj2_arg a0 Hla).
    + right.
      exists (a_Case qq a' b1 b2 (a_Lam r (a_Sum A1 A2) B0)).
      apply S_CaseCong.
      * exact (@typing_lc _ _ _ _ H3).
      * exact (@typing_lc _ _ _ _ H4).
      * exact HBlam.
      * exact Hstep.
  - (* T_Sigma *) left. apply val_ty. constructor.
  - (* T_Tensor *) left. apply val_tensor.
  - (* T_Spread *)
    assert (Hob : forall x, lc_tm (open_tm_wrt_tm b (a_Var_f x))).
    { pick fresh x0 for L.
      assert (Hx0 : x0 \notin L) by assumption.
      pose proof (Hfun2 x0 Hx0) as Hxy.
      pick fresh y0 for (L \u {{x0}}).
      assert (Hy0 : y0 \notin L \u {{x0}}) by assumption.
      apply (lc_open_all b x0).
      exact (@typing_lc _ _ _ _ (Hxy y0 Hy0)). }
    assert (HBlam : lc_tm (a_Lam r A1 B1)).
    { apply (lc_lam_from_body_ty r r A1 B1 L D5 G3);
        [exact ((@typing_lc_ty _ _ _ _ H1)) | exact Hfun3]. }
    assert (Hwhole : lc_tm (a_Spread a b (a_Lam r A1 B1))).
    { apply lc_a_Spread.
      - exact (@typing_lc _ _ _ _ H1).
      - exact Hob.
      - exact HBlam. }
    destruct (IH1 ED) as [Hva | [a' Hstep]].
    + right.
      assert (Hbeta : Beta A1 (a_Sigma qq A2 A3)).
      { rewrite Heq. apply B_Refl. pose proof ((@typing_lc_ty _ _ _ _ H1)) as Hc. rewrite Heq in Hc. exact Hc. }
      destruct (val_sigma_inv_gen qq A2 A3 D5 G1 a A1 H1 ED Hva Hbeta)
        as [q0 [a0 [a1 Heq2]]].
      exists (a_App (open_tm_wrt_tm b a0) a1).
      rewrite Heq2.
      assert (Hla : lc_tm (a_Tensor a0 a1)).
      { pose proof (@typing_lc _ _ _ _ H1) as Hlc. rewrite Heq2 in Hlc. exact Hlc. }
      assert (Hwhole' : lc_tm (a_Spread (a_Tensor a0 a1) b (a_Lam r A1 B1))).
      { rewrite Heq2 in Hwhole. exact Hwhole. }
      apply S_SpreadBeta.
      * exact Hwhole'.
      * exact HBlam.
      * apply (lc_tensor_fst a0 a1 Hla).
      * apply (lc_tensor_snd a0 a1 Hla).
    + right.
      exists (a_Spread a' b (a_Lam r A1 B1)).
      apply S_SpreadCong.
      * exact Hwhole.
      * exact HBlam.
      * exact Hstep.
Qed.

(* ---------- list/context splitting helpers for substitution ---------- *)

Lemma app_split_eq : forall (A:Type) (l1 l2 r1 r2:list A),
  length l1 = length r1 -> l1 ++ l2 = r1 ++ r2 -> l1 = r1 /\ l2 = r2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 r1 r2 Hlen Heq.
  - destruct r1 as [|b r1]; simpl in *; [auto|discriminate].
  - destruct r1 as [|b r1]; simpl in Hlen; [discriminate|].
    simpl in Hlen. injection Hlen as Hlen. simpl in Heq. injection Heq as Hab Htail.
    subst b. destruct (IH l2 r1 r2 Hlen Htail) as [E1 E2]. subst. auto.
Qed.

Lemma app_split_eq_ctx : forall (l1 l2 r1 r2:context),
  length l1 = length r1 -> l1 ++ l2 = r1 ++ r2 -> l1 = r1 /\ l2 = r2.
Proof.
  intros l1 l2 r1 r2 Hlen Heq.
  exact (app_split_eq (atom * (usage * sort)) l1 l2 r1 r2 Hlen Heq).
Qed.

Lemma split_eq_of_length : forall (P1 T1 P2 T2:context) (x:atom) (q1 q2:usage) (Ax:tm),
  length P1 = length P2 ->
  P1 ++ (x,(q1,Tm Ax)) :: T1 = P2 ++ (x,(q2,Tm Ax)) :: T2 ->
  P1 = P2 /\ q1 = q2 /\ T1 = T2.
Proof.
  intros P1 T1 P2 T2 x q1 q2 Ax Hlen Heq.
  destruct (app_split_eq_ctx P1 ((x,(q1,Tm Ax))::T1) P2 ((x,(q2,Tm Ax))::T2) Hlen Heq) as [HP Hrest].
  subst P1. inversion Hrest. subst. auto.
Qed.

Lemma nodup_gnames_shape : forall (D0:D) (G:context),
  shapeDG D0 G -> nodupD D0 -> NoDup (gnames G).
Proof.
  intros D0 G Hsh Hnd. pose proof (@sh_names D0 G Hsh) as Hn.
  rewrite <- Hn. exact Hnd.
Qed.

(* ---------- more context algebra for substitution ---------- *)

Lemma length_ctx_mul : forall (q:usage) (G:context), length (ctx_mul q G) = length G.
Proof. intros. apply length_map. Qed.

Lemma ctx_mul_split_form : forall (q0:usage) (Gpre Gtail:context) (x:atom) (q:usage) (Ax:tm),
  ctx_mul q0 (Gpre ++ (x,(q,Tm Ax)) :: Gtail)
  = ctx_mul q0 Gpre ++ (x,(q0*q,Tm Ax)) :: ctx_mul q0 Gtail.
Proof.
  intros. rewrite ctx_mul_app. rewrite ctx_mul_cons. reflexivity.
Qed.

Lemma ctx_plus_split_form : forall (G1pre G1tail G2pre G2tail:context)
  (x:atom) (q1 q2:usage) (Ax:tm),
  length G1pre = length G2pre ->
  ctx_plus (G1pre ++ (x,(q1,Tm Ax)) :: G1tail)
           (G2pre ++ (x,(q2,Tm Ax)) :: G2tail)
  = ctx_plus G1pre G2pre ++ (x,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail.
Proof.
  intros. rewrite (ctx_plus_app G1pre ((x,(q1,Tm Ax))::G1tail)
                        G2pre ((x,(q2,Tm Ax))::G2tail) H).
  rewrite ctx_plus_cons. reflexivity.
Qed.

Lemma ctx_plus_mul_split_form : forall (G1pre G1tail G2pre G2tail:context)
  (q0:usage) (x:atom) (q1 q2:usage) (Ax:tm),
  length G1pre = length G2pre ->
  ctx_plus (ctx_mul q0 (G1pre ++ (x,(q1,Tm Ax)) :: G1tail))
           (G2pre ++ (x,(q2,Tm Ax)) :: G2tail)
  = ctx_plus (ctx_mul q0 G1pre) G2pre
      ++ (x,(q0*q1+q2,Tm Ax)) :: ctx_plus (ctx_mul q0 G1tail) G2tail.
Proof.
  intros. rewrite ctx_mul_split_form.
  assert (Hlen : length (ctx_mul q0 G1pre) = length G2pre).
  { rewrite length_ctx_mul. exact H. }
  rewrite (ctx_plus_app (ctx_mul q0 G1pre) ((x,(q0*q1,Tm Ax))::ctx_mul q0 G1tail)
                        G2pre ((x,(q2,Tm Ax))::G2tail) Hlen).
  rewrite ctx_plus_cons. reflexivity.
Qed.

Lemma length_ctx_plus_shape : forall (D0:D) (G1 G2:context),
  shapeDG D0 G1 -> shapeDG D0 G2 -> length (ctx_plus G1 G2) = length G1.
Proof.
  intros D0 G1 G2 H1 H2. revert G2 H2.
  induction H1 as [| x q A D0' G1' H1' IH]; intros G2 H2.
  - destruct G2; reflexivity.
  - inversion H2 as [| y q2 A2 D2 G2' H2']; subst.
    simpl. f_equal. apply (IH G2' H2').
Qed.

Lemma length_ctx_plus_shape_r : forall (D0:D) (G1 G2:context),
  shapeDG D0 G1 -> shapeDG D0 G2 -> length (ctx_plus G1 G2) = length G2.
Proof.
  intros D0 G1 G2 H1 H2.
  rewrite (length_ctx_plus_shape D0 G1 G2 H1 H2).
  exact (csh_length G1 G2 (sh_sym D0 G1 G2 H1 H2)).
Qed.

Lemma ctx_mul_add : forall (q1 q2:usage) (G:context),
  ctx_plus (ctx_mul q1 G) (ctx_mul q2 G) = ctx_mul (q1+q2) G.
Proof.
  intros q1 q2 G. induction G as [|[x [q A]] G IH]; simpl.
  - reflexivity.
  - rewrite distr_l. rewrite IH. reflexivity.
Qed.

Lemma ctx_plus_assoc_shape : forall (D0:D) (G1 G2 G3:context),
  shapeDG D0 G1 -> shapeDG D0 G2 -> shapeDG D0 G3 ->
  ctx_plus (ctx_plus G1 G2) G3 = ctx_plus G1 (ctx_plus G2 G3).
Proof.
  intros D0 G1 G2 G3 H1 H2 H3.
  revert D0 G2 G3 H1 H2 H3.
  induction G1 as [|[x [q1 A1]] G1 IH]; intros D0 G2 G3 H1 H2 H3.
  - destruct D0 as [| [p Ap] D0].
    + destruct G2 as [|[p2 [q2 A2]] G2]; [|inversion H2].
      destruct G3 as [|[p3 [q3 A3]] G3]; [|inversion H3].
      reflexivity.
    + inversion H1.
  - inversion H1 as [| y q A D1 G1' H1']; subst.
    inversion H2 as [| y2 q2 A2 D2 G2' H2']; subst.
    inversion H3 as [| y3 q3 A3 D3 G3' H3']; subst.
    simpl. rewrite (IH D1 G2' G3' H1' H2' H3'). rewrite qplus_assoc. reflexivity.
Qed.

Lemma ctx_plus_comm_shape2 : forall (D0:D) (G1 G2:context),
  shapeDG D0 G1 -> shapeDG D0 G2 -> ctx_plus G1 G2 = ctx_plus G2 G1.
Proof. intros. apply ctx_plus_comm_shape. apply (sh_sym D0 G1 G2 H H0). Qed.

Lemma qplus4 : forall a b c d:usage, (a+b)+(c+d) = (a+c)+(b+d).
Proof.
  intros a b c d.
  rewrite <- (qplus_assoc a b (c+d)).
  rewrite (qplus_assoc b c d).
  rewrite (qplus_comm b c).
  rewrite <- (qplus_assoc c b d).
  rewrite <- (qplus_assoc a c (b+d)).
  reflexivity.
Qed.

(* tail rearrangement used when combining contexts in binary rules *)
Lemma tail_combine : forall (Dtail:D) (G1tail G2tail Gt:context) (q1 q2:usage),
  shapeDG Dtail G1tail -> shapeDG Dtail G2tail -> shapeDG Dtail Gt ->
  ctx_plus (ctx_plus G1tail (ctx_mul q1 Gt)) (ctx_plus G2tail (ctx_mul q2 Gt))
  = ctx_plus (ctx_plus G1tail G2tail) (ctx_mul (q1+q2) Gt).
Proof.
  intros Dtail G1tail G2tail Gt q1 q2 H1 H2 HG.
  revert G1tail G2tail Gt q1 q2 H1 H2 HG.
  induction Dtail as [|[x A] Dtail IH].
  - intros G1 G2 Gt q1 q2 H1 H2 HG.
    inversion H1. inversion H2. inversion HG. reflexivity.
  - destruct A as [A]. intros G1 G2 Gt q1 q2 H1 H2 HG.
    inversion H1 as [| y q A1 D1 G1' H1']; subst.
    inversion H2 as [| y2 q2' A2 D2 G2' H2']; subst.
    inversion HG as [| yg qg Ag Dg Gt' HG']; subst.
    simpl. rewrite (IH G1' G2' Gt' q1 q2 H1' H2' HG').
    rewrite distr_l. rewrite qplus4. reflexivity.
Qed.

Lemma self_notin_union : forall (x:atom) (A B:atoms),
  x \notin A \u B -> x \notin A /\ x \notin B.
Proof.
  intros x A B H. split; intro C.
  - apply H. apply union_iff. left. exact C.
  - apply H. apply union_iff. right. exact C.
Qed.

Lemma self_notin_add : forall (x y:atom) (A:atoms),
  x \notin add y A -> x <> y /\ x \notin A.
Proof.
  intros x y A H. split.
  - intro C. apply H. apply add_iff. left. exact (@Logic.eq_sym atom x y C).
  - intro C. apply H. apply add_iff. right. exact C.
Qed.

Lemma self_notin_singleton : forall (x y:atom),
  x \notin singleton y -> x <> y.
Proof.
  intros x y H C. apply H. apply singleton_iff. exact (@Logic.eq_sym atom x y C).
Qed.

Lemma dnames_app : forall (D1 D2:D), dnames (D1++D2) = dnames D1 ++ dnames D2.
Proof. intros. unfold dnames. apply List.map_app. Qed.

Lemma nodupD_Dsubst : forall (sb:tm) (xv:tmvar) (D0:D),
  nodupD (Dsubst sb xv D0) <-> nodupD D0.
Proof.
  intros. change (NoDup (dnames (Dsubst sb xv D0)) <-> NoDup (dnames D0)).
  rewrite dnames_Dsubst. reflexivity.
Qed.

Lemma nodupD_app_l : forall (D1 D2:D), nodupD (D1++D2) -> nodupD D1.
Proof.
  intros D1. induction D1 as [|[y A] D1 IH]; intros D2 H.
  - apply nodupD_nil.
  - destruct A as [A]. apply nodupD_cons.
    + apply (IH D2). exact (proj2 (nodupD_cons_inv y (Tm A) (D1++D2) H)).
    + intro C. apply (proj1 (nodupD_cons_inv y (Tm A) (D1++D2) H)).
      rewrite dom_app. apply union_iff. left. exact C.
Qed.

Lemma nodupD_app_r : forall (D1 D2:D), nodupD (D1++D2) -> nodupD D2.
Proof.
  intros D1. induction D1 as [|[y A] D1 IH]; intros D2 H.
  - exact H.
  - destruct A as [A]. apply (IH D2).
    exact (proj2 (nodupD_cons_inv y (Tm A) (D1++D2) H)).
Qed.


(* context assembly lemmas for the substitution proof *)
Lemma hctx_plus : forall (Dpre Dtail:D) (G1pre G1tail G2pre G2tail Gt Gpre Gtail:context)
  (xv:atom) (q1 q2 qu:usage) (sb:tm),
  shapeDG Dpre G1pre -> shapeDG Dpre G2pre ->
  shapeDG Dtail G1tail -> shapeDG Dtail G2tail -> shapeDG Dtail Gt ->
  Gpre = ctx_plus G1pre G2pre -> Gtail = ctx_plus G1tail G2tail -> qu = q1 + q2 ->
  ctx_plus (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
           (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
  = Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail xv q1 q2 qu sb
         H1 H2 H3 H4 H5 HGp HGt Hqu.
  subst Gpre. subst Gtail. subst qu.
  assert (Hlen : length (Gsubst sb xv G1pre) = length (Gsubst sb xv G2pre)).
  { rewrite length_Gsubst. rewrite length_Gsubst.
    exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre H1 H2)). }
  rewrite (ctx_plus_app (Gsubst sb xv G1pre) (ctx_plus G1tail (ctx_mul q1 Gt))
                        (Gsubst sb xv G2pre) (ctx_plus G2tail (ctx_mul q2 Gt)) Hlen).
  rewrite <- Gsubst_ctx_plus.
  rewrite (tail_combine Dtail G1tail G2tail Gt q1 q2 H3 H4 H5).
  reflexivity.
Qed.

Lemma hctx_mul : forall (Gsp Gst Gt Gpre Gtail:context) (xv:atom) (qg qq qu:usage) (sb:tm),
  Gpre = ctx_mul qq Gsp -> Gtail = ctx_mul qq Gst -> qu = qq*qg ->
  ctx_mul qq (Gsubst sb xv Gsp ++ ctx_plus Gst (ctx_mul qg Gt))
  = Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros. subst Gpre. subst Gtail. subst qu.
  rewrite ctx_mul_app.
  rewrite ctx_mul_ctx_plus.
  rewrite ctx_mul_ctx_mul.
  rewrite <- Gsubst_ctx_mul.
  reflexivity.
Qed.

Lemma hctx_plus_mul : forall (Dpre Dtail:D) (G1pre G1tail G2pre G2tail Gt Gpre Gtail:context)
  (xv:atom) (q1 q2 qq qu:usage) (sb:tm),
  shapeDG Dpre G1pre -> shapeDG Dpre G2pre ->
  shapeDG Dtail G1tail -> shapeDG Dtail G2tail -> shapeDG Dtail Gt ->
  Gpre = ctx_plus (ctx_mul qq G1pre) G2pre ->
  Gtail = ctx_plus (ctx_mul qq G1tail) G2tail -> qu = qq*q1 + q2 ->
  ctx_plus (ctx_mul qq (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt)))
           (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
  = Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail xv q1 q2 qq qu sb
         H1 H2 H3 H4 H5 HGp HGt Hqu.
  subst Gpre. subst Gtail. subst qu.
  rewrite ctx_mul_app.
  rewrite ctx_mul_ctx_plus.
  rewrite ctx_mul_ctx_mul.
  assert (Hlen : length (ctx_mul qq (Gsubst sb xv G1pre)) = length (Gsubst sb xv G2pre)).
  { rewrite length_ctx_mul. rewrite length_Gsubst. rewrite length_Gsubst.
    exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre H1 H2)). }
  rewrite (ctx_plus_app (ctx_mul qq (Gsubst sb xv G1pre))
                        (ctx_plus (ctx_mul qq G1tail) (ctx_mul (qq*q1) Gt))
                        (Gsubst sb xv G2pre)
                        (ctx_plus G2tail (ctx_mul q2 Gt)) Hlen).
  rewrite <- Gsubst_ctx_mul.
  rewrite <- Gsubst_ctx_plus.
  rewrite (tail_combine Dtail (ctx_mul qq G1tail) G2tail Gt (qq*q1) q2
             (shapeDG_mul Dtail G1tail qq H3) H4 H5).
  reflexivity.
Qed.

Lemma ctx_plus_zero : forall (D0:D) (G1 G2:context),
  shapeDG D0 G1 -> shapeDG D0 G2 -> ctx_plus G1 (ctx_mul 0 G2) = G1.
Proof.
  intros D0 G1 G2 H1 H2. revert G2 H2.
  induction H1 as [| x q A D0' G1' H1' IH]; intros G2 H2.
  - destruct G2; reflexivity.
  - inversion H2 as [| y q2 A2 D2 G2' H2']; subst.
    simpl. rewrite qmul_0_l. rewrite qplus_comm. rewrite qplus_0_l.
    f_equal. apply (IH G2' H2').
Qed.

Lemma hctx_plus_mul_r : forall (Dpre Dtail:D) (G1pre G1tail G2pre G2tail Gt Gpre Gtail:context)
  (xv:atom) (q1 q2 qq qu:usage) (sb:tm),
  shapeDG Dpre G1pre -> shapeDG Dpre G2pre ->
  shapeDG Dtail G1tail -> shapeDG Dtail G2tail -> shapeDG Dtail Gt ->
  Gpre = ctx_plus G1pre (ctx_mul qq G2pre) ->
  Gtail = ctx_plus G1tail (ctx_mul qq G2tail) -> qu = q1 + qq*q2 ->
  ctx_plus (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
           (ctx_mul qq (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt)))
  = Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail xv q1 q2 qq qu sb
         H1 H2 H3 H4 H5 HGp HGt Hqu.
  subst Gpre. subst Gtail. subst qu.
  rewrite ctx_mul_app.
  rewrite ctx_mul_ctx_plus.
  rewrite ctx_mul_ctx_mul.
  assert (Hlen : length (Gsubst sb xv G1pre) = length (ctx_mul qq (Gsubst sb xv G2pre))).
  { rewrite length_ctx_mul. rewrite length_Gsubst. rewrite length_Gsubst.
    exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre H1 H2)). }
  rewrite (ctx_plus_app (Gsubst sb xv G1pre) (ctx_plus G1tail (ctx_mul q1 Gt))
                        (ctx_mul qq (Gsubst sb xv G2pre))
                        (ctx_plus (ctx_mul qq G2tail) (ctx_mul (qq*q2) Gt)) Hlen).
  rewrite <- Gsubst_ctx_mul.
  rewrite <- Gsubst_ctx_plus.
  rewrite (tail_combine Dtail G1tail (ctx_mul qq G2tail) Gt q1 (qq*q2)
             H3 (shapeDG_mul Dtail G2tail qq H4) H5).
  reflexivity.
Qed.

Lemma ctx_plus_mul_split_form_r : forall (G1pre G1tail G2pre G2tail:context)
  (qq:usage) (x:atom) (q1 q2:usage) (Ax:tm),
  length G1pre = length G2pre ->
  ctx_plus (G1pre ++ (x,(q1,Tm Ax)) :: G1tail)
           (ctx_mul qq (G2pre ++ (x,(q2,Tm Ax)) :: G2tail))
  = ctx_plus G1pre (ctx_mul qq G2pre)
      ++ (x,(q1+qq*q2,Tm Ax)) :: ctx_plus G1tail (ctx_mul qq G2tail).
Proof.
  intros. rewrite ctx_mul_split_form.
  apply (ctx_plus_split_form G1pre G1tail (ctx_mul qq G2pre) (ctx_mul qq G2tail)
           x q1 (qq*q2) Ax).
  rewrite length_ctx_mul. exact H.
Qed.

Lemma nodupD_app : forall (D1 D2:D),
  nodupD D1 -> nodupD D2 -> (forall y, y \in dom D1 -> y \notin dom D2) ->
  nodupD (D1++D2).
Proof.
  intros D1. induction D1 as [|[y A] D1 IH]; intros D2 H1 H2 Hdis.
  - exact H2.
  - destruct A as [A]. apply nodupD_cons.
    + apply (IH D2 (proj2 (nodupD_cons_inv y (Tm A) D1 H1)) H2).
      intros z Hz. apply (Hdis z). apply (proj2 (in_dom_cons z y A D1) (or_intror Hz)).
    + intro C. apply (Hdis y).
      * apply (proj2 (in_dom_cons y y A D1) (or_introl (@Logic.eq_refl atom y))).
      * rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
        -- exfalso. exact ((proj1 (nodupD_cons_inv y (Tm A) D1 H1)) C).
        -- exact C.
Qed.

Lemma close_cl_eq : forall (t:tm) (k:nat) (y:tmvar),
  cl k t -> y \notin fv_tm_tm t -> close_tm_wrt_tm_rec k y t = t.
Proof.
  intros t. induction t as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n | x
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros k y Hc Hfv; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct Hc as [Ha [Hb HB]]. f_equal.
    + apply (IHa k y Ha). intro C. apply Hfv. fsetdec.
    + apply (IHb k y Hb). intro C. apply Hfv. fsetdec.
    + apply (IHB k y HB). intro C. apply Hfv. fsetdec.
  - destruct Hc as [HA HB]. f_equal.
    + apply (IHA k y HA). intro C. apply Hfv. fsetdec.
    + apply (IHB (S k) y HB). intro C. apply Hfv. fsetdec.
  - destruct Hc as [HA Ha]. f_equal.
    + apply (IHA k y HA). intro C. apply Hfv. fsetdec.
    + apply (IHa (S k) y Ha). intro C. apply Hfv. fsetdec.
  - destruct Hc as [Ha Hb]. f_equal.
    + apply (IHa k y Ha). intro C. apply Hfv. fsetdec.
    + apply (IHb k y Hb). intro C. apply Hfv. fsetdec.
  - f_equal. apply (IHA k y Hc). intro C. apply Hfv. fsetdec.
  - destruct Hc as [Ha [Hb HB]]. f_equal.
    + apply (IHa k y Ha). intro C. apply Hfv. fsetdec.
    + apply (IHb (S k) y Hb). intro C. apply Hfv. fsetdec.
    + apply (IHB k y HB). intro C. apply Hfv. fsetdec.
  - reflexivity.
  - destruct (lt_ge_dec n k) as [Hlt|Hge]; [reflexivity|].
    exfalso. lia.
  - destruct (eq_var y x) as [Hyx|Hneq]; [|reflexivity].
    exfalso. apply Hfv. apply singleton_iff. exact (@Logic.eq_sym atom y x Hyx).
  - f_equal. apply (IHa k y Hc). intro C. apply Hfv. fsetdec.
  - destruct Hc as [Ha Hb]. f_equal.
    + apply (IHa k y Ha). intro C. apply Hfv. fsetdec.
    + apply (IHb (S k) y Hb). intro C. apply Hfv. fsetdec.
  - destruct Hc as [H1 H2]. f_equal.
    + apply (IHA1 k y H1). intro C. apply Hfv. fsetdec.
    + apply (IHA2 k y H2). intro C. apply Hfv. fsetdec.
  - f_equal. apply (IHa k y Hc). intro C. apply Hfv. fsetdec.
  - f_equal. apply (IHa k y Hc). intro C. apply Hfv. fsetdec.
  - destruct Hc as [Ha [Hb1 [Hb2 HB]]]. f_equal.
    + apply (IHa k y Ha). intro C. apply Hfv. fsetdec.
    + apply (IHb1 k y Hb1). intro C. apply Hfv. fsetdec.
    + apply (IHb2 k y Hb2). intro C. apply Hfv. fsetdec.
    + apply (IHB k y HB). intro C. apply Hfv. fsetdec.
  - destruct Hc as [HA HB]. f_equal.
    + apply (IHA k y HA). intro C. apply Hfv. fsetdec.
    + apply (IHB (S k) y HB). intro C. apply Hfv. fsetdec.
  - destruct Hc as [Ha Hb]. f_equal.
    + apply (IHa k y Ha). intro C. apply Hfv. fsetdec.
    + apply (IHb k y Hb). intro C. apply Hfv. fsetdec.
  - destruct Hc as [Ha [Hb HB]]. f_equal.
    + apply (IHa k y Ha). intro C. apply Hfv. fsetdec.
    + apply (IHb (S k) y Hb). intro C. apply Hfv. fsetdec.
    + apply (IHB k y HB). intro C. apply Hfv. fsetdec.
Qed.

Lemma subst_var_self : forall (sb:tm) (xv:tmvar),
  subst_tm_tm sb xv (a_Var_f xv) = sb.
Proof.
  intros.
  change (match (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X xv xv) with
          | left _ => sb | right _ => a_Var_f xv end = sb).
  rewrite (@eq_dec_refl tmvar EqDec_eq_of_X xv). simpl. reflexivity.
Qed.

Lemma subst_var_neq : forall (sb:tm) (xv z:tmvar), z <> xv ->
  subst_tm_tm sb xv (a_Var_f z) = a_Var_f z.
Proof.
  intros sb xv z H. apply subst_fresh. simpl. intro C.
  apply H. apply singleton_iff in C. exact C.
Qed.

Lemma close_var_eq : forall (y z:tmvar) (n:nat), y = z ->
  close_tm_wrt_tm_rec n y (a_Var_f z) = a_Var_b n.
Proof.
  intros y z n Hyz. subst z.
  change (match (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X y y) with
          | left _ => a_Var_b n | right _ => a_Var_f y end = a_Var_b n).
  rewrite (@eq_dec_refl tmvar EqDec_eq_of_X y). simpl. reflexivity.
Qed.

Lemma close_var_neq : forall (y z:tmvar) (n:nat), y <> z ->
  close_tm_wrt_tm_rec n y (a_Var_f z) = a_Var_f z.
Proof.
  intros y z n Hneq.
  change (match (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X y z) with
          | left _ => a_Var_b n | right _ => a_Var_f z end = a_Var_f z).
  destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X y z) as [Heq|Hneq'];
    [exfalso; exact (Hneq Heq)|reflexivity].
Qed.

Lemma subst_close_rec_comm : forall (sb:tm) (xv y:tmvar) (n:nat) (t:tm),
  lc_tm sb -> xv <> y -> y \notin fv_tm_tm sb ->
  subst_tm_tm sb xv (close_tm_wrt_tm_rec n y t)
  = close_tm_wrt_tm_rec n y (subst_tm_tm sb xv t).
Proof.
  intros sb xv y n t. revert n. induction t as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | m | z
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros n Hlc Hxy Hfvy; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply (IHa n Hlc Hxy Hfvy).
    + apply (IHb n Hlc Hxy Hfvy).
    + apply (IHB n Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHA n Hlc Hxy Hfvy).
    + apply (IHB (S n) Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHA n Hlc Hxy Hfvy).
    + apply (IHa (S n) Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHa n Hlc Hxy Hfvy).
    + apply (IHb n Hlc Hxy Hfvy).
  - f_equal. apply (IHA n Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHa n Hlc Hxy Hfvy).
    + apply (IHb (S n) Hlc Hxy Hfvy).
    + apply (IHB n Hlc Hxy Hfvy).
  - reflexivity.
  - destruct (lt_ge_dec m n) as [Hlt|Hge]; reflexivity.
  - destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X y z) as [Hyz|Hnyz].
    + (* y = z *)
      assert (Hnzx : z <> xv).
      { intro C. apply Hxy. exact (Logic.eq_trans (@Logic.eq_sym atom z xv C) (@Logic.eq_sym atom y z Hyz)). }
      assert (Hneqdec : (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X z xv) = right Hnzx).
      { destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X z xv) as [Heq|Hneq'];
          [exfalso; exact (Hnzx Heq)| f_equal; apply proof_irrelevance]. }
      rewrite Hneqdec. simpl.
      rewrite Hyz. rewrite (@eq_dec_refl tmvar EqDec_eq_of_X z). simpl. reflexivity.
    + (* y <> z *)
      destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X z xv) as [Hzx|Hnzx].
      * assert (Hynxv : y <> xv).
        { intro C. apply Hnyz. exact (Logic.eq_trans C (@Logic.eq_sym atom z xv Hzx)). }
        rewrite Hzx. rewrite (subst_var_self sb xv).
        assert (Hcln : cl n sb) by (apply (cl_mono sb 0 n (Nat.le_0_l n)); apply lc_cl; exact Hlc).
        rewrite (close_cl_eq sb n y Hcln Hfvy). reflexivity.
      * rewrite (subst_var_neq sb xv z Hnzx).
        rewrite (close_var_neq y z n Hnyz). reflexivity.
  - f_equal. apply (IHa n Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHa n Hlc Hxy Hfvy).
    + apply (IHb (S n) Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHA1 n Hlc Hxy Hfvy).
    + apply (IHA2 n Hlc Hxy Hfvy).
  - f_equal. apply (IHa n Hlc Hxy Hfvy).
  - f_equal. apply (IHa n Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHa n Hlc Hxy Hfvy).
    + apply (IHb1 n Hlc Hxy Hfvy).
    + apply (IHb2 n Hlc Hxy Hfvy).
    + apply (IHB n Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHA n Hlc Hxy Hfvy).
    + apply (IHB (S n) Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHa n Hlc Hxy Hfvy).
    + apply (IHb n Hlc Hxy Hfvy).
  - f_equal.
    + apply (IHa n Hlc Hxy Hfvy).
    + apply (IHb (S n) Hlc Hxy Hfvy).
    + apply (IHB n Hlc Hxy Hfvy).
Qed.

Lemma subst_tensor_vars : forall (sb:tm) (xv x y:tmvar), x <> xv -> y <> xv ->
  subst_tm_tm sb xv (a_Tensor (a_Var_f x) (a_Var_f y))
  = a_Tensor (a_Var_f x) (a_Var_f y).
Proof.
  intros sb xv x y Hx Hy.
  change (a_Tensor (subst_tm_tm sb xv (a_Var_f x)) (subst_tm_tm sb xv (a_Var_f y))
          = a_Tensor (a_Var_f x) (a_Var_f y)).
  rewrite (subst_var_neq sb xv x Hx). rewrite (subst_var_neq sb xv y Hy). reflexivity.
Qed.

(* ===== inlined from Subst.v ===== *)
Lemma typing_subst_gen :
 forall (Dpre:D) (xv:tmvar) (Ax:tm) (Dtail:D) (Gpre Gtail:context)
        (qu:usage) (t:tm) (Ty:tm) (Gt:context) (sb:tm),
 Typing (Dpre ++ (xv,Tm Ax) :: Dtail) (Gpre ++ (xv,(qu,Tm Ax)) :: Gtail) t Ty ->
 shapeDG Dpre Gpre -> shapeDG Dtail Gtail ->
 nodupD (Dpre ++ (xv,Tm Ax) :: Dtail) ->
 xv \notin fv_tm_tm Ax -> lc_tm sb ->
 shapeDG Dtail Gt ->
 Typing Dtail Gt sb Ax ->
 Typing (Dsubst sb xv Dpre ++ Dtail)
        (Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt))
        (subst_tm_tm sb xv t) (subst_tm_tm sb xv Ty).
Proof.
  intros Dpre xv Ax Dtail Gpre Gtail qu t Ty Gt sb H.
  remember (Dpre ++ (xv,Tm Ax) :: Dtail) as Dd eqn:ED.
  remember (Gpre ++ (xv,(qu,Tm Ax)) :: Gtail) as Gd eqn:EG.
  revert Dpre xv Ax Dtail Gpre Gtail qu Gt sb ED EG.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros Dpre xv Ax Dtail Gpre Gtail qu Gt sb ED EG HSpre HStail Hnd Hfv Hlc HshGt Hb.
  - (* T_sub *)
    pose proof (@typing_align D5 G1 a A0 H1) as Hsh1.
    destruct (shape_split D5 G1 Hsh1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres.
    rewrite ED in Hsub. rewrite HG1 in Hsub. rewrite EG in Hsub.
    destruct (ctx_sub_decomp Dpre xv Ax Dtail G1pre G1tail Gpre Gtail q1 qu
                HS1pre HSpre HS1tail HStail Hsub) as [Hle [Hsubpre Hsubtail]].
    assert (Hndp : nodupD (Dsubst sb xv Dpre ++ Dtail)).
    { assert (Hnd5 : nodupD (Dpre ++ (xv,Tm Ax) :: Dtail)) by (rewrite <- ED; exact Hnd).
      apply nodupD_app.
      - apply (proj2 (nodupD_Dsubst sb xv Dpre)).
        exact (nodupD_app_l Dpre ((xv,Tm Ax)::Dtail) Hnd5).
      - exact (proj2 (nodupD_cons_inv xv (Tm Ax) Dtail (nodupD_app_r Dpre ((xv,Tm Ax)::Dtail) Hnd5))).
      - intros y Hy HyD2.
        exact ((nodupD_app_disj Dpre ((xv,Tm Ax)::Dtail) y Hnd5)
                 (proj1 (in_dom_Dsubst sb xv Dpre y) Hy)
                 (proj2 (in_dom_cons y xv Ax Dtail) (or_intror HyD2))). }
    assert (Hsubres : ctx_sub (Dsubst sb xv Dpre ++ Dtail)
                (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
                (Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt))).
    { apply (ctx_sub_combine (Dsubst sb xv Dpre) Dtail
               (Gsubst sb xv G1pre) (Gsubst sb xv Gpre)
               (ctx_plus G1tail (ctx_mul q1 Gt)) (ctx_plus Gtail (ctx_mul qu Gt))).
      - exact Hndp.
      - apply sh_Dsubst. exact HS1pre.
      - apply sh_Dsubst. exact HSpre.
      - apply shapeDG_plus. exact HS1tail. apply shapeDG_mul. exact HshGt.
      - apply shapeDG_plus. exact HStail. apply shapeDG_mul. exact HshGt.
      - apply (ctx_sub_Gsubst sb xv Dpre G1pre Gpre Hsubpre).
      - apply (ctx_sub_plus_mul Dtail G1tail Gtail Hsubtail Gt HshGt q1 qu Hle). }
    exact (T_sub (Dsubst sb xv Dpre ++ Dtail)
             (Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt))
             (subst_tm_tm sb xv a) (subst_tm_tm sb xv A0)
             (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
             Hres Hsubres).
  - (* T_type *) destruct Dpre; simpl in ED; discriminate.
  - (* T_var *)
    destruct Dpre as [|[p Ap] Dpre].
    + (* Dpre = nil *)
      simpl in ED. inversion ED; subst.
      assert (Hlen0 : length Gpre = 0%nat).
      { assert (HE := f_equal (@length (atom*(usage*sort))) EG).
        simpl in HE. rewrite !length_app in HE. rewrite length_ctx_mul in HE.
        simpl in HE.
        pose proof (@sh_length_l Dtail G (@typing_align Dtail G Ax a_Type H1)) as HGlen.
        pose proof (@sh_length_l Dtail Gtail HStail) as HGtlen.
        lia. }
      apply length_zero_iff_nil in Hlen0. subst Gpre.
      simpl in EG. inversion EG; subst.
      assert (Hn : gnames G = gnames Gt).
      { rewrite <- (@sh_names Dtail G (@typing_align Dtail G Ax a_Type H1)).
        rewrite <- (@sh_names Dtail Gt HshGt). reflexivity. }
      assert (Hs : gsorts G = gsorts Gt).
      { rewrite <- (@sh_sorts Dtail G (@typing_align Dtail G Ax a_Type H1)).
        rewrite <- (@sh_sorts Dtail Gt HshGt). reflexivity. }
      rewrite (ctx_plus_zero_one G Gt Hn Hs).
      rewrite Dsubst_nil. rewrite Gsubst_nil. simpl.
      rewrite (subst_fresh Ax sb xv Hfv). simpl.
      destruct (eq_var xv xv) as [Heq|Hneq]; [exact Hb | exfalso; exact (Hneq (@Logic.eq_refl atom xv))].
    + (* Dpre = p :: Dpre *)
      simpl in ED. injection ED as Hx HA Htail. subst p. subst Ap.
      pose proof (@typing_align D5 G Ax0 a_Type H1) as Hsh.
      destruct (shape_split D5 G Hsh Dpre xv Ax Dtail Htail)
        as [Gs [qg [Gt' [HG [HSg HSg']]]]].
      pose proof (IH1 Dpre xv Ax Dtail Gs Gt' qg Gt sb Htail HG HSg HSg'
                   (nodupD_app_r (x ~ Tm Ax0) D5 Hnd) Hfv Hlc HshGt Hb) as Hres.
      assert (HC : (x ~ (1,Tm Ax0)) ++ ctx_mul 0 G
                 = ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)
                   ++ (xv,(0*qg,Tm Ax)) :: ctx_mul 0 Gt').
      { rewrite HG. rewrite ctx_mul_split_form. rewrite app_assoc. reflexivity. }
      assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
                 = ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)
                   ++ (xv,(0*qg,Tm Ax)) :: ctx_mul 0 Gt').
      { rewrite <- EG. exact HC. }
      assert (Hlen2 : length Gpre = length ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)).
      { rewrite <- (@sh_length_l ((x,Tm Ax0)::Dpre) Gpre HSpre).
        rewrite length_app. simpl. rewrite length_ctx_mul.
        f_equal. exact (@sh_length_l Dpre Gs HSg). }
      destruct (split_eq_of_length Gpre Gtail ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)
                  (ctx_mul 0 Gt') xv qu (0*qg) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
      assert (Hctx : Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt)
                 = (x ~ (1,Tm (subst_tm_tm sb xv Ax0)))
                   ++ ctx_mul 0 (Gsubst sb xv Gs ++ ctx_plus Gt' (ctx_mul qg Gt))).
      { rewrite HGpre. rewrite HGtail. rewrite Hqu.
        rewrite Gsubst_app. rewrite Gsubst_ctx_mul. simpl.
        rewrite ctx_mul_app. rewrite ctx_mul_ctx_plus. rewrite ctx_mul_ctx_mul.
        reflexivity. }
      assert (Hxnv : x <> xv).
      { intro C.
        assert (Hnin : x \notin dom D5).
        { apply (nodupD_app_disj (x ~ Tm Ax0) D5 x Hnd).
          apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
        assert (Hin : xv \in dom D5).
        { rewrite Htail. rewrite dom_app. apply union_iff. right.
          apply (proj2 (in_dom_cons xv xv Ax Dtail) (or_introl (@Logic.eq_refl atom xv))). }
        subst x. exact (Hnin Hin). }
      assert (Hterm : subst_tm_tm sb xv (a_Var_f x) = a_Var_f x).
      { simpl. destruct (eq_var x xv) as [Hxeq|Hxneq]; [exfalso; exact (Hxnv Hxeq)|reflexivity]. }
      rewrite Hctx. rewrite Hterm. rewrite Dsubst_cons. simpl.
      refine (T_var (Dsubst sb xv Dpre ++ Dtail) x (subst_tm_tm sb xv Ax0)
                (Gsubst sb xv Gs ++ ctx_plus Gt' (ctx_mul qg Gt)) _ Hres).
      intro C. apply Hnotin. rewrite Htail. rewrite dom_app. apply union_iff.
      rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
      * left. exact (proj1 (in_dom_Dsubst sb xv Dpre x) C).
      * right. exact (proj2 (in_dom_cons x xv Ax Dtail) (or_intror C)).
  - (* T_weak *)
    destruct Dpre as [|[p Ap] Dpre].
    + (* Dpre = nil *)
      simpl in ED. inversion ED; subst.
      assert (Hlen0 : length Gpre = 0%nat).
      { assert (HE := f_equal (@length (atom*(usage*sort))) EG).
        simpl in HE. rewrite !length_app in HE. simpl in HE.
        pose proof (@sh_length_l Dtail G1 (@typing_align Dtail G1 a B0 H1)) as HGlen.
        pose proof (@sh_length_l Dtail Gtail HStail) as HGtlen.
        lia. }
      apply length_zero_iff_nil in Hlen0. subst Gpre.
      simpl in EG. injection EG as Hqu0 HGt0. subst qu. subst Gtail.
      assert (Hxd : xv \notin dom Dtail).
      { apply (nodupD_app_disj (xv ~ Tm Ax) Dtail xv Hnd).
        apply (proj2 (in_dom_cons xv xv Ax nil) (or_introl (@Logic.eq_refl atom xv))). }
      assert (Hfva : xv \notin fv_tm_tm a).
      { intro C. exact (Hxd ((proj1 (@typing_fv Dtail G1 a B0 H1)) xv C)). }
      assert (HfvB : xv \notin fv_tm_tm B0).
      { intro C. exact (Hxd ((proj2 (@typing_fv Dtail G1 a B0 H1)) xv C)). }
      rewrite (ctx_plus_zero Dtail G1 Gt (@typing_align Dtail G1 a B0 H1) HshGt).
      rewrite Dsubst_nil. rewrite Gsubst_nil. simpl.
      rewrite (subst_fresh a sb xv Hfva). rewrite (subst_fresh B0 sb xv HfvB).
      exact H1.
    + (* Dpre = p :: Dpre *)
      simpl in ED. injection ED as Hx HA Htail. subst p. subst Ap.
      pose proof (@typing_align D5 G1 a B0 H1) as Hsh1.
      destruct (shape_split D5 G1 Hsh1 Dpre xv Ax Dtail Htail)
        as [Gs [qg [Gt' [HG [HSg HSg']]]]].
      pose proof (@typing_align D5 G2 Ax0 a_Type H2) as Hsh2.
      destruct (shape_split D5 G2 Hsh2 Dpre xv Ax Dtail Htail)
        as [G2s [q2 [G2t [HG2 [HS2s HS2t]]]]].
      pose proof (IH1 Dpre xv Ax Dtail Gs Gt' qg Gt sb Htail HG HSg HSg'
                   (nodupD_app_r (x ~ Tm Ax0) D5 Hnd) Hfv Hlc HshGt Hb) as Hres.
      pose proof (IH2 Dpre xv Ax Dtail G2s G2t q2 Gt sb Htail HG2 HS2s HS2t
                   (nodupD_app_r (x ~ Tm Ax0) D5 Hnd) Hfv Hlc HshGt Hb) as Hty2.
      assert (HC : (x ~ (0,Tm Ax0)) ++ G1
                 = ((x ~ (0,Tm Ax0)) ++ Gs) ++ (xv,(qg,Tm Ax)) :: Gt').
      { rewrite HG. rewrite app_assoc. reflexivity. }
      assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
                 = ((x ~ (0,Tm Ax0)) ++ Gs) ++ (xv,(qg,Tm Ax)) :: Gt').
      { rewrite <- EG. exact HC. }
      assert (Hlen2 : length Gpre = length ((x ~ (0,Tm Ax0)) ++ Gs)).
      { rewrite <- (@sh_length_l ((x,Tm Ax0)::Dpre) Gpre HSpre).
        rewrite length_app. simpl.
        f_equal. exact (@sh_length_l Dpre Gs HSg). }
      destruct (split_eq_of_length Gpre Gtail ((x ~ (0,Tm Ax0)) ++ Gs) Gt'
                  xv qu qg Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
      assert (Hctx : Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt)
                 = (x ~ (0,Tm (subst_tm_tm sb xv Ax0)))
                   ++ (Gsubst sb xv Gs ++ ctx_plus Gt' (ctx_mul qg Gt))).
      { rewrite HGpre. rewrite HGtail. rewrite Hqu.
        rewrite Gsubst_app. simpl. reflexivity. }
      assert (Hxnv : x <> xv).
      { intro C.
        assert (Hnin : x \notin dom D5).
        { apply (nodupD_app_disj (x ~ Tm Ax0) D5 x Hnd).
          apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
        assert (Hin : xv \in dom D5).
        { rewrite Htail. rewrite dom_app. apply union_iff. right.
          apply (proj2 (in_dom_cons xv xv Ax Dtail) (or_introl (@Logic.eq_refl atom xv))). }
        subst x. exact (Hnin Hin). }
      rewrite Hctx. rewrite Dsubst_cons. simpl.
      refine (T_weak (Dsubst sb xv Dpre ++ Dtail) x (subst_tm_tm sb xv Ax0)
                (Gsubst sb xv Gs ++ ctx_plus Gt' (ctx_mul qg Gt))
                (subst_tm_tm sb xv a) (subst_tm_tm sb xv B0)
                (Gsubst sb xv G2s ++ ctx_plus G2t (ctx_mul q2 Gt)) _ Hres Hty2).
      intro C. apply Hnotin. rewrite Htail. rewrite dom_app. apply union_iff.
      rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
      * left. exact (proj1 (in_dom_Dsubst sb xv Dpre x) C).
      * right. exact (proj2 (in_dom_cons x xv Ax Dtail) (or_intror C)).
  - (* T_pi *)
    pose proof (@typing_align D5 G1 A1 a_Type H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L A1 r D5 G2). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G2)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hty1.
    assert (Hlen : length (Gsubst sb xv G1pre) = length (Gsubst sb xv G2pre)).
    { rewrite length_Gsubst. rewrite length_Gsubst.
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    assert (Hctx : ctx_plus (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
                            (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
                 = Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt)).
    { rewrite (ctx_plus_app (Gsubst sb xv G1pre) (ctx_plus G1tail (ctx_mul q1 Gt))
                            (Gsubst sb xv G2pre) (ctx_plus G2tail (ctx_mul q2 Gt)) Hlen).
      rewrite <- Gsubst_ctx_plus.
      rewrite (tail_combine Dtail G1tail G2tail Gt q1 q2 HS1tail HS2tail HshGt).
      rewrite HGpre. rewrite Hqu. rewrite HGtail. reflexivity. }
    rewrite <- Hctx.
    eapply (T_pi ((L \u dom D5) \u {{xv}})).
    + exact Hty1.
    + intros y Hy.
      assert (Hy1 : y \notin L \u dom D5).
      { exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (Hy2 : y \notin {{xv}}).
      { exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm A1)) ++ G2
                 = ((y ~ (r,Tm A1)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G2pre)).
      { apply (sh_cons y r A1 Dpre G2pre HS2pre). }
      pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (r,Tm A1)) ++ G2pre) G2tail
                    q2 Gt sb EDy EGy HSpre_y HS2tail Hndy Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
  - (* T_lam *)
    pose proof (@typing_align D5 G2 A1 a_Type H2) as Hsh2.
    destruct (shape_split D5 G2 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hty2.
    eapply (T_lam ((L \u dom D5) \u {{xv}})).
    + intros y Hy.
      assert (Hy1 : y \notin L \u dom D5).
      { exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (Hy2 : y \notin {{xv}}).
      { exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (qq,Tm A1)) ++ G1
                 = ((y ~ (qq,Tm A1)) ++ Gpre) ++ (xv,(qu,Tm Ax)) :: Gtail).
      { rewrite EG. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (qq,Tm A1)) ++ Gpre)).
      { apply (sh_cons y qq A1 Dpre Gpre HSpre). }
      pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (qq,Tm A1)) ++ Gpre) Gtail
                    qu Gt sb EDy EGy HSpre_y HStail Hndy Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y a Hlc Hyneq) in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
    + exact Hty2.
  - (* T_app *)
    pose proof (@typing_align D5 G1 a (a_Pi qq A1 B1) H1) as HshG1.
    pose proof (@typing_align D5 G2 b A1 H2) as HshG2.
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres2.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre (ctx_mul qq G2pre)
                 ++ (xv,(q1+qq*q2,Tm Ax)) :: ctx_plus G1tail (ctx_mul qq G2tail)).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_mul_split_form_r G1pre G1tail G2pre G2tail qq xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre (ctx_mul qq G2pre))).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre (ctx_mul qq G2pre))
               (shapeDG_plus Dpre G1pre (ctx_mul qq G2pre) HS1pre
                  (shapeDG_mul Dpre G2pre qq HS2pre))). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre (ctx_mul qq G2pre))
                (ctx_plus G1tail (ctx_mul qq G2tail))
                xv qu (q1+qq*q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_mul_r Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 xv q1 q2 qq qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B1 xv 0 b).
    refine (T_app (Dsubst sb xv Dpre ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt)) qq
              (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b)
              (subst_tm_tm sb xv B1) (subst_tm_tm sb xv A1) Hres1 Hres2).
  - (* T_conv *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu Gt sb ED EG HSpre HStail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (@typing_align D5 G2 B0 a_Type H2) as Hsh2.
    destruct (shape_split D5 G2 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres2.
    eapply T_conv.
    + exact Hres1.
    + exact Hres2.
    + exact (subst_Beta1 sb xv A1 B0 Hlc Hbconv).
  - (* T_unit *) destruct Dpre; simpl in ED; discriminate.
  - (* T_Unit *) destruct Dpre; simpl in ED; discriminate.
  - (* T_UnitE *)
    pose proof (@typing_align D5 G1 a a_TyUnit H1) as HshG1.
    pose proof (@typing_align D5 G2 b B1 H2) as HshG2.
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L a_TyUnit r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm a_TyUnit) ++ D5) ((y ~ (r,Tm a_TyUnit)) ++ G3)
                (open_tm_wrt_tm B0 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres2.
    assert (Heq' : subst_tm_tm sb xv B1 = open_tm_wrt_tm (subst_tm_tm sb xv B0) a_TmUnit).
    { rewrite Heq. rewrite (subst_open_comm sb Hlc B0 xv 0 a_TmUnit). simpl. reflexivity. }
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 xv q1 q2 qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B0 xv 0 a).
    refine (T_UnitE ((L \u dom D5) \u {{xv}})
              (Dsubst sb xv Dpre ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b) r
              (subst_tm_tm sb xv B0) (subst_tm_tm sb xv B1)
              (Gsubst sb xv G3pre ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Hres1 Heq' Hres2 _).
    intros y Hy.
    assert (Hy1 : y \notin L \u dom D5).
    { exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
    assert (Hy2 : y \notin {{xv}}).
    { exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
    assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
    assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
    assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
    assert (Hndy : nodupD ((y ~ Tm a_TyUnit) ++ D5)).
    { apply nodupD_cons. exact Hnd. exact Hydom. }
    assert (EDy : (y ~ Tm a_TyUnit) ++ D5 = ((y ~ Tm a_TyUnit) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
    { rewrite ED. rewrite app_assoc. reflexivity. }
    assert (EGy : (y ~ (r,Tm a_TyUnit)) ++ G3
               = ((y ~ (r,Tm a_TyUnit)) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
    { rewrite HG3. rewrite app_assoc. reflexivity. }
    assert (HSpre_y : shapeDG ((y ~ Tm a_TyUnit) ++ Dpre) ((y ~ (r,Tm a_TyUnit)) ++ G3pre)).
    { apply (sh_cons y r a_TyUnit Dpre G3pre HS3pre). }
    pose proof (IHfun y HyL ((y ~ Tm a_TyUnit) ++ Dpre) xv Ax Dtail
                  ((y ~ (r,Tm a_TyUnit)) ++ G3pre) G3tail q3 Gt sb
                  EDy EGy HSpre_y HS3tail Hndy Hfv Hlc HshGt Hb) as Hbody.
    rewrite Dsubst_app in Hbody.
    rewrite Gsubst_app in Hbody.
    simpl in Hbody.
    rewrite (subst_open_var sb xv y B0 Hlc Hyneq) in Hbody.
    exact Hbody.
  - (* T_Box *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu Gt sb ED EG HSpre HStail
                 Hnd Hfv Hlc HshGt Hb) as Hres.
    apply T_Box. exact Hres.
  - (* T_box *)
    pose proof (@typing_align D5 G a A1 H1) as Hsh.
    destruct (shape_split D5 G Hsh Dpre xv Ax Dtail ED)
      as [Gsp [qg [Gst [HG [HSsp HSst]]]]].
    pose proof (IH1 Dpre xv Ax Dtail Gsp Gst qg Gt sb ED HG HSsp HSst
                 Hnd Hfv Hlc HshGt Hb) as Hres.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_mul qq Gsp ++ (xv,(qq*qg,Tm Ax)) :: ctx_mul qq Gst).
    { rewrite <- EG. rewrite HG. apply (ctx_mul_split_form qq Gsp Gst xv qg Ax). }
    assert (Hlen2 : length Gpre = length (ctx_mul qq Gsp)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre). rewrite length_ctx_mul.
      exact (sh_length_l Dpre Gsp HSsp). }
    destruct (split_eq_of_length Gpre Gtail (ctx_mul qq Gsp) (ctx_mul qq Gst)
                xv qu (qq*qg) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_mul Gsp Gst Gt Gpre Gtail xv qg qq qu sb HGpre HGtail Hqu).
    apply T_box. exact Hres.
  - (* T_letbox *)
    pose proof (@typing_align D5 G1 a (a_Box qq A1) H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L A1 qq D5 G2). intros x Hx.
      apply (@typing_align ((x ~ Tm A1) ++ D5) ((x ~ (qq,Tm A1)) ++ G2)
                (open_tm_wrt_tm b (a_Var_f x))
                (open_tm_wrt_tm B1 (a_box qq (a_Var_f x))) (Hfun2 x Hx)). }
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L (a_Box qq A1) r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm (a_Box qq A1)) ++ D5) ((y ~ (r,Tm (a_Box qq A1))) ++ G3)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun3 y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 xv q1 q2 qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B1 xv 0 a).
    refine (T_letbox ((L \u dom D5) \u {{xv}})
              (Dsubst sb xv Dpre ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b) r qq
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv B1)
              (Gsubst sb xv G3pre ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Hres1 _ _).
    + (* second premise: forall x *)
      intros x Hx.
      assert (Hx1 : x \notin L \u dom D5).
      { exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} Hx)). }
      assert (Hx2 : x \notin {{xv}}).
      { exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} Hx)). }
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxdom : x \notin dom D5) by (exact (proj2 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      assert (Hndx : nodupD ((x ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hxdom. }
      assert (EDx : (x ~ Tm A1) ++ D5 = ((x ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGx : (x ~ (qq,Tm A1)) ++ G2
                 = ((x ~ (qq,Tm A1)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_x : shapeDG ((x ~ Tm A1) ++ Dpre) ((x ~ (qq,Tm A1)) ++ G2pre)).
      { apply (sh_cons x qq A1 Dpre G2pre HS2pre). }
      pose proof (IHfun2 x HxL ((x ~ Tm A1) ++ Dpre) xv Ax Dtail
                    ((x ~ (qq,Tm A1)) ++ G2pre) G2tail q2 Gt sb
                    EDx EGx HSpre_x HS2tail Hndx Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv x b Hlc Hxneq) in Hbody.
      rewrite (subst_open_comm sb Hlc B1 xv 0 (a_box qq (a_Var_f x))) in Hbody.
      assert (Hnf : xv \notin fv_tm_tm (a_Var_f x)).
      { simpl. intro C. apply Hxneq. apply singleton_iff in C. exact C. }
      assert (Hvx : subst_tm_tm sb xv (a_Var_f x) = a_Var_f x)
        by (apply subst_fresh; exact Hnf).
      assert (Hc : subst_tm_tm sb xv (a_box qq (a_Var_f x)) = a_box qq (a_Var_f x)).
      { change (a_box qq (subst_tm_tm sb xv (a_Var_f x)) = a_box qq (a_Var_f x)).
        rewrite Hvx. reflexivity. }
      rewrite Hc in Hbody.
      exact Hbody.
    + (* third premise: forall y *)
      intros y Hy.
      assert (Hy1 : y \notin L \u dom D5).
      { exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (Hy2 : y \notin {{xv}}).
      { exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm (a_Box qq A1)) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (EDy : (y ~ Tm (a_Box qq A1)) ++ D5
                 = ((y ~ Tm (a_Box qq A1)) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm (a_Box qq A1))) ++ G3
                 = ((y ~ (r,Tm (a_Box qq A1))) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
      { rewrite HG3. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm (a_Box qq A1)) ++ Dpre)
                         ((y ~ (r,Tm (a_Box qq A1))) ++ G3pre)).
      { apply (sh_cons y r (a_Box qq A1) Dpre G3pre HS3pre). }
      pose proof (IHfun3 y HyL ((y ~ Tm (a_Box qq A1)) ++ Dpre) xv Ax Dtail
                    ((y ~ (r,Tm (a_Box qq A1))) ++ G3pre) G3tail q3 Gt sb
                    EDy EGy HSpre_y HS3tail Hndy Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
  - (* T_sum *)
    pose proof (@typing_align D5 G1 A1 a_Type H1) as HshG1.
    pose proof (@typing_align D5 G2 A2 a_Type H2) as HshG2.
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres2.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 xv q1 q2 qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    eapply T_sum.
    + exact Hres1.
    + exact Hres2.
  - (* T_inj1 *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu Gt sb ED EG HSpre HStail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (@typing_align D5 G1 A2 a_Type H2) as Hsh2.
    destruct (shape_split D5 G1 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres2.
    exact (T_inj1 (Dsubst sb xv Dpre ++ Dtail)
                  (Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt))
                  (subst_tm_tm sb xv a) (subst_tm_tm sb xv A1) (subst_tm_tm sb xv A2)
                  (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
                  Hres1 Hres2).
  - (* T_inj2 *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu Gt sb ED EG HSpre HStail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (@typing_align D5 G1 A1 a_Type H2) as Hsh2.
    destruct (shape_split D5 G1 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres2.
    exact (T_inj2 (Dsubst sb xv Dpre ++ Dtail)
                  (Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt))
                  (subst_tm_tm sb xv a) (subst_tm_tm sb xv A1) (subst_tm_tm sb xv A2)
                  (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
                  Hres1 Hres2).
  - (* T_case *)
    pose proof (@typing_align D5 G1 a (a_Sum A1 A2) H1) as HshG1.
    pose proof (@typing_align D5 G2 b1 (a_Pi qq A1 B1) H3) as HshG2.
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L (a_Sum A1 A2) r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm (a_Sum A1 A2)) ++ D5)
                ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3)
                (open_tm_wrt_tm B0 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH3 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres3.
    pose proof (IH4 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres4.
    assert (Hinj1 : forall x, x <> xv ->
              subst_tm_tm sb xv (a_Inj1 (a_Var_f x)) = a_Inj1 (a_Var_f x)).
    { intros x Hxneq. apply subst_fresh. simpl. intro C. apply Hxneq.
      apply singleton_iff in C. exact C. }
    assert (Hinj2 : forall x, x <> xv ->
              subst_tm_tm sb xv (a_Inj2 (a_Var_f x)) = a_Inj2 (a_Var_f x)).
    { intros x Hxneq. apply subst_fresh. simpl. intro C. apply Hxneq.
      apply singleton_iff in C. exact C. }
    assert (Heq1' : forall x, x \notin ((L \u dom D5) \u {{xv}}) ->
              open_tm_wrt_tm (subst_tm_tm sb xv B1) (a_Var_f x)
              = open_tm_wrt_tm (subst_tm_tm sb xv B0) (a_Inj1 (a_Var_f x))).
    { intros x Hx.
      assert (Hx1 : x \notin L \u dom D5) by (exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} Hx))).
      assert (Hx2 : x \notin {{xv}}) by (exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} Hx))).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      rewrite <- (subst_open_var sb xv x B1 Hlc Hxneq).
      rewrite (Heq1 x HxL).
      rewrite (subst_open_comm sb Hlc B0 xv 0 (a_Inj1 (a_Var_f x))).
      rewrite (Hinj1 x Hxneq). reflexivity. }
    assert (Heq2' : forall x, x \notin ((L \u dom D5) \u {{xv}}) ->
              open_tm_wrt_tm (subst_tm_tm sb xv B2) (a_Var_f x)
              = open_tm_wrt_tm (subst_tm_tm sb xv B0) (a_Inj2 (a_Var_f x))).
    { intros x Hx.
      assert (Hx1 : x \notin L \u dom D5) by (exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} Hx))).
      assert (Hx2 : x \notin {{xv}}) by (exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} Hx))).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      rewrite <- (subst_open_var sb xv x B2 Hlc Hxneq).
      rewrite (Heq2 x HxL).
      rewrite (subst_open_comm sb Hlc B0 xv 0 (a_Inj2 (a_Var_f x))).
      rewrite (Hinj2 x Hxneq). reflexivity. }
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus (ctx_mul qq G1pre) G2pre
                 ++ (xv,(qq*q1+q2,Tm Ax)) :: ctx_plus (ctx_mul qq G1tail) G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_mul_split_form G1pre G1tail G2pre G2tail qq xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus (ctx_mul qq G1pre) G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus (ctx_mul qq G1pre) G2pre)
               (shapeDG_plus Dpre (ctx_mul qq G1pre) G2pre
                  (shapeDG_mul Dpre G1pre qq HS1pre) HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus (ctx_mul qq G1pre) G2pre)
                (ctx_plus (ctx_mul qq G1tail) G2tail)
                xv qu (qq*q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_mul Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 xv q1 q2 qq qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B0 xv 0 a).
    refine (T_case ((L \u dom D5) \u {{xv}})
              (Dsubst sb xv Dpre ++ Dtail) qq
              (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b1) (subst_tm_tm sb xv b2) r
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv A2)
              (subst_tm_tm sb xv B0) (subst_tm_tm sb xv B1) (subst_tm_tm sb xv B2)
              (Gsubst sb xv G3pre ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Hq Hres1 Heq1' Heq2' Hres3 Hres4 _).
    intros y Hy.
    assert (Hy1 : y \notin L \u dom D5).
    { exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
    assert (Hy2 : y \notin {{xv}}).
    { exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
    assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
    assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
    assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
    assert (Hndy : nodupD ((y ~ Tm (a_Sum A1 A2)) ++ D5)).
    { apply nodupD_cons. exact Hnd. exact Hydom. }
    assert (EDy : (y ~ Tm (a_Sum A1 A2)) ++ D5
               = ((y ~ Tm (a_Sum A1 A2)) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
    { rewrite ED. rewrite app_assoc. reflexivity. }
    assert (EGy : (y ~ (r,Tm (a_Sum A1 A2))) ++ G3
               = ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
    { rewrite HG3. rewrite app_assoc. reflexivity. }
    assert (HSpre_y : shapeDG ((y ~ Tm (a_Sum A1 A2)) ++ Dpre)
                       ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3pre)).
    { apply (sh_cons y r (a_Sum A1 A2) Dpre G3pre HS3pre). }
    pose proof (IHfun y HyL ((y ~ Tm (a_Sum A1 A2)) ++ Dpre) xv Ax Dtail
                  ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3pre) G3tail q3 Gt sb
                  EDy EGy HSpre_y HS3tail Hndy Hfv Hlc HshGt Hb) as Hbody.
    rewrite Dsubst_app in Hbody.
    rewrite Gsubst_app in Hbody.
    simpl in Hbody.
    rewrite (subst_open_var sb xv y B0 Hlc Hyneq) in Hbody.
    exact Hbody.
  - (* T_Sigma *)
    pose proof (@typing_align D5 G1 A1 a_Type H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L A1 r D5 G2). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G2)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hty1.
    assert (Hlen : length (Gsubst sb xv G1pre) = length (Gsubst sb xv G2pre)).
    { rewrite length_Gsubst. rewrite length_Gsubst.
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    assert (Hctx : ctx_plus (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
                            (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
                 = Gsubst sb xv Gpre ++ ctx_plus Gtail (ctx_mul qu Gt)).
    { rewrite (ctx_plus_app (Gsubst sb xv G1pre) (ctx_plus G1tail (ctx_mul q1 Gt))
                            (Gsubst sb xv G2pre) (ctx_plus G2tail (ctx_mul q2 Gt)) Hlen).
      rewrite <- Gsubst_ctx_plus.
      rewrite (tail_combine Dtail G1tail G2tail Gt q1 q2 HS1tail HS2tail HshGt).
      rewrite HGpre. rewrite Hqu. rewrite HGtail. reflexivity. }
    rewrite <- Hctx.
    eapply (T_Sigma ((L \u dom D5) \u {{xv}})).
    + exact Hty1.
    + intros y Hy.
      assert (Hy1 : y \notin L \u dom D5).
      { exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (Hy2 : y \notin {{xv}}).
      { exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm A1)) ++ G2
                 = ((y ~ (r,Tm A1)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G2pre)).
      { apply (sh_cons y r A1 Dpre G2pre HS2pre). }
      pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (r,Tm A1)) ++ G2pre) G2tail
                    q2 Gt sb EDy EGy HSpre_y HS2tail Hndy Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
  - (* T_Tensor *)
    pose proof (@typing_align D5 G1 a A1 H1) as HshG1.
    pose proof (@typing_align D5 G2 b (open_tm_wrt_tm B1 a) H2) as HshG2.
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L A1 r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G3)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 Gt sb ED HG2 HS2pre HS2tail
                 Hnd Hfv Hlc HshGt Hb) as Hres2.
    rewrite (subst_open_comm sb Hlc B1 xv 0 a) in Hres2.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus (ctx_mul qq G1pre) G2pre
                 ++ (xv,(qq*q1+q2,Tm Ax)) :: ctx_plus (ctx_mul qq G1tail) G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_mul_split_form G1pre G1tail G2pre G2tail qq xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus (ctx_mul qq G1pre) G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus (ctx_mul qq G1pre) G2pre)
               (shapeDG_plus Dpre (ctx_mul qq G1pre) G2pre
                  (shapeDG_mul Dpre G1pre qq HS1pre) HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus (ctx_mul qq G1pre) G2pre)
                (ctx_plus (ctx_mul qq G1tail) G2tail)
                xv qu (qq*q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_mul Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 xv q1 q2 qq qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    refine (T_Tensor ((L \u dom D5) \u {{xv}})
              (Dsubst sb xv Dpre ++ Dtail) qq
              (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b)
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv B1)
              (Gsubst sb xv G3pre ++ ctx_plus G3tail (ctx_mul q3 Gt)) r
              Hres1 Hres2 _).
    intros y Hy.
    assert (Hy1 : y \notin L \u dom D5).
    { exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
    assert (Hy2 : y \notin {{xv}}).
    { exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy)). }
    assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
    assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
    assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
    assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
    { apply nodupD_cons. exact Hnd. exact Hydom. }
    assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
    { rewrite ED. rewrite app_assoc. reflexivity. }
    assert (EGy : (y ~ (r,Tm A1)) ++ G3
               = ((y ~ (r,Tm A1)) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
    { rewrite HG3. rewrite app_assoc. reflexivity. }
    assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G3pre)).
    { apply (sh_cons y r A1 Dpre G3pre HS3pre). }
    pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (r,Tm A1)) ++ G3pre) G3tail
                  q3 Gt sb EDy EGy HSpre_y HS3tail Hndy Hfv Hlc HshGt Hb) as Hbody.
    rewrite Dsubst_app in Hbody.
    rewrite Gsubst_app in Hbody.
    simpl in Hbody.
    rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
    exact Hbody.
  - (* T_Spread *)
    pose proof (@typing_align D5 G1 a A1 H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv2 L A2 qq D5 G2). intros x Hx y Hy.
      apply (@typing_align ((x ~ Tm A2) ++ D5) ((x ~ (qq,Tm A2)) ++ G2)
                (open_tm_wrt_tm b (a_Var_f x))
                (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                   (close_tm_wrt_tm y (open_tm_wrt_tm B1
                      (a_Tensor (a_Var_f x) (a_Var_f y)))))
                (Hfun2 x Hx y Hy)). }
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L A1 r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G3)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun3 y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 Gt sb ED HG1 HS1pre HS1tail
                 Hnd Hfv Hlc HshGt Hb) as Hres1.
    assert (Heq' : subst_tm_tm sb xv A1
               = a_Sigma qq (subst_tm_tm sb xv A2) (subst_tm_tm sb xv A3)).
    { rewrite Heq. simpl. reflexivity. }
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 xv q1 q2 qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B1 xv 0 a).
    refine (T_Spread (((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)
              (Dsubst sb xv Dpre ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b) r
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv B1) qq
              (subst_tm_tm sb xv A2) (subst_tm_tm sb xv A3)
              (Gsubst sb xv G3pre ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Heq' Hres1 _ _).
    + (* second premise: forall x y *)
      intros x Hx.
      assert (Hxout : x \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union x ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) Hx))).
      assert (Hxfs : x \notin fv_tm_tm sb)
        by (exact (proj2 (self_notin_union x ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) Hx))).
      assert (Hx1 : x \notin L \u dom D5)
        by (exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} Hxout))).
      assert (Hx2 : x \notin {{xv}})
        by (exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} Hxout))).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxdom : x \notin dom D5) by (exact (proj2 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      intros y Hy.
      assert (Hyout : y \notin ((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)
        by (exact (proj1 (self_notin_union y (((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb) {{x}} Hy))).
      assert (Hyx : y <> x) by (exact (self_notin_singleton y x (proj2 (self_notin_union y (((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb) {{x}} Hy)))).
      assert (Hy1 : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) Hyout))).
      assert (Hyfs : y \notin fv_tm_tm sb)
        by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) Hyout))).
      assert (Hy2 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hy1))).
      assert (Hy3 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hy1))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy2))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy2))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy3)).
      assert (HyLx : y \notin L \u {{x}}).
      { intro C. apply union_iff in C. destruct C as [C|C].
        - exact (HyL C).
        - apply Hyx. apply singleton_iff in C. exact (@Logic.eq_sym atom x y C). }
      assert (Hndx : nodupD ((x ~ Tm A2) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hxdom. }
      assert (EDx : (x ~ Tm A2) ++ D5 = ((x ~ Tm A2) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGx : (x ~ (qq,Tm A2)) ++ G2
                 = ((x ~ (qq,Tm A2)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_x : shapeDG ((x ~ Tm A2) ++ Dpre) ((x ~ (qq,Tm A2)) ++ G2pre)).
      { change (shapeDG ((x,Tm A2) :: Dpre) ((x,(qq,Tm A2)) :: G2pre)).
        apply (sh_cons x qq A2 Dpre G2pre HS2pre). }
      pose proof (IHfun2 x HxL y HyLx ((x ~ Tm A2) ++ Dpre) xv Ax Dtail
                    ((x ~ (qq,Tm A2)) ++ G2pre) G2tail q2 Gt sb
                    EDx EGx HSpre_x HS2tail Hndx Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv x b Hlc Hxneq) in Hbody.
      rewrite (subst_open_var sb xv x A3 Hlc Hxneq) in Hbody.
      rewrite (subst_close_rec_comm sb xv y 0
                 (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))
                 Hlc (fun H : xv = y => Hyneq (@Logic.eq_sym atom xv y H)) Hyfs) in Hbody.
      rewrite (subst_open_comm sb Hlc B1 xv 0 (a_Tensor (a_Var_f x) (a_Var_f y))) in Hbody.
      rewrite (subst_tensor_vars sb xv x y Hxneq Hyneq) in Hbody.
      exact Hbody.
    + (* third premise: forall y *)
      intros y Hy.
      assert (Hyout : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) Hy))).
      assert (Hy1 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hyout))).
      assert (Hy2 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hyout))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm A1)) ++ G3
                 = ((y ~ (r,Tm A1)) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
      { rewrite HG3. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G3pre)).
      { change (shapeDG ((y,Tm A1) :: Dpre) ((y,(r,Tm A1)) :: G3pre)).
        apply (sh_cons y r A1 Dpre G3pre HS3pre). }
      pose proof (IHfun3 y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail
                    ((y ~ (r,Tm A1)) ++ G3pre) G3tail q3 Gt sb
                    EDy EGy HSpre_y HS3tail Hndy Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
Qed.

(* ===== inlined from SubstDe.v ===== *)
(* ---------- helpers for the De-general substitution lemma ---------- *)

Lemma shapeDG_app : forall (D1:D) (G1:context) (D2:D) (G2:context),
  shapeDG D1 G1 -> shapeDG D2 G2 -> shapeDG (D1++D2) (G1++G2).
Proof.
  intros D1 G1 D2 G2 H1. revert D2 G2.
  induction H1 as [| x q A D0 G0 H0 IH]; intros D2 G2 H2.
  - simpl. exact H2.
  - simpl. apply sh_cons. apply (IH D2 G2 H2).
Qed.

Lemma De_ok_nodupD' : forall (De:D) (D0:D), De_ok De D0 -> nodupD De.
Proof. intros De D0 [Hdis Hnd]. exact Hnd. Qed.

Lemma De_ok_shrink_head : forall (De:D) (y:atom) (A:sort) (D0:D),
  De_ok De ((y,A)::D0) -> De_ok De D0.
Proof.
  intros De y A D0 [Hdis Hnd]. split; [|exact Hnd].
  intros z Hz C. apply (Hdis z Hz). rewrite dom_cons.
  apply union_iff. right. exact C.
Qed.

Lemma De_ok_remove_prefix : forall (De:D) (D1 D2:D),
  De_ok De (D1++D2) -> De_ok De D2.
Proof.
  intros De D1. induction D1 as [|[y A] D1 IH]; intros D2 H.
  - exact H.
  - apply (IH D2).
    change (De_ok De ((y,A)::(D1++D2))) in H.
    apply (De_ok_shrink_head De y A (D1++D2)). exact H.
Qed.

Lemma De_ok_extend_head : forall (De:D) (y:atom) (A:sort) (D0:D),
  De_ok De D0 -> y \notin dom De -> De_ok De ((y,A)::D0).
Proof.
  intros De y A D0 [Hdis Hnd] Hy. split; [|exact Hnd].
  intros z Hz C. rewrite dom_cons in C. apply union_iff in C.
  destruct C as [C|C].
  - apply singleton_iff in C. subst z. exact (Hy Hz).
  - exact (Hdis z Hz C).
Qed.

Lemma dom_rotate_mem : forall (y:atom) (A:sort) (D1 D2:D) (z:atom),
  z \in dom (((y,A)::D1) ++ D2) -> z \in dom (D1 ++ (y,A) :: D2).
Proof.
  intros y A D1 D2 z C.
  rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
  - rewrite dom_cons in C. apply union_iff in C. destruct C as [C|C].
    + rewrite dom_app. apply union_iff. right. rewrite dom_cons. apply union_iff. left. exact C.
    + rewrite dom_app. apply union_iff. left. exact C.
  - rewrite dom_app. apply union_iff. right. rewrite dom_cons. apply union_iff. right. exact C.
Qed.

(* membership transfer when the split head is added in front of Dpre *)
Lemma dom_rotate_mem2 : forall (y:atom) (A:sort) (D1 D2:D) (z:atom),
  z \in dom ((y,A)::(D1++D2)) -> z \in dom (((y,A)::D1)++D2).
Proof.
  intros y A D1 D2 z C.
  rewrite dom_cons in C. apply union_iff in C. destruct C as [C|C].
  - rewrite dom_app. apply union_iff. left. rewrite dom_cons.
    apply union_iff. left. exact C.
  - rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
    + rewrite dom_app. apply union_iff. left. rewrite dom_cons.
      apply union_iff. right. exact C.
    + rewrite dom_app. apply union_iff. right. exact C.
Qed.

Lemma De_ok_extend_pre : forall (De:D) (y:atom) (A:sort) (Dpre Dtail:D),
  De_ok De (Dpre ++ (y,A) :: Dtail) -> De_ok De (((y,A)::Dpre) ++ Dtail).
Proof.
  intros De y A Dpre Dtail [Hdis Hnd]. split; [|exact Hnd].
  intros z Hz C. exact (Hdis z Hz (dom_rotate_mem y A Dpre Dtail z C)).
Qed.

Lemma De_ok_extend_pre2 : forall (De:D) (y:atom) (A:sort) (Dpre Dtail:D),
  De_ok De ((y,A)::(Dpre++Dtail)) -> De_ok De (((y,A)::Dpre)++Dtail).
Proof.
  intros De y A Dpre Dtail [Hdis Hnd]. split; [|exact Hnd].
  intros z Hz C. exact (Hdis z Hz (dom_rotate_mem2 y A Dpre Dtail z C)).
Qed.

(* nodupD (De ++ Dtail) from the stronger De_ok and nodupD of the a-env *)
Lemma nodupD_De_append : forall (De:D) (Dpre:D) (xv:atom) (Ax:tm) (Dtail:D),
  nodupD (Dpre ++ (xv,Tm Ax) :: Dtail) ->
  De_ok De (Dpre ++ (xv,Tm Ax) :: Dtail) ->
  nodupD (De ++ Dtail).
Proof.
  intros De Dpre xv Ax Dtail Hnd Hok.
  assert (Hnd5 : nodupD (Dpre ++ (xv,Tm Ax) :: Dtail)) by exact Hnd.
  assert (HndTail : nodupD ((xv,Tm Ax) :: Dtail))
    by (exact (nodupD_app_r Dpre ((xv,Tm Ax)::Dtail) Hnd5)).
  assert (HndDtail : nodupD Dtail)
    by (exact (proj2 (nodupD_cons_inv xv (Tm Ax) Dtail HndTail))).
  assert (HndDe : nodupD De) by (exact (De_ok_nodupD' De (Dpre++(xv,Tm Ax)::Dtail) Hok)).
  apply nodupD_app.
  - exact HndDe.
  - exact HndDtail.
  - intros z Hz HzD.
    assert (Hzbig : z \in dom (Dpre ++ (xv,Tm Ax) :: Dtail)).
    { rewrite dom_app. apply union_iff. right. rewrite dom_cons.
      apply union_iff. right. exact HzD. }
    exact ((proj1 Hok) z Hz Hzbig).
Qed.

(* context assembly with De prefix: binary ctx_plus rules *)
Lemma hctx_plus_de : forall (Dpre Dtail:D) (G1pre G1tail G2pre G2tail Gt Gpre Gtail:context)
  (De:D) (Ge:context) (xv:atom) (q1 q2 qu:usage) (sb:tm),
  length G1pre = length G2pre ->
  shapeDG Dpre G1pre -> shapeDG Dpre G2pre ->
  shapeDG Dtail G1tail -> shapeDG Dtail G2tail -> shapeDG Dtail Gt ->
  Gpre = ctx_plus G1pre G2pre -> Gtail = ctx_plus G1tail G2tail -> qu = q1 + q2 ->
  ctx_plus (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
           (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
  = Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge xv q1 q2 qu sb
         Hlen0 H1 H2 H3 H4 H5 HGp HGt Hqu.
  subst Gpre. subst Gtail. subst qu.
  assert (Hlen1 : length (Gsubst sb xv G1pre) = length (Gsubst sb xv G2pre)).
  { rewrite length_Gsubst. rewrite length_Gsubst.
    exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre H1 H2)). }
  rewrite (ctx_plus_app (Gsubst sb xv G1pre)
                        (ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
                        (Gsubst sb xv G2pre)
                        (ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt)) Hlen1).
  rewrite <- Gsubst_ctx_plus.
  assert (Hlen2 : length (ctx_mul q1 Ge) = length (ctx_mul q2 Ge)).
  { rewrite length_ctx_mul. rewrite length_ctx_mul. reflexivity. }
  rewrite (ctx_plus_app (ctx_mul q1 Ge) (ctx_plus G1tail (ctx_mul q1 Gt))
                        (ctx_mul q2 Ge) (ctx_plus G2tail (ctx_mul q2 Gt)) Hlen2).
  rewrite (ctx_mul_add q1 q2 Ge).
  rewrite (tail_combine Dtail G1tail G2tail Gt q1 q2 H3 H4 H5).
  reflexivity.
Qed.


Lemma hctx_mul_de : forall (Gsp Gst Gt:context) (De:D) (Ge:context)
  (xv:atom) (qg qq qu:usage) (sb:tm) (Gpre Gtail:context),
  Gpre = ctx_mul qq Gsp -> Gtail = ctx_mul qq Gst -> qu = qq*qg ->
  ctx_mul qq (Gsubst sb xv Gsp ++ ctx_mul qg Ge ++ ctx_plus Gst (ctx_mul qg Gt))
  = Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros Gsp Gst Gt De Ge xv qg qq qu sb Gpre Gtail HGp HGt Hqu.
  subst Gpre. subst Gtail. subst qu.
  rewrite ctx_mul_app. rewrite ctx_mul_app.
  rewrite ctx_mul_ctx_mul. rewrite ctx_mul_ctx_plus. rewrite ctx_mul_ctx_mul.
  rewrite <- Gsubst_ctx_mul.
  reflexivity.
Qed.

Lemma hctx_plus_mul_de : forall (Dpre Dtail:D)
  (G1pre G1tail G2pre G2tail Gt Gpre Gtail:context)
  (De:D) (Ge:context) (xv:atom) (q1 q2 qq qu:usage) (sb:tm),
  shapeDG Dpre G1pre -> shapeDG Dpre G2pre ->
  shapeDG Dtail G1tail -> shapeDG Dtail G2tail -> shapeDG Dtail Gt ->
  Gpre = ctx_plus (ctx_mul qq G1pre) G2pre ->
  Gtail = ctx_plus (ctx_mul qq G1tail) G2tail -> qu = qq*q1 + q2 ->
  ctx_plus (ctx_mul qq (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt)))
           (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
  = Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge xv q1 q2 qq qu sb
         H1 H2 H3 H4 H5 HGp HGt Hqu.
  subst Gpre. subst Gtail. subst qu.
  rewrite ctx_mul_app. rewrite ctx_mul_app.
  rewrite ctx_mul_ctx_mul. rewrite ctx_mul_ctx_plus. rewrite ctx_mul_ctx_mul.
  rewrite <- Gsubst_ctx_mul.
  assert (Hlen1 : length (Gsubst sb xv (ctx_mul qq G1pre)) = length (Gsubst sb xv G2pre)).
  { rewrite length_Gsubst. rewrite length_Gsubst. rewrite length_ctx_mul.
    exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre H1 H2)). }
  rewrite (ctx_plus_app (Gsubst sb xv (ctx_mul qq G1pre))
                        ((ctx_mul (qq*q1) Ge) ++ ctx_plus (ctx_mul qq G1tail) (ctx_mul (qq*q1) Gt))
                        (Gsubst sb xv G2pre)
                        ((ctx_mul q2 Ge) ++ ctx_plus G2tail (ctx_mul q2 Gt)) Hlen1).
  rewrite <- Gsubst_ctx_plus.
  assert (Hlen2 : length (ctx_mul (qq*q1) Ge) = length (ctx_mul q2 Ge)).
  { rewrite length_ctx_mul. rewrite length_ctx_mul. reflexivity. }
  rewrite (ctx_plus_app (ctx_mul (qq*q1) Ge) (ctx_plus (ctx_mul qq G1tail) (ctx_mul (qq*q1) Gt))
                        (ctx_mul q2 Ge) (ctx_plus G2tail (ctx_mul q2 Gt)) Hlen2).
  rewrite (ctx_mul_add (qq*q1) q2 Ge).
  rewrite (tail_combine Dtail (ctx_mul qq G1tail) G2tail Gt (qq*q1) q2
             (shapeDG_mul Dtail G1tail qq H3) H4 H5).
  reflexivity.
Qed.

Lemma hctx_plus_mul_r_de : forall (Dpre Dtail:D)
  (G1pre G1tail G2pre G2tail Gt Gpre Gtail:context)
  (De:D) (Ge:context) (xv:atom) (q1 q2 qq qu:usage) (sb:tm),
  shapeDG Dpre G1pre -> shapeDG Dpre G2pre ->
  shapeDG Dtail G1tail -> shapeDG Dtail G2tail -> shapeDG Dtail Gt ->
  Gpre = ctx_plus G1pre (ctx_mul qq G2pre) ->
  Gtail = ctx_plus G1tail (ctx_mul qq G2tail) -> qu = q1 + qq*q2 ->
  ctx_plus (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
           (ctx_mul qq (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt)))
  = Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt).
Proof.
  intros Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge xv q1 q2 qq qu sb
         H1 H2 H3 H4 H5 HGp HGt Hqu.
  subst Gpre. subst Gtail. subst qu.
  rewrite ctx_mul_app. rewrite ctx_mul_app.
  rewrite ctx_mul_ctx_mul. rewrite ctx_mul_ctx_plus. rewrite ctx_mul_ctx_mul.
  assert (Hlen1 : length (Gsubst sb xv G1pre) = length (ctx_mul qq (Gsubst sb xv G2pre))).
  { rewrite length_ctx_mul. rewrite length_Gsubst. rewrite length_Gsubst.
    exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre H1 H2)). }
  rewrite (ctx_plus_app (Gsubst sb xv G1pre)
                        ((ctx_mul q1 Ge) ++ ctx_plus G1tail (ctx_mul q1 Gt))
                        (ctx_mul qq (Gsubst sb xv G2pre))
                        ((ctx_mul (qq*q2) Ge) ++ ctx_plus (ctx_mul qq G2tail) (ctx_mul (qq*q2) Gt)) Hlen1).
  rewrite <- Gsubst_ctx_mul.
  rewrite <- Gsubst_ctx_plus.
  assert (Hlen2 : length (ctx_mul q1 Ge) = length (ctx_mul (qq*q2) Ge)).
  { rewrite length_ctx_mul. rewrite length_ctx_mul. reflexivity. }
  rewrite (ctx_plus_app (ctx_mul q1 Ge) (ctx_plus G1tail (ctx_mul q1 Gt))
                        (ctx_mul (qq*q2) Ge) (ctx_plus (ctx_mul qq G2tail) (ctx_mul (qq*q2) Gt)) Hlen2).
  rewrite (ctx_mul_add q1 (qq*q2) Ge).
  rewrite (tail_combine Dtail G1tail (ctx_mul qq G2tail) Gt q1 (qq*q2)
             H3 (shapeDG_mul Dtail G2tail qq H4) H5).
  reflexivity.
Qed.

Lemma typing_subst_gen_de :
 forall (Dpre:D) (xv:tmvar) (Ax:tm) (Dtail:D) (Gpre Gtail:context)
        (qu:usage) (t:tm) (Ty:tm) (De:D) (Ge:context) (Gt:context) (sb:tm),
 Typing (Dpre ++ (xv,Tm Ax) :: Dtail) (Gpre ++ (xv,(qu,Tm Ax)) :: Gtail) t Ty ->
 shapeDG Dpre Gpre -> shapeDG Dtail Gtail ->
 nodupD (Dpre ++ (xv,Tm Ax) :: Dtail) ->
 shapeDG De Ge ->
 De_ok De (Dpre ++ (xv,Tm Ax) :: Dtail) ->
 xv \notin fv_tm_tm Ax -> lc_tm sb ->
 shapeDG Dtail Gt ->
 Typing (De ++ Dtail) (Ge ++ Gt) sb Ax ->
 Typing (Dsubst sb xv Dpre ++ De ++ Dtail)
        (Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt))
        (subst_tm_tm sb xv t) (subst_tm_tm sb xv Ty).
Proof.
  intros Dpre xv Ax Dtail Gpre Gtail qu t Ty De Ge Gt sb H.
  remember (Dpre ++ (xv,Tm Ax) :: Dtail) as Dd eqn:ED.
  remember (Gpre ++ (xv,(qu,Tm Ax)) :: Gtail) as Gd eqn:EG.
  revert Dpre xv Ax Dtail Gpre Gtail qu De Ge Gt sb ED EG.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros Dpre xv Ax Dtail Gpre Gtail qu De Ge Gt sb ED EG HSpre HStail Hnd HshDe Hok Hfv Hlc HshGt Hb.
  - (* T_sub *)
    pose proof (@typing_align D5 G1 a A0 H1) as Hsh1.
    destruct (shape_split D5 G1 Hsh1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres.
    rewrite ED in Hsub. rewrite HG1 in Hsub. rewrite EG in Hsub.
    destruct (ctx_sub_decomp Dpre xv Ax Dtail G1pre G1tail Gpre Gtail q1 qu
                HS1pre HSpre HS1tail HStail Hsub) as [Hle [Hsubpre Hsubtail]].
    assert (Hnd5 : nodupD (Dpre ++ (xv,Tm Ax) :: Dtail))
      by (rewrite <- ED; exact Hnd).
    assert (Hok5 : De_ok De (Dpre ++ (xv,Tm Ax) :: Dtail))
      by (rewrite <- ED; exact Hok).
    assert (HndDpre : nodupD Dpre)
      by (exact (nodupD_app_l Dpre ((xv,Tm Ax)::Dtail) Hnd5)).
    assert (HndDeDtail : nodupD (De ++ Dtail))
      by (exact (nodupD_De_append De Dpre xv Ax Dtail Hnd5 Hok5)).
    assert (HndDsub : nodupD (Dsubst sb xv Dpre))
      by (exact (proj2 (nodupD_Dsubst sb xv Dpre) HndDpre)).
    assert (Hndp : nodupD (Dsubst sb xv Dpre ++ (De ++ Dtail))).
    { apply nodupD_app.
      - exact HndDsub.
      - exact HndDeDtail.
      - intros z Hz HzDE.
        assert (Hzpre : z \in dom Dpre)
          by (exact (proj1 (in_dom_Dsubst sb xv Dpre z) Hz)).
        rewrite dom_app in HzDE. apply union_iff in HzDE. destruct HzDE as [HzDE|HzDE].
        + assert (Hzbig : z \in dom (Dpre ++ (xv,Tm Ax) :: Dtail)).
          { rewrite dom_app. apply union_iff. left. exact Hzpre. }
          exact ((proj1 Hok5) z HzDE Hzbig).
        + exact ((nodupD_app_disj Dpre ((xv,Tm Ax)::Dtail) z Hnd5 Hzpre)
                   (proj2 (in_dom_cons z xv Ax Dtail) (or_intror HzDE))). }
    assert (Hsubres : ctx_sub (Dsubst sb xv Dpre ++ (De ++ Dtail))
                (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
                (Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt))).
    { apply (ctx_sub_combine (Dsubst sb xv Dpre) (De ++ Dtail)
               (Gsubst sb xv G1pre) (Gsubst sb xv Gpre)
               (ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
               (ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt))).
      - exact Hndp.
      - apply sh_Dsubst. exact HS1pre.
      - apply sh_Dsubst. exact HSpre.
      - apply shapeDG_app.
        + apply shapeDG_mul. exact HshDe.
        + apply shapeDG_plus. exact HS1tail. apply shapeDG_mul. exact HshGt.
      - apply shapeDG_app.
        + apply shapeDG_mul. exact HshDe.
        + apply shapeDG_plus. exact HStail. apply shapeDG_mul. exact HshGt.
      - apply (ctx_sub_Gsubst sb xv Dpre G1pre Gpre Hsubpre).
      - apply (ctx_sub_combine De Dtail
                 (ctx_mul q1 Ge) (ctx_mul qu Ge)
                 (ctx_plus G1tail (ctx_mul q1 Gt)) (ctx_plus Gtail (ctx_mul qu Gt))).
        + exact HndDeDtail.
        + apply shapeDG_mul. exact HshDe.
        + apply shapeDG_mul. exact HshDe.
        + apply shapeDG_plus. exact HS1tail. apply shapeDG_mul. exact HshGt.
        + apply shapeDG_plus. exact HStail. apply shapeDG_mul. exact HshGt.
        + apply (ctx_sub_mul_le De Ge q1 qu HshDe
                   (De_ok_nodupD' De (Dpre ++ (xv,Tm Ax) :: Dtail) Hok5) Hle).
        + apply (ctx_sub_plus_mul Dtail G1tail Gtail Hsubtail Gt HshGt q1 qu Hle). }
    exact (T_sub (Dsubst sb xv Dpre ++ De ++ Dtail)
             (Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt))
             (subst_tm_tm sb xv a) (subst_tm_tm sb xv A0)
             (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
             Hres Hsubres).
  - (* T_type *) destruct Dpre; simpl in ED; discriminate.
  - (* T_var *)
    destruct Dpre as [|[p Ap] Dpre].
    + (* Dpre = nil *)
      simpl in ED. inversion ED; subst.
      assert (Hlen0 : length Gpre = 0%nat).
      { assert (HE := f_equal (@length (atom*(usage*sort))) EG).
        simpl in HE. rewrite !length_app in HE. rewrite length_ctx_mul in HE.
        simpl in HE.
        pose proof (@sh_length_l Dtail G (@typing_align Dtail G Ax a_Type H1)) as HGlen.
        pose proof (@sh_length_l Dtail Gtail HStail) as HGtlen.
        lia. }
      apply length_zero_iff_nil in Hlen0. subst Gpre.
      simpl in EG. injection EG as Hqu0 HGt0. subst qu. subst Gtail.
      assert (Hn : gnames G = gnames Gt).
      { rewrite <- (@sh_names Dtail G (@typing_align Dtail G Ax a_Type H1)).
        rewrite <- (@sh_names Dtail Gt HshGt). reflexivity. }
      assert (Hs : gsorts G = gsorts Gt).
      { rewrite <- (@sh_sorts Dtail G (@typing_align Dtail G Ax a_Type H1)).
        rewrite <- (@sh_sorts Dtail Gt HshGt). reflexivity. }
      rewrite (ctx_plus_zero_one G Gt Hn Hs).
      rewrite (ctx_mul_1 Ge).
      rewrite Dsubst_nil. simpl.
      rewrite (@eq_dec_refl tmvar EqDec_eq_of_X xv). simpl.
      rewrite (subst_fresh Ax sb xv Hfv).
      exact Hb.
    + (* Dpre = p :: Dpre *)
      simpl in ED. injection ED as Hx HA Htail. subst p. subst Ap.
      pose proof (@typing_align D5 G Ax0 a_Type H1) as Hsh.
      destruct (shape_split D5 G Hsh Dpre xv Ax Dtail Htail)
        as [Gs [qg [Gt' [HG [HSg HSg']]]]].
      assert (Hnd5 : nodupD D5)
        by (exact (nodupD_app_r (x ~ Tm Ax0) D5 Hnd)).
      assert (Hok5 : De_ok De D5).
      { change (De_ok De (((x,Tm Ax0)::nil) ++ D5)) in Hok.
        apply (De_ok_shrink_head De x (Tm Ax0) D5 Hok). }
      pose proof (IH1 Dpre xv Ax Dtail Gs Gt' qg De Ge Gt sb Htail HG HSg HSg'
                   Hnd5 HshDe Hok5 Hfv Hlc HshGt Hb) as Hres.
      assert (HC : (x ~ (1,Tm Ax0)) ++ ctx_mul 0 G
                 = ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)
                   ++ (xv,(0*qg,Tm Ax)) :: ctx_mul 0 Gt').
      { rewrite HG. rewrite ctx_mul_split_form. rewrite app_assoc. reflexivity. }
      assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
                 = ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)
                   ++ (xv,(0*qg,Tm Ax)) :: ctx_mul 0 Gt').
      { rewrite <- EG. exact HC. }
      assert (Hlen2 : length Gpre = length ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)).
      { rewrite <- (@sh_length_l ((x,Tm Ax0)::Dpre) Gpre HSpre).
        rewrite length_app. simpl. rewrite length_ctx_mul.
        f_equal. exact (@sh_length_l Dpre Gs HSg). }
      destruct (split_eq_of_length Gpre Gtail ((x ~ (1,Tm Ax0)) ++ ctx_mul 0 Gs)
                  (ctx_mul 0 Gt') xv qu (0*qg) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
      assert (Hctx : Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt)
                 = (x ~ (1,Tm (subst_tm_tm sb xv Ax0)))
                   ++ ctx_mul 0 (Gsubst sb xv Gs ++ ctx_mul qg Ge ++ ctx_plus Gt' (ctx_mul qg Gt))).
      { rewrite HGpre. rewrite HGtail. rewrite Hqu.
        rewrite Gsubst_app. rewrite Gsubst_ctx_mul. simpl.
        rewrite ctx_mul_app. rewrite ctx_mul_app.
        rewrite ctx_mul_ctx_mul. rewrite ctx_mul_ctx_plus. rewrite ctx_mul_ctx_mul.
        reflexivity. }
      assert (Hxnv : x <> xv).
      { intro C.
        assert (Hnin : x \notin dom D5).
        { apply (nodupD_app_disj (x ~ Tm Ax0) D5 x Hnd).
          apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
        assert (Hin : xv \in dom D5).
        { rewrite Htail. rewrite dom_app. apply union_iff. right.
          apply (proj2 (in_dom_cons xv xv Ax Dtail) (or_introl (@Logic.eq_refl atom xv))). }
        subst x. exact (Hnin Hin). }
      assert (Hterm : subst_tm_tm sb xv (a_Var_f x) = a_Var_f x).
      { assert (Hnf : xv \notin fv_tm_tm (a_Var_f x)).
        { simpl. intro C. apply Hxnv. apply singleton_iff in C. exact C. }
        exact (subst_fresh (a_Var_f x) sb xv Hnf). }
      rewrite Hctx. rewrite Hterm. rewrite Dsubst_cons. simpl.
      refine (T_var (Dsubst sb xv Dpre ++ De ++ Dtail) x (subst_tm_tm sb xv Ax0)
                (Gsubst sb xv Gs ++ ctx_mul qg Ge ++ ctx_plus Gt' (ctx_mul qg Gt)) _ Hres).
      intro C. 
      assert (HxDe : x \notin dom De).
      { intro CD.
        assert (Hxbig : x \in dom ((x ~ Tm Ax0) ++ D5)).
        { rewrite dom_app. apply union_iff. left. rewrite dom_cons.
          apply union_iff. left. apply singleton_iff. reflexivity. }
        exact ((proj1 Hok) x CD Hxbig). }
      rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
      * (* x in dom (Dsubst Dpre) *)
        apply Hnotin. rewrite Htail. rewrite dom_app. apply union_iff. left.
        exact (proj1 (in_dom_Dsubst sb xv Dpre x) C).
      * (* x in dom (De ++ Dtail) *)
        rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
        -- exact (HxDe C).
        -- apply Hnotin. rewrite Htail. rewrite dom_app. apply union_iff. right.
           exact (proj2 (in_dom_cons x xv Ax Dtail) (or_intror C)).
  - (* T_weak *)
    destruct Dpre as [|[p Ap] Dpre].
    + (* Dpre = nil *)
      simpl in ED. inversion ED; subst.
      assert (Hlen0 : length Gpre = 0%nat).
      { assert (HE := f_equal (@length (atom*(usage*sort))) EG).
        simpl in HE. rewrite !length_app in HE. simpl in HE.
        pose proof (@sh_length_l Dtail G1 (@typing_align Dtail G1 a B0 H1)) as HGlen.
        pose proof (@sh_length_l Dtail Gtail HStail) as HGtlen.
        lia. }
      apply length_zero_iff_nil in Hlen0. subst Gpre.
      simpl in EG. injection EG as Hqu0 HGt0. subst qu. subst Gtail.
      assert (Hxd : xv \notin dom Dtail).
      { apply (nodupD_app_disj (xv ~ Tm Ax) Dtail xv Hnd).
        apply (proj2 (in_dom_cons xv xv Ax nil) (or_introl (@Logic.eq_refl atom xv))). }
      assert (Hfva : xv \notin fv_tm_tm a).
      { intro C. exact (Hxd ((proj1 (@typing_fv Dtail G1 a B0 H1)) xv C)). }
      assert (HfvB : xv \notin fv_tm_tm B0).
      { intro C. exact (Hxd ((proj2 (@typing_fv Dtail G1 a B0 H1)) xv C)). }
      assert (HokDtail : De_ok De Dtail).
      { exact (De_ok_remove_prefix De (xv ~ Tm Ax) Dtail Hok). }
      pose proof (typing_add_zero_prefix De Ge Dtail G1 a B0 HshDe HokDtail
                    (@typing_env_wf (De ++ Dtail) (Ge ++ Gt) sb Ax Hb) H1) as Hzw.
      rewrite (ctx_plus_zero Dtail G1 Gt (@typing_align Dtail G1 a B0 H1) HshGt).
      rewrite Dsubst_nil. rewrite Gsubst_nil. simpl.
      rewrite (subst_fresh a sb xv Hfva). rewrite (subst_fresh B0 sb xv HfvB).
      exact Hzw.
    + (* Dpre = p :: Dpre *)
      simpl in ED. injection ED as Hx HA Htail. subst p. subst Ap.
      pose proof (@typing_align D5 G1 a B0 H1) as Hsh1.
      destruct (shape_split D5 G1 Hsh1 Dpre xv Ax Dtail Htail)
        as [Gs [qg [Gt' [HG [HSg HSg']]]]].
      pose proof (@typing_align D5 G2 Ax0 a_Type H2) as Hsh2.
      destruct (shape_split D5 G2 Hsh2 Dpre xv Ax Dtail Htail)
        as [G2s [q2 [G2t [HG2 [HS2s HS2t]]]]].
      assert (Hnd5 : nodupD D5)
        by (exact (nodupD_app_r (x ~ Tm Ax0) D5 Hnd)).
      assert (Hok5 : De_ok De D5).
      { change (De_ok De (((x,Tm Ax0)::nil) ++ D5)) in Hok.
        apply (De_ok_shrink_head De x (Tm Ax0) D5 Hok). }
      pose proof (IH1 Dpre xv Ax Dtail Gs Gt' qg De Ge Gt sb Htail HG HSg HSg'
                   Hnd5 HshDe Hok5 Hfv Hlc HshGt Hb) as Hres.
      pose proof (IH2 Dpre xv Ax Dtail G2s G2t q2 De Ge Gt sb Htail HG2 HS2s HS2t
                   Hnd5 HshDe Hok5 Hfv Hlc HshGt Hb) as Hty2.
      assert (HC : (x ~ (0,Tm Ax0)) ++ G1
                 = ((x ~ (0,Tm Ax0)) ++ Gs) ++ (xv,(qg,Tm Ax)) :: Gt').
      { rewrite HG. rewrite app_assoc. reflexivity. }
      assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
                 = ((x ~ (0,Tm Ax0)) ++ Gs) ++ (xv,(qg,Tm Ax)) :: Gt').
      { rewrite <- EG. exact HC. }
      assert (Hlen2 : length Gpre = length ((x ~ (0,Tm Ax0)) ++ Gs)).
      { rewrite <- (@sh_length_l ((x,Tm Ax0)::Dpre) Gpre HSpre).
        rewrite length_app. simpl.
        f_equal. exact (@sh_length_l Dpre Gs HSg). }
      destruct (split_eq_of_length Gpre Gtail ((x ~ (0,Tm Ax0)) ++ Gs) Gt'
                  xv qu qg Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
      assert (Hctx : Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt)
                 = (x ~ (0,Tm (subst_tm_tm sb xv Ax0)))
                   ++ (Gsubst sb xv Gs ++ ctx_mul qg Ge ++ ctx_plus Gt' (ctx_mul qg Gt))).
      { rewrite HGpre. rewrite HGtail. rewrite Hqu.
        rewrite Gsubst_app. simpl. reflexivity. }
      assert (Hxnv : x <> xv).
      { intro C.
        assert (Hnin : x \notin dom D5).
        { apply (nodupD_app_disj (x ~ Tm Ax0) D5 x Hnd).
          apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
        assert (Hin : xv \in dom D5).
        { rewrite Htail. rewrite dom_app. apply union_iff. right.
          apply (proj2 (in_dom_cons xv xv Ax Dtail) (or_introl (@Logic.eq_refl atom xv))). }
        subst x. exact (Hnin Hin). }
      rewrite Hctx. rewrite Dsubst_cons. simpl.
      refine (T_weak (Dsubst sb xv Dpre ++ De ++ Dtail) x (subst_tm_tm sb xv Ax0)
                (Gsubst sb xv Gs ++ ctx_mul qg Ge ++ ctx_plus Gt' (ctx_mul qg Gt))
                (subst_tm_tm sb xv a) (subst_tm_tm sb xv B0)
                (Gsubst sb xv G2s ++ ctx_mul q2 Ge ++ ctx_plus G2t (ctx_mul q2 Gt)) _ Hres Hty2).
      intro C.
      assert (HxDe : x \notin dom De).
      { intro CD.
        assert (Hxbig : x \in dom ((x ~ Tm Ax0) ++ D5)).
        { rewrite dom_app. apply union_iff. left. rewrite dom_cons.
          apply union_iff. left. apply singleton_iff. reflexivity. }
        exact ((proj1 Hok) x CD Hxbig). }
      rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
      * apply Hnotin. rewrite Htail. rewrite dom_app. apply union_iff. left.
        exact (proj1 (in_dom_Dsubst sb xv Dpre x) C).
      * rewrite dom_app in C. apply union_iff in C. destruct C as [C|C].
        -- exact (HxDe C).
        -- apply Hnotin. rewrite Htail. rewrite dom_app. apply union_iff. right.
           exact (proj2 (in_dom_cons x xv Ax Dtail) (or_intror C)).
  - (* T_pi *)
    pose proof (@typing_align D5 G1 A1 a_Type H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L A1 r D5 G2). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G2)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hty1.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge
                 xv q1 q2 qu sb
                 (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre))
                 HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    eapply (T_pi (((L \u dom D5) \u {{xv}}) \u dom De)).
    + exact Hty1.
    + intros y Hy.
      assert (HyOut : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (HyDe : y \notin dom De)
        by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (Hy1 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (Hy2 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (HokExt : De_ok De ((y ~ Tm A1) ++ D5)).
      { apply (De_ok_extend_head De y (Tm A1) D5 Hok HyDe). }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm A1)) ++ G2
                 = ((y ~ (r,Tm A1)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G2pre)).
      { apply (sh_cons y r A1 Dpre G2pre HS2pre). }
      pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (r,Tm A1)) ++ G2pre) G2tail
                    q2 De Ge Gt sb EDy EGy HSpre_y HS2tail Hndy HshDe HokExt Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
  - (* T_lam *)
    pose proof (@typing_align D5 G2 A1 a_Type H2) as Hsh2.
    destruct (shape_split D5 G2 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hty2.
    eapply (T_lam (((L \u dom D5) \u {{xv}}) \u dom De)).
    + intros y Hy.
      assert (HyOut : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (HyDe : y \notin dom De)
        by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (Hy1 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (Hy2 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (HokExt : De_ok De ((y ~ Tm A1) ++ D5)).
      { apply (De_ok_extend_head De y (Tm A1) D5 Hok HyDe). }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (qq,Tm A1)) ++ G1
                 = ((y ~ (qq,Tm A1)) ++ Gpre) ++ (xv,(qu,Tm Ax)) :: Gtail).
      { rewrite EG. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (qq,Tm A1)) ++ Gpre)).
      { apply (sh_cons y qq A1 Dpre Gpre HSpre). }
      pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (qq,Tm A1)) ++ Gpre) Gtail
                    qu De Ge Gt sb EDy EGy HSpre_y HStail Hndy HshDe HokExt Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y a Hlc Hyneq) in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
    + exact Hty2.
  - (* T_app *)
    pose proof (@typing_align D5 G1 a (a_Pi qq A1 B1) H1) as HshG1.
    pose proof (@typing_align D5 G2 b A1 H2) as HshG2.
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres2.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre (ctx_mul qq G2pre)
                 ++ (xv,(q1+qq*q2,Tm Ax)) :: ctx_plus G1tail (ctx_mul qq G2tail)).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_mul_split_form_r G1pre G1tail G2pre G2tail qq xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre (ctx_mul qq G2pre))).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre (ctx_mul qq G2pre))
               (shapeDG_plus Dpre G1pre (ctx_mul qq G2pre) HS1pre
                  (shapeDG_mul Dpre G2pre qq HS2pre))). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre (ctx_mul qq G2pre))
                (ctx_plus G1tail (ctx_mul qq G2tail))
                xv qu (q1+qq*q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_mul_r_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 De Ge xv q1 q2 qq qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B1 xv 0 b).
    refine (T_app (Dsubst sb xv Dpre ++ De ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt)) qq
              (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b)
              (subst_tm_tm sb xv B1) (subst_tm_tm sb xv A1) Hres1 Hres2).
  - (* T_conv *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu De Ge Gt sb ED EG HSpre HStail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (@typing_align D5 G2 B0 a_Type H2) as Hsh2.
    destruct (shape_split D5 G2 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres2.
    eapply T_conv.
    + exact Hres1.
    + exact Hres2.
    + exact (subst_Beta1 sb xv A1 B0 Hlc Hbconv).
  - (* T_unit *) destruct Dpre; simpl in ED; discriminate.
  - (* T_Unit *) destruct Dpre; simpl in ED; discriminate.
  - (* T_UnitE *)
    pose proof (@typing_align D5 G1 a a_TyUnit H1) as HshG1.
    pose proof (@typing_align D5 G2 b B1 H2) as HshG2.
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L a_TyUnit r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm a_TyUnit) ++ D5) ((y ~ (r,Tm a_TyUnit)) ++ G3)
                (open_tm_wrt_tm B0 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres2.
    assert (Heq' : subst_tm_tm sb xv B1 = open_tm_wrt_tm (subst_tm_tm sb xv B0) a_TmUnit).
    { rewrite Heq. rewrite (subst_open_comm sb Hlc B0 xv 0 a_TmUnit). simpl. reflexivity. }
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge
                 xv q1 q2 qu sb
                 (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre))
                 HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B0 xv 0 a).
    refine (T_UnitE (((L \u dom D5) \u {{xv}}) \u dom De)
              (Dsubst sb xv Dpre ++ De ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b) r
              (subst_tm_tm sb xv B0) (subst_tm_tm sb xv B1)
              (Gsubst sb xv G3pre ++ ctx_mul q3 Ge ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Hres1 Heq' Hres2 _).
    intros y Hy.
    assert (HyOut : y \notin (L \u dom D5) \u {{xv}})
      by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
    assert (HyDe : y \notin dom De)
      by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
    assert (Hy1 : y \notin L \u dom D5)
      by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
    assert (Hy2 : y \notin {{xv}})
      by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
    assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
    assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
    assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
    assert (Hndy : nodupD ((y ~ Tm a_TyUnit) ++ D5)).
    { apply nodupD_cons. exact Hnd. exact Hydom. }
    assert (HokExt : De_ok De ((y ~ Tm a_TyUnit) ++ D5)).
    { apply (De_ok_extend_head De y (Tm a_TyUnit) D5 Hok HyDe). }
    assert (EDy : (y ~ Tm a_TyUnit) ++ D5 = ((y ~ Tm a_TyUnit) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
    { rewrite ED. rewrite app_assoc. reflexivity. }
    assert (EGy : (y ~ (r,Tm a_TyUnit)) ++ G3
               = ((y ~ (r,Tm a_TyUnit)) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
    { rewrite HG3. rewrite app_assoc. reflexivity. }
    assert (HSpre_y : shapeDG ((y ~ Tm a_TyUnit) ++ Dpre) ((y ~ (r,Tm a_TyUnit)) ++ G3pre)).
    { apply (sh_cons y r a_TyUnit Dpre G3pre HS3pre). }
    pose proof (IHfun y HyL ((y ~ Tm a_TyUnit) ++ Dpre) xv Ax Dtail
                  ((y ~ (r,Tm a_TyUnit)) ++ G3pre) G3tail q3 De Ge Gt sb
                  EDy EGy HSpre_y HS3tail Hndy HshDe HokExt Hfv Hlc HshGt Hb) as Hbody.
    rewrite Dsubst_app in Hbody.
    rewrite Gsubst_app in Hbody.
    simpl in Hbody.
    rewrite (subst_open_var sb xv y B0 Hlc Hyneq) in Hbody.
    exact Hbody.
  - (* T_Box *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu De Ge Gt sb ED EG HSpre HStail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres.
    apply T_Box. exact Hres.
  - (* T_box *)
    pose proof (@typing_align D5 G a A1 H1) as Hsh.
    destruct (shape_split D5 G Hsh Dpre xv Ax Dtail ED)
      as [Gsp [qg [Gst [HG [HSsp HSst]]]]].
    pose proof (IH1 Dpre xv Ax Dtail Gsp Gst qg De Ge Gt sb ED HG HSsp HSst
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_mul qq Gsp ++ (xv,(qq*qg,Tm Ax)) :: ctx_mul qq Gst).
    { rewrite <- EG. rewrite HG. apply (ctx_mul_split_form qq Gsp Gst xv qg Ax). }
    assert (Hlen2 : length Gpre = length (ctx_mul qq Gsp)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre). rewrite length_ctx_mul.
      exact (sh_length_l Dpre Gsp HSsp). }
    destruct (split_eq_of_length Gpre Gtail (ctx_mul qq Gsp) (ctx_mul qq Gst)
                xv qu (qq*qg) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_mul_de Gsp Gst Gt De Ge xv qg qq qu sb Gpre Gtail HGpre HGtail Hqu).
    apply T_box. exact Hres.
  - (* T_letbox *)
    pose proof (@typing_align D5 G1 a (a_Box qq A1) H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L A1 qq D5 G2). intros x Hx.
      apply (@typing_align ((x ~ Tm A1) ++ D5) ((x ~ (qq,Tm A1)) ++ G2)
                (open_tm_wrt_tm b (a_Var_f x))
                (open_tm_wrt_tm B1 (a_box qq (a_Var_f x))) (Hfun2 x Hx)). }
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L (a_Box qq A1) r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm (a_Box qq A1)) ++ D5) ((y ~ (r,Tm (a_Box qq A1))) ++ G3)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun3 y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge
                 xv q1 q2 qu sb
                 (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre))
                 HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B1 xv 0 a).
    refine (T_letbox (((L \u dom D5) \u {{xv}}) \u dom De)
              (Dsubst sb xv Dpre ++ De ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b) r qq
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv B1)
              (Gsubst sb xv G3pre ++ ctx_mul q3 Ge ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Hres1 _ _).
    + (* second premise: forall x *)
      intros x Hx.
      assert (HxOut : x \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union x ((L \u dom D5) \u {{xv}}) (dom De) Hx))).
      assert (HxDe : x \notin dom De)
        by (exact (proj2 (self_notin_union x ((L \u dom D5) \u {{xv}}) (dom De) Hx))).
      assert (Hx1 : x \notin L \u dom D5)
        by (exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} HxOut))).
      assert (Hx2 : x \notin {{xv}})
        by (exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} HxOut))).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxdom : x \notin dom D5) by (exact (proj2 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      assert (Hndx : nodupD ((x ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hxdom. }
      assert (HokExtX : De_ok De ((x ~ Tm A1) ++ D5)).
      { apply (De_ok_extend_head De x (Tm A1) D5 Hok HxDe). }
      assert (EDx : (x ~ Tm A1) ++ D5 = ((x ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGx : (x ~ (qq,Tm A1)) ++ G2
                 = ((x ~ (qq,Tm A1)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_x : shapeDG ((x ~ Tm A1) ++ Dpre) ((x ~ (qq,Tm A1)) ++ G2pre)).
      { apply (sh_cons x qq A1 Dpre G2pre HS2pre). }
      pose proof (IHfun2 x HxL ((x ~ Tm A1) ++ Dpre) xv Ax Dtail
                    ((x ~ (qq,Tm A1)) ++ G2pre) G2tail q2 De Ge Gt sb
                    EDx EGx HSpre_x HS2tail Hndx HshDe HokExtX Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv x b Hlc Hxneq) in Hbody.
      rewrite (subst_open_comm sb Hlc B1 xv 0 (a_box qq (a_Var_f x))) in Hbody.
      assert (Hnf : xv \notin fv_tm_tm (a_Var_f x)).
      { simpl. intro C. apply Hxneq. apply singleton_iff in C. exact C. }
      assert (Hvx : subst_tm_tm sb xv (a_Var_f x) = a_Var_f x)
        by (apply subst_fresh; exact Hnf).
      assert (Hc : subst_tm_tm sb xv (a_box qq (a_Var_f x)) = a_box qq (a_Var_f x)).
      { change (a_box qq (subst_tm_tm sb xv (a_Var_f x)) = a_box qq (a_Var_f x)).
        rewrite Hvx. reflexivity. }
      rewrite Hc in Hbody.
      exact Hbody.
    + (* third premise: forall y *)
      intros y Hy.
      assert (HyOut : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (HyDe : y \notin dom De)
        by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (Hy1 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (Hy2 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm (a_Box qq A1)) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (HokExtY : De_ok De ((y ~ Tm (a_Box qq A1)) ++ D5)).
      { apply (De_ok_extend_head De y (Tm (a_Box qq A1)) D5 Hok HyDe). }
      assert (EDy : (y ~ Tm (a_Box qq A1)) ++ D5
                 = ((y ~ Tm (a_Box qq A1)) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm (a_Box qq A1))) ++ G3
                 = ((y ~ (r,Tm (a_Box qq A1))) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
      { rewrite HG3. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm (a_Box qq A1)) ++ Dpre)
                         ((y ~ (r,Tm (a_Box qq A1))) ++ G3pre)).
      { apply (sh_cons y r (a_Box qq A1) Dpre G3pre HS3pre). }
      pose proof (IHfun3 y HyL ((y ~ Tm (a_Box qq A1)) ++ Dpre) xv Ax Dtail
                    ((y ~ (r,Tm (a_Box qq A1))) ++ G3pre) G3tail q3 De Ge Gt sb
                    EDy EGy HSpre_y HS3tail Hndy HshDe HokExtY Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
  - (* T_sum *)
    pose proof (@typing_align D5 G1 A1 a_Type H1) as HshG1.
    pose proof (@typing_align D5 G2 A2 a_Type H2) as HshG2.
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres2.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge
                 xv q1 q2 qu sb
                 (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre))
                 HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    eapply T_sum.
    + exact Hres1.
    + exact Hres2.
  - (* T_inj1 *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu De Ge Gt sb ED EG HSpre HStail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (@typing_align D5 G1 A2 a_Type H2) as Hsh2.
    destruct (shape_split D5 G1 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres2.
    exact (T_inj1 (Dsubst sb xv Dpre ++ De ++ Dtail)
                  (Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt))
                  (subst_tm_tm sb xv a) (subst_tm_tm sb xv A1) (subst_tm_tm sb xv A2)
                  (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
                  Hres1 Hres2).
  - (* T_inj2 *)
    pose proof (IH1 Dpre xv Ax Dtail Gpre Gtail qu De Ge Gt sb ED EG HSpre HStail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (@typing_align D5 G1 A1 a_Type H2) as Hsh2.
    destruct (shape_split D5 G1 Hsh2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres2.
    exact (T_inj2 (Dsubst sb xv Dpre ++ De ++ Dtail)
                  (Gsubst sb xv Gpre ++ ctx_mul qu Ge ++ ctx_plus Gtail (ctx_mul qu Gt))
                  (subst_tm_tm sb xv a) (subst_tm_tm sb xv A1) (subst_tm_tm sb xv A2)
                  (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
                  Hres1 Hres2).
  - (* T_case *)
    pose proof (@typing_align D5 G1 a (a_Sum A1 A2) H1) as HshG1.
    pose proof (@typing_align D5 G2 b1 (a_Pi qq A1 B1) H3) as HshG2.
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L (a_Sum A1 A2) r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm (a_Sum A1 A2)) ++ D5)
                ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3)
                (open_tm_wrt_tm B0 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH3 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres3.
    pose proof (IH4 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres4.
    assert (Hinj1 : forall x, x <> xv ->
              subst_tm_tm sb xv (a_Inj1 (a_Var_f x)) = a_Inj1 (a_Var_f x)).
    { intros x Hxneq. apply subst_fresh. simpl. intro C. apply Hxneq.
      apply singleton_iff in C. exact C. }
    assert (Hinj2 : forall x, x <> xv ->
              subst_tm_tm sb xv (a_Inj2 (a_Var_f x)) = a_Inj2 (a_Var_f x)).
    { intros x Hxneq. apply subst_fresh. simpl. intro C. apply Hxneq.
      apply singleton_iff in C. exact C. }
    assert (Heq1' : forall x, x \notin (((L \u dom D5) \u {{xv}}) \u dom De) ->
              open_tm_wrt_tm (subst_tm_tm sb xv B1) (a_Var_f x)
              = open_tm_wrt_tm (subst_tm_tm sb xv B0) (a_Inj1 (a_Var_f x))).
    { intros x Hx.
      assert (HxOut : x \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union x ((L \u dom D5) \u {{xv}}) (dom De) Hx))).
      assert (Hx1 : x \notin L \u dom D5) by (exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} HxOut))).
      assert (Hx2 : x \notin {{xv}}) by (exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} HxOut))).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      rewrite <- (subst_open_var sb xv x B1 Hlc Hxneq).
      rewrite (Heq1 x HxL).
      rewrite (subst_open_comm sb Hlc B0 xv 0 (a_Inj1 (a_Var_f x))).
      rewrite (Hinj1 x Hxneq). reflexivity. }
    assert (Heq2' : forall x, x \notin (((L \u dom D5) \u {{xv}}) \u dom De) ->
              open_tm_wrt_tm (subst_tm_tm sb xv B2) (a_Var_f x)
              = open_tm_wrt_tm (subst_tm_tm sb xv B0) (a_Inj2 (a_Var_f x))).
    { intros x Hx.
      assert (HxOut : x \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union x ((L \u dom D5) \u {{xv}}) (dom De) Hx))).
      assert (Hx1 : x \notin L \u dom D5) by (exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} HxOut))).
      assert (Hx2 : x \notin {{xv}}) by (exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} HxOut))).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      rewrite <- (subst_open_var sb xv x B2 Hlc Hxneq).
      rewrite (Heq2 x HxL).
      rewrite (subst_open_comm sb Hlc B0 xv 0 (a_Inj2 (a_Var_f x))).
      rewrite (Hinj2 x Hxneq). reflexivity. }
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus (ctx_mul qq G1pre) G2pre
                 ++ (xv,(qq*q1+q2,Tm Ax)) :: ctx_plus (ctx_mul qq G1tail) G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_mul_split_form G1pre G1tail G2pre G2tail qq xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus (ctx_mul qq G1pre) G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus (ctx_mul qq G1pre) G2pre)
               (shapeDG_plus Dpre (ctx_mul qq G1pre) G2pre
                  (shapeDG_mul Dpre G1pre qq HS1pre) HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus (ctx_mul qq G1pre) G2pre)
                (ctx_plus (ctx_mul qq G1tail) G2tail)
                xv qu (qq*q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_mul_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 De Ge xv q1 q2 qq qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B0 xv 0 a).
    refine (T_case (((L \u dom D5) \u {{xv}}) \u dom De)
              (Dsubst sb xv Dpre ++ De ++ Dtail) qq
              (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b1) (subst_tm_tm sb xv b2) r
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv A2)
              (subst_tm_tm sb xv B0) (subst_tm_tm sb xv B1) (subst_tm_tm sb xv B2)
              (Gsubst sb xv G3pre ++ ctx_mul q3 Ge ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Hq Hres1 Heq1' Heq2' Hres3 Hres4 _).
    intros y Hy.
    assert (HyOut : y \notin (L \u dom D5) \u {{xv}})
      by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
    assert (HyDe : y \notin dom De)
      by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
    assert (Hy1 : y \notin L \u dom D5)
      by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
    assert (Hy2 : y \notin {{xv}})
      by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
    assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
    assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
    assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
    assert (Hndy : nodupD ((y ~ Tm (a_Sum A1 A2)) ++ D5)).
    { apply nodupD_cons. exact Hnd. exact Hydom. }
    assert (HokExt : De_ok De ((y ~ Tm (a_Sum A1 A2)) ++ D5)).
    { apply (De_ok_extend_head De y (Tm (a_Sum A1 A2)) D5 Hok HyDe). }
    assert (EDy : (y ~ Tm (a_Sum A1 A2)) ++ D5
               = ((y ~ Tm (a_Sum A1 A2)) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
    { rewrite ED. rewrite app_assoc. reflexivity. }
    assert (EGy : (y ~ (r,Tm (a_Sum A1 A2))) ++ G3
               = ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
    { rewrite HG3. rewrite app_assoc. reflexivity. }
    assert (HSpre_y : shapeDG ((y ~ Tm (a_Sum A1 A2)) ++ Dpre)
                       ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3pre)).
    { apply (sh_cons y r (a_Sum A1 A2) Dpre G3pre HS3pre). }
    pose proof (IHfun y HyL ((y ~ Tm (a_Sum A1 A2)) ++ Dpre) xv Ax Dtail
                  ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3pre) G3tail q3 De Ge Gt sb
                  EDy EGy HSpre_y HS3tail Hndy HshDe HokExt Hfv Hlc HshGt Hb) as Hbody.
    rewrite Dsubst_app in Hbody.
    rewrite Gsubst_app in Hbody.
    simpl in Hbody.
    rewrite (subst_open_var sb xv y B0 Hlc Hyneq) in Hbody.
    exact Hbody.
  - (* T_Sigma *)
    pose proof (@typing_align D5 G1 A1 a_Type H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L A1 r D5 G2). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G2)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hty1.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge
                 xv q1 q2 qu sb
                 (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre))
                 HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    eapply (T_Sigma (((L \u dom D5) \u {{xv}}) \u dom De)).
    + exact Hty1.
    + intros y Hy.
      assert (HyOut : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (HyDe : y \notin dom De)
        by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
      assert (Hy1 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (Hy2 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (HokExt : De_ok De ((y ~ Tm A1) ++ D5)).
      { apply (De_ok_extend_head De y (Tm A1) D5 Hok HyDe). }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm A1)) ++ G2
                 = ((y ~ (r,Tm A1)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G2pre)).
      { apply (sh_cons y r A1 Dpre G2pre HS2pre). }
      pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (r,Tm A1)) ++ G2pre) G2tail
                    q2 De Ge Gt sb EDy EGy HSpre_y HS2tail Hndy HshDe HokExt Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
  - (* T_Tensor *)
    pose proof (@typing_align D5 G1 a A1 H1) as HshG1.
    pose proof (@typing_align D5 G2 b (open_tm_wrt_tm B1 a) H2) as HshG2.
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L A1 r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G3)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    pose proof (IH2 Dpre xv Ax Dtail G2pre G2tail q2 De Ge Gt sb ED HG2 HS2pre HS2tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres2.
    rewrite (subst_open_comm sb Hlc B1 xv 0 a) in Hres2.
    assert (Heq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus (ctx_mul qq G1pre) G2pre
                 ++ (xv,(qq*q1+q2,Tm Ax)) :: ctx_plus (ctx_mul qq G1tail) G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_mul_split_form G1pre G1tail G2pre G2tail qq xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus (ctx_mul qq G1pre) G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus (ctx_mul qq G1pre) G2pre)
               (shapeDG_plus Dpre (ctx_mul qq G1pre) G2pre
                  (shapeDG_mul Dpre G1pre qq HS1pre) HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus (ctx_mul qq G1pre) G2pre)
                (ctx_plus (ctx_mul qq G1tail) G2tail)
                xv qu (qq*q1+q2) Ax Hlen2 Heq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_mul_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail
                 De Ge xv q1 q2 qq qu sb HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    refine (T_Tensor (((L \u dom D5) \u {{xv}}) \u dom De)
              (Dsubst sb xv Dpre ++ De ++ Dtail) qq
              (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b)
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv B1)
              (Gsubst sb xv G3pre ++ ctx_mul q3 Ge ++ ctx_plus G3tail (ctx_mul q3 Gt)) r
              Hres1 Hres2 _).
    intros y Hy.
    assert (HyOut : y \notin (L \u dom D5) \u {{xv}})
      by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
    assert (HyDe : y \notin dom De)
      by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (dom De) Hy))).
    assert (Hy1 : y \notin L \u dom D5)
      by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
    assert (Hy2 : y \notin {{xv}})
      by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} HyOut))).
    assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
    assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
    assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
    assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
    { apply nodupD_cons. exact Hnd. exact Hydom. }
    assert (HokExt : De_ok De ((y ~ Tm A1) ++ D5)).
    { apply (De_ok_extend_head De y (Tm A1) D5 Hok HyDe). }
    assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
    { rewrite ED. rewrite app_assoc. reflexivity. }
    assert (EGy : (y ~ (r,Tm A1)) ++ G3
               = ((y ~ (r,Tm A1)) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
    { rewrite HG3. rewrite app_assoc. reflexivity. }
    assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G3pre)).
    { apply (sh_cons y r A1 Dpre G3pre HS3pre). }
    pose proof (IHfun y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail ((y ~ (r,Tm A1)) ++ G3pre) G3tail
                  q3 De Ge Gt sb EDy EGy HSpre_y HS3tail Hndy HshDe HokExt Hfv Hlc HshGt Hb) as Hbody.
    rewrite Dsubst_app in Hbody.
    rewrite Gsubst_app in Hbody.
    simpl in Hbody.
    rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
    exact Hbody.
  - (* T_Spread *)
    pose proof (@typing_align D5 G1 a A1 H1) as HshG1.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv2 L A2 qq D5 G2). intros x Hx y Hy.
      apply (@typing_align ((x ~ Tm A2) ++ D5) ((x ~ (qq,Tm A2)) ++ G2)
                (open_tm_wrt_tm b (a_Var_f x))
                (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                   (close_tm_wrt_tm y (open_tm_wrt_tm B1
                      (a_Tensor (a_Var_f x) (a_Var_f y)))))
                (Hfun2 x Hx y Hy)). }
    assert (HshG3 : shapeDG D5 G3).
    { apply (shapeDG_binder_inv L A1 r D5 G3). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (r,Tm A1)) ++ G3)
                (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun3 y Hy)). }
    destruct (shape_split D5 G1 HshG1 Dpre xv Ax Dtail ED)
      as [G1pre [q1 [G1tail [HG1 [HS1pre HS1tail]]]]].
    destruct (shape_split D5 G2 HshG2 Dpre xv Ax Dtail ED)
      as [G2pre [q2 [G2tail [HG2 [HS2pre HS2tail]]]]].
    destruct (shape_split D5 G3 HshG3 Dpre xv Ax Dtail ED)
      as [G3pre [q3 [G3tail [HG3 [HS3pre HS3tail]]]]].
    pose proof (IH1 Dpre xv Ax Dtail G1pre G1tail q1 De Ge Gt sb ED HG1 HS1pre HS1tail
                 Hnd HshDe Hok Hfv Hlc HshGt Hb) as Hres1.
    assert (Heq' : subst_tm_tm sb xv A1
               = a_Sigma qq (subst_tm_tm sb xv A2) (subst_tm_tm sb xv A3)).
    { rewrite Heq. simpl. reflexivity. }
    assert (HctxEq : Gpre ++ (xv,(qu,Tm Ax)) :: Gtail
               = ctx_plus G1pre G2pre ++ (xv,(q1+q2,Tm Ax)) :: ctx_plus G1tail G2tail).
    { rewrite <- EG. rewrite HG1. rewrite HG2.
      apply (ctx_plus_split_form G1pre G1tail G2pre G2tail xv q1 q2 Ax).
      exact (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre)). }
    assert (Hlen2 : length Gpre = length (ctx_plus G1pre G2pre)).
    { rewrite <- (sh_length_l Dpre Gpre HSpre).
      apply (sh_length_l Dpre (ctx_plus G1pre G2pre)
               (shapeDG_plus Dpre G1pre G2pre HS1pre HS2pre)). }
    destruct (split_eq_of_length Gpre Gtail (ctx_plus G1pre G2pre) (ctx_plus G1tail G2tail)
                xv qu (q1+q2) Ax Hlen2 HctxEq) as [HGpre [Hqu HGtail]].
    rewrite <- (hctx_plus_de Dpre Dtail G1pre G1tail G2pre G2tail Gt Gpre Gtail De Ge
                 xv q1 q2 qu sb
                 (csh_length G1pre G2pre (sh_sym Dpre G1pre G2pre HS1pre HS2pre))
                 HS1pre HS2pre HS1tail HS2tail HshGt HGpre HGtail Hqu).
    rewrite (subst_open_comm sb Hlc B1 xv 0 a).
    refine (T_Spread ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb) \u dom De)
              (Dsubst sb xv Dpre ++ De ++ Dtail)
              (Gsubst sb xv G1pre ++ ctx_mul q1 Ge ++ ctx_plus G1tail (ctx_mul q1 Gt))
              (Gsubst sb xv G2pre ++ ctx_mul q2 Ge ++ ctx_plus G2tail (ctx_mul q2 Gt))
              (subst_tm_tm sb xv a) (subst_tm_tm sb xv b) r
              (subst_tm_tm sb xv A1) (subst_tm_tm sb xv B1) qq
              (subst_tm_tm sb xv A2) (subst_tm_tm sb xv A3)
              (Gsubst sb xv G3pre ++ ctx_mul q3 Ge ++ ctx_plus G3tail (ctx_mul q3 Gt))
              Heq' Hres1 _ _).
    + (* second premise: forall x y *)
      intros x Hx.
      assert (HxBase : x \notin ((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)
        by (exact (proj1 (self_notin_union x ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)) (dom De) Hx))).
      assert (HxDe : x \notin dom De)
        by (exact (proj2 (self_notin_union x ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)) (dom De) Hx))).
      assert (Hxout : x \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union x ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) HxBase))).
      assert (Hxfs : x \notin fv_tm_tm sb)
        by (exact (proj2 (self_notin_union x ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) HxBase))).
      assert (Hx1 : x \notin L \u dom D5)
        by (exact (proj1 (self_notin_union x (L \u dom D5) {{xv}} Hxout))).
      assert (Hx2 : x \notin {{xv}})
        by (exact (proj2 (self_notin_union x (L \u dom D5) {{xv}} Hxout))).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxdom : x \notin dom D5) by (exact (proj2 (self_notin_union x L (dom D5) Hx1))).
      assert (Hxneq : x <> xv) by (exact (self_notin_singleton x xv Hx2)).
      intros y Hy.
      assert (HyBase : y \notin (((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb) \u dom De)
        by (exact (proj1 (self_notin_union y ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb) \u dom De) {{x}} Hy))).
      assert (Hyx : y <> x) by (exact (self_notin_singleton y x (proj2 (self_notin_union y ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb) \u dom De) {{x}} Hy)))).
      assert (HyBase2 : y \notin ((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)
        by (exact (proj1 (self_notin_union y ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)) (dom De) HyBase))).
      assert (HyDe : y \notin dom De)
        by (exact (proj2 (self_notin_union y ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)) (dom De) HyBase))).
      assert (Hyout : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) HyBase2))).
      assert (Hyfs : y \notin fv_tm_tm sb)
        by (exact (proj2 (self_notin_union y ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) HyBase2))).
      assert (Hy1 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hyout))).
      assert (Hy2 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hyout))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (HyLx : y \notin L \u {{x}}).
      { intro C. apply union_iff in C. destruct C as [C|C].
        - exact (HyL C).
        - apply Hyx. apply singleton_iff in C. exact (@Logic.eq_sym atom x y C). }
      assert (Hndx : nodupD ((x ~ Tm A2) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hxdom. }
      assert (HokExtX : De_ok De ((x ~ Tm A2) ++ D5)).
      { apply (De_ok_extend_head De x (Tm A2) D5 Hok HxDe). }
      assert (EDx : (x ~ Tm A2) ++ D5 = ((x ~ Tm A2) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGx : (x ~ (qq,Tm A2)) ++ G2
                 = ((x ~ (qq,Tm A2)) ++ G2pre) ++ (xv,(q2,Tm Ax)) :: G2tail).
      { rewrite HG2. rewrite app_assoc. reflexivity. }
      assert (HSpre_x : shapeDG ((x ~ Tm A2) ++ Dpre) ((x ~ (qq,Tm A2)) ++ G2pre)).
      { change (shapeDG ((x,Tm A2) :: Dpre) ((x,(qq,Tm A2)) :: G2pre)).
        apply (sh_cons x qq A2 Dpre G2pre HS2pre). }
      pose proof (IHfun2 x HxL y HyLx ((x ~ Tm A2) ++ Dpre) xv Ax Dtail
                    ((x ~ (qq,Tm A2)) ++ G2pre) G2tail q2 De Ge Gt sb
                    EDx EGx HSpre_x HS2tail Hndx HshDe HokExtX Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv x b Hlc Hxneq) in Hbody.
      rewrite (subst_open_var sb xv x A3 Hlc Hxneq) in Hbody.
      rewrite (subst_close_rec_comm sb xv y 0
                 (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))
                 Hlc (fun H : xv = y => Hyneq (@Logic.eq_sym atom xv y H)) Hyfs) in Hbody.
      rewrite (subst_open_comm sb Hlc B1 xv 0 (a_Tensor (a_Var_f x) (a_Var_f y))) in Hbody.
      rewrite (subst_tensor_vars sb xv x y Hxneq Hyneq) in Hbody.
      exact Hbody.
    + (* third premise: forall y *)
      intros y Hy.
      assert (HyBase : y \notin ((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)
        by (exact (proj1 (self_notin_union y ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)) (dom De) Hy))).
      assert (HyDe : y \notin dom De)
        by (exact (proj2 (self_notin_union y ((((L \u dom D5) \u {{xv}}) \u fv_tm_tm sb)) (dom De) Hy))).
      assert (Hyout : y \notin (L \u dom D5) \u {{xv}})
        by (exact (proj1 (self_notin_union y ((L \u dom D5) \u {{xv}}) (fv_tm_tm sb) HyBase))).
      assert (Hy1 : y \notin L \u dom D5)
        by (exact (proj1 (self_notin_union y (L \u dom D5) {{xv}} Hyout))).
      assert (Hy2 : y \notin {{xv}})
        by (exact (proj2 (self_notin_union y (L \u dom D5) {{xv}} Hyout))).
      assert (HyL : y \notin L) by (exact (proj1 (self_notin_union y L (dom D5) Hy1))).
      assert (Hydom : y \notin dom D5) by (exact (proj2 (self_notin_union y L (dom D5) Hy1))).
      assert (Hyneq : y <> xv) by (exact (self_notin_singleton y xv Hy2)).
      assert (Hndy : nodupD ((y ~ Tm A1) ++ D5)).
      { apply nodupD_cons. exact Hnd. exact Hydom. }
      assert (HokExtY : De_ok De ((y ~ Tm A1) ++ D5)).
      { apply (De_ok_extend_head De y (Tm A1) D5 Hok HyDe). }
      assert (EDy : (y ~ Tm A1) ++ D5 = ((y ~ Tm A1) ++ Dpre) ++ (xv,Tm Ax) :: Dtail).
      { rewrite ED. rewrite app_assoc. reflexivity. }
      assert (EGy : (y ~ (r,Tm A1)) ++ G3
                 = ((y ~ (r,Tm A1)) ++ G3pre) ++ (xv,(q3,Tm Ax)) :: G3tail).
      { rewrite HG3. rewrite app_assoc. reflexivity. }
      assert (HSpre_y : shapeDG ((y ~ Tm A1) ++ Dpre) ((y ~ (r,Tm A1)) ++ G3pre)).
      { change (shapeDG ((y,Tm A1) :: Dpre) ((y,(r,Tm A1)) :: G3pre)).
        apply (sh_cons y r A1 Dpre G3pre HS3pre). }
      pose proof (IHfun3 y HyL ((y ~ Tm A1) ++ Dpre) xv Ax Dtail
                    ((y ~ (r,Tm A1)) ++ G3pre) G3tail q3 De Ge Gt sb
                    EDy EGy HSpre_y HS3tail Hndy HshDe HokExtY Hfv Hlc HshGt Hb) as Hbody.
      rewrite Dsubst_app in Hbody.
      rewrite Gsubst_app in Hbody.
      simpl in Hbody.
      rewrite (subst_open_var sb xv y B1 Hlc Hyneq) in Hbody.
      exact Hbody.
Qed.

(* ===== inlined from PiWf.v ===== *)
Lemma typing_nodup_local : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> nodupD D0.
Proof.
  intros D0 G a A H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ].
  all: try assumption.
  - apply nodupD_nil.
  - change (nodupD ((x,Tm Ax0) :: D5)). apply nodupD_cons; assumption.
  - change (nodupD ((x,Tm Ax0) :: D5)). apply nodupD_cons; assumption.
  - apply nodupD_nil.
  - apply nodupD_nil.
Qed.

Lemma pi_wf_open_de_beta :
 forall (De Dd:D) (Ge G1 Gt:context) (qt:usage) (At Bt arg T t:tm),
  t = a_Pi qt At Bt ->
  shapeDG De Ge -> De_ok De Dd -> shapeDG Dd Gt ->
  Typing Dd G1 t T -> Beta T a_Type ->
  Typing (De++Dd) (Ge++Gt) arg At ->
  exists Gty, Typing (De++Dd) Gty (open_tm_wrt_tm Bt arg) a_Type.
Proof.
  intros De Dd Ge G1 Gt qt At Bt arg T t Et HshDe Hok HshapeD Hp Hbeta Harg.
  revert De Ge Gt qt At Bt Et Hbeta HshDe Hok HshapeD Harg.
  induction Hp as
  [ D5 G2 a A0 G1b H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1b a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1b G2 qq0 A0 B0 r H_A IHA Hfun IHfun
  | L D5 G1b qq0 A0 a B0 G2 Hfun IHfun H2 IH2
  | D5 G1b qq0 G2 a b B0 A0 H1 IH1 H2 IH2
  | D5 G1b a B0 A1b G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1b G2 a b r B0 B1b G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq0 A0 H1 IH1
  | D5 qq0 G a A0 H1 IH1
  | L D5 G1b G2 a b r qq0 A0 B0 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2 A0 A1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | D5 G a A1b A0 G1b H1 IH1 H2 IH2
  | L D5 qq0 G1b G2 a b1 b2 r A0 A1b B0 B1b B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2 qq0 A0 B0 r H1 IH1 Hfun IHfun
  | L D5 qq0 G1b G2 a b A0 B0 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1b G2 a b r A0 B0 qq0 A1b A2b G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt qt At Bt Et Hbeta HshDe Hok HshapeD Harg.
  - (* T_sub *)
    exact (IH1 De Ge Gt qt At Bt Et Hbeta HshDe Hok HshapeD Harg).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    simpl in HshapeD.
    inversion HshapeD as [| xx qx Axx Dxx Gs HS]; subst.
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (qx,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(qx,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (qx,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    assert (Harg_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5)
                         ((Ge ++ (x ~ (qx,Tm Ax0))) ++ Gs) arg At).
    { rewrite !app_assoc. exact Harg. }
    destruct (IH1 (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0))) Gs qt At Bt
                 (@Logic.eq_refl tm (a_Pi qt At Bt)) Hbeta HshDe_new Hok_new HS Harg_new) as [Gty Hty].
    rewrite app_assoc in Hty.
    eexists. exact Hty.
  - (* T_pi *)
    injection Et as Hq HA HB. subst qq0. subst A0. subst B0.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L At r D5 G2). intros y Hy.
      apply (@typing_align ((y ~ Tm At) ++ D5) ((y ~ (r,Tm At)) ++ G2)
                (open_tm_wrt_tm Bt (a_Var_f y)) a_Type (Hfun y Hy)). }
    pick fresh y for (L \u fv_tm_tm At \u fv_tm_tm Bt \u dom De).
    assert (HyL : y \notin L) by
      (exact (proj1 (self_notin_union y L (fv_tm_tm At \u fv_tm_tm Bt \u dom De) Fr))).
    assert (Hy1 : y \notin fv_tm_tm At \u fv_tm_tm Bt \u dom De) by
      (exact (proj2 (self_notin_union y L (fv_tm_tm At \u fv_tm_tm Bt \u dom De) Fr))).
    assert (HyAt : y \notin fv_tm_tm At) by
      (exact (proj1 (self_notin_union y (fv_tm_tm At) (fv_tm_tm Bt \u dom De) Hy1))).
    assert (Hy2 : y \notin fv_tm_tm Bt \u dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm At) (fv_tm_tm Bt \u dom De) Hy1))).
    assert (HyBt : y \notin fv_tm_tm Bt) by
      (exact (proj1 (self_notin_union y (fv_tm_tm Bt) (dom De) Hy2))).
    assert (HyDe : y \notin dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm Bt) (dom De) Hy2))).
    pose proof (Hfun y HyL) as Hbody.
    assert (Hnd0 : nodupD ((y ~ Tm At) ++ D5)) by
      (exact (@typing_nodup_local ((y ~ Tm At) ++ D5) ((y ~ (r,Tm At)) ++ G2)
                (open_tm_wrt_tm Bt (a_Var_f y)) a_Type Hbody)).
    assert (Hnd : nodupD (nil ++ (y,Tm At) :: D5)) by
      (simpl; change (nodupD ((y,Tm At) :: D5)); exact Hnd0).
    assert (Dok : De_ok De (nil ++ (y,Tm At) :: D5)) by
      (simpl; change (De_ok De ((y,Tm At) :: D5));
       apply (De_ok_extend_head De y (Tm At) D5 Hok HyDe)).
    pose proof (typing_subst_gen_de nil y At D5 nil G2 r (open_tm_wrt_tm Bt (a_Var_f y))
                  a_Type De Ge Gt arg Hbody sh_nil HshG2 Hnd HshDe Dok HyAt
                  (typing_lc _ _ _ _ Harg) HshapeD Harg) as Hres.
    simpl in Hres.
    rewrite (subst_open_self arg y Bt (typing_lc _ _ _ _ Harg) HyBt) in Hres.
    simpl in Hres. eexists. exact Hres.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    exact (IH1 De Ge Gt qt At Bt Et (B_Trans A1b a_Type B0 Hbconv Hbeta)
             HshDe Hok HshapeD Harg).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma pi_wf_open_de :
 forall (De Dd:D) (Ge G1 Gt:context) (qq:usage) (A B arg:tm),
  shapeDG De Ge -> De_ok De Dd ->
  shapeDG Dd Gt ->
  Typing Dd G1 (a_Pi qq A B) a_Type ->
  Typing (De++Dd) (Ge++Gt) arg A ->
  exists Gty, Typing (De++Dd) Gty (open_tm_wrt_tm B arg) a_Type.
Proof.
  intros. eapply pi_wf_open_de_beta with (t := a_Pi qq A B) (T := a_Type).
  - reflexivity.
  - exact H.
  - exact H0.
  - exact H1.
  - exact H2.
  - apply B_Refl. apply lc_a_Type.
  - exact H3.
Qed.

(* ===== inlined from ValueBeta.v ===== *)
(* Well-formedness opening helpers for syntactic type constructors,
   with an extra environment prefix De and target-type Beta T a_Type. *)

Lemma box_wf_open_de_beta :
 forall (De Dd:D) (Ge G1:context) (q:usage) (A T t:tm),
  t = a_Box q A ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De ++ Dd) ->
  Typing Dd G1 t T -> Beta T a_Type ->
  exists G', Typing (De ++ Dd) G' A a_Type.
Proof.
  intros De Dd Ge G1 q A T t Et HshDe Hok Henv Hp Hbeta.
  revert De Ge q A Et Hbeta HshDe Hok Henv.
  induction Hp as
  [ D5 G2 a A0 G1b H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1b a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1b G2 qq0 A0 B0 r H_A IHA Hfun IHfun
  | L D5 G1b qq0 A0 a B0 G2 Hfun IHfun H2 IH2
  | D5 G1b qq0 G2 a b B0 A0 H1 IH1 H2 IH2
  | D5 G1b a B0 A1b G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1b G2 a b r B0 B1b G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq0 A0 H1 IH1
  | D5 qq0 G a A0 H1 IH1
  | L D5 G1b G2 a b r qq0 A0 B0 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2 A0 A1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | L D5 qq0 G1b G2 a b1 b2 r A0 A1b B0 B1b B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2 qq0 A0 B0 r H1 IH1 Hfun IHfun
  | L D5 qq0 G1b G2 a b A0 B0 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1b G2 a b r A0 B0 qq0 A1b A2b G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge q A Et Hbeta HshDe Hok Henv.
  - (* T_sub *)
    exact (IH1 De Ge q A Et Hbeta HshDe Hok Henv).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    simpl in Henv.
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (q, Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(q,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (q,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (q,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    destruct (IH1 (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (q,Tm Ax0))) q A
                 Et Hbeta HshDe_new Hok_new Henv_new)
      as [G' Hty].
    rewrite app_assoc in Hty. eexists. exact Hty.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    exact (IH1 De Ge q A Et (B_Trans A1b a_Type B0 Hbconv Hbeta)
             HshDe Hok Henv).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *)
    injection Et as Hq HA. subst qq0. subst A0.
    pose proof (typing_add_zero_prefix De Ge D5 G A a_Type HshDe Hok Henv H1) as Hw.
    eexists. exact Hw.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma sum_wf_open_de_beta1 :
 forall (De Dd:D) (Ge G1:context) (A1 A2 T t:tm),
  t = a_Sum A1 A2 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De ++ Dd) ->
  Typing Dd G1 t T -> Beta T a_Type ->
  exists G', Typing (De ++ Dd) G' A1 a_Type.
Proof.
  intros De Dd Ge G1 A1 A2 T t Et HshDe Hok Henv Hp Hbeta.
  revert De Ge A1 A2 Et Hbeta HshDe Hok Henv.
  induction Hp as
  [ D5 G2 a A0 G1b H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1b a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1b G2 qq0 A0 B0 r H_A IHA Hfun IHfun
  | L D5 G1b qq0 A0 a B0 G2 Hfun IHfun H2 IH2
  | D5 G1b qq0 G2 a b B0 A0 H1 IH1 H2 IH2
  | D5 G1b a B0 A1b G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1b G2 a b r B0 B1b G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq0 A0 H1 IH1
  | D5 qq0 G a A0 H1 IH1
  | L D5 G1b G2 a b r qq0 A0 B0 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2 A0 A1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | L D5 qq0 G1b G2 a b1 b2 r A0 A1b B0 B1b B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2 qq0 A0 B0 r H1 IH1 Hfun IHfun
  | L D5 qq0 G1b G2 a b A0 B0 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1b G2 a b r A0 B0 qq0 A1b A2b G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge A1 A2 Et Hbeta HshDe Hok Henv.
  - exact (IH1 De Ge A1 A2 Et Hbeta HshDe Hok Henv).
  - discriminate Et.
  - discriminate Et.
  - simpl in Henv.
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0, Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (0,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    destruct (IH1 (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) A1 A2
                 Et Hbeta HshDe_new Hok_new Henv_new) as [G' Hty].
    rewrite app_assoc in Hty. eexists. exact Hty.
  - discriminate Et.
  - discriminate Et.
  - discriminate Et.
  - exact (IH1 De Ge A1 A2 Et (B_Trans A1b a_Type B0 Hbconv Hbeta)
             HshDe Hok Henv).
  - discriminate Et. (* T_unit *)
  - discriminate Et. (* T_Unit *)
  - discriminate Et. (* T_UnitE *)
  - discriminate Et. (* T_Box *)
  - discriminate Et. (* T_box *)
  - discriminate Et. (* T_letbox *)
  - (* T_sum *)
    injection Et as HA1 HA2. subst A0. subst A1b.
    pose proof (typing_add_zero_prefix De Ge D5 G1b A1 a_Type HshDe Hok Henv H1) as Hw.
    eexists. exact Hw.
  - discriminate Et. (* T_inj1 *)
  - discriminate Et. (* T_inj2 *)
  - discriminate Et. (* T_case *)
  - discriminate Et. (* T_Sigma *)
  - discriminate Et. (* T_Tensor *)
  - discriminate Et. (* T_Spread *)
Qed.

Lemma sum_wf_open_de_beta2 :
 forall (De Dd:D) (Ge G1:context) (A1 A2 T t:tm),
  t = a_Sum A1 A2 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De ++ Dd) ->
  Typing Dd G1 t T -> Beta T a_Type ->
  exists G', Typing (De ++ Dd) G' A2 a_Type.
Proof.
  intros De Dd Ge G1 A1 A2 T t Et HshDe Hok Henv Hp Hbeta.
  revert De Ge A1 A2 Et Hbeta HshDe Hok Henv.
  induction Hp as
  [ D5 G2 a A0 G1b H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1b a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1b G2 qq0 A0 B0 r H_A IHA Hfun IHfun
  | L D5 G1b qq0 A0 a B0 G2 Hfun IHfun H2 IH2
  | D5 G1b qq0 G2 a b B0 A0 H1 IH1 H2 IH2
  | D5 G1b a B0 A1b G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1b G2 a b r B0 B1b G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq0 A0 H1 IH1
  | D5 qq0 G a A0 H1 IH1
  | L D5 G1b G2 a b r qq0 A0 B0 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2 A0 A1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | L D5 qq0 G1b G2 a b1 b2 r A0 A1b B0 B1b B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2 qq0 A0 B0 r H1 IH1 Hfun IHfun
  | L D5 qq0 G1b G2 a b A0 B0 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1b G2 a b r A0 B0 qq0 A1b A2b G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge A1 A2 Et Hbeta HshDe Hok Henv.
  - exact (IH1 De Ge A1 A2 Et Hbeta HshDe Hok Henv).
  - discriminate Et.
  - discriminate Et.
  - simpl in Henv.
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0, Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (0,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    destruct (IH1 (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) A1 A2
                 Et Hbeta HshDe_new Hok_new Henv_new) as [G' Hty].
    rewrite app_assoc in Hty. eexists. exact Hty.
  - discriminate Et.
  - discriminate Et.
  - discriminate Et.
  - exact (IH1 De Ge A1 A2 Et (B_Trans A1b a_Type B0 Hbconv Hbeta)
             HshDe Hok Henv).
  - discriminate Et. (* T_unit *)
  - discriminate Et. (* T_Unit *)
  - discriminate Et. (* T_UnitE *)
  - discriminate Et. (* T_Box *)
  - discriminate Et. (* T_box *)
  - discriminate Et. (* T_letbox *)
  - (* T_sum *)
    injection Et as HA1 HA2. subst A0. subst A1b.
    pose proof (typing_add_zero_prefix De Ge D5 G2 A2 a_Type HshDe Hok Henv H2) as Hw.
    eexists. exact Hw.
  - discriminate Et. (* T_inj1 *)
  - discriminate Et. (* T_inj2 *)
  - discriminate Et. (* T_case *)
  - discriminate Et. (* T_Sigma *)
  - discriminate Et. (* T_Tensor *)
  - discriminate Et. (* T_Spread *)
Qed.

Lemma sigma_wf_open_de_beta1 :
 forall (De Dd:D) (Ge G1:context) (q:usage) (A B T t:tm),
  t = a_Sigma q A B ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De ++ Dd) ->
  Typing Dd G1 t T -> Beta T a_Type ->
  exists G', Typing (De ++ Dd) G' A a_Type.
Proof.
  intros De Dd Ge G1 q A B T t Et HshDe Hok Henv Hp Hbeta.
  revert De Ge q A B Et Hbeta HshDe Hok Henv.
  induction Hp as
  [ D5 G2 a A0 G1b H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1b a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1b G2 qq0 A0 B0 r H_A IHA Hfun IHfun
  | L D5 G1b qq0 A0 a B0 G2 Hfun IHfun H2 IH2
  | D5 G1b qq0 G2 a b B0 A0 H1 IH1 H2 IH2
  | D5 G1b a B0 A1b G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1b G2 a b r B0 B1b G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq0 A0 H1 IH1
  | D5 qq0 G a A0 H1 IH1
  | L D5 G1b G2 a b r qq0 A0 B0 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2 A0 A1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | L D5 qq0 G1b G2 a b1 b2 r A0 A1b B0 B1b B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2 qq0 A0 B0 r H1 IH1 Hfun IHfun
  | L D5 qq0 G1b G2 a b A0 B0 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1b G2 a b r A0 B0 qq0 A1b A2b G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge q A B Et Hbeta HshDe Hok Henv.
  - (* T_sub *)
    exact (IH1 De Ge q A B Et Hbeta HshDe Hok Henv).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    simpl in Henv.
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (q, Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(q,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (q,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (q,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    destruct (IH1 (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (q,Tm Ax0))) q A B
                 Et Hbeta HshDe_new Hok_new Henv_new)
      as [G' Hty].
    rewrite app_assoc in Hty. eexists. exact Hty.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    exact (IH1 De Ge q A B Et (B_Trans A1b a_Type B0 Hbconv Hbeta)
             HshDe Hok Henv).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *)
    injection Et as Hq HA HB. subst qq0. subst A0. subst B0.
    pose proof (typing_add_zero_prefix De Ge D5 G1b A a_Type HshDe Hok Henv H1) as Hw.
    eexists. exact Hw.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

(* ===== inlined from LamBeta.v ===== *)
Lemma typing_nodup_lb : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> nodupD D0.
Proof.
  intros D0 G a A H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ].
  all: try assumption.
  - apply nodupD_nil.
  - change (nodupD ((x,Tm Ax0) :: D5)). apply nodupD_cons; assumption.
  - change (nodupD ((x,Tm Ax0) :: D5)). apply nodupD_cons; assumption.
  - apply nodupD_nil.
  - apply nodupD_nil.
Qed.

Lemma Beta_open_arg : forall (BL B1 arg:tm) (x:tmvar),
  Beta (open_tm_wrt_tm BL (a_Var_f x)) (open_tm_wrt_tm B1 (a_Var_f x)) ->
  x \notin fv_tm_tm BL -> x \notin fv_tm_tm B1 -> lc_tm arg ->
  Beta (open_tm_wrt_tm BL arg) (open_tm_wrt_tm B1 arg).
Proof.
  intros BL B1 arg x HB HxL Hx1 Hlc.
  pose proof (subst_Beta1 arg x (open_tm_wrt_tm BL (a_Var_f x))
                (open_tm_wrt_tm B1 (a_Var_f x)) Hlc HB) as Hb.
  rewrite (subst_open_self arg x BL Hlc HxL) in Hb.
  rewrite (subst_open_self arg x B1 Hlc Hx1) in Hb.
  exact Hb.
Qed.

Lemma ctx_sub_scaled : forall (De Dd:D) (Ge G1 G1pre Gt:context) (q:usage),
  De_ok De Dd -> shapeDG De Ge -> shapeDG Dd Gt -> shapeDG Dd G1pre -> nodupD Dd ->
  ctx_sub Dd G1pre G1 ->
  ctx_sub (De++Dd) (ctx_mul q Ge ++ ctx_plus G1pre (ctx_mul q Gt))
                      (ctx_mul q Ge ++ ctx_plus G1 (ctx_mul q Gt)).
Proof.
  intros De Dd Ge G1 G1pre Gt q Hok HshDe HshD Hsh1pre Hnd Hsub.
  assert (Hndall : nodupD (De++Dd)).
  { apply nodupD_app.
    - exact (proj2 Hok).
    - exact Hnd.
    - intros y Hy. exact (proj1 Hok y Hy). }
  assert (Hsubpre : ctx_sub Dd G1pre G1) by exact Hsub.
  assert (Hshape1 : shapeDG Dd G1pre) by exact Hsh1pre.
  assert (HshapeG1 : shapeDG Dd G1) by (apply (ctx_sub_shape Dd G1pre G1 Hsub Hsh1pre)).
  assert (HshPu : shapeDG De (ctx_mul q Ge)) by (apply shapeDG_mul; exact HshDe).
  assert (HshPt : shapeDG Dd (ctx_plus G1pre (ctx_mul q Gt)))
    by (apply shapeDG_plus; [exact Hshape1 | apply shapeDG_mul; exact HshD]).
  assert (HshPt' : shapeDG Dd (ctx_plus G1 (ctx_mul q Gt)))
    by (apply shapeDG_plus; [exact HshapeG1 | apply shapeDG_mul; exact HshD]).
  eapply ctx_sub_combine with (D1:=De) (D2:=Dd)
    (G1:=ctx_mul q Ge) (G1':=ctx_mul q Ge)
    (G2:=ctx_plus G1pre (ctx_mul q Gt)) (G2':=ctx_plus G1 (ctx_mul q Gt)).
  - exact Hndall.
  - exact HshPu.
  - exact HshPu.
  - exact HshPt.
  - exact HshPt'.
  - apply ctx_sub_refl_nodup; [exact HshPu | exact (proj2 Hok)].
  - apply (ctx_sub_plus_mul Dd G1pre G1 Hsub Gt HshD q q (ule_refl q)).
Qed.

Lemma lam_beta_wf_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context) (Gty:context)
        (q0:usage) (A0 body:tm) (qq:usage) (A1 B1 arg:tm),
  tm0 = a_Lam q0 A0 body ->
  shapeDG De Ge -> De_ok De Dd -> shapeDG Dd Gt ->
  Typing Dd G1 tm0 TT ->
  Beta TT (a_Pi qq A1 B1) ->
  Typing (De++Dd) Gty (open_tm_wrt_tm B1 arg) a_Type ->
  Typing (De++Dd) (Ge++Gt) arg A1 ->
  Typing (De++Dd) (ctx_mul qq Ge ++ ctx_plus G1 (ctx_mul qq Gt))
         (open_tm_wrt_tm body arg) (open_tm_wrt_tm B1 arg).
Proof.
  intros tm0 TT De Dd Ge G1 Gt Gty q0 A0 body qq A1 B1 arg Et HshDe Hok HshD H1 Hbeta Hwf Harg.
  revert De Ge Gt Gty q0 A0 body Et HshDe Hok HshD Hbeta Hwf Harg.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0b G2b Hnotin H1b IH1b H2b IH2b
  | L D5 G1b G2b qqB A1b B1b r H1b IH1b Hfun IHfun
  | L D5 G1b qL AL a B0b G2b Hfun IHfun H2b IH2b
  | D5 G1b qqB G2b a b B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0b A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | L D5 G1b G2b a b r B0b B1b G3 H1b IH1b Heq H2b IH2b Hfun IHfun
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | L D5 G1b G2b a b r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | L D5 qqB G1b G2b a b1 b2 r A1b A2b B0b B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2b qqB A1b B1b r H1b IH1b Hfun IHfun
  | L D5 qqB G1b G2b a b A1b B1b G3 r H1b IH1b H2b IH2b Hfun IHfun
  | L D5 G1b G2b a b r A1b B1b qqB A2b A3b G3 Heq H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt Gty q0 A0 body Et HshDe Hok HshD Hbeta Hwf Harg.
  - (* T_sub *)
    assert (Hres := IH1b De Ge Gt Gty q0 A0 body Et HshDe Hok HshD Hbeta Hwf Harg).
    assert (Hsh1b : shapeDG D5 G1b) by (apply (@typing_align D5 G1b a A0b H1b)).
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsubc := ctx_sub_scaled De D5 Ge G2b G1b Gt qq Hok HshDe HshD Hsh1b Hnd5 Hsub).
    exact (T_sub (De++D5) (ctx_mul qq Ge ++ ctx_plus G2b (ctx_mul qq Gt))
             (open_tm_wrt_tm body arg) (open_tm_wrt_tm B1 arg)
             (ctx_mul qq Ge ++ ctx_plus G1b (ctx_mul qq Gt)) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    simpl in HshD.
    inversion HshD as [| xx qx Axx Dxx Gs HS]; subst.
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (qx,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(qx,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (qx,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    assert (Hwf_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gty
                        (open_tm_wrt_tm B1 arg) a_Type).
    { rewrite app_assoc. exact Hwf. }
    assert (Harg_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5)
                         ((Ge ++ (x ~ (qx,Tm Ax0))) ++ Gs) arg A1).
    { rewrite !app_assoc. exact Harg. }
    assert (Hres := IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0)))
                    Gs Gty q0 A0 body (@Logic.eq_refl tm (a_Lam q0 A0 body))
                    HshDe_new Hok_new HS Hbeta Hwf_new Harg_new).
    rewrite app_assoc in Hres.
    assert (Hctx : ctx_mul qq (Ge ++ (x ~ (qx,Tm Ax0))) ++ ctx_plus G1b (ctx_mul qq Gs)
                 = ctx_mul qq Ge ++ ctx_plus ((x ~ (0,Tm Ax0)) ++ G1b)
                     (ctx_mul qq ((x ~ (qx,Tm Ax0)) ++ Gs))).
    { rewrite !ctx_mul_app. simpl. rewrite qplus_0_l. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres.
    exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *)
    injection Et as Hq HA Ha. subst qL. subst AL. subst a.
    pose proof (invert_Beta_a_Pi0 Hbeta) as Hqeq.
    pose proof (invert_Beta_a_Pi1 Hbeta) as HBA.
    assert (HshG1 : shapeDG D5 G1b).
    { apply (shapeDG_binder_inv L A0 q0 D5 G1b). intros y Hy.
      apply (@typing_align ((y ~ Tm A0) ++ D5) ((y ~ (q0,Tm A0)) ++ G1b)
                (open_tm_wrt_tm body (a_Var_f y)) (open_tm_wrt_tm B0b (a_Var_f y))
                (Hfun y Hy)). }
    pick fresh y for (L \u fv_tm_tm A0 \u fv_tm_tm body \u fv_tm_tm B0b \u dom De).
    assert (HyL : y \notin L) by
      (exact (proj1 (self_notin_union y L (fv_tm_tm A0 \u fv_tm_tm body \u fv_tm_tm B0b \u dom De) Fr))).
    assert (Hyrest : y \notin fv_tm_tm A0 \u fv_tm_tm body \u fv_tm_tm B0b \u dom De) by
      (exact (proj2 (self_notin_union y L (fv_tm_tm A0 \u fv_tm_tm body \u fv_tm_tm B0b \u dom De) Fr))).
    assert (HyA0 : y \notin fv_tm_tm A0) by
      (exact (proj1 (self_notin_union y (fv_tm_tm A0) (fv_tm_tm body \u fv_tm_tm B0b \u dom De) Hyrest))).
    assert (Hyrest2 : y \notin fv_tm_tm body \u fv_tm_tm B0b \u dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm A0) (fv_tm_tm body \u fv_tm_tm B0b \u dom De) Hyrest))).
    assert (Hybody : y \notin fv_tm_tm body) by
      (exact (proj1 (self_notin_union y (fv_tm_tm body) (fv_tm_tm B0b \u dom De) Hyrest2))).
    assert (Hyrest3 : y \notin fv_tm_tm B0b \u dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm body) (fv_tm_tm B0b \u dom De) Hyrest2))).
    assert (HyB0 : y \notin fv_tm_tm B0b) by
      (exact (proj1 (self_notin_union y (fv_tm_tm B0b) (dom De) Hyrest3))).
    assert (HyDe : y \notin dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm B0b) (dom De) Hyrest3))).
    pose proof (Hfun y HyL) as Hbody.
    assert (Hndbody : nodupD ((y ~ Tm A0) ++ D5)) by
      (exact (@typing_nodup_lb ((y ~ Tm A0) ++ D5) ((y ~ (q0,Tm A0)) ++ G1b)
                (open_tm_wrt_tm body (a_Var_f y)) (open_tm_wrt_tm B0b (a_Var_f y)) Hbody)).
    assert (Hndy : nodupD (nil ++ (y,Tm A0) :: D5)) by
      (simpl; change (nodupD ((y,Tm A0) :: D5)); exact Hndbody).
    assert (Dok : De_ok De (nil ++ (y,Tm A0) :: D5)) by
      (simpl; change (De_ok De ((y,Tm A0) :: D5));
       apply (De_ok_extend_head De y (Tm A0) D5 Hok HyDe)).
    assert (HtyAw : Typing (De++D5) (ctx_mul 0 Ge ++ G2b) A0 a_Type).
    { apply (typing_add_zero_prefix De Ge D5 G2b A0 a_Type HshDe Hok
               (typing_env_wf _ _ _ _ Harg) H2b). }
    assert (ArgAL : Typing (De++D5) (Ge++Gt) arg A0).
    { exact (T_conv (De++D5) (Ge++Gt) arg A0 A1 (ctx_mul 0 Ge ++ G2b) Harg HtyAw (B_Sym A1 A0 HBA)). }
    pose proof (typing_subst_gen_de nil y A0 D5 nil G1b q0 (open_tm_wrt_tm body (a_Var_f y))
                  (open_tm_wrt_tm B0b (a_Var_f y)) De Ge Gt arg Hbody sh_nil HshG1
                  Hndy HshDe Dok HyA0 (typing_lc _ _ _ _ Harg) HshD ArgAL) as Hres.
    simpl in Hres.
    rewrite (subst_open_self arg y body (typing_lc _ _ _ _ Harg) Hybody) in Hres.
    rewrite (subst_open_self arg y B0b (typing_lc _ _ _ _ Harg) HyB0) in Hres.
    rewrite Hqeq in Hres.
    pick fresh x for (fv_tm_tm B0b \u fv_tm_tm B1).
    assert (Hxf : x \notin fv_tm_tm B0b \u fv_tm_tm B1) by assumption.
    assert (Hx0 : x \notin fv_tm_tm B0b) by
      (exact (proj1 (self_notin_union x (fv_tm_tm B0b) (fv_tm_tm B1) Hxf))).
    assert (Hx1 : x \notin fv_tm_tm B1) by
      (exact (proj2 (self_notin_union x (fv_tm_tm B0b) (fv_tm_tm B1) Hxf))).
    pose proof (invert_Beta_a_Pi2 Hbeta x (notin_union x (fv_tm_tm B0b) (fv_tm_tm B1) Hx0 Hx1)) as HBx.
    pose proof (Beta_open_arg B0b B1 arg x HBx Hx0 Hx1 (typing_lc _ _ _ _ Harg)) as HBarg.
    exact (T_conv (De++D5) (ctx_mul qq Ge ++ ctx_plus G1b (ctx_mul qq Gt))
             (open_tm_wrt_tm body arg) (open_tm_wrt_tm B1 arg)
             (open_tm_wrt_tm B0b arg) Gty Hres Hwf HBarg).
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    exact (IH1b De Ge Gt Gty q0 A0 body Et HshDe Hok HshD
             (B_Trans A1b (a_Pi qq A1 B1) B0b Hbconv Hbeta) Hwf Harg).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma lam_beta_noWF_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context)
        (q0:usage) (A0 body:tm) (qq:usage) (A1 B1 arg:tm),
  tm0 = a_Lam q0 A0 body -> TT = a_Pi qq A1 B1 ->
  shapeDG De Ge -> De_ok De Dd -> shapeDG Dd Gt ->
  Typing Dd G1 tm0 TT ->
  Typing (De++Dd) (Ge++Gt) arg A1 ->
  Typing (De++Dd) (ctx_mul qq Ge ++ ctx_plus G1 (ctx_mul qq Gt))
         (open_tm_wrt_tm body arg) (open_tm_wrt_tm B1 arg).
Proof.
  intros tm0 TT De Dd Ge G1 Gt q0 A0 body qq A1 B1 arg Et ET HshDe Hok HshD H1 Harg.
  revert De Ge Gt q0 A0 body Et ET HshDe Hok HshD Harg.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0b G2b Hnotin H1b IH1b H2b IH2b
  | L D5 G1b G2b qqB A1b B1b r H1b IH1b Hfun IHfun
  | L D5 G1b qL AL a B0b G2b Hfun IHfun H2b IH2b
  | D5 G1b qqB G2b a b B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0b A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | L D5 G1b G2b a b r B0b B1b G3 H1b IH1b Heq H2b IH2b Hfun IHfun
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | L D5 G1b G2b a b r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | L D5 qqB G1b G2b a b1 b2 r A1b A2b B0b B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2b qqB A1b B1b r H1b IH1b Hfun IHfun
  | L D5 qqB G1b G2b a b A1b B1b G3 r H1b IH1b H2b IH2b Hfun IHfun
  | L D5 G1b G2b a b r A1b B1b qqB A2b A3b G3 Heq H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt q0 A0 body Et ET HshDe Hok HshD Harg.
  - (* T_sub *)
    assert (Hres := IH1b De Ge Gt q0 A0 body Et ET HshDe Hok HshD Harg).
    assert (Hsh1b : shapeDG D5 G1b) by (apply (@typing_align D5 G1b a A0b H1b)).
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsubc := ctx_sub_scaled De D5 Ge G2b G1b Gt qq Hok HshDe HshD Hsh1b Hnd5 Hsub).
    exact (T_sub (De++D5) (ctx_mul qq Ge ++ ctx_plus G2b (ctx_mul qq Gt))
             (open_tm_wrt_tm body arg) (open_tm_wrt_tm B1 arg)
             (ctx_mul qq Ge ++ ctx_plus G1b (ctx_mul qq Gt)) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    simpl in HshD.
    inversion HshD as [| xx qx Axx Dxx Gs HS]; subst.
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (qx,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(qx,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (qx,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    assert (Harg_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5)
                         ((Ge ++ (x ~ (qx,Tm Ax0))) ++ Gs) arg A1).
    { rewrite !app_assoc. exact Harg. }
    assert (Hres := IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0)))
                    Gs q0 A0 body (@Logic.eq_refl tm (a_Lam q0 A0 body))
                    (@Logic.eq_refl tm (a_Pi qq A1 B1))
                    HshDe_new Hok_new HS Harg_new).
    rewrite app_assoc in Hres.
    assert (Hctx : ctx_mul qq (Ge ++ (x ~ (qx,Tm Ax0))) ++ ctx_plus G1b (ctx_mul qq Gs)
                 = ctx_mul qq Ge ++ ctx_plus ((x ~ (0,Tm Ax0)) ++ G1b)
                     (ctx_mul qq ((x ~ (qx,Tm Ax0)) ++ Gs))).
    { rewrite !ctx_mul_app. simpl. rewrite qplus_0_l. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *)
    injection Et as Hq HA Ha. subst qL. subst AL. subst a.
    injection ET as Hqq HAL HBL. subst q0. subst A0. subst B0b.
    assert (HshG1 : shapeDG D5 G1b).
    { apply (shapeDG_binder_inv L A1 qq D5 G1b). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ D5) ((y ~ (qq,Tm A1)) ++ G1b)
                (open_tm_wrt_tm body (a_Var_f y)) (open_tm_wrt_tm B1 (a_Var_f y))
                (Hfun y Hy)). }
    pick fresh y for (L \u fv_tm_tm A1 \u fv_tm_tm body \u fv_tm_tm B1 \u dom De).
    assert (HyL : y \notin L) by
      (exact (proj1 (self_notin_union y L (fv_tm_tm A1 \u fv_tm_tm body \u fv_tm_tm B1 \u dom De) Fr))).
    assert (Hyrest : y \notin fv_tm_tm A1 \u fv_tm_tm body \u fv_tm_tm B1 \u dom De) by
      (exact (proj2 (self_notin_union y L (fv_tm_tm A1 \u fv_tm_tm body \u fv_tm_tm B1 \u dom De) Fr))).
    assert (HyA1 : y \notin fv_tm_tm A1) by
      (exact (proj1 (self_notin_union y (fv_tm_tm A1) (fv_tm_tm body \u fv_tm_tm B1 \u dom De) Hyrest))).
    assert (Hyrest2 : y \notin fv_tm_tm body \u fv_tm_tm B1 \u dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm A1) (fv_tm_tm body \u fv_tm_tm B1 \u dom De) Hyrest))).
    assert (Hybody : y \notin fv_tm_tm body) by
      (exact (proj1 (self_notin_union y (fv_tm_tm body) (fv_tm_tm B1 \u dom De) Hyrest2))).
    assert (Hyrest3 : y \notin fv_tm_tm B1 \u dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm body) (fv_tm_tm B1 \u dom De) Hyrest2))).
    assert (HyB1 : y \notin fv_tm_tm B1) by
      (exact (proj1 (self_notin_union y (fv_tm_tm B1) (dom De) Hyrest3))).
    assert (HyDe : y \notin dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm B1) (dom De) Hyrest3))).
    pose proof (Hfun y HyL) as Hbody.
    assert (Hndbody : nodupD ((y ~ Tm A1) ++ D5)) by
      (exact (@typing_nodup_lb ((y ~ Tm A1) ++ D5) ((y ~ (qq,Tm A1)) ++ G1b)
                (open_tm_wrt_tm body (a_Var_f y)) (open_tm_wrt_tm B1 (a_Var_f y)) Hbody)).
    assert (Hndy : nodupD (nil ++ (y,Tm A1) :: D5)) by
      (simpl; change (nodupD ((y,Tm A1) :: D5)); exact Hndbody).
    assert (Dok : De_ok De (nil ++ (y,Tm A1) :: D5)) by
      (simpl; change (De_ok De ((y,Tm A1) :: D5));
       apply (De_ok_extend_head De y (Tm A1) D5 Hok HyDe)).
    pose proof (typing_subst_gen_de nil y A1 D5 nil G1b qq (open_tm_wrt_tm body (a_Var_f y))
                  (open_tm_wrt_tm B1 (a_Var_f y)) De Ge Gt arg Hbody sh_nil HshG1
                  Hndy HshDe Dok HyA1 (typing_lc _ _ _ _ Harg) HshD Harg) as Hres.
    simpl in Hres.
    rewrite (subst_open_self arg y body (typing_lc _ _ _ _ Harg) Hybody) in Hres.
    rewrite (subst_open_self arg y B1 (typing_lc _ _ _ _ Harg) HyB1) in Hres.
    exact Hres.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    rewrite ET in H2b.
    rewrite ET in Hbconv.
    destruct (pi_wf_open_de De D5 Ge G2b Gt qq A1 B1 arg HshDe Hok HshD H2b Harg)
      as [Gty Hwf].
    exact (lam_beta_wf_gen a A1b De D5 Ge G1b Gt Gty q0 A0 body qq A1 B1 arg
             Et HshDe Hok HshD H1b Hbconv Hwf Harg).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma lam_beta_noWF_de :
 forall (De Dd:D) (Ge G1 Gt:context) (q0:usage) (A0 body:tm) (qq:usage) (A1 B1 arg:tm),
  shapeDG De Ge -> De_ok De Dd -> shapeDG Dd Gt ->
  Typing Dd G1 (a_Lam q0 A0 body) (a_Pi qq A1 B1) ->
  Typing (De++Dd) (Ge++Gt) arg A1 ->
  Typing (De++Dd) (ctx_mul qq Ge ++ ctx_plus G1 (ctx_mul qq Gt))
         (open_tm_wrt_tm body arg) (open_tm_wrt_tm B1 arg).
Proof.
  intros. eapply (lam_beta_noWF_gen (a_Lam q0 A0 body) (a_Pi qq A1 B1)).
  - reflexivity.
  - reflexivity.
  - exact H.
  - exact H0.
  - exact H1.
  - exact H2.
  - exact H3.
Qed.

Lemma lam_beta_wf_de :
 forall (De Dd:D) (Ge G1 Gt:context) (q0:usage) (A0 body:tm) (T:tm)
        (Gty:context) (qq:usage) (A1 B1 arg:tm),
  shapeDG De Ge -> De_ok De Dd -> shapeDG Dd Gt ->
  Typing Dd G1 (a_Lam q0 A0 body) T ->
  Beta T (a_Pi qq A1 B1) ->
  Typing (De++Dd) Gty (open_tm_wrt_tm B1 arg) a_Type ->
  Typing (De++Dd) (Ge++Gt) arg A1 ->
  Typing (De++Dd) (ctx_mul qq Ge ++ ctx_plus G1 (ctx_mul qq Gt))
         (open_tm_wrt_tm body arg) (open_tm_wrt_tm B1 arg).
Proof.
  intros. eapply (lam_beta_wf_gen (a_Lam q0 A0 body) T).
  - reflexivity.
  - exact H.
  - exact H0.
  - exact H1.
  - exact H2.
  - exact H3.
  - exact H4.
  - exact H5.
Qed.

(* ===== inlined from BoxBeta.v ===== *)
Lemma box_wf_inner : forall (Dd:D) (Gty:context) (qq:usage) (A1:tm),
  Typing Dd Gty (a_Box qq A1) a_Type ->
  exists G', Typing Dd G' A1 a_Type.
Proof.
  intros Dd Gty qq A1 H.
  destruct (box_wf_open_de_beta nil Dd nil Gty qq A1 a_Type (a_Box qq A1)) as [G' HG'].
  - reflexivity.
  - apply sh_nil.
  - apply De_ok_nil.
  - apply (typing_env_wf _ _ _ _ H).
  - exact H.
  - apply B_Refl. apply lc_a_Type.
  - exists G'. simpl in HG'. exact HG'.
Qed.

Lemma ctx_sub_box : forall (De Dd:D) (Ge G1 G1pre Gt:context),
  De_ok De Dd -> nodupD Dd -> shapeDG De Ge -> shapeDG Dd G1pre ->
  shapeDG (De++Dd) Gt -> ctx_sub Dd G1pre G1 ->
  ctx_sub (De++Dd) (ctx_plus (ctx_mul 0 Ge ++ G1pre) Gt)
                      (ctx_plus (ctx_mul 0 Ge ++ G1) Gt).
Proof.
  intros De Dd Ge G1 G1pre Gt Hok Hnd HshDe Hsh1pre HshGt Hsub.
  assert (Hndall : nodupD (De++Dd)).
  { apply nodupD_app.
    - exact (De_ok_nodupD' De Dd Hok).
    - exact Hnd.
    - intros y Hy. exact (proj1 Hok y Hy). }
  assert (HshG1 : shapeDG Dd G1) by (apply (ctx_sub_shape Dd G1pre G1 Hsub Hsh1pre)).
  assert (HshPre : shapeDG (De++Dd) (ctx_mul 0 Ge ++ G1pre)).
  { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact Hsh1pre]. }
  assert (HshPre' : shapeDG (De++Dd) (ctx_mul 0 Ge ++ G1)).
  { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact HshG1]. }
  assert (HpreSub : ctx_sub (De++Dd) (ctx_mul 0 Ge ++ G1pre) (ctx_mul 0 Ge ++ G1)).
  { apply (ctx_sub_combine De Dd (ctx_mul 0 Ge) (ctx_mul 0 Ge) G1pre G1).
    - exact Hndall.
    - apply shapeDG_mul; exact HshDe.
    - apply shapeDG_mul; exact HshDe.
    - exact Hsh1pre.
    - exact HshG1.
    - apply ctx_sub_refl_nodup; [apply shapeDG_mul; exact HshDe | exact (De_ok_nodupD' De Dd Hok)].
    - exact Hsub. }
  assert (HtailSub := ctx_sub_plus_mul (De++Dd) (ctx_mul 0 Ge ++ G1pre)
             (ctx_mul 0 Ge ++ G1) HpreSub Gt HshGt 1 1 (ule_refl 1)).
  simpl in HtailSub. rewrite ctx_mul_1 in HtailSub. exact HtailSub.
Qed.

Lemma De_ok_append_cons : forall (De:D) (y:atom) (A:sort) (D0:D),
  De_ok De ((y,A)::D0) -> y \notin dom De -> y \notin dom D0 ->
  De_ok (De ++ (y,A)::nil) D0.
Proof.
  intros De y A D0 [Hdis Hnd] HyDe HyD0. destruct A as [A]. split.
  - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
    destruct Hz as [Hz|Hz].
    + apply (Hdis z Hz). rewrite dom_cons. apply union_iff. right. exact C.
    + change (z \in dom ((y,A)::nil)) in Hz.
      apply (proj1 (in_dom_cons z y A nil)) in Hz.
      destruct Hz as [Hz|Hz]; [subst z; exact (HyD0 C) | exact (in_dom_nil z Hz)].
  - apply nodupD_app.
    + exact Hnd.
    + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil y).
    + intros z Hz C. change (z \in dom ((y,A)::nil)) in C.
      apply (proj1 (in_dom_cons z y A nil)) in C.
      destruct C as [C|C]; [subst z; exact (HyDe Hz) | exact (in_dom_nil z C)].
Qed.

Lemma box_beta_wf_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context) (Gty:context)
        (q qq:usage) (A1 a0 b B1:tm) (L:atoms),
  tm0 = a_box q a0 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  Beta TT (a_Box qq A1) ->
  Typing (De++Dd) Gty (a_Box qq A1) a_Type ->
  (forall x, x \notin L ->
     Typing ((x ~ Tm A1) ++ (De++Dd)) ((x ~ (qq,Tm A1)) ++ Gt)
       (open_tm_wrt_tm b (a_Var_f x))
       (open_tm_wrt_tm B1 (a_box qq (a_Var_f x)))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul 0 Ge ++ G1) Gt)
         (open_tm_wrt_tm b a0) (open_tm_wrt_tm B1 (a_box qq a0)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt Gty q qq A1 a0 b B1 L Et HshDe Hok Henv H1 Hbeta Hwf Hfun.
  revert De Ge Gt Gty q qq A1 a0 b B1 L Et HshDe Hok Henv Hbeta Hwf Hfun.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0b G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0b G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1 B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0b A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1 r B0b B1b G3 H1b IH1b Heq H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1 r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1 b2 r A1b A2b B0b B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3 IH3 H4 IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1 A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1 r A1b B1b qqB A2b A3b G3 Heq H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt Gty q qq A1 a0 b B1 L Et HshDe Hok Henv Hbeta Hwf Hfun.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt Gty q qq A1 a0 b B1 L Et HshDe Hok Henv Hbeta Hwf Hfun) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (HshGt : shapeDG (De++D5) Gt).
    { apply (shapeDG_binder_inv L A1 qq (De++D5) Gt). intros x Hx.
      apply (@typing_align ((x ~ Tm A1) ++ (De++D5)) ((x ~ (qq,Tm A1)) ++ Gt)
                (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B1 (a_box qq (a_Var_f x))) (Hfun x Hx)). }
    assert (Hsubc := ctx_sub_box De D5 Ge G2b G1b Gt Hok Hnd5 HshDe Hsh1b HshGt Hsub).
    exact (T_sub (De++D5) (ctx_plus (ctx_mul 0 Ge ++ G2b) Gt)
             (open_tm_wrt_tm b a0) (open_tm_wrt_tm B1 (a_box qq a0))
             (ctx_plus (ctx_mul 0 Ge ++ G1b) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _]. assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hfun_new : forall y, y \notin L ->
       Typing ((y ~ Tm A1) ++ ((De ++ (x ~ Tm Ax0)) ++ D5))
         ((y ~ (qq,Tm A1)) ++ Gt) (open_tm_wrt_tm b (a_Var_f y))
         (open_tm_wrt_tm B1 (a_box qq (a_Var_f y)))).
    { intros y Hy. rewrite app_assoc. exact (Hfun y Hy). }
    assert (Hwf_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gty (a_Box qq A1) a_Type).
    { rewrite app_assoc. exact Hwf. }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt Gty q qq A1
                  a0 b B1 L Et HshDe_new Hok_new Henv_new Hbeta Hwf_new Hfun_new) as Hres.
    assert (Hctx : ctx_plus (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b) Gt
                 = ctx_plus (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b)) Gt).
    { rewrite ctx_mul_app.
      assert (Hsm : ctx_mul 0 (x ~ (0,Tm Ax0)) = (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_cons. simpl. rewrite qmul_0_l. reflexivity. }
      rewrite Hsm. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite <- app_assoc. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    pose proof (IH1b De Ge Gt Gty q qq A1 a0 b B1 L Et HshDe Hok Henv
                  (B_Trans A1b (a_Box qq A1) B0b Hbconv Hbeta) Hwf Hfun) as Hres.
    exact Hres.
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *)
    injection Et as Hq Ha. subst q. subst a0.
    assert (Hqq : qqB = qq) by (apply (invert_Beta_Box2 Hbeta)).
    subst qqB. assert (HA : Beta A1b A1) by (apply (invert_Beta_Box1 Hbeta)).
    assert (HshG0 : shapeDG D5 Gb) by (exact (@typing_align D5 Gb a A1b H1b)).
    pose proof (@typing_add_zero_prefix De Ge D5 Gb a A1b HshDe Hok Henv H1b) as Hpayfull0.
    assert (Hboxwf : exists G', Typing (De++D5) G' A1 a_Type).
    { apply (box_wf_open_de_beta nil (De++D5) nil Gty qq A1 a_Type (a_Box qq A1)).
      - reflexivity.
      - apply sh_nil.
      - apply De_ok_nil.
      - apply (typing_env_wf _ _ _ _ Hwf).
      - exact Hwf.
      - apply B_Refl. apply lc_a_Type. }
    destruct Hboxwf as [Gw HwfA].
    assert (HpayA1 : Typing (De++D5) (ctx_mul 0 Ge ++ Gb) a A1).
      { exact (T_conv (De++D5) (ctx_mul 0 Ge ++ Gb) a A1 A1b Gw Hpayfull0 HwfA HA). }
    assert (HshG0full : shapeDG (De++D5) (ctx_mul 0 Ge ++ Gb)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact HshG0]. }
    pick fresh x for (L \u fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De).
    assert (HxL : x \notin L) by
      (exact (proj1 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))).
    pose proof (Hfun x HxL) as Hbody.
    assert (HshGt : shapeDG (De++D5) Gt).
    { apply (shapeDG_binder_inv L A1 qq (De++D5) Gt). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ (De++D5)) ((y ~ (qq,Tm A1)) ++ Gt)
                (open_tm_wrt_tm b (a_Var_f y)) (open_tm_wrt_tm B1 (a_box qq (a_Var_f y))) (Hfun y Hy)). }
    assert (Hndbody : nodupD ((x ~ Tm A1) ++ (De++D5))) by (exact (@typing_nodup_lb ((x ~ Tm A1) ++ (De++D5)) ((x ~ (qq,Tm A1)) ++ Gt) (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B1 (a_box qq (a_Var_f x))) Hbody)).
    assert (Hndy : nodupD (nil ++ (x,Tm A1) :: (De++D5))) by (simpl; change (nodupD ((x,Tm A1) :: (De++D5))); exact Hndbody).
    assert (HyA1 : x \notin fv_tm_tm A1).
    { assert (Hrest : x \notin fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) by
        (exact (proj2 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))).
      exact (proj1 (self_notin_union x (fv_tm_tm A1) (fv_tm_tm b \u fv_tm_tm B1 \u dom De) Hrest)). }
    assert (Hxb : x \notin fv_tm_tm b).
    { assert (Hrest : x \notin fv_tm_tm b \u fv_tm_tm B1 \u dom De) by
        (exact (proj2 (self_notin_union x (fv_tm_tm A1) (fv_tm_tm b \u fv_tm_tm B1 \u dom De)
                 (proj2 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))))).
      exact (proj1 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u dom De) Hrest)). }
    assert (HxB1 : x \notin fv_tm_tm B1).
    { assert (Hrest : x \notin fv_tm_tm B1 \u dom De) by
        (exact (proj2 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u dom De)
                 (proj2 (self_notin_union x (fv_tm_tm A1) (fv_tm_tm b \u fv_tm_tm B1 \u dom De)
                   (proj2 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))))))).
      exact (proj1 (self_notin_union x (fv_tm_tm B1) (dom De) Hrest)). }
    pose proof (typing_subst_gen nil x A1 (De++D5) nil Gt qq
                  (open_tm_wrt_tm b (a_Var_f x))
                  (open_tm_wrt_tm B1 (a_box qq (a_Var_f x)))
                  (ctx_mul 0 Ge ++ Gb) a
                  Hbody sh_nil HshGt Hndy HyA1 (typing_lc _ _ _ _ HpayA1)
                  HshG0full HpayA1) as Hres.
    simpl in Hres.
    rewrite (subst_open_self a x b (typing_lc _ _ _ _ HpayA1) Hxb) in Hres.
    rewrite (subst_open_comm a (typing_lc _ _ _ _ HpayA1) B1 x 0 (a_box qq (a_Var_f x))) in Hres.
    rewrite (subst_fresh B1 a x HxB1) in Hres.
    assert (Hc : subst_tm_tm a x (a_box qq (a_Var_f x)) = a_box qq a).
    { change (a_box qq (subst_tm_tm a x (a_Var_f x)) = a_box qq a).
      rewrite (subst_var_self a x). reflexivity. }
    rewrite Hc in Hres.
    assert (Hctx : ctx_plus Gt (ctx_mul qq (ctx_mul 0 Ge ++ Gb))
                 = ctx_plus (ctx_mul 0 Ge ++ ctx_mul qq Gb) Gt).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r.
      apply (ctx_plus_comm_shape2 (De++D5) Gt
               (ctx_mul 0 Ge ++ ctx_mul qq Gb)).
      - exact HshGt.
      - apply shapeDG_app; [apply shapeDG_mul; exact HshDe | apply shapeDG_mul; exact HshG0]. }
    rewrite Hctx in Hres. exact Hres.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma box_beta_noWF_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context)
        (q qq:usage) (A1 a0 b B1:tm) (L:atoms),
  tm0 = a_box q a0 ->
  TT = a_Box qq A1 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  (forall x, x \notin L ->
     Typing ((x ~ Tm A1) ++ (De++Dd)) ((x ~ (qq,Tm A1)) ++ Gt)
       (open_tm_wrt_tm b (a_Var_f x))
       (open_tm_wrt_tm B1 (a_box qq (a_Var_f x)))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul 0 Ge ++ G1) Gt)
         (open_tm_wrt_tm b a0) (open_tm_wrt_tm B1 (a_box qq a0)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt q qq A1 a0 b B1 L Et ET HshDe Hok Henv H1 Hfun.
  revert De Ge Gt q qq A1 a0 b B1 L Et ET HshDe Hok Henv Hfun.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0b G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0b G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1 B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0b A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1 r B0b B1b G3 H1b IH1b Heq H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1 r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1 b2 r A1b A2b B0b B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3 IH3 H4 IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1 A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1 r A1b B1b qqB A2b A3b G3 Heq H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt q qq A1 a0 b B1 L Et ET HshDe Hok Henv Hfun.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt q qq A1 a0 b B1 L Et ET HshDe Hok Henv Hfun) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (HshGt : shapeDG (De++D5) Gt).
    { apply (shapeDG_binder_inv L A1 qq (De++D5) Gt). intros x Hx.
      apply (@typing_align ((x ~ Tm A1) ++ (De++D5)) ((x ~ (qq,Tm A1)) ++ Gt)
                (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B1 (a_box qq (a_Var_f x))) (Hfun x Hx)). }
    assert (Hsubc := ctx_sub_box De D5 Ge G2b G1b Gt Hok Hnd5 HshDe Hsh1b HshGt Hsub).
    exact (T_sub (De++D5) (ctx_plus (ctx_mul 0 Ge ++ G2b) Gt)
             (open_tm_wrt_tm b a0) (open_tm_wrt_tm B1 (a_box qq a0))
             (ctx_plus (ctx_mul 0 Ge ++ G1b) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _]. assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hfun_new : forall y, y \notin L ->
       Typing ((y ~ Tm A1) ++ ((De ++ (x ~ Tm Ax0)) ++ D5))
         ((y ~ (qq,Tm A1)) ++ Gt) (open_tm_wrt_tm b (a_Var_f y))
         (open_tm_wrt_tm B1 (a_box qq (a_Var_f y)))).
    { intros y Hy. rewrite app_assoc. exact (Hfun y Hy). }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt q qq A1
                  a0 b B1 L Et ET HshDe_new Hok_new Henv_new Hfun_new) as Hres.
    assert (Hctx : ctx_plus (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b) Gt
                 = ctx_plus (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b)) Gt).
    { rewrite ctx_mul_app.
      assert (Hsm : ctx_mul 0 (x ~ (0,Tm Ax0)) = (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_cons. simpl. rewrite qmul_0_l. reflexivity. }
      rewrite Hsm. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite <- app_assoc. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    rewrite ET in H2b.
    rewrite ET in Hbconv.
    pose proof (typing_add_zero_prefix De Ge D5 G2b (a_Box qq A1) a_Type
                  HshDe Hok Henv H2b) as Hwf.
    exact (box_beta_wf_gen a A1b De D5 Ge G1b Gt (ctx_mul 0 Ge ++ G2b)
             q qq A1 a0 b B1 L Et HshDe Hok Henv H1b Hbconv Hwf Hfun).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *)
    injection Et as Hq Ha.
    injection ET as Hqq HAL.
    subst q. subst a0. subst qqB. subst A1b.
    assert (HshG0 : shapeDG D5 Gb) by (exact (@typing_align D5 Gb a A1 H1b)).
    pose proof (@typing_add_zero_prefix De Ge D5 Gb a A1 HshDe Hok Henv H1b) as Hpayfull0.
    assert (HshG0full : shapeDG (De++D5) (ctx_mul 0 Ge ++ Gb)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact HshG0]. }
    pick fresh x for (L \u fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De).
    assert (HxL : x \notin L) by
      (exact (proj1 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))).
    pose proof (Hfun x HxL) as Hbody.
    assert (HshGt : shapeDG (De++D5) Gt).
    { apply (shapeDG_binder_inv L A1 qq (De++D5) Gt). intros y Hy.
      apply (@typing_align ((y ~ Tm A1) ++ (De++D5)) ((y ~ (qq,Tm A1)) ++ Gt)
                (open_tm_wrt_tm b (a_Var_f y)) (open_tm_wrt_tm B1 (a_box qq (a_Var_f y))) (Hfun y Hy)). }
    assert (Hndbody : nodupD ((x ~ Tm A1) ++ (De++D5))) by (exact (@typing_nodup_lb ((x ~ Tm A1) ++ (De++D5)) ((x ~ (qq,Tm A1)) ++ Gt) (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B1 (a_box qq (a_Var_f x))) Hbody)).
    assert (Hndy : nodupD (nil ++ (x,Tm A1) :: (De++D5))) by (simpl; change (nodupD ((x,Tm A1) :: (De++D5))); exact Hndbody).
    assert (HyA1 : x \notin fv_tm_tm A1).
    { assert (Hrest : x \notin fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) by
        (exact (proj2 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))).
      exact (proj1 (self_notin_union x (fv_tm_tm A1) (fv_tm_tm b \u fv_tm_tm B1 \u dom De) Hrest)). }
    assert (Hxb : x \notin fv_tm_tm b).
    { assert (Hrest : x \notin fv_tm_tm b \u fv_tm_tm B1 \u dom De) by
        (exact (proj2 (self_notin_union x (fv_tm_tm A1) (fv_tm_tm b \u fv_tm_tm B1 \u dom De)
                 (proj2 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))))).
      exact (proj1 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u dom De) Hrest)). }
    assert (HxB1 : x \notin fv_tm_tm B1).
    { assert (Hrest : x \notin fv_tm_tm B1 \u dom De) by
        (exact (proj2 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u dom De)
                 (proj2 (self_notin_union x (fv_tm_tm A1) (fv_tm_tm b \u fv_tm_tm B1 \u dom De)
                   (proj2 (self_notin_union x L (fv_tm_tm A1 \u fv_tm_tm b \u fv_tm_tm B1 \u dom De) Fr))))))).
      exact (proj1 (self_notin_union x (fv_tm_tm B1) (dom De) Hrest)). }
    pose proof (typing_subst_gen nil x A1 (De++D5) nil Gt qq
                  (open_tm_wrt_tm b (a_Var_f x))
                  (open_tm_wrt_tm B1 (a_box qq (a_Var_f x)))
                  (ctx_mul 0 Ge ++ Gb) a
                  Hbody sh_nil HshGt Hndy HyA1 (typing_lc _ _ _ _ Hpayfull0)
                  HshG0full Hpayfull0) as Hres.
    simpl in Hres.
    rewrite (subst_open_self a x b (typing_lc _ _ _ _ Hpayfull0) Hxb) in Hres.
    rewrite (subst_open_comm a (typing_lc _ _ _ _ Hpayfull0) B1 x 0 (a_box qq (a_Var_f x))) in Hres.
    rewrite (subst_fresh B1 a x HxB1) in Hres.
    assert (Hc : subst_tm_tm a x (a_box qq (a_Var_f x)) = a_box qq a).
    { change (a_box qq (subst_tm_tm a x (a_Var_f x)) = a_box qq a).
      rewrite (subst_var_self a x). reflexivity. }
    rewrite Hc in Hres.
    assert (Hctx : ctx_plus Gt (ctx_mul qq (ctx_mul 0 Ge ++ Gb))
                 = ctx_plus (ctx_mul 0 Ge ++ ctx_mul qq Gb) Gt).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r.
      apply (ctx_plus_comm_shape2 (De++D5) Gt
               (ctx_mul 0 Ge ++ ctx_mul qq Gb)).
      - exact HshGt.
      - apply shapeDG_app; [apply shapeDG_mul; exact HshDe | apply shapeDG_mul; exact HshG0]. }
    rewrite Hctx in Hres. exact Hres.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma box_beta_typing :
 forall (D:D) (G1:context) (q qq:usage) (A1:tm) (a0 b:tm) (G2:context) (B1:tm) (L:atoms),
  Typing D G1 (a_box q a0) (a_Box qq A1) ->
  (forall x, x \notin L ->
     Typing ((x ~ Tm A1) ++ D) ((x ~ (qq,Tm A1)) ++ G2)
       (open_tm_wrt_tm b (a_Var_f x))
       (open_tm_wrt_tm B1 (a_box qq (a_Var_f x)))) ->
  Typing D (ctx_plus G1 G2) (open_tm_wrt_tm b a0)
    (open_tm_wrt_tm B1 (a_box qq a0)).
Proof.
  intros D G1 q qq A1 a0 b G2 B1 L H1 Hfun.
  pose proof (box_beta_noWF_gen (a_box q a0) (a_Box qq A1) nil D nil G1 G2
                q qq A1 a0 b B1 L
                (@Logic.eq_refl tm (a_box q a0)) (@Logic.eq_refl tm (a_Box qq A1))
                sh_nil (De_ok_nil D) (typing_env_wf D G1 (a_box q a0) (a_Box qq A1) H1)
                H1 Hfun) as Hres.
  simpl in Hres. exact Hres.
Qed.

(* ===== inlined from InjCaseBeta.v ===== *)
Lemma open_inj1_eq : forall (B0 B1 a0:tm) (L:atoms),
  (forall x, x \notin L -> open_tm_wrt_tm B1 (a_Var_f x)
       = open_tm_wrt_tm B0 (a_Inj1 (a_Var_f x))) ->
  lc_tm a0 -> open_tm_wrt_tm B1 a0 = open_tm_wrt_tm B0 (a_Inj1 a0).
Proof.
  intros B0 B1 a0 L Heq Hlc.
  pick fresh x for (L \u fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm B0).
  assert (Hrest : x \notin L \u fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm B0) by assumption.
  assert (HxL : x \notin L) by
    (exact (proj1 (self_notin_union x L (fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm B0) Hrest))).
  assert (Hrest2 : x \notin fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm B0) by
    (exact (proj2 (self_notin_union x L (fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm B0) Hrest))).
  assert (Hxa : x \notin fv_tm_tm a0) by
    (exact (proj1 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm B1 \u fv_tm_tm B0) Hrest2))).
  assert (Hrest3 : x \notin fv_tm_tm B1 \u fv_tm_tm B0) by
    (exact (proj2 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm B1 \u fv_tm_tm B0) Hrest2))).
  assert (HxB1 : x \notin fv_tm_tm B1) by
    (exact (proj1 (self_notin_union x (fv_tm_tm B1) (fv_tm_tm B0) Hrest3))).
  assert (HxB0 : x \notin fv_tm_tm B0) by
    (exact (proj2 (self_notin_union x (fv_tm_tm B1) (fv_tm_tm B0) Hrest3))).
  pose proof (Heq x HxL) as Hx.
  assert (Hx' := f_equal (subst_tm_tm a0 x) Hx).
  rewrite (subst_open_self a0 x B1 Hlc HxB1) in Hx'.
  rewrite (subst_open_comm a0 Hlc B0 x 0 (a_Inj1 (a_Var_f x))) in Hx'.
  rewrite (subst_fresh B0 a0 x HxB0) in Hx'.
  assert (Hc : subst_tm_tm a0 x (a_Inj1 (a_Var_f x)) = a_Inj1 a0).
  { change (a_Inj1 (subst_tm_tm a0 x (a_Var_f x)) = a_Inj1 a0).
    rewrite (subst_var_self a0 x). reflexivity. }
  rewrite Hc in Hx'. exact Hx'.
Qed.

Lemma open_inj2_eq : forall (B0 B2 a0:tm) (L:atoms),
  (forall x, x \notin L -> open_tm_wrt_tm B2 (a_Var_f x)
       = open_tm_wrt_tm B0 (a_Inj2 (a_Var_f x))) ->
  lc_tm a0 -> open_tm_wrt_tm B2 a0 = open_tm_wrt_tm B0 (a_Inj2 a0).
Proof.
  intros B0 B2 a0 L Heq Hlc.
  pick fresh x for (L \u fv_tm_tm a0 \u fv_tm_tm B2 \u fv_tm_tm B0).
  assert (Hrest : x \notin L \u fv_tm_tm a0 \u fv_tm_tm B2 \u fv_tm_tm B0) by assumption.
  assert (HxL : x \notin L) by
    (exact (proj1 (self_notin_union x L (fv_tm_tm a0 \u fv_tm_tm B2 \u fv_tm_tm B0) Hrest))).
  assert (Hrest2 : x \notin fv_tm_tm a0 \u fv_tm_tm B2 \u fv_tm_tm B0) by
    (exact (proj2 (self_notin_union x L (fv_tm_tm a0 \u fv_tm_tm B2 \u fv_tm_tm B0) Hrest))).
  assert (Hxa : x \notin fv_tm_tm a0) by
    (exact (proj1 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm B2 \u fv_tm_tm B0) Hrest2))).
  assert (Hrest3 : x \notin fv_tm_tm B2 \u fv_tm_tm B0) by
    (exact (proj2 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm B2 \u fv_tm_tm B0) Hrest2))).
  assert (HxB2 : x \notin fv_tm_tm B2) by
    (exact (proj1 (self_notin_union x (fv_tm_tm B2) (fv_tm_tm B0) Hrest3))).
  assert (HxB0 : x \notin fv_tm_tm B0) by
    (exact (proj2 (self_notin_union x (fv_tm_tm B2) (fv_tm_tm B0) Hrest3))).
  pose proof (Heq x HxL) as Hx.
  assert (Hx' := f_equal (subst_tm_tm a0 x) Hx).
  rewrite (subst_open_self a0 x B2 Hlc HxB2) in Hx'.
  rewrite (subst_open_comm a0 Hlc B0 x 0 (a_Inj2 (a_Var_f x))) in Hx'.
  rewrite (subst_fresh B0 a0 x HxB0) in Hx'.
  assert (Hc : subst_tm_tm a0 x (a_Inj2 (a_Var_f x)) = a_Inj2 a0).
  { change (a_Inj2 (subst_tm_tm a0 x (a_Var_f x)) = a_Inj2 a0).
    rewrite (subst_var_self a0 x). reflexivity. }
  rewrite Hc in Hx'. exact Hx'.
Qed.

Lemma ctx_sub_scaled_gen : forall (De Dd:D) (Ge G1 G1pre Gt:context) (q:usage),
  De_ok De Dd -> nodupD Dd -> shapeDG De Ge ->
  shapeDG Dd G1pre -> shapeDG Dd G1 -> shapeDG (De++Dd) Gt ->
  ctx_sub Dd G1pre G1 ->
  ctx_sub (De++Dd) (ctx_plus (ctx_mul q (ctx_mul 0 Ge ++ G1pre)) Gt)
                    (ctx_plus (ctx_mul q (ctx_mul 0 Ge ++ G1)) Gt).
Proof.
  intros De Dd Ge G1 G1pre Gt q Hok Hnd HshDe Hsh1p Hsh1 HshGt Hsub.
  assert (HokD : NoDup (List.map (fun p => fst p) De)).
  { exact (proj2 Hok). }
  assert (Hdis : forall y, y \in dom De -> y \notin dom Dd).
  { exact (proj1 Hok). }
  assert (HndApp : nodupD (De++Dd)).
  { apply nodupD_app; [exact HokD | exact Hnd | exact Hdis]. }
  assert (Hscale : ctx_sub (De++Dd)
        (ctx_mul q (ctx_mul 0 Ge ++ G1pre)) (ctx_mul q (ctx_mul 0 Ge ++ G1))).
  { rewrite !ctx_mul_app.
    rewrite !ctx_mul_ctx_mul.
    rewrite !qmul_0_r.
    apply (ctx_sub_combine De Dd (ctx_mul 0 Ge) (ctx_mul 0 Ge) (ctx_mul q G1pre) (ctx_mul q G1)).
    - exact HndApp.
    - apply shapeDG_mul; exact HshDe.
    - apply shapeDG_mul; exact HshDe.
    - apply shapeDG_mul; exact Hsh1p.
    - apply shapeDG_mul; exact Hsh1.
    - apply (ctx_sub_refl_nodup De (ctx_mul 0 Ge) (shapeDG_mul De Ge 0 HshDe) HokD).
    - apply (ctx_sub_mul Dd G1pre G1 Hsub q). }
  rewrite <- (ctx_mul_1 Gt).
  apply (ctx_sub_plus_mul (De++Dd) (ctx_mul q (ctx_mul 0 Ge ++ G1pre))
           (ctx_mul q (ctx_mul 0 Ge ++ G1)) Hscale Gt HshGt 1 1 (ule_refl 1)).
Qed.

Lemma inj1_case_beta_wf_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context) (Gw:context)
        (qq:usage) (A1 A2 a0 b1 B0 B1:tm) (L:atoms),
  tm0 = a_Inj1 a0 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  Beta TT (a_Sum A1 A2) ->
  Typing (De++Dd) Gw A1 a_Type ->
  Typing (De++Dd) Gt b1 (a_Pi qq A1 B1) ->
  (forall x, x \notin L -> open_tm_wrt_tm B1 (a_Var_f x)
      = open_tm_wrt_tm B0 (a_Inj1 (a_Var_f x))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1)) Gt)
         (a_App b1 a0) (open_tm_wrt_tm B0 (a_Inj1 a0)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt Gw qq A1 A2 a0 b1 B0 B1 L Et HshDe Hok Henv H1 Hbeta HwfA1 H3 Heq.
  revert De Ge Gt Gw qq A1 A2 a0 b1 B0 B1 L Et HshDe Hok Henv Hbeta HwfA1 H3 Heq.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0c G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0c G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1b B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0c A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1b r B0c B1b G3 H1b IH1b Heq0 H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1b r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1b b2b r A1b A2b B0c B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3b IH3 H4b IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1b A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1b r A1b B1b qqB A2b A3b G3 Heq0 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt Gw qq A1 A2 a0 b1 B0 B1 L Et HshDe Hok Henv Hbeta HwfA1 H3 Heq.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt Gw qq A1 A2 a0 b1 B0 B1 L Et HshDe Hok Henv Hbeta HwfA1 H3 Heq) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (Hsh2b : shapeDG D5 G2b) by (apply (ctx_sub_shape D5 G1b G2b Hsub); exact Hsh1b).
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b1 (a_Pi qq A1 B1) H3)).
    assert (Hsubc : ctx_sub (De++D5)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)).
    { apply (ctx_sub_scaled_gen De D5 Ge G2b G1b Gt qq Hok Hnd5 HshDe Hsh1b Hsh2b HshGt Hsub). }
    exact (T_sub (De++D5) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)
             (a_App b1 a0) (open_tm_wrt_tm B0 (a_Inj1 a0))
             (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _].
      assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (H3_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gt b1 (a_Pi qq A1 B1)).
    { rewrite app_assoc. exact H3. }
    assert (Hwf_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gw A1 a_Type).
    { rewrite app_assoc. exact HwfA1. }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt Gw
                  qq A1 A2 a0 b1 B0 B1 L Et HshDe_new Hok_new Henv_new Hbeta Hwf_new H3_new Heq) as Hres.
    assert (Hctx : ctx_plus (ctx_mul qq (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b)) Gt
                 = ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b))) Gt).
    { assert (Hinner : ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0)))
                     = ctx_mul 0 Ge ++ (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_app. rewrite ctx_mul_cons. rewrite qmul_0_l. simpl. reflexivity. }
      rewrite Hinner. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite app_assoc in Hres. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    assert (Hbeta' : Beta A1b (a_Sum A1 A2)).
    { exact (B_Trans A1b (a_Sum A1 A2) B0c Hbconv Hbeta). }
    exact (IH1b De Ge Gt Gw qq A1 A2 a0 b1 B0 B1 L Et HshDe Hok Henv Hbeta' HwfA1 H3 Heq).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *)
    injection Et as Ha. subst a0.
    assert (Hbeta1 : Beta A1b A1) by (apply (invert_Beta_Sum1 Hbeta)).
    assert (HshG : shapeDG D5 Gb) by (exact (@typing_align D5 Gb a A1b H1b)).
    pose proof (@typing_add_zero_prefix De Ge D5 Gb a A1b HshDe Hok Henv H1b) as HpayFull.
    pose proof (T_conv (De++D5) (ctx_mul 0 Ge ++ Gb) a A1 A1b Gw
                  HpayFull HwfA1 Hbeta1) as HpayA1.
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b1 (a_Pi qq A1 B1) H3)).
    assert (HshSc : shapeDG (De++D5) (ctx_mul qq (ctx_mul 0 Ge ++ Gb))).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r.
      apply shapeDG_app.
      - apply shapeDG_mul; exact HshDe.
      - apply shapeDG_mul; exact HshG. }
    pose proof (T_app (De++D5) Gt qq (ctx_mul 0 Ge ++ Gb) b1 a B1 A1 H3 HpayA1) as Happ.
    rewrite (open_inj1_eq B0 B1 a L Heq (typing_lc _ _ _ _ H1b)) in Happ.
    rewrite (ctx_plus_comm_shape2 (De++D5) Gt (ctx_mul qq (ctx_mul 0 Ge ++ Gb)) HshGt HshSc) in Happ.
    exact Happ.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma inj1_case_beta_noWF_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context)
        (qq:usage) (A1 A2 a0 b1 B0 B1:tm) (L:atoms),
  tm0 = a_Inj1 a0 ->
  TT = a_Sum A1 A2 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  Typing (De++Dd) Gt b1 (a_Pi qq A1 B1) ->
  (forall x, x \notin L -> open_tm_wrt_tm B1 (a_Var_f x)
      = open_tm_wrt_tm B0 (a_Inj1 (a_Var_f x))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1)) Gt)
         (a_App b1 a0) (open_tm_wrt_tm B0 (a_Inj1 a0)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt qq A1 A2 a0 b1 B0 B1 L Et ET HshDe Hok Henv H1 H3 Heq.
  revert De Ge Gt qq A1 A2 a0 b1 B0 B1 L Et ET HshDe Hok Henv H3 Heq.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0c G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0c G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1b B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0c A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1b r B0c B1b G3 H1b IH1b Heq0 H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1b r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1b b2b r A1b A2b B0c B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3b IH3 H4b IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1b A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1b r A1b B1b qqB A2b A3b G3 Heq0 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt qq A1 A2 a0 b1 B0 B1 L Et ET HshDe Hok Henv H3 Heq.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt qq A1 A2 a0 b1 B0 B1 L Et ET HshDe Hok Henv H3 Heq) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (Hsh2b : shapeDG D5 G2b) by (apply (ctx_sub_shape D5 G1b G2b Hsub); exact Hsh1b).
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b1 (a_Pi qq A1 B1) H3)).
    assert (Hsubc : ctx_sub (De++D5)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)).
    { apply (ctx_sub_scaled_gen De D5 Ge G2b G1b Gt qq Hok Hnd5 HshDe Hsh1b Hsh2b HshGt Hsub). }
    exact (T_sub (De++D5) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)
             (a_App b1 a0) (open_tm_wrt_tm B0 (a_Inj1 a0))
             (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _].
      assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (H3_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gt b1 (a_Pi qq A1 B1)).
    { rewrite app_assoc. exact H3. }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt
                  qq A1 A2 a0 b1 B0 B1 L Et ET HshDe_new Hok_new Henv_new H3_new Heq) as Hres.
    assert (Hctx : ctx_plus (ctx_mul qq (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b)) Gt
                 = ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b))) Gt).
    { assert (Hinner : ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0)))
                     = ctx_mul 0 Ge ++ (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_app. rewrite ctx_mul_cons. rewrite qmul_0_l. simpl. reflexivity. }
      rewrite Hinner. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite app_assoc in Hres. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    assert (HbetaSum : Beta B0c (a_Sum A1 A2)).
    { assert (HlcB : lc_tm B0c) by (exact (@typing_lc D5 G2b B0c a_Type H2b)).
      rewrite ET in HlcB. rewrite ET. apply B_Refl. exact HlcB. }
    assert (Hbeta' : Beta A1b (a_Sum A1 A2)).
    { exact (B_Trans A1b (a_Sum A1 A2) B0c Hbconv HbetaSum). }
    assert (Hne : env_wf (De++D5)) by exact Henv.
    rewrite ET in H2b.
    destruct (sum_wf_open_de_beta1 De D5 Ge G2b A1 A2 a_Type (a_Sum A1 A2)
                (@Logic.eq_refl tm (a_Sum A1 A2)) HshDe Hok Hne H2b
                (@B_Refl a_Type lc_a_Type)) as [Gw HwfA1].
    exact (inj1_case_beta_wf_gen a A1b De D5 Ge G1b Gt Gw qq A1 A2 a0 b1 B0 B1 L
             Et HshDe Hok Hne H1b Hbeta' HwfA1 H3 Heq).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *)
    injection Et as Ha. subst a0.
    injection ET as HA1 HA2. subst A1b. subst A2b.
    assert (HshG : shapeDG D5 Gb) by (exact (@typing_align D5 Gb a A1 H1b)).
    pose proof (@typing_add_zero_prefix De Ge D5 Gb a A1 HshDe Hok Henv H1b) as Hpay.
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b1 (a_Pi qq A1 B1) H3)).
    assert (HshSc : shapeDG (De++D5) (ctx_mul qq (ctx_mul 0 Ge ++ Gb))).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r.
      apply shapeDG_app.
      - apply shapeDG_mul; exact HshDe.
      - apply shapeDG_mul; exact HshG. }
    pose proof (T_app (De++D5) Gt qq (ctx_mul 0 Ge ++ Gb) b1 a B1 A1 H3 Hpay) as Happ.
    rewrite (open_inj1_eq B0 B1 a L Heq (typing_lc _ _ _ _ H1b)) in Happ.
    rewrite (ctx_plus_comm_shape2 (De++D5) Gt (ctx_mul qq (ctx_mul 0 Ge ++ Gb)) HshGt HshSc) in Happ.
    exact Happ.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma inj1_case_beta_typing :
 forall (D:D) (G1 G2:context) (q:usage) (A1 A2 a0 b1 B B1:tm) (L:atoms),
  Typing D G1 (a_Inj1 a0) (a_Sum A1 A2) ->
  Typing D G2 b1 (a_Pi q A1 B1) ->
  (forall x, x \notin L -> open_tm_wrt_tm B1 (a_Var_f x)
       = open_tm_wrt_tm B (a_Inj1 (a_Var_f x))) ->
  Typing D (ctx_plus (ctx_mul q G1) G2) (a_App b1 a0)
    (open_tm_wrt_tm B (a_Inj1 a0)).
Proof.
  intros D G1 G2 q A1 A2 a0 b1 B B1 L H1 H3 Heq.
  pose proof (inj1_case_beta_noWF_gen (a_Inj1 a0) (a_Sum A1 A2) nil D nil G1 G2
                q A1 A2 a0 b1 B B1 L
                (@Logic.eq_refl tm (a_Inj1 a0)) (@Logic.eq_refl tm (a_Sum A1 A2))
                sh_nil (De_ok_nil D)
                (typing_env_wf D G1 (a_Inj1 a0) (a_Sum A1 A2) H1) H1 H3 Heq) as Hres.
  simpl in Hres. exact Hres.
Qed.
Lemma inj2_case_beta_wf_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context) (Gw:context)
        (qq:usage) (A1 A2 a0 b2 B0 B2:tm) (L:atoms),
  tm0 = a_Inj2 a0 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  Beta TT (a_Sum A1 A2) ->
  Typing (De++Dd) Gw A2 a_Type ->
  Typing (De++Dd) Gt b2 (a_Pi qq A2 B2) ->
  (forall x, x \notin L -> open_tm_wrt_tm B2 (a_Var_f x)
      = open_tm_wrt_tm B0 (a_Inj2 (a_Var_f x))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1)) Gt)
         (a_App b2 a0) (open_tm_wrt_tm B0 (a_Inj2 a0)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt Gw qq A1 A2 a0 b2 B0 B2 L Et HshDe Hok Henv H1 Hbeta HwfA2 H3 Heq.
  revert De Ge Gt Gw qq A1 A2 a0 b2 B0 B2 L Et HshDe Hok Henv Hbeta HwfA2 H3 Heq.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0c G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0c G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1b B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0c A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1b r B0c B1b G3 H1b IH1b Heq0 H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1b r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1b b2b r A1b A2b B0c B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3b IH3 H4b IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1b A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1b r A1b B1b qqB A2b A3b G3 Heq0 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt Gw qq A1 A2 a0 b2 B0 B2 L Et HshDe Hok Henv Hbeta HwfA2 H3 Heq.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt Gw qq A1 A2 a0 b2 B0 B2 L Et HshDe Hok Henv Hbeta HwfA2 H3 Heq) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (Hsh2b : shapeDG D5 G2b) by (apply (ctx_sub_shape D5 G1b G2b Hsub); exact Hsh1b).
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b2 (a_Pi qq A2 B2) H3)).
    assert (Hsubc : ctx_sub (De++D5)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)).
    { apply (ctx_sub_scaled_gen De D5 Ge G2b G1b Gt qq Hok Hnd5 HshDe Hsh1b Hsh2b HshGt Hsub). }
    exact (T_sub (De++D5) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)
             (a_App b2 a0) (open_tm_wrt_tm B0 (a_Inj2 a0))
             (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _].
      assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (H3_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gt b2 (a_Pi qq A2 B2)).
    { rewrite app_assoc. exact H3. }
    assert (Hwf_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gw A2 a_Type).
    { rewrite app_assoc. exact HwfA2. }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt Gw
                  qq A1 A2 a0 b2 B0 B2 L Et HshDe_new Hok_new Henv_new Hbeta Hwf_new H3_new Heq) as Hres.
    assert (Hctx : ctx_plus (ctx_mul qq (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b)) Gt
                 = ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b))) Gt).
    { assert (Hinner : ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0)))
                     = ctx_mul 0 Ge ++ (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_app. rewrite ctx_mul_cons. rewrite qmul_0_l. simpl. reflexivity. }
      rewrite Hinner. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite app_assoc in Hres. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    assert (Hbeta' : Beta A1b (a_Sum A1 A2)).
    { exact (B_Trans A1b (a_Sum A1 A2) B0c Hbconv Hbeta). }
    exact (IH1b De Ge Gt Gw qq A1 A2 a0 b2 B0 B2 L Et HshDe Hok Henv Hbeta' HwfA2 H3 Heq).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *)
    injection Et as Ha. subst a0.
    assert (Hbeta2 : Beta A2b A2) by (apply (invert_Beta_Sum2 Hbeta)).
    assert (HshG : shapeDG D5 Gb) by (exact (@typing_align D5 Gb a A2b H1b)).
    pose proof (@typing_add_zero_prefix De Ge D5 Gb a A2b HshDe Hok Henv H1b) as HpayFull.
    pose proof (T_conv (De++D5) (ctx_mul 0 Ge ++ Gb) a A2 A2b Gw
                  HpayFull HwfA2 Hbeta2) as HpayA2.
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b2 (a_Pi qq A2 B2) H3)).
    assert (HshSc : shapeDG (De++D5) (ctx_mul qq (ctx_mul 0 Ge ++ Gb))).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r.
      apply shapeDG_app.
      - apply shapeDG_mul; exact HshDe.
      - apply shapeDG_mul; exact HshG. }
    pose proof (T_app (De++D5) Gt qq (ctx_mul 0 Ge ++ Gb) b2 a B2 A2 H3 HpayA2) as Happ.
    rewrite (open_inj2_eq B0 B2 a L Heq (typing_lc _ _ _ _ H1b)) in Happ.
    rewrite (ctx_plus_comm_shape2 (De++D5) Gt (ctx_mul qq (ctx_mul 0 Ge ++ Gb)) HshGt HshSc) in Happ.
    exact Happ.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.
Lemma inj2_case_beta_noWF_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context)
        (qq:usage) (A1 A2 a0 b2 B0 B2:tm) (L:atoms),
  tm0 = a_Inj2 a0 ->
  TT = a_Sum A1 A2 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  Typing (De++Dd) Gt b2 (a_Pi qq A2 B2) ->
  (forall x, x \notin L -> open_tm_wrt_tm B2 (a_Var_f x)
      = open_tm_wrt_tm B0 (a_Inj2 (a_Var_f x))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1)) Gt)
         (a_App b2 a0) (open_tm_wrt_tm B0 (a_Inj2 a0)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt qq A1 A2 a0 b2 B0 B2 L Et ET HshDe Hok Henv H1 H3 Heq.
  revert De Ge Gt qq A1 A2 a0 b2 B0 B2 L Et ET HshDe Hok Henv H3 Heq.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0c G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0c G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1b B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0c A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1b r B0c B1b G3 H1b IH1b Heq0 H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1b r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1b b2b r A1b A2b B0c B1b B2b G3 Hq H1b IH1b Heq1 Heq2 H3b IH3 H4b IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1b A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1b r A1b B1b qqB A2b A3b G3 Heq0 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt qq A1 A2 a0 b2 B0 B2 L Et ET HshDe Hok Henv H3 Heq.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt qq A1 A2 a0 b2 B0 B2 L Et ET HshDe Hok Henv H3 Heq) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (Hsh2b : shapeDG D5 G2b) by (apply (ctx_sub_shape D5 G1b G2b Hsub); exact Hsh1b).
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b2 (a_Pi qq A2 B2) H3)).
    assert (Hsubc : ctx_sub (De++D5)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt)
              (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)).
    { apply (ctx_sub_scaled_gen De D5 Ge G2b G1b Gt qq Hok Hnd5 HshDe Hsh1b Hsh2b HshGt Hsub). }
    exact (T_sub (De++D5) (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G2b)) Gt)
             (a_App b2 a0) (open_tm_wrt_tm B0 (a_Inj2 a0))
             (ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ G1b)) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _].
      assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (H3_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gt b2 (a_Pi qq A2 B2)).
    { rewrite app_assoc. exact H3. }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt
                  qq A1 A2 a0 b2 B0 B2 L Et ET HshDe_new Hok_new Henv_new H3_new Heq) as Hres.
    assert (Hctx : ctx_plus (ctx_mul qq (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b)) Gt
                 = ctx_plus (ctx_mul qq (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b))) Gt).
    { assert (Hinner : ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0)))
                     = ctx_mul 0 Ge ++ (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_app. rewrite ctx_mul_cons. rewrite qmul_0_l. simpl. reflexivity. }
      rewrite Hinner. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite app_assoc in Hres. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    assert (HbetaSum : Beta B0c (a_Sum A1 A2)).
    { assert (HlcB : lc_tm B0c) by (exact (@typing_lc D5 G2b B0c a_Type H2b)).
      rewrite ET in HlcB. rewrite ET. apply B_Refl. exact HlcB. }
    assert (Hbeta' : Beta A1b (a_Sum A1 A2)).
    { exact (B_Trans A1b (a_Sum A1 A2) B0c Hbconv HbetaSum). }
    assert (Hne : env_wf (De++D5)) by exact Henv.
    rewrite ET in H2b.
    destruct (sum_wf_open_de_beta2 De D5 Ge G2b A1 A2 a_Type (a_Sum A1 A2)
                (@Logic.eq_refl tm (a_Sum A1 A2)) HshDe Hok Hne H2b
                (@B_Refl a_Type lc_a_Type)) as [Gw HwfA2].
    exact (inj2_case_beta_wf_gen a A1b De D5 Ge G1b Gt Gw qq A1 A2 a0 b2 B0 B2 L
             Et HshDe Hok Hne H1b Hbeta' HwfA2 H3 Heq).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *)
    injection Et as Ha. subst a0.
    injection ET as HA1 HA2. subst A1b. subst A2b.
    assert (HshG : shapeDG D5 Gb) by (exact (@typing_align D5 Gb a A2 H1b)).
    pose proof (@typing_add_zero_prefix De Ge D5 Gb a A2 HshDe Hok Henv H1b) as Hpay.
    assert (HshGt : shapeDG (De++D5) Gt) by (exact (@typing_align (De++D5) Gt b2 (a_Pi qq A2 B2) H3)).
    assert (HshSc : shapeDG (De++D5) (ctx_mul qq (ctx_mul 0 Ge ++ Gb))).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r.
      apply shapeDG_app.
      - apply shapeDG_mul; exact HshDe.
      - apply shapeDG_mul; exact HshG. }
    pose proof (T_app (De++D5) Gt qq (ctx_mul 0 Ge ++ Gb) b2 a B2 A2 H3 Hpay) as Happ.
    rewrite (open_inj2_eq B0 B2 a L Heq (typing_lc _ _ _ _ H1b)) in Happ.
    rewrite (ctx_plus_comm_shape2 (De++D5) Gt (ctx_mul qq (ctx_mul 0 Ge ++ Gb)) HshGt HshSc) in Happ.
    exact Happ.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.
Lemma inj2_case_beta_typing :
 forall (D:D) (G1 G2:context) (q:usage) (A1 A2 a0 b2 B B2:tm) (L:atoms),
  Typing D G1 (a_Inj2 a0) (a_Sum A1 A2) ->
  Typing D G2 b2 (a_Pi q A2 B2) ->
  (forall x, x \notin L -> open_tm_wrt_tm B2 (a_Var_f x)
       = open_tm_wrt_tm B (a_Inj2 (a_Var_f x))) ->
  Typing D (ctx_plus (ctx_mul q G1) G2) (a_App b2 a0)
    (open_tm_wrt_tm B (a_Inj2 a0)).
Proof.
  intros D G1 G2 q A1 A2 a0 b2 B B2 L H1 H3 Heq.
  pose proof (inj2_case_beta_noWF_gen (a_Inj2 a0) (a_Sum A1 A2) nil D nil G1 G2
                q A1 A2 a0 b2 B B2 L
                (@Logic.eq_refl tm (a_Inj2 a0)) (@Logic.eq_refl tm (a_Sum A1 A2))
                sh_nil (De_ok_nil D)
                (typing_env_wf D G1 (a_Inj2 a0) (a_Sum A1 A2) H1) H1 H3 Heq) as Hres.
  simpl in Hres. exact Hres.
Qed.

(* ===== inlined from TensorBeta.v ===== *)
Lemma open_close_cl : forall (T:tm) (k:nat) (y:tmvar) (u:tm),
  cl k T -> open_tm_wrt_tm_rec k u (close_tm_wrt_tm_rec k y T) = subst_tm_tm u y T.
Proof.
  intros T. induction T as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n | x
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros k y u Hc; simpl in *.
- simpl. reflexivity.
- simpl. reflexivity.
  - destruct Hc as [Ha [Hb HB]]. f_equal.
    + apply (IHa k y u Ha).
    + apply (IHb k y u Hb).
    + apply (IHB k y u HB).
  - destruct Hc as [HA HB]. f_equal.
    + apply (IHA k y u HA).
    + apply (IHB (S k) y u HB).
  - destruct Hc as [HA Ha]. f_equal.
    + apply (IHA k y u HA).
    + apply (IHa (S k) y u Ha).
  - destruct Hc as [Ha Hb]. f_equal.
    + apply (IHa k y u Ha).
    + apply (IHb k y u Hb).
  - f_equal. apply (IHA k y u Hc).
  - destruct Hc as [Ha [Hb HB]]. f_equal.
    + apply (IHa k y u Ha).
    + apply (IHb (S k) y u Hb).
    + apply (IHB k y u HB).
- simpl. reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[H1|H2]|H3].
    + destruct (lt_ge_dec n k) as [Hlt|Hge]; [|lia].
      simpl. destruct (lt_eq_lt_dec n k) as [[H1'|H2]|H3]; [reflexivity|lia|lia].
    + exfalso; lia.
    + exfalso; lia.
  - destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X y x) as [Hyx|Hnyx]; simpl.
    + destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X x y) as [Hxy|Hnxy];
        [|exfalso; exact (Hnxy (@Logic.eq_sym atom y x Hyx))].
      simpl. destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [exfalso; lia| |exfalso; lia].
      reflexivity.
    + destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X x y) as [Hxy|Hnxy];
        [exfalso; exact (Hnyx (@Logic.eq_sym atom x y Hxy))|].
      simpl. reflexivity.
  - f_equal. apply (IHa k y u Hc).
  - destruct Hc as [Ha Hb]. f_equal.
    + apply (IHa k y u Ha).
    + apply (IHb (S k) y u Hb).
  - destruct Hc as [H1 H2]. f_equal.
    + apply (IHA1 k y u H1).
    + apply (IHA2 k y u H2).
  - f_equal. apply (IHa k y u Hc).
  - f_equal. apply (IHa k y u Hc).
  - destruct Hc as [Ha [Hb1 [Hb2 HB]]]. f_equal.
    + apply (IHa k y u Ha).
    + apply (IHb1 k y u Hb1).
    + apply (IHb2 k y u Hb2).
    + apply (IHB k y u HB).
  - destruct Hc as [HA HB]. f_equal.
    + apply (IHA k y u HA).
    + apply (IHB (S k) y u HB).
  - destruct Hc as [Ha Hb]. f_equal.
    + apply (IHa k y u Ha).
    + apply (IHb k y u Hb).
  - destruct Hc as [Ha [Hb HB]]. f_equal.
    + apply (IHa k y u Ha).
    + apply (IHb (S k) y u Hb).
    + apply (IHB k y u HB).
Qed.


Lemma open_var_b_ge : forall k n x, n >= k ->
  open_tm_wrt_tm_rec k (a_Var_f x) (a_Var_b (S n)) = a_Var_b n.
Proof.
  induction k as [|k IH]; intros n x Hge.
  - simpl. replace (n - 0) with n by lia. reflexivity.
  - simpl.
    destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + exfalso; lia.
    + exfalso; lia.
    + simpl. replace (n - 0) with n by lia. reflexivity.
Qed.

Lemma open_var_b_lt : forall n k x, n < k ->
  open_tm_wrt_tm_rec k (a_Var_f x) (a_Var_b n) = a_Var_b n.
Proof.
  induction n as [|n IH]; intros k x Hlt.
  - destruct k as [|k]; [lia|]. simpl. reflexivity.
  - destruct k as [|k]; [lia|]. simpl.
    destruct (lt_eq_lt_dec n k) as [[Hlt'|Heq]|Hgt].
    + simpl. reflexivity.
    + exfalso; lia.
    + simpl. f_equal. lia.
Qed.

Lemma open_var_b_eq : forall k x,
  open_tm_wrt_tm_rec k (a_Var_f x) (a_Var_b k) = a_Var_f x.
Proof.
  induction k as [|k IH]; intros x; simpl.
  - reflexivity.
  - destruct (lt_eq_lt_dec k k) as [[H1|H2]|H3]; [lia|reflexivity|lia].
Qed.

Lemma open_close_self_gen : forall (T:tm) (k:nat) (x:tmvar),
  open_tm_wrt_tm_rec k (a_Var_f x) (close_tm_wrt_tm_rec k x T) = T.
Proof.
  intros T. induction T as
  [ | | a IHa b IHb B IHB
    | q A IHA B IHB
    | q A IHA a IHa
    | a IHa b IHb
    | q A IHA
    | a IHa b IHb B IHB
    | | n | z
    | q a IHa
    | a IHa b IHb
    | A1 IHA1 A2 IHA2
    | a IHa
    | a IHa
    | q a IHa b1 IHb1 b2 IHb2 B IHB
    | q A IHA B IHB
    | a IHa b IHb
    | a IHa b IHb B IHB ]; intros k x; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply (IHa k x).
    + apply (IHb k x).
    + apply (IHB k x).
  - f_equal.
    + apply (IHA k x).
    + apply (IHB (S k) x).
  - f_equal.
    + apply (IHA k x).
    + apply (IHa (S k) x).
  - f_equal.
    + apply (IHa k x).
    + apply (IHb k x).
  - f_equal. apply (IHA k x).
  - f_equal.
    + apply (IHa k x).
    + apply (IHb (S k) x).
    + apply (IHB k x).
  - reflexivity.
  - destruct (lt_ge_dec n k) as [Hlt|Hge].
    + exact (open_var_b_lt n k x Hlt).
    + exact (open_var_b_ge k n x Hge).
  - destruct (@CoqEqDec.eq_dec tmvar EqDec_eq_of_X x z) as [Heq|Hneq].
    + subst z. exact (open_var_b_eq k x).
    + reflexivity.
  - f_equal. apply (IHa k x).
  - f_equal.
    + apply (IHa k x).
    + apply (IHb (S k) x).
  - f_equal.
    + apply (IHA1 k x).
    + apply (IHA2 k x).
  - f_equal. apply (IHa k x).
  - f_equal. apply (IHa k x).
  - f_equal.
    + apply (IHa k x).
    + apply (IHb1 k x).
    + apply (IHb2 k x).
    + apply (IHB k x).
  - f_equal.
    + apply (IHA k x).
    + apply (IHB (S k) x).
  - f_equal.
    + apply (IHa k x).
    + apply (IHb k x).
  - f_equal.
    + apply (IHa k x).
    + apply (IHb (S k) x).
    + apply (IHB k x).
Qed.

Lemma open_close_self : forall (T:tm) (y:tmvar),
  open_tm_wrt_tm (close_tm_wrt_tm y T) (a_Var_f y) = T.
Proof.
  intros T y. unfold open_tm_wrt_tm, close_tm_wrt_tm.
  apply (open_close_self_gen T 0 y).
Qed.

Lemma sigma_wf_open_de_beta2 :
 forall (De Dd:D) (Ge G1 Gt:context) (qt:usage) (At Bt arg T t:tm),
  t = a_Sigma qt At Bt ->
  shapeDG De Ge -> De_ok De Dd -> shapeDG Dd Gt ->
  Typing Dd G1 t T -> Beta T a_Type ->
  Typing (De++Dd) (Ge++Gt) arg At ->
  exists Gty, Typing (De++Dd) Gty (open_tm_wrt_tm Bt arg) a_Type.
Proof.
  intros De Dd Ge G1 Gt qt At Bt arg T t Et HshDe Hok HshapeD Hp Hbeta Harg.
  revert De Ge Gt qt At Bt Et Hbeta HshDe Hok HshapeD Harg.
  induction Hp as
  [ D5 G2 a A0 G1b H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1b a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1b G2 qq0 A0 B0 r H_A IHA Hfun IHfun
  | L D5 G1b qq0 A0 a B0 G2 Hfun IHfun H2 IH2
  | D5 G1b qq0 G2 a b B0 A0 H1 IH1 H2 IH2
  | D5 G1b a B0 A1b G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1b G2 a b r B0 B1b G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq0 A0 H1 IH1
  | D5 qq0 G a A0 H1 IH1
  | L D5 G1b G2 a b r qq0 A0 B0 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2 A0 A1b H1 IH1 H2 IH2
  | D5 G a A0 A1b G1b H1 IH1 H2 IH2
  | D5 G a A1b A0 G1b H1 IH1 H2 IH2
  | L D5 qq0 G1b G2 a b1 b2 r A0 A1b B0 B1b B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1b G2 qq0 A0 B0 r H1 IH1 Hfun IHfun
  | L D5 qq0 G1b G2 a b A0 B0 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1b G2 a b r A0 B0 qq0 A1b A2b G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt qt At Bt Et Hbeta HshDe Hok HshapeD Harg.
  - (* T_sub *)
    exact (IH1 De Ge Gt qt At Bt Et Hbeta HshDe Hok HshapeD Harg).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    simpl in HshapeD.
    inversion HshapeD as [| xx qx Axx Dxx Gs HS]; subst.
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (qx,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(qx,Tm Ax0))::nil)).
      apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0)))).
    { apply (shapeDG_app De Ge (x ~ Tm Ax0) (x ~ (qx,Tm Ax0)) HshDe Hsingle). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { destruct Hok as [Hdis Hnd]. split.
      - intros z Hz C. rewrite dom_app in Hz. apply union_iff in Hz.
        destruct Hz as [Hz|Hz].
        + apply (Hdis z Hz). rewrite dom_app. apply union_iff. right. exact C.
        + change (z \in dom ((x,Tm Ax0) :: nil)) in Hz.
          apply (proj1 (in_dom_cons z x Ax0 nil)) in Hz.
          destruct Hz as [Hz|Hz]; [subst z; exact (Hnotin C)|].
          exact (in_dom_nil z Hz).
      - apply nodupD_app.
        + exact Hnd.
        + apply nodupD_cons. apply nodupD_nil. exact (in_dom_nil x).
        + intros z Hz C. apply (Hdis z Hz). rewrite dom_app. apply union_iff. left. exact C. }
    assert (Harg_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5)
                         ((Ge ++ (x ~ (qx,Tm Ax0))) ++ Gs) arg At).
    { rewrite !app_assoc. exact Harg. }
    destruct (IH1 (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (qx,Tm Ax0))) Gs qt At Bt
                 (@Logic.eq_refl tm (a_Sigma qt At Bt)) Hbeta HshDe_new Hok_new HS Harg_new) as [Gty Hty].
    rewrite app_assoc in Hty.
    eexists. exact Hty.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    exact (IH1 De Ge Gt qt At Bt Et (B_Trans A1b a_Type B0 Hbconv Hbeta)
             HshDe Hok HshapeD Harg).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *)
    injection Et as Hq HA HB. subst qq0. subst A0. subst B0.
    assert (HshG2 : shapeDG D5 G2).
    { apply (shapeDG_binder_inv L At r D5 G2). intros y Hy.
      apply (@typing_align ((y ~ Tm At) ++ D5) ((y ~ (r,Tm At)) ++ G2)
                (open_tm_wrt_tm Bt (a_Var_f y)) a_Type (Hfun y Hy)). }
    pick fresh y for (L \u fv_tm_tm At \u fv_tm_tm Bt \u dom De).
    assert (HyL : y \notin L) by
      (exact (proj1 (self_notin_union y L (fv_tm_tm At \u fv_tm_tm Bt \u dom De) Fr))).
    assert (Hy1 : y \notin fv_tm_tm At \u fv_tm_tm Bt \u dom De) by
      (exact (proj2 (self_notin_union y L (fv_tm_tm At \u fv_tm_tm Bt \u dom De) Fr))).
    assert (HyAt : y \notin fv_tm_tm At) by
      (exact (proj1 (self_notin_union y (fv_tm_tm At) (fv_tm_tm Bt \u dom De) Hy1))).
    assert (Hy2 : y \notin fv_tm_tm Bt \u dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm At) (fv_tm_tm Bt \u dom De) Hy1))).
    assert (HyBt : y \notin fv_tm_tm Bt) by
      (exact (proj1 (self_notin_union y (fv_tm_tm Bt) (dom De) Hy2))).
    assert (HyDe : y \notin dom De) by
      (exact (proj2 (self_notin_union y (fv_tm_tm Bt) (dom De) Hy2))).
    pose proof (Hfun y HyL) as Hbody.
    assert (Hnd0 : nodupD ((y ~ Tm At) ++ D5)) by
      (exact (@typing_nodup_local ((y ~ Tm At) ++ D5) ((y ~ (r,Tm At)) ++ G2)
                (open_tm_wrt_tm Bt (a_Var_f y)) a_Type Hbody)).
    assert (Hnd : nodupD (nil ++ (y,Tm At) :: D5)) by
      (simpl; change (nodupD ((y,Tm At) :: D5)); exact Hnd0).
    assert (Dok : De_ok De (nil ++ (y,Tm At) :: D5)) by
      (simpl; change (De_ok De ((y,Tm At) :: D5));
       apply (De_ok_extend_head De y (Tm At) D5 Hok HyDe)).
    pose proof (typing_subst_gen_de nil y At D5 nil G2 r (open_tm_wrt_tm Bt (a_Var_f y))
                  a_Type De Ge Gt arg Hbody sh_nil HshG2 Hnd HshDe Dok HyAt
                  (typing_lc _ _ _ _ Harg) HshapeD Harg) as Hres.
    simpl in Hres.
    rewrite (subst_open_self arg y Bt (typing_lc _ _ _ _ Harg) HyBt) in Hres.
    simpl in Hres. eexists. exact Hres.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.


Lemma qplus_0_r_local : forall (q:usage), q + 0 = q.
Proof.
  intros q. rewrite qplus_comm. rewrite qplus_0_l. reflexivity.
Qed.

Lemma ctx_plus_zero_self : forall (G:context),
  ctx_plus (ctx_mul 0 G) (ctx_mul 0 G) = ctx_mul 0 G.
Proof.
  intros G. rewrite (ctx_mul_add 0 0 G). rewrite qplus_0_l. reflexivity.
Qed.

Lemma spread_ctx_eq : forall (De Dtail:D) (Ge G1b G2b Gt:context) (qq:usage),
  shapeDG De Ge -> shapeDG Dtail G1b -> shapeDG Dtail G2b ->
  shapeDG (De++Dtail) Gt ->
  ctx_plus (ctx_plus Gt (ctx_mul 0 Ge ++ ctx_mul qq G1b))
           (ctx_mul 0 Ge ++ G2b)
  = ctx_plus (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b) Gt.
Proof.
  intros De Dtail Ge G1b G2b Gt qq HshGe Hsh1 Hsh2 HshGt.
  revert Dtail G1b G2b Gt qq Hsh1 Hsh2 HshGt.
  induction HshGe as [| x qx A De' Ge' HshGe' IH];
    intros Dtail G1b G2b Gt qq Hsh1 Hsh2 HshGt.
  - simpl.
    assert (HA : shapeDG Dtail (ctx_mul qq G1b)).
    { apply shapeDG_mul. exact Hsh1. }
    assert (HAB : shapeDG Dtail (ctx_plus (ctx_mul qq G1b) G2b)).
    { apply shapeDG_plus; [exact HA | exact Hsh2]. }
    rewrite (ctx_plus_assoc_shape Dtail Gt (ctx_mul qq G1b) G2b HshGt HA Hsh2).
    rewrite (ctx_plus_comm_shape2 Dtail Gt (ctx_plus (ctx_mul qq G1b) G2b) HshGt HAB).
    reflexivity.
  - simpl in HshGt.
    inversion HshGt as [| y qg Ag Dg Gt' HshGt']; subst.
    simpl.
    rewrite qmul_0_l.
    assert (HqL : (qg + 0) + 0 = qg) by (rewrite qplus_0_r_local; exact (qplus_0_r_local qg)).
    rewrite HqL.
    assert (HqR : 0 + qg = qg) by (rewrite qplus_0_l; reflexivity).
    rewrite HqR.
    f_equal. exact (IH Dtail G1b G2b Gt' qq Hsh1 Hsh2 HshGt').
Qed.

Lemma open_close_tensor_eq : forall (B1 a0 a1:tm) (y:tmvar),
  cl 0 (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))) ->
  y \notin fv_tm_tm B1 -> y \notin fv_tm_tm a0 -> lc_tm a1 ->
  open_tm_wrt_tm
    (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))) a1
  = open_tm_wrt_tm B1 (a_Tensor a0 a1).
Proof.
  intros B1 a0 a1 y Hcl HyB1 Hya0 Hlc.
  assert (Heq1 :
    open_tm_wrt_tm_rec 0 a1
      (close_tm_wrt_tm_rec 0 y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))))
    = subst_tm_tm a1 y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))).
  { apply (open_close_cl (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))) 0 y a1 Hcl). }
  assert (Heq2 :
    subst_tm_tm a1 y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))
    = open_tm_wrt_tm B1 (a_Tensor a0 a1)).
  { rewrite (subst_open_comm a1 Hlc B1 y 0 (a_Tensor a0 (a_Var_f y))).
    rewrite (subst_fresh B1 a1 y HyB1).
    simpl.
    rewrite (subst_fresh a0 a1 y Hya0).
    destruct (eq_var y y) as [Hy|Hny].
    + reflexivity.
    + exfalso. exact (Hny (@Logic.eq_refl atom y)). }
  unfold open_tm_wrt_tm, close_tm_wrt_tm.
  rewrite Heq1. exact Heq2.
Qed.

Lemma tensor_beta_wf_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context) (Gty:context)
        (q qq:usage) (A2 A3 a0 a1 b B1:tm) (L:atoms),
  tm0 = a_Tensor a0 a1 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  Beta TT (a_Sigma qq A2 A3) ->
  Typing (De++Dd) Gty (a_Sigma qq A2 A3) a_Type ->
  (forall x, x \notin L -> forall y, y \notin L \u {{x}} ->
     Typing ((x ~ Tm A2) ++ (De++Dd)) ((x ~ (qq,Tm A2)) ++ Gt)
       (open_tm_wrt_tm b (a_Var_f x))
       (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
               (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul 0 Ge ++ G1) Gt)
         (a_App (open_tm_wrt_tm b a0) a1)
         (open_tm_wrt_tm B1 (a_Tensor a0 a1)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt Gty q qq A2 A3 a0 a1 b B1 L Et HshDe Hok Henv H1 Hbeta Hwf Hfun.
  revert De Ge Gt Gty q qq A2 A3 a0 a1 b B1 L Et HshDe Hok Henv Hbeta Hwf Hfun.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0b G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0b G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1 B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0b A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1 r B0b B1b G3 H1b IH1b Heq H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1 r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1 b2 r A1b A2b B0b B1b B2b G3 Hq0 H1b IH1b Heq1 Heq2 H3 IH3 H4 IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1 A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1 r A1b B1b qqB A2b A3b G3 Heq H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt Gty q qq A2 A3 a0 a1 b B1 L Et HshDe Hok Henv Hbeta Hwf Hfun.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt Gty q qq A2 A3 a0 a1 b B1 L Et HshDe Hok Henv Hbeta Hwf Hfun) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (HshGt : shapeDG (De++D5) Gt).
    { apply (shapeDG_binder_inv L A2 qq (De++D5) Gt). intros x Hx.
      pick fresh y for (L \u {{x}}).
      assert (Hy : y \notin L \u {{x}}) by assumption.
      exact (@typing_align _ _ _ _ (Hfun x Hx y Hy)). }
    assert (Hsubc := ctx_sub_box De D5 Ge G2b G1b Gt Hok Hnd5 HshDe Hsh1b HshGt Hsub).
    exact (T_sub (De++D5) (ctx_plus (ctx_mul 0 Ge ++ G2b) Gt)
             (a_App (open_tm_wrt_tm b a0) a1) (open_tm_wrt_tm B1 (a_Tensor a0 a1))
             (ctx_plus (ctx_mul 0 Ge ++ G1b) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _]. assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hfun_new : forall y, y \notin L -> forall z, z \notin L \u {{y}} ->
       Typing ((y ~ Tm A2) ++ ((De ++ (x ~ Tm Ax0)) ++ D5))
         ((y ~ (qq,Tm A2)) ++ Gt) (open_tm_wrt_tm b (a_Var_f y))
         (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f y))
                 (close_tm_wrt_tm z (open_tm_wrt_tm B1 (a_Tensor (a_Var_f y) (a_Var_f z)))))).
    { intros y Hy z Hz. rewrite app_assoc. exact (Hfun y Hy z Hz). }
    assert (Hwf_new : Typing ((De ++ (x ~ Tm Ax0)) ++ D5) Gty
                        (a_Sigma qq A2 A3) a_Type).
    { rewrite app_assoc. exact Hwf. }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt Gty q qq
                  A2 A3 a0 a1 b B1 L Et HshDe_new Hok_new Henv_new Hbeta Hwf_new Hfun_new) as Hres.
    assert (Hctx : ctx_plus (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b) Gt
                 = ctx_plus (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b)) Gt).
    { rewrite ctx_mul_app.
      assert (Hsm : ctx_mul 0 (x ~ (0,Tm Ax0)) = (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_cons. simpl. rewrite qmul_0_l. reflexivity. }
      rewrite Hsm. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite <- app_assoc. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    pose proof (IH1b De Ge Gt Gty q qq A2 A3 a0 a1 b B1 L Et HshDe Hok Henv
                  (B_Trans A1b (a_Sigma qq A2 A3) B0b Hbconv Hbeta) Hwf Hfun) as Hres.
    exact Hres.
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *)
    injection Et as Ha Hb. subst a. subst b1.
    assert (HqB : qqB = qq) by (exact (invert_Beta_a_Sigma0 Hbeta)).
    subst qqB.
    assert (HA : Beta A1b A2) by (exact (invert_Beta_a_Sigma1 Hbeta)).
    assert (HshG1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a0 A1b H1b)).
    assert (HshG2b : shapeDG D5 G2b) by (exact (@typing_align D5 G2b a1 (open_tm_wrt_tm B1b a0) H2b)).
    pose proof (@typing_add_zero_prefix De Ge D5 G1b a0 A1b HshDe Hok Henv H1b) as Hpayfull0.
    assert (HshG1bfull : shapeDG (De++D5) (ctx_mul 0 Ge ++ G1b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact HshG1b]. }
    assert (HwfA2 : exists Gw, Typing (De++D5) Gw A2 a_Type).
    { apply (sigma_wf_open_de_beta1 nil (De++D5) nil Gty qq A2 A3 a_Type (a_Sigma qq A2 A3)).
      - reflexivity.
      - apply sh_nil.
      - apply De_ok_nil.
      - apply (typing_env_wf _ _ _ _ Hwf).
      - exact Hwf.
      - apply B_Refl. apply (typing_lc_ty _ _ _ _ Hwf). }
    destruct HwfA2 as [Gw HwfA2].
    assert (HpayA2 : Typing (De++D5) (ctx_mul 0 Ge ++ G1b) a0 A2).
    { exact (T_conv (De++D5) (ctx_mul 0 Ge ++ G1b) a0 A2 A1b Gw Hpayfull0 HwfA2 HA). }
    assert (Hargfull0 : Typing (De++D5) (ctx_mul 0 Ge ++ G2b) a1 (open_tm_wrt_tm B1b a0)).
    { exact (@typing_add_zero_prefix De Ge D5 G2b a1 (open_tm_wrt_tm B1b a0) HshDe Hok Henv H2b). }
    pick fresh x for (L \u fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1
                     \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De).
    assert (Hxfresh : x \notin (L \u fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De)) by assumption.
    assert (HxL : x \notin L) by
      (exact (proj1 (self_notin_union x L (fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxfresh))).
    assert (Hxrest : x \notin fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x L (fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxfresh))).
    assert (HxA2 : x \notin fv_tm_tm A2) by
      (exact (proj1 (self_notin_union x (fv_tm_tm A2) (fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest))).
    assert (Hxrest2 : x \notin fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm A2) (fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest))).
    assert (HxA3 : x \notin fv_tm_tm A3) by
      (exact (proj1 (self_notin_union x (fv_tm_tm A3) (fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest2))).
    assert (Hxrest3 : x \notin fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm A3) (fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest2))).
    assert (Hxb : x \notin fv_tm_tm b) by
      (exact (proj1 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest3))).
    assert (Hxrest4 : x \notin fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest3))).
    assert (HxB1 : x \notin fv_tm_tm B1) by
      (exact (proj1 (self_notin_union x (fv_tm_tm B1) (fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest4))).
    assert (Hxrest5 : x \notin fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm B1) (fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest4))).
    assert (Hxa0 : x \notin fv_tm_tm a0) by
      (exact (proj1 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm a1 \u dom De) Hxrest5))).
    assert (Hxa1 : x \notin fv_tm_tm a1) by
      (exact (proj1 (self_notin_union x (fv_tm_tm a1) (dom De) (proj2 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm a1 \u dom De) Hxrest5))))).
    assert (HxDe : x \notin dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm a1) (dom De) (proj2 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm a1 \u dom De) Hxrest5))))).
    pick fresh y for ((L \u {{x}}) \u (fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm B1b \u fv_tm_tm A3)).
    assert (HyL : y \notin L \u {{x}}) by (intro C; apply Fr0; fsetdec).
    assert (Hy0 : y \notin L) by
      (exact (proj1 (self_notin_union y L {{x}} HyL))).
    assert (Hyx : y \notin {{x}}) by
      (exact (proj2 (self_notin_union y L {{x}} HyL))).
    assert (Hyx' : y <> x) by (intro C; apply Hyx; apply singleton_iff; exact (@Logic.eq_sym atom y x C)).
    assert (Hyrest : y \notin fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm B1b \u fv_tm_tm A3) by
      (intro C; apply Fr0; fsetdec).
    assert (Hya0 : y \notin fv_tm_tm a0) by
      (exact (proj1 (self_notin_union y (fv_tm_tm a0) (fv_tm_tm B1 \u fv_tm_tm B1b \u fv_tm_tm A3) Hyrest))).
    assert (HyrestB : y \notin fv_tm_tm B1 \u fv_tm_tm B1b \u fv_tm_tm A3) by
      (exact (proj2 (self_notin_union y (fv_tm_tm a0) (fv_tm_tm B1 \u fv_tm_tm B1b \u fv_tm_tm A3) Hyrest))).
    assert (HyB1 : y \notin fv_tm_tm B1) by
      (exact (proj1 (self_notin_union y (fv_tm_tm B1) (fv_tm_tm B1b \u fv_tm_tm A3) HyrestB))).
    assert (HyrestB2 : y \notin fv_tm_tm B1b \u fv_tm_tm A3) by
      (exact (proj2 (self_notin_union y (fv_tm_tm B1) (fv_tm_tm B1b \u fv_tm_tm A3) HyrestB))).
    assert (HyB1b : y \notin fv_tm_tm B1b) by
      (exact (proj1 (self_notin_union y (fv_tm_tm B1b) (fv_tm_tm A3) HyrestB2))).
    assert (HyA3 : y \notin fv_tm_tm A3) by
      (exact (proj2 (self_notin_union y (fv_tm_tm B1b) (fv_tm_tm A3) HyrestB2))).
    pose proof (invert_Beta_a_Sigma2 Hbeta y (@notin_union y (fv_tm_tm B1b) (fv_tm_tm A3) HyB1b HyA3)) as HBy.
    pose proof (Beta_open_arg B1b A3 a0 y HBy HyB1b HyA3 (typing_lc _ _ _ _ H1b)) as HBarg.
    assert (HwfA3 : exists Gw3, Typing (De++D5) Gw3 (open_tm_wrt_tm A3 a0) a_Type).
    { apply (sigma_wf_open_de_beta2 nil (De++D5) nil Gty (ctx_mul 0 Ge ++ G1b)
               qq A2 A3 a0 a_Type (a_Sigma qq A2 A3)).
      - reflexivity.
      - apply sh_nil.
      - apply De_ok_nil.
      - exact HshG1bfull.
      - exact Hwf.
      - apply B_Refl. apply (typing_lc_ty _ _ _ _ Hwf).
      - exact HpayA2. }
    destruct HwfA3 as [Gw3 HwfA3].
    assert (Hargconv : Typing (De++D5) (ctx_mul 0 Ge ++ G2b) a1 (open_tm_wrt_tm A3 a0)).
    { exact (T_conv (De++D5) (ctx_mul 0 Ge ++ G2b) a1 (open_tm_wrt_tm A3 a0)
               (open_tm_wrt_tm B1b a0) Gw3 Hargfull0 HwfA3 HBarg). }
    pose proof (Hfun x HxL y HyL) as Hbody.
    assert (HshGt : shapeDG (De++D5) Gt).
    { pose proof (@typing_align ((x ~ Tm A2) ++ (De++D5)) ((x ~ (qq,Tm A2)) ++ Gt)
              (open_tm_wrt_tm b (a_Var_f x))
              (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                      (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))
              Hbody) as Hshfull.
      inversion Hshfull as [| z qz Az Dz Gz HS]; subst. exact HS. }
    assert (Hndbody : nodupD ((x ~ Tm A2) ++ (De++D5))) by
      (exact (@typing_nodup_lb ((x ~ Tm A2) ++ (De++D5)) ((x ~ (qq,Tm A2)) ++ Gt)
                (open_tm_wrt_tm b (a_Var_f x))
                (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                        (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y))))) Hbody)).
    assert (Hndy : nodupD (nil ++ (x,Tm A2) :: (De++D5))) by
      (simpl; change (nodupD ((x,Tm A2) :: (De++D5))); exact Hndbody).
    assert (Hlca0 : lc_tm a0) by (exact (typing_lc _ _ _ _ H1b)).
    assert (Hlca1 : lc_tm a1) by (exact (typing_lc _ _ _ _ H2b)).
    pose proof (typing_subst_gen nil x A2 (De++D5) nil Gt qq
                  (open_tm_wrt_tm b (a_Var_f x))
                  (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                          (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))
                  (ctx_mul 0 Ge ++ G1b) a0
                  Hbody sh_nil HshGt Hndy HxA2 Hlca0 HshG1bfull HpayA2) as Hres.
    rewrite (subst_open_self a0 x b Hlca0 Hxb) in Hres.
    assert (Htyeq : subst_tm_tm a0 x
             (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                     (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))
           = a_Pi 1 (open_tm_wrt_tm A3 a0)
                     (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))))).
    { simpl.
      rewrite (subst_open_self a0 x A3 Hlca0 HxA3).
      rewrite (subst_close_rec_comm a0 x y 0 (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y))) Hlca0 (fun C => Hyx' (@Logic.eq_sym atom x y C)) Hya0).
      rewrite (subst_open_comm a0 Hlca0 B1 x 0 (a_Tensor (a_Var_f x) (a_Var_f y))).
      rewrite (subst_fresh B1 a0 x HxB1).
      assert (HcTensor : subst_tm_tm a0 x (a_Tensor (a_Var_f x) (a_Var_f y))
                       = a_Tensor a0 (a_Var_f y)).
      { change (a_Tensor (subst_tm_tm a0 x (a_Var_f x))
                         (subst_tm_tm a0 x (a_Var_f y)) = a_Tensor a0 (a_Var_f y)).
        rewrite (subst_var_self a0 x). rewrite (subst_var_neq a0 x y Hyx'). reflexivity. }
      rewrite HcTensor. reflexivity. }
    rewrite Htyeq in Hres.
    assert (Happ := T_app (De++D5)
             (ctx_plus Gt (ctx_mul qq (ctx_mul 0 Ge ++ G1b))) 1
             (ctx_mul 0 Ge ++ G2b) (open_tm_wrt_tm b a0) a1
             (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))))
             (open_tm_wrt_tm A3 a0) Hres Hargconv).
    assert (HlcE : lc_tm (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))).
    { pose proof (typing_lc_ty _ _ _ _ Hres) as HlcPi.
      inversion HlcPi as [| | | q0 A0 B0 HlcA0 HlcB0 | | | | | | | | | | | | | | |]; subst.
      specialize (HlcB0 y).
      rewrite (open_close_self (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))) y) in HlcB0.
      exact HlcB0. }
    assert (HclE : cl 0 (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))) by (apply lc_cl; exact HlcE).
    assert (Hcloseop : open_tm_wrt_tm (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))) a1
                     = subst_tm_tm a1 y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))).
    { unfold open_tm_wrt_tm, close_tm_wrt_tm.
      apply (open_close_cl (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))) 0 y a1 HclE). }
    rewrite Hcloseop in Happ.
    assert (HsubE : subst_tm_tm a1 y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))
                  = open_tm_wrt_tm B1 (a_Tensor a0 a1)).
    { rewrite (subst_open_comm a1 Hlca1 B1 y 0 (a_Tensor a0 (a_Var_f y))).
      rewrite (subst_fresh B1 a1 y HyB1).
      assert (HcTensor1 : subst_tm_tm a1 y (a_Tensor a0 (a_Var_f y))
                        = a_Tensor a0 a1).
      { change (a_Tensor (subst_tm_tm a1 y a0)
                         (subst_tm_tm a1 y (a_Var_f y)) = a_Tensor a0 a1).
        rewrite (subst_fresh a0 a1 y Hya0). rewrite (subst_var_self a1 y). reflexivity. }
      rewrite HcTensor1. reflexivity. }
    rewrite HsubE in Happ.
    assert (Hqmul : ctx_mul qq (ctx_mul 0 Ge ++ G1b)
                  = ctx_mul 0 Ge ++ ctx_mul qq G1b).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r. reflexivity. }
    rewrite Hqmul in Happ.
    rewrite (ctx_mul_1 (ctx_mul 0 Ge ++ G2b)) in Happ.
    assert (HAA : ctx_plus (ctx_mul 0 Ge) (ctx_mul 0 Ge) = ctx_mul 0 Ge).
    { apply (ctx_plus_zero De (ctx_mul 0 Ge) Ge); [apply shapeDG_mul; exact HshDe | exact HshDe]. }
    assert (Hplus : ctx_plus (ctx_mul 0 Ge ++ ctx_mul qq G1b) (ctx_mul 0 Ge ++ G2b)
                  = ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b).
    { rewrite (ctx_plus_app (ctx_mul 0 Ge) (ctx_mul qq G1b) (ctx_mul 0 Ge) G2b (@Logic.eq_refl nat (length (ctx_mul 0 Ge)))).
      rewrite HAA. reflexivity. }
    assert (HshAB : shapeDG (De++D5) (ctx_mul 0 Ge ++ ctx_mul qq G1b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | apply shapeDG_mul; exact HshG1b]. }
    assert (HshAC : shapeDG (De++D5) (ctx_mul 0 Ge ++ G2b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact HshG2b]. }
    assert (HshABC : shapeDG (De++D5) (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe |
        apply shapeDG_plus; [apply shapeDG_mul; exact HshG1b | exact HshG2b]]. }
    assert (HctxR : ctx_plus (ctx_plus Gt (ctx_mul 0 Ge ++ ctx_mul qq G1b))
                             (ctx_mul 0 Ge ++ G2b)
                  = ctx_plus (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b) Gt).
    { transitivity (ctx_plus Gt (ctx_plus (ctx_mul 0 Ge ++ ctx_mul qq G1b)
                                          (ctx_mul 0 Ge ++ G2b))).
      - apply (ctx_plus_assoc_shape (De++D5) Gt
                 (ctx_mul 0 Ge ++ ctx_mul qq G1b) (ctx_mul 0 Ge ++ G2b) HshGt HshAB HshAC).
      - rewrite Hplus.
        apply (@Logic.eq_sym (context)
                 (ctx_plus (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b) Gt)
                 (ctx_plus Gt (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b))).
        apply (ctx_plus_comm_shape2 (De++D5)
                 (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b) Gt HshABC HshGt). }
    rewrite HctxR in Happ.
    exact Happ.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma tensor_beta_noWF_gen :
 forall (tm0 TT:tm) (De Dd:D) (Ge G1 Gt:context)
        (q qq:usage) (A2 A3 a0 a1 b B1:tm) (L:atoms),
  tm0 = a_Tensor a0 a1 -> TT = a_Sigma qq A2 A3 ->
  shapeDG De Ge -> De_ok De Dd -> env_wf (De++Dd) ->
  Typing Dd G1 tm0 TT ->
  (forall x, x \notin L -> forall y, y \notin L \u {{x}} ->
     Typing ((x ~ Tm A2) ++ (De++Dd)) ((x ~ (qq,Tm A2)) ++ Gt)
       (open_tm_wrt_tm b (a_Var_f x))
       (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
               (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))) ->
  Typing (De++Dd) (ctx_plus (ctx_mul 0 Ge ++ G1) Gt)
         (a_App (open_tm_wrt_tm b a0) a1)
         (open_tm_wrt_tm B1 (a_Tensor a0 a1)).
Proof.
  intros tm0 TT De Dd Ge G1 Gt q qq A2 A3 a0 a1 b B1 L Et ET HshDe Hok Henv H1 Hfun.
  revert De Ge Gt q qq A2 A3 a0 a1 b B1 L Et ET HshDe Hok Henv Hfun.
  induction H1 as
  [ D5 G2b a A0b G1b H1b IH1b Hsub
  | | D5 x Ax0 Gb Hnotin H1b IH1b
  | D5 x Ax0 G1b a B0b G2b Hnotin H1b IH1b H2b IH2b
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 G1b qL AL a B0b G2b Hfunb IHfunb H2b IH2b
  | D5 G1b qqB G2b a b1 B1b A1b H1b IH1b H2b IH2b
  | D5 G1b a B0b A1b G2b H1b IH1b H2b IH2b Hbconv
  | |
  | Lb D5 G1b G2b a b1 r B0b B1b G3 H1b IH1b Heq H2b IH2b Hfunb IHfunb
  | D5 Gb qqB A1b H1b IH1b
  | D5 qqB Gb a A1b H1b IH1b
  | Lb D5 G1b G2b a b1 r qqB A1b B1b G3 H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1b G2b A1b A2b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | D5 Gb a A1b A2b G1b H1b IH1b H2b IH2b
  | Lb D5 qqB G1b G2b a b1 b2 r A1b A2b B0b B1b B2b G3 Hq0 H1b IH1b Heq1 Heq2 H3 IH3 H4 IH4 Hfunb IHfunb
  | Lb D5 G1b G2b qqB A1b B1b r H1b IH1b Hfunb IHfunb
  | Lb D5 qqB G1b G2b a b1 A1b B1b G3 r H1b IH1b H2b IH2b Hfunb IHfunb
  | Lb D5 G1b G2b a b1 r A1b B1b qqB A2b A3b G3 Heq H1b IH1b Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros De Ge Gt q qq A2 A3 a0 a1 b B1 L Et ET HshDe Hok Henv Hfun.
  - (* T_sub *)
    pose proof (IH1b De Ge Gt q qq A2 A3 a0 a1 b B1 L Et ET HshDe Hok Henv Hfun) as Hres.
    assert (Hnd5 : nodupD D5) by (exact (@typing_nodup_lb D5 G1b a A0b H1b)).
    assert (Hsh1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a A0b H1b)).
    assert (HshGt : shapeDG (De++D5) Gt).
    { apply (shapeDG_binder_inv L A2 qq (De++D5) Gt). intros x Hx.
      pick fresh y for (L \u {{x}}).
      assert (Hy : y \notin L \u {{x}}) by assumption.
      exact (@typing_align _ _ _ _ (Hfun x Hx y Hy)). }
    assert (Hsubc := ctx_sub_box De D5 Ge G2b G1b Gt Hok Hnd5 HshDe Hsh1b HshGt Hsub).
    exact (T_sub (De++D5) (ctx_plus (ctx_mul 0 Ge ++ G2b) Gt)
             (a_App (open_tm_wrt_tm b a0) a1) (open_tm_wrt_tm B1 (a_Tensor a0 a1))
             (ctx_plus (ctx_mul 0 Ge ++ G1b) Gt) Hres Hsubc).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *)
    assert (Hsingle : shapeDG (x ~ Tm Ax0) (x ~ (0,Tm Ax0))).
    { change (shapeDG ((x,Tm Ax0)::nil) ((x,(0,Tm Ax0))::nil)). apply sh_cons. apply sh_nil. }
    assert (HshDe_new : shapeDG (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0)))).
    { apply shapeDG_app; [exact HshDe | exact Hsingle]. }
    assert (HxDe : x \notin dom De).
    { intro C. destruct Hok as [Hdis _]. assert (Hx : x \in dom ((x ~ Tm Ax0) ++ D5)).
      { rewrite dom_app. apply union_iff. left.
        apply (proj2 (in_dom_cons x x Ax0 nil) (or_introl (@Logic.eq_refl atom x))). }
      exact (Hdis x C Hx). }
    assert (Hok_new : De_ok (De ++ (x ~ Tm Ax0)) D5).
    { apply (De_ok_append_cons De x (Tm Ax0) D5).
      - change (De_ok De ((x,Tm Ax0)::D5)). exact Hok.
      - exact HxDe.
      - exact Hnotin. }
    assert (Henv_new : env_wf ((De ++ (x ~ Tm Ax0)) ++ D5)).
    { rewrite app_assoc. exact Henv. }
    assert (Hfun_new : forall y, y \notin L -> forall z, z \notin L \u {{y}} ->
       Typing ((y ~ Tm A2) ++ ((De ++ (x ~ Tm Ax0)) ++ D5))
         ((y ~ (qq,Tm A2)) ++ Gt) (open_tm_wrt_tm b (a_Var_f y))
         (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f y))
                 (close_tm_wrt_tm z (open_tm_wrt_tm B1 (a_Tensor (a_Var_f y) (a_Var_f z)))))).
    { intros y Hy z Hz. rewrite app_assoc. exact (Hfun y Hy z Hz). }
    pose proof (IH1b (De ++ (x ~ Tm Ax0)) (Ge ++ (x ~ (0,Tm Ax0))) Gt q qq
                  A2 A3 a0 a1 b B1 L Et ET HshDe_new Hok_new Henv_new Hfun_new) as Hres.
    assert (Hctx : ctx_plus (ctx_mul 0 (Ge ++ (x ~ (0,Tm Ax0))) ++ G1b) Gt
                 = ctx_plus (ctx_mul 0 Ge ++ ((x ~ (0,Tm Ax0)) ++ G1b)) Gt).
    { rewrite ctx_mul_app.
      assert (Hsm : ctx_mul 0 (x ~ (0,Tm Ax0)) = (x ~ (0,Tm Ax0))).
      { rewrite ctx_mul_cons. simpl. rewrite qmul_0_l. reflexivity. }
      rewrite Hsm. rewrite app_assoc. reflexivity. }
    rewrite Hctx in Hres. rewrite <- app_assoc. exact Hres.
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    rewrite ET in H2b. rewrite ET in Hbconv.
    pose proof (@typing_add_zero_prefix De Ge D5 G2b (a_Sigma qq A2 A3) a_Type
                  HshDe Hok Henv H2b) as Hwf.
    exact (tensor_beta_wf_gen a A1b De D5 Ge G1b Gt (ctx_mul 0 Ge ++ G2b)
             q qq A2 A3 a0 a1 b B1 L Et HshDe Hok Henv H1b Hbconv Hwf Hfun).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *) discriminate Et.
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *)
    injection Et as Ha Hb. subst a. subst b1.
    injection ET as Hq HAL HBL. subst qqB. subst A1b. subst B1b.
    assert (HshG1b : shapeDG D5 G1b) by (exact (@typing_align D5 G1b a0 A2 H1b)).
    assert (HshG2b : shapeDG D5 G2b) by (exact (@typing_align D5 G2b a1 (open_tm_wrt_tm A3 a0) H2b)).
    pose proof (@typing_add_zero_prefix De Ge D5 G1b a0 A2 HshDe Hok Henv H1b) as Hpayfull.
    pose proof (@typing_add_zero_prefix De Ge D5 G2b a1 (open_tm_wrt_tm A3 a0) HshDe Hok Henv H2b) as Hargfull.
    assert (HshG1bfull : shapeDG (De++D5) (ctx_mul 0 Ge ++ G1b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact HshG1b]. }
    pick fresh x for (L \u fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1
                     \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De).
    assert (HxL : x \notin L) by
      (exact (proj1 (self_notin_union x L (fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Fr))).
    assert (Hxrest : x \notin fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x L (fv_tm_tm A2 \u fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Fr))).
    assert (HxA2 : x \notin fv_tm_tm A2) by
      (exact (proj1 (self_notin_union x (fv_tm_tm A2) (fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest))).
    assert (Hxrest2 : x \notin fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm A2) (fv_tm_tm A3 \u fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest))).
    assert (HxA3 : x \notin fv_tm_tm A3) by
      (exact (proj1 (self_notin_union x (fv_tm_tm A3) (fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest2))).
    assert (Hxrest3 : x \notin fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm A3) (fv_tm_tm b \u fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest2))).
    assert (Hxb : x \notin fv_tm_tm b) by
      (exact (proj1 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest3))).
    assert (Hxrest4 : x \notin fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm b) (fv_tm_tm B1 \u fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest3))).
    assert (HxB1 : x \notin fv_tm_tm B1) by
      (exact (proj1 (self_notin_union x (fv_tm_tm B1) (fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest4))).
    assert (Hxrest5 : x \notin fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm B1) (fv_tm_tm a0 \u fv_tm_tm a1 \u dom De) Hxrest4))).
    assert (Hxa0 : x \notin fv_tm_tm a0) by
      (exact (proj1 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm a1 \u dom De) Hxrest5))).
    assert (Hxa1 : x \notin fv_tm_tm a1) by
      (exact (proj1 (self_notin_union x (fv_tm_tm a1) (dom De) (proj2 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm a1 \u dom De) Hxrest5))))).
    assert (HxDe : x \notin dom De) by
      (exact (proj2 (self_notin_union x (fv_tm_tm a1) (dom De) (proj2 (self_notin_union x (fv_tm_tm a0) (fv_tm_tm a1 \u dom De) Hxrest5))))).
    pick fresh y for ((L \u {{x}}) \u (fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm A3 \u fv_tm_tm b)).
    assert (HyL : y \notin L \u {{x}}) by (intro C; apply Fr0; fsetdec).
    assert (Hy0 : y \notin L) by
      (exact (proj1 (self_notin_union y L {{x}} HyL))).
    assert (Hyx : y \notin {{x}}) by
      (exact (proj2 (self_notin_union y L {{x}} HyL))).
    assert (Hyx' : y <> x) by (intro C; apply Hyx; apply singleton_iff; exact (@Logic.eq_sym atom y x C)).
    assert (Hyrest : y \notin fv_tm_tm a0 \u fv_tm_tm B1 \u fv_tm_tm A3 \u fv_tm_tm b) by
      (intro C; apply Fr0; fsetdec).
    assert (Hya0 : y \notin fv_tm_tm a0) by
      (exact (proj1 (self_notin_union y (fv_tm_tm a0) (fv_tm_tm B1 \u fv_tm_tm A3 \u fv_tm_tm b) Hyrest))).
    assert (Hyrest2 : y \notin fv_tm_tm B1 \u fv_tm_tm A3 \u fv_tm_tm b) by
      (exact (proj2 (self_notin_union y (fv_tm_tm a0) (fv_tm_tm B1 \u fv_tm_tm A3 \u fv_tm_tm b) Hyrest))).
    assert (HyB1 : y \notin fv_tm_tm B1) by
      (exact (proj1 (self_notin_union y (fv_tm_tm B1) (fv_tm_tm A3 \u fv_tm_tm b) Hyrest2))).
    pose proof (Hfun x HxL y HyL) as Hbody.
    assert (HshGt : shapeDG (De++D5) Gt).
    { pose proof (@typing_align _ _ _ _ Hbody) as Hshfull.
      inversion Hshfull as [| z qz Az Dz Gz HS]; subst. exact HS. }
    assert (Hndbody : nodupD ((x ~ Tm A2) ++ (De++D5))) by
      (exact (@typing_nodup_lb ((x ~ Tm A2) ++ (De++D5)) ((x ~ (qq,Tm A2)) ++ Gt)
                (open_tm_wrt_tm b (a_Var_f x))
                (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                        (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y))))) Hbody)).
    assert (Hndy : nodupD (nil ++ (x,Tm A2) :: (De++D5))) by
      (simpl; change (nodupD ((x,Tm A2) :: (De++D5))); exact Hndbody).
    assert (Hlca0 : lc_tm a0) by (exact (typing_lc _ _ _ _ H1b)).
    assert (Hlca1 : lc_tm a1) by (exact (typing_lc _ _ _ _ H2b)).
    pose proof (typing_subst_gen nil x A2 (De++D5) nil Gt qq
                  (open_tm_wrt_tm b (a_Var_f x))
                  (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                          (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))
                  (ctx_mul 0 Ge ++ G1b) a0
                  Hbody sh_nil HshGt Hndy HxA2 Hlca0 HshG1bfull Hpayfull) as Hres.
    rewrite (subst_open_self a0 x b Hlca0 Hxb) in Hres.
    assert (Htyeq : subst_tm_tm a0 x
             (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
                     (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))
           = a_Pi 1 (open_tm_wrt_tm A3 a0)
                     (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))))).
    { simpl.
      rewrite (subst_open_self a0 x A3 Hlca0 HxA3).
      rewrite (subst_close_rec_comm a0 x y 0 (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y))) Hlca0 (fun C => Hyx' (@Logic.eq_sym atom x y C)) Hya0).
      rewrite (subst_open_comm a0 Hlca0 B1 x 0 (a_Tensor (a_Var_f x) (a_Var_f y))).
      rewrite (subst_fresh B1 a0 x HxB1).
      assert (HcTensor : subst_tm_tm a0 x (a_Tensor (a_Var_f x) (a_Var_f y))
                       = a_Tensor a0 (a_Var_f y)).
      { change (a_Tensor (subst_tm_tm a0 x (a_Var_f x))
                         (subst_tm_tm a0 x (a_Var_f y)) = a_Tensor a0 (a_Var_f y)).
        rewrite (subst_var_self a0 x). rewrite (subst_var_neq a0 x y Hyx'). reflexivity. }
      rewrite HcTensor. reflexivity. }
    rewrite Htyeq in Hres.
    assert (Happ := T_app (De++D5)
             (ctx_plus Gt (ctx_mul qq (ctx_mul 0 Ge ++ G1b))) 1
             (ctx_mul 0 Ge ++ G2b) (open_tm_wrt_tm b a0) a1
             (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))))
             (open_tm_wrt_tm A3 a0) Hres Hargfull).
    assert (HlcE : lc_tm (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))).
    { pose proof (typing_lc_ty _ _ _ _ Hres) as HlcPi.
      inversion HlcPi as [| | | q0 A0 B0 HlcA0 HlcB0 | | | | | | | | | | | | | | |]; subst.
      specialize (HlcB0 y).
      rewrite (open_close_self (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))) y) in HlcB0.
      exact HlcB0. }
    assert (HclE : cl 0 (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))) by (apply lc_cl; exact HlcE).
    assert (Hcloseop : open_tm_wrt_tm (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))) a1
                     = subst_tm_tm a1 y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))).
    { unfold open_tm_wrt_tm, close_tm_wrt_tm.
      apply (open_close_cl (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y))) 0 y a1 HclE). }
    rewrite Hcloseop in Happ.
    assert (HsubE : subst_tm_tm a1 y (open_tm_wrt_tm B1 (a_Tensor a0 (a_Var_f y)))
                  = open_tm_wrt_tm B1 (a_Tensor a0 a1)).
    { rewrite (subst_open_comm a1 Hlca1 B1 y 0 (a_Tensor a0 (a_Var_f y))).
      rewrite (subst_fresh B1 a1 y HyB1).
      assert (HcTensor1 : subst_tm_tm a1 y (a_Tensor a0 (a_Var_f y))
                        = a_Tensor a0 a1).
      { change (a_Tensor (subst_tm_tm a1 y a0)
                         (subst_tm_tm a1 y (a_Var_f y)) = a_Tensor a0 a1).
        rewrite (subst_fresh a0 a1 y Hya0). rewrite (subst_var_self a1 y). reflexivity. }
      rewrite HcTensor1. reflexivity. }
    rewrite HsubE in Happ.
    assert (Hqmul : ctx_mul qq (ctx_mul 0 Ge ++ G1b)
                  = ctx_mul 0 Ge ++ ctx_mul qq G1b).
    { rewrite ctx_mul_app. rewrite ctx_mul_ctx_mul. rewrite qmul_0_r. reflexivity. }
    rewrite Hqmul in Happ.
    rewrite (ctx_mul_1 (ctx_mul 0 Ge ++ G2b)) in Happ.
    assert (HAA : ctx_plus (ctx_mul 0 Ge) (ctx_mul 0 Ge) = ctx_mul 0 Ge).
    { apply (ctx_plus_zero De (ctx_mul 0 Ge) Ge); [apply shapeDG_mul; exact HshDe | exact HshDe]. }
    assert (Hplus : ctx_plus (ctx_mul 0 Ge ++ ctx_mul qq G1b) (ctx_mul 0 Ge ++ G2b)
                  = ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b).
    { rewrite (ctx_plus_app (ctx_mul 0 Ge) (ctx_mul qq G1b) (ctx_mul 0 Ge) G2b (@Logic.eq_refl nat (length (ctx_mul 0 Ge)))).
      rewrite HAA. reflexivity. }
    assert (HshAB : shapeDG (De++D5) (ctx_mul 0 Ge ++ ctx_mul qq G1b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | apply shapeDG_mul; exact HshG1b]. }
    assert (HshAC : shapeDG (De++D5) (ctx_mul 0 Ge ++ G2b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe | exact HshG2b]. }
    assert (HshABC : shapeDG (De++D5) (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b)).
    { apply shapeDG_app; [apply shapeDG_mul; exact HshDe |
        apply shapeDG_plus; [apply shapeDG_mul; exact HshG1b | exact HshG2b]]. }
    assert (HctxR : ctx_plus (ctx_plus Gt (ctx_mul 0 Ge ++ ctx_mul qq G1b))
                             (ctx_mul 0 Ge ++ G2b)
                  = ctx_plus (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b) Gt).
    { transitivity (ctx_plus Gt (ctx_plus (ctx_mul 0 Ge ++ ctx_mul qq G1b)
                                          (ctx_mul 0 Ge ++ G2b))).
      - apply (ctx_plus_assoc_shape (De++D5) Gt
                 (ctx_mul 0 Ge ++ ctx_mul qq G1b) (ctx_mul 0 Ge ++ G2b) HshGt HshAB HshAC).
      - rewrite Hplus.
        apply (@Logic.eq_sym (context)
                 (ctx_plus (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b) Gt)
                 (ctx_plus Gt (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b))).
        apply (ctx_plus_comm_shape2 (De++D5)
                 (ctx_mul 0 Ge ++ ctx_plus (ctx_mul qq G1b) G2b) Gt HshABC HshGt). }
    rewrite HctxR in Happ.
    exact Happ.
  - (* T_Spread *) discriminate Et.
Qed.

Lemma tensor_spread_beta_typing :
 forall (D:D) (G1:context) (a0 a1:tm) (A2 A3:tm) (qq:usage) (G2:context)
        (b:tm) (B1:tm) (L:atoms),
  Typing D G1 (a_Tensor a0 a1) (a_Sigma qq A2 A3) ->
  (forall x, x \notin L -> forall y, y \notin L \u {{x}} ->
     Typing ((x ~ Tm A2) ++ D) ((x ~ (qq,Tm A2)) ++ G2)
       (open_tm_wrt_tm b (a_Var_f x))
       (a_Pi 1 (open_tm_wrt_tm A3 (a_Var_f x))
               (close_tm_wrt_tm y (open_tm_wrt_tm B1 (a_Tensor (a_Var_f x) (a_Var_f y)))))) ->
  Typing D (ctx_plus G1 G2) (a_App (open_tm_wrt_tm b a0) a1)
    (open_tm_wrt_tm B1 (a_Tensor a0 a1)).
Proof.
  intros D G1 a0 a1 A2 A3 qq G2 b B1 L H1 Hfun.
  pose proof (tensor_beta_noWF_gen (a_Tensor a0 a1) (a_Sigma qq A2 A3)
                nil D nil G1 G2 qq qq A2 A3 a0 a1 b B1 L
                (@Logic.eq_refl tm (a_Tensor a0 a1))
                (@Logic.eq_refl tm (a_Sigma qq A2 A3))
                sh_nil (De_ok_nil D)
                (typing_env_wf D G1 (a_Tensor a0 a1) (a_Sigma qq A2 A3) H1)
                H1 Hfun) as Hres.
  simpl in Hres. exact Hres.
Qed.

(* ===== inlined from Pres.v ===== *)
Definition ctx_nonneg (G:context) : Prop :=
  forall (x:atom) (q:usage) (s:sort), List.In (x,(q,s)) G -> 0 <= q.

Lemma ule_add_0_l : forall (q1 q2:usage), 0 <= q1 -> q2 <= q1 + q2.
Proof.
  intros q1 q2 H. pose proof (po_semiring1 0 q1 q2 H) as Hh.
  rewrite qplus_0_l in Hh. exact Hh.
Qed.

Lemma ctx_sub_nonneg : forall (D0:D) (G1 G2:context),
  ctx_sub D0 G1 G2 -> ctx_nonneg G1 -> ctx_nonneg G2.
Proof.
  intros D0 G1 G2 H. induction H as [| D x a G1' q1 G2' q2 Hle Hsub IH Hnotin];
    intros Hnn x0 q s Hin.
  - simpl in Hin. destruct Hin.
  - simpl in Hin. destruct Hin as [Heq|Hin].
    + inversion Heq; subst.
      apply (ule_trans 0 q1 _).
      * apply (Hnn x0 q1 s). simpl. left. reflexivity.
      * exact Hle.
    + apply (IH (fun y qq ss Hy => Hnn y qq ss (or_intror Hy)) x0 q s Hin).
Qed.

Lemma ctx_sub_add_ctx : forall (D0:D) (G1 G2:context),
  nodupD D0 -> shapeDG D0 G1 -> shapeDG D0 G2 ->
  ctx_nonneg G1 -> ctx_sub D0 G2 (ctx_plus G1 G2).
Proof.
  intros D0. induction D0 as [|[x A] D0 IH]; intros G1 G2 Hnd HS1 HS2 Hnn.
  - inversion HS1. inversion HS2. constructor.
  - destruct A as [A]. inversion HS1 as [| y q1 A1 D1 G1' HS1']; subst.
    inversion HS2 as [| y2 q2 A2 D2 G2' HS2']; subst.
    simpl. apply CS_ConsTm.
    + apply (ule_add_0_l q1 q2). apply (Hnn x q1 (Tm A)). simpl. left. reflexivity.
    + apply (IH G1' G2').
      * exact (proj2 (nodupD_cons_inv x (Tm A) D0 Hnd)).
      * exact HS1'.
      * exact HS2'.
      * intros y qq ss Hy. apply (Hnn y qq ss). simpl. right. exact Hy.
    + exact (proj1 (nodupD_cons_inv x (Tm A) D0 Hnd)).
Qed.

Lemma typing_nodup : forall (D0:D) (G:context) (a A:tm), Typing D0 G a A -> nodupD D0.
Proof.
  intros D0 G a A H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ].
  all: try assumption.
  - apply nodupD_nil.
  - change (nodupD ((x,Tm Ax0) :: D5)). apply nodupD_cons; assumption.
  - change (nodupD ((x,Tm Ax0) :: D5)). apply nodupD_cons; assumption.
  - apply nodupD_nil.
  - apply nodupD_nil.
Qed.


Lemma typing_TmUnit_ctx_nonneg : forall (D0:D) (G:context) (t A:tm),
  Typing D0 G t A -> t = a_TmUnit -> ctx_nonneg G.
Proof.
  intros D0 G t A H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros Hequnit xmem qmem smem Hinmem.
  - (* T_sub *) exact (ctx_sub_nonneg D5 G1 G2 Hsub (IH1 Hequnit) xmem qmem smem Hinmem).
  - (* T_type *) discriminate Hequnit.
  - (* T_var *) discriminate Hequnit.
  - (* T_weak *)
    simpl in Hinmem. destruct Hinmem as [Hin|Hin].
    + inversion Hin; subst. apply ule_refl.
    + exact (IH1 Hequnit xmem qmem smem Hin).
  - (* T_pi *) discriminate Hequnit.
  - (* T_lam *) discriminate Hequnit.
  - (* T_app *) discriminate Hequnit.
  - (* T_conv *) exact (IH1 Hequnit xmem qmem smem Hinmem).
  - (* T_unit *) simpl in Hinmem. destruct Hinmem.
  - (* T_Unit *) discriminate Hequnit.
  - (* T_UnitE *) discriminate Hequnit.
  - (* T_Box *) discriminate Hequnit.
  - (* T_box *) discriminate Hequnit.
  - (* T_letbox *) discriminate Hequnit.
  - (* T_sum *) discriminate Hequnit.
  - (* T_inj1 *) discriminate Hequnit.
  - (* T_inj2 *) discriminate Hequnit.
  - (* T_case *) discriminate Hequnit.
  - (* T_Sigma *) discriminate Hequnit.
  - (* T_Tensor *) discriminate Hequnit.
  - (* T_Spread *) discriminate Hequnit.
Qed.


Lemma Beta_open_comm : forall (a a' B:tm) (x:tmvar),
  lc_tm a -> lc_tm a' -> Beta a a' -> x \notin fv_tm_tm B ->
  lc_tm (open_tm_wrt_tm B (a_Var_f x)) ->
  Beta (open_tm_wrt_tm B a) (open_tm_wrt_tm B a').
Proof.
  intros a a' B x Hla Hla' HB Hx Hlc.
  pose proof (subst_Beta2 a a' x (open_tm_wrt_tm B (a_Var_f x)) Hlc HB) as Hb.
  rewrite (subst_open_self a x B Hla Hx) in Hb.
  rewrite (subst_open_self a' x B Hla' Hx) in Hb.
  exact Hb.
Qed.

Lemma typing_open_type : forall (L:atoms) (D0:D) (A0 B0 a:tm) (r:usage) (G3 Gt:context),
  (forall y, y \notin L -> Typing ((y ~ Tm A0) ++ D0) ((y ~ (r,Tm A0)) ++ G3)
      (open_tm_wrt_tm B0 (a_Var_f y)) a_Type) ->
  Typing D0 Gt a A0 ->
  shapeDG D0 G3 ->
  Typing D0 (ctx_plus G3 (ctx_mul r Gt)) (open_tm_wrt_tm B0 a) a_Type.
Proof.
  intros L D0 A0 B0 a r G3 Gt Hfun Harg HshG3.
  pick fresh y for (L \u fv_tm_tm B0 \u fv_tm_tm A0).
  assert (HyL : y \notin L) by
    (exact (proj1 (self_notin_union y L (fv_tm_tm B0 \u fv_tm_tm A0) Fr))).
  assert (HyBA : y \notin fv_tm_tm B0 \u fv_tm_tm A0) by
    (exact (proj2 (self_notin_union y L (fv_tm_tm B0 \u fv_tm_tm A0) Fr))).
  assert (HyB : y \notin fv_tm_tm B0) by
    (exact (proj1 (self_notin_union y (fv_tm_tm B0) (fv_tm_tm A0) HyBA))).
  assert (Hy2 : y \notin fv_tm_tm A0) by
    (exact (proj2 (self_notin_union y (fv_tm_tm B0) (fv_tm_tm A0) HyBA))).
  pose proof (Hfun y HyL) as Hbody.
  pose proof (typing_subst_gen nil y A0 D0 nil G3 r (open_tm_wrt_tm B0 (a_Var_f y)) a_Type
                Gt a Hbody sh_nil HshG3
                (typing_nodup _ _ _ _ Hbody) Hy2 (typing_lc _ _ _ _ Harg)
                (typing_align _ _ _ _ Harg) Harg) as Hres.
  simpl in Hres.
  rewrite (subst_open_self a y B0 (typing_lc _ _ _ _ Harg) HyB) in Hres.
  simpl in Hres. exact Hres.
Qed.


Lemma box_usage_beta : forall (D0:D) (G:context) (t0 T:tm), Typing D0 G t0 T ->
  forall (q:usage) (a0:tm) (qq:usage) (A1:tm),
  t0 = a_box q a0 -> Beta T (a_Box qq A1) -> q = qq.
Proof.
  intros D0 G t0 T H.
  induction H as
  [ D5 G2 a A0b G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0b G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qqB A1b B1b r H1 IH1 Hfun IHfun
  | L D5 G1 qqB A1b a B1b G2 Hfun IHfun H2 IH2
  | D5 G1 qqB G2 a b B1b A1b H1 IH1 H2 IH2
  | D5 G1 a B0b A1b G2 H1 IH1 H2 IH2 Hbconv
  | |
  | L D5 G1 G2 a b r B0b B1b G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qqB A1b H1 IH1
  | D5 qqB G a A1b H1 IH1
  | L D5 G1 G2 a b r qqB A1b B1b G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1b A2b H1 IH1 H2 IH2
  | D5 G a A1b A2b G1 H1 IH1 H2 IH2
  | D5 G a A1b A2b G1 H1 IH1 H2 IH2
  | L D5 qqB G1 G2 a b1 b2 r A1b A2b B0b B1b B2b G3 HqB H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qqB A1b B1b r H1 IH1 Hfun IHfun
  | L D5 qqB G1 G2 a b A1b B1b G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1b B1b qqB A2b A3b G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros q a0 qq0 A1 Et Hb.
  - (* T_sub *) apply (IH1 q a0 qq0 A1 Et Hb).
  - (* T_type *) discriminate Et.
  - (* T_var *) discriminate Et.
  - (* T_weak *) apply (IH1 q a0 qq0 A1 Et Hb).
  - (* T_pi *) discriminate Et.
  - (* T_lam *) discriminate Et.
  - (* T_app *) discriminate Et.
  - (* T_conv *)
    eapply IH1.
    + exact Et.
    + exact (B_Trans A1b (a_Box qq0 A1) B0b Hbconv Hb).
  - (* T_unit *) discriminate Et.
  - (* T_Unit *) discriminate Et.
  - (* T_UnitE *) discriminate Et.
  - (* T_Box *) discriminate Et.
  - (* T_box *)
    injection Et as Hq Ha. subst qqB. subst a.
    apply (invert_Beta_Box2 Hb).
  - (* T_letbox *) discriminate Et.
  - (* T_sum *) discriminate Et.
  - (* T_inj1 *) discriminate Et.
  - (* T_inj2 *) discriminate Et.
  - (* T_case *) discriminate Et.
  - (* T_Sigma *) discriminate Et.
  - (* T_Tensor *) discriminate Et.
  - (* T_Spread *) discriminate Et.
Qed.

Theorem preservation : forall D G a A,
  Typing D G a A -> forall a', Step a a' -> Typing D G a' A.
Proof.
  intros D G a A H.
  induction H as
  [ D5 G2 a A0 G1 H1 IH1 Hsub
  | | D5 x Ax0 G Hnotin H1 IH1
  | D5 x Ax0 G1 a B0 G2 Hnotin H1 IH1 H2 IH2
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 G1 qq A1 a B1 G2 Hfun IHfun H2 IH2
  | D5 G1 qq G2 a b B1 A1 H1 IH1 H2 IH2
  | D5 G1 a B0 A1 G2 H1 IH1 H2 IH2 Hbconv
  | | 
  | L D5 G1 G2 a b r B0 B1 G3 H1 IH1 Heq H2 IH2 Hfun IHfun
  | D5 G qq A1 H1 IH1
  | D5 qq G a A1 H1 IH1
  | L D5 G1 G2 a b r qq A1 B1 G3 H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3
  | D5 G1 G2 A1 A2 H1 IH1 H2 IH2
  | D5 G a A1 A2 G1 H1 IH1 H2 IH2
  | D5 G a A2 A1 G1 H1 IH1 H2 IH2
  | L D5 qq G1 G2 a b1 b2 r A1 A2 B0 B1 B2 G3 Hq H1 IH1 Heq1 Heq2 H3 IH3 H4 IH4 Hfun IHfun
  | L D5 G1 G2 qq A1 B1 r H1 IH1 Hfun IHfun
  | L D5 qq G1 G2 a b A1 B1 G3 r H1 IH1 H2 IH2 Hfun IHfun
  | L D5 G1 G2 a b r A1 B1 qq A2 A3 G3 Heq H1 IH1 Hfun2 IHfun2 Hfun3 IHfun3 ];
    intros a' Hstep.
  - (* T_sub *) exact (T_sub D5 G2 a' A0 G1 (IH1 a' Hstep) Hsub).
  - (* T_type *) inversion Hstep.
  - (* T_var *) inversion Hstep.
  - (* T_weak *) exact (T_weak D5 x Ax0 G1 a' B0 G2 Hnotin (IH1 a' Hstep) H2).
  - (* T_pi *) inversion Hstep.
  - (* T_lam *) inversion Hstep.
  - (* T_app *)
    inversion Hstep; subst.
    + (* S_AppCong *) exact (T_app D5 G1 qq G2 a'0 b B1 A1 (IH1 a'0 H5) H2).
    + (* S_Beta *)
      exact (lam_beta_noWF_de nil D5 nil G1 G2 q A a0 qq A1 B1 b
               sh_nil (De_ok_nil D5) (@typing_align D5 G2 b A1 H2) H1 H2).
  - (* T_conv *) exact (T_conv D5 G1 a' B0 A1 G2 (IH1 a' Hstep) H2 Hbconv).
  - (* T_unit *) inversion Hstep.
  - (* T_Unit *) inversion Hstep.
  - (* T_UnitE *)
    inversion Hstep; subst.
    + (* S_UnitCong *)
      pose proof (@typing_align D5 G1 a a_TyUnit H1) as HshG1.
      assert (HshG3 : shapeDG D5 G3).
      { apply (shapeDG_binder_inv L a_TyUnit r D5 G3). intros y Hy.
        apply (@typing_align ((y ~ Tm a_TyUnit) ++ D5) ((y ~ (r,Tm a_TyUnit)) ++ G3)
                  (open_tm_wrt_tm B0 (a_Var_f y)) a_Type (Hfun y Hy)). }
      pose proof (typing_open_type L D5 a_TyUnit B0 a r G3 G1 Hfun H1 HshG3) as Hty.
      pose proof (T_UnitE L D5 G1 G2 a'0 b r B0 (open_tm_wrt_tm B0 a_TmUnit) G3
                    (IH1 a'0 H7) (@Logic.eq_refl tm (open_tm_wrt_tm B0 a_TmUnit)) H2 Hfun) as HTU.
      pick fresh x for (L \u fv_tm_tm B0).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (fv_tm_tm B0) Fr))).
      assert (HxB : x \notin fv_tm_tm B0) by (exact (proj2 (self_notin_union x L (fv_tm_tm B0) Fr))).
      pose proof (Beta_open_comm a a'0 B0 x (typing_lc _ _ _ _ H1)
                    (typing_lc _ _ _ _ (IH1 a'0 H7)) (B_Step a a'0 H7) HxB
                    (typing_lc _ _ _ _ (Hfun x HxL))) as HBeta.
      exact (T_conv D5 (ctx_plus G1 G2) (a_letunitB a'0 b (a_Lam r a_TyUnit B0))
               (open_tm_wrt_tm B0 a) (open_tm_wrt_tm B0 a'0)
               (ctx_plus G3 (ctx_mul r G1)) HTU Hty (B_Sym _ _ HBeta)).
    + (* S_UnitBeta *)
      pose proof (@typing_nodup D5 G1 a_TmUnit a_TyUnit H1) as Hnd.
      pose proof (@typing_align D5 G1 a_TmUnit a_TyUnit H1) as HshG1.
      pose proof (@typing_align D5 G2 a' (open_tm_wrt_tm B0 a_TmUnit) H2) as HshG2.
      pose proof (@typing_TmUnit_ctx_nonneg D5 G1 a_TmUnit a_TyUnit H1 (@Logic.eq_refl tm a_TmUnit)) as Hnn.
      pose proof (ctx_sub_add_ctx D5 G1 G2 Hnd HshG1 HshG2 Hnn) as Hsub.
      exact (T_sub D5 (ctx_plus G1 G2) a' (open_tm_wrt_tm B0 a_TmUnit) G2 H2 Hsub).
  - (* T_Box *) inversion Hstep.
  - (* T_box *) inversion Hstep.
  - (* T_letbox *)
    inversion Hstep; subst.
    + (* S_BoxCong *)
      assert (HshG3 : shapeDG D5 G3).
      { apply (shapeDG_binder_inv L (a_Box qq A1) r D5 G3). intros y Hy.
        apply (@typing_align ((y ~ Tm (a_Box qq A1)) ++ D5)
                  ((y ~ (r,Tm (a_Box qq A1))) ++ G3)
                  (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun3 y Hy)). }
      pose proof (typing_open_type L D5 (a_Box qq A1) B1 a r G3 G1 Hfun3 H1 HshG3) as Hty.
      pose proof (T_letbox L D5 G1 G2 a'0 b r qq A1 B1 G3
                    (IH1 a'0 H6) Hfun2 Hfun3) as HTU.
      pick fresh x for (L \u fv_tm_tm B1).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (fv_tm_tm B1) Fr))).
      assert (HxB : x \notin fv_tm_tm B1) by (exact (proj2 (self_notin_union x L (fv_tm_tm B1) Fr))).
      pose proof (Beta_open_comm a a'0 B1 x (typing_lc _ _ _ _ H1)
                    (typing_lc _ _ _ _ (IH1 a'0 H6)) (B_Step a a'0 H6) HxB
                    (typing_lc _ _ _ _ (Hfun3 x HxL))) as HBeta.
      exact (T_conv D5 (ctx_plus G1 G2)
               (a_LetBoxB a'0 b (a_Lam r (a_Box qq A1) B1))
               (open_tm_wrt_tm B1 a) (open_tm_wrt_tm B1 a'0)
               (ctx_plus G3 (ctx_mul r G1)) HTU Hty (B_Sym _ _ HBeta)).
    + (* S_BoxBeta *)
      assert (Hq : q = qq) by
        (apply (box_usage_beta D5 G1 (a_box q a0) (a_Box qq A1) H1 q a0 qq A1
                  (@Logic.eq_refl tm (a_box q a0)));
         apply B_Refl; apply typing_lc_ty in H1; exact H1).
      rewrite Hq.
      exact (box_beta_typing D5 G1 q qq A1 a0 b G2 B1 L H1 Hfun2).
  - (* T_sum *) inversion Hstep.
  - (* T_inj1 *) inversion Hstep.
  - (* T_inj2 *) inversion Hstep.
  - (* T_case *)
    inversion Hstep; subst.
    + (* S_CaseCong *)
      assert (HshG3 : shapeDG D5 G3).
      { apply (shapeDG_binder_inv L (a_Sum A1 A2) r D5 G3). intros y Hy.
        apply (@typing_align ((y ~ Tm (a_Sum A1 A2)) ++ D5)
                  ((y ~ (r,Tm (a_Sum A1 A2))) ++ G3)
                  (open_tm_wrt_tm B0 (a_Var_f y)) a_Type (Hfun y Hy)). }
      pose proof (typing_open_type L D5 (a_Sum A1 A2) B0 a r G3 G1 Hfun H1 HshG3) as Hty.
      pose proof (T_case L D5 qq G1 G2 a'0 b1 b2 r A1 A2 B0 B1 B2 G3
                    Hq (IH1 a'0 H11) Heq1 Heq2 H3 H4 Hfun) as HTU.
      pick fresh x for (L \u fv_tm_tm B0).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (fv_tm_tm B0) Fr))).
      assert (HxB : x \notin fv_tm_tm B0) by (exact (proj2 (self_notin_union x L (fv_tm_tm B0) Fr))).
      pose proof (Beta_open_comm a a'0 B0 x (typing_lc _ _ _ _ H1)
                    (typing_lc _ _ _ _ (IH1 a'0 H11)) (B_Step a a'0 H11) HxB
                    (typing_lc _ _ _ _ (Hfun x HxL))) as HBeta.
      exact (T_conv D5 (ctx_plus (ctx_mul qq G1) G2)
               (a_Case qq a'0 b1 b2 (a_Lam r (a_Sum A1 A2) B0))
               (open_tm_wrt_tm B0 a) (open_tm_wrt_tm B0 a'0)
               (ctx_plus G3 (ctx_mul r G1)) HTU Hty (B_Sym _ _ HBeta)).
    + (* S_Case1Beta *)
      exact (inj1_case_beta_typing D5 G1 G2 qq A1 A2 a0 b1 B0 B1 L H1 H3 Heq1).
    + (* S_Case2Beta *)
      exact (inj2_case_beta_typing D5 G1 G2 qq A1 A2 a0 b2 B0 B2 L H1 H4 Heq2).
  - (* T_Sigma *) inversion Hstep.
  - (* T_Tensor *) inversion Hstep.
  - (* T_Spread *)
    inversion Hstep; subst.
    + (* S_SpreadCong *)
      assert (HshG3 : shapeDG D5 G3).
      { apply (shapeDG_binder_inv L (a_Sigma qq A2 A3) r D5 G3). intros y Hy.
        apply (@typing_align ((y ~ Tm (a_Sigma qq A2 A3)) ++ D5)
                  ((y ~ (r,Tm (a_Sigma qq A2 A3))) ++ G3)
                  (open_tm_wrt_tm B1 (a_Var_f y)) a_Type (Hfun3 y Hy)). }
      pose proof (typing_open_type L D5 (a_Sigma qq A2 A3) B1 a r G3 G1
                    Hfun3 H1 HshG3) as Hty.
      pose proof (T_Spread L D5 G1 G2 a'0 b r (a_Sigma qq A2 A3) B1 qq A2 A3 G3
                    (@Logic.eq_refl tm (a_Sigma qq A2 A3)) (IH1 a'0 H6) Hfun2 Hfun3) as HTU.
      pick fresh x for (L \u fv_tm_tm B1).
      assert (HxL : x \notin L) by (exact (proj1 (self_notin_union x L (fv_tm_tm B1) Fr))).
      assert (HxB : x \notin fv_tm_tm B1) by (exact (proj2 (self_notin_union x L (fv_tm_tm B1) Fr))).
      pose proof (Beta_open_comm a a'0 B1 x (typing_lc _ _ _ _ H1)
                    (typing_lc _ _ _ _ (IH1 a'0 H6)) (B_Step a a'0 H6) HxB
                    (typing_lc _ _ _ _ (Hfun3 x HxL))) as HBeta.
      exact (T_conv D5 (ctx_plus G1 G2)
               (a_Spread a'0 b (a_Lam r (a_Sigma qq A2 A3) B1))
               (open_tm_wrt_tm B1 a) (open_tm_wrt_tm B1 a'0)
               (ctx_plus G3 (ctx_mul r G1)) HTU Hty (B_Sym _ _ HBeta)).
    + (* S_SpreadBeta *)
      exact (tensor_spread_beta_typing D5 G1 a0 a1 A2 A3 qq G2 b B1 L H1 Hfun2).
Qed.

Theorem progress : forall a A,
  Typing nil nil a A -> value a \/ exists a', Step a a'.
Proof.
  intros a A H.
  exact (progress_gen nil nil a A H (@Logic.eq_refl D nil)).
Qed.
