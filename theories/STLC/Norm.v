Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Stdlib Require Import List.
From AutoProof Require Import Maps.
From AutoProof Require Import Smallstep.
From AutoProof.STLC Require Import Syntax.
From AutoProof.STLC Require Import StlcProp.



Module STLCNorm.
Import STLC.
Import STLCProp.

(* -->*表示零步或多步归约 *)
(* 程序终止的定义 *)
Definition halts  (t:tm) : Prop :=  exists t', t -->* t' /\  value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros t h1.
  unfold halts.
  exists t.
  split.
  - apply multi_refl.
  - exact h1.
Qed.

(* R是比终止更强、由类型决定的程序性质 *)
Fixpoint R (T:ty) (t:tm) : Prop :=
  <{ empty |-- t \in T }> /\ halts t /\
  (match T with
   (* <{{ Bool }}> 是类型 notation，等价于 Ty_Bool。 *)
   | <{{ Bool }}> => True
   (* <{{ T1 -> T2 }}> 等价于 Ty_Arrow T1 T2。 *)
   (* 保证好函数t使用好参数t1后（好函数和好参数本身都是好程序），结果仍然是好程序。 *)
   | <{{ T1 -> T2 }}> => (forall t1, R T1 t1 -> R T2 <{ t t1 }>)
   end).

(* 显然，定义 *)
Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
    intros.
    destruct T.
    - unfold R in H.
      destruct H.
      destruct H0.
      assumption.
    - unfold R in H.
      destruct H.
      destruct H0.
      assumption.
Qed.

(* 显然，定义 *)
Lemma R_typable_empty : forall {T} {t}, R T t -> <{ empty |-- t \in T }>.
Proof.
    intros.
    destruct T; unfold R in H; destruct H as [H _]; assumption.
Qed.

(* value 不可能再进行一步归约。 *)
Lemma value__normal : forall v,
  value v -> ~ exists t', v --> t'.
Proof.
  intros v Hv [t' Hstep].
  (* 对value各个构造器情况讨论 *)
  inversion Hv. 
  - subst.
    (* 函数不能继续归约 *)
    inversion Hstep.
  - subst.
    inversion Hstep.
  - subst.
    inversion Hstep.
Qed.

(* [appears_free_in x t] 表示变量 x 在程序 t 中自由出现，即没有被对应的 lambda 绑定。 *)
Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
  (* booleans *)
  | afi_test0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  (* pairs这些对于完成p0用不到 *)
  (* | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ (t1 , t2) }>
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.fst }>
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.snd }> *)
.

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* 环境只要在程序的自由变量上保持一致，程序的类型就不变。 *)
(* 显然 *)
Lemma context_invariance : forall Gamma Gamma' t T,
     <{Gamma |-- t \in T}>  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     <{Gamma' |-- t \in T}>.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros.
  - (* T_Var *)
    apply T_Var. 
    rewrite <- H.
    symmetry.
    apply H0.
    (* 显然 *)
    auto.

  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type.
    intros.
    destruct (eqb_spec x0 x1) as [Heq | Hneq].
    + subst.
      rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + subst.
      rewrite update_neq.
      rewrite update_neq.
      apply H0.
      apply afi_abs.
      auto.
      auto.
      auto.
      auto.

    
  - (* T_App *)
    apply (T_App T1 T2).
    + apply IHhas_type1.
      intros.
      apply H1.
      auto.
    + apply IHhas_type2.
      intros.
      apply H1.
      auto.
  - auto.
  - auto.
  - apply T_If.
    + apply IHhas_type1.
      intros.
      apply H2.
      apply afi_test0.
      exact H3.
    + apply IHhas_type2.
      intros.
      apply H2.
      apply afi_test1.
      exact H3.
    + apply IHhas_type3.
      intros.
      apply H2.
      apply afi_test2.
      exact H3.


Qed.

(* 显然 *)
Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
  intros x y. rewrite String.eqb_neq.
  intros H. apply H. Qed.

(* x要映射到一个类型，不然包含了x的t也无法映射到一个类型 *)
Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   <{Gamma |-- t \in T}> ->
   exists T', Gamma x = Some T'.
Proof.
  intros.
  induction H0.
  - assert (x0=x1).
    {
      inversion H.
      auto.
    }
    subst.
    eauto.
  - inversion H.
    subst.
    assert (exists T' : ty, <{ x1 |-> T2; Gamma }> x0 = Some T').
    {
      eauto.
    }
    destruct H1.
    rewrite update_neq in H1.
    eauto.
    assumption.
  - inversion H;subst.
    + apply IHhas_type1.
      exact H2.
    + apply IHhas_type2.
      exact H2.
  - (*H显然不成立*)
    inversion H.
  - (*H显然不成立*)
    inversion H.
  - inversion H;subst.
    + apply IHhas_type1.
      exact H2.
    + apply IHhas_type2.
      exact H2.
    + apply IHhas_type3.
      exact H2.

Qed.

Corollary typable_empty__closed : forall t T,
    <{empty |-- t \in T}>  ->
    closed t.
Proof.
  intros.
  unfold closed.
  intros.
  (* 反证法 *)
  intro.
  destruct (free_in_context x0 t T empty H0 H)
    as [T' Hlookup].
  (* 空环境对任何变量都返回none，所以Hlookup不成立 *)
  discriminate Hlookup.
Qed.



Ltac solve_by_value_nf :=
  match goal with
  | Hv : value ?v, Hstep : ?v --> ?v' |- _ =>
      exfalso; apply value__normal in Hv; eauto
  end.

(* 一步归约是确定的：同一个程序一步归约后的结果唯一。 *)
Lemma step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  intros t t' t'' E1.
  generalize dependent t''.
  (* 对step进行归纳 *)
  induction E1.
  - intros t'' h1.
    (* 对t''分构造器情况讨论 *)
    inversion h1.
    + subst.
      reflexivity.
    + subst.
      inversion H3.
    + subst.
      (* 这里H4矛盾了，因为v是value了 *)
      exfalso.
      apply value__normal in H.
      apply H.
      exists t2'.
      exact H4.
  - intros t'' h1.
    inversion h1.
    + subst.
      (* E1不成立，因为函数定义不能继续归约 *)
      exfalso.
      inversion E1.
    + subst.
      assert (Heq : t1' = t1'0).
      {
        apply IHE1.
        exact H2.
      }
      rewrite Heq.
      reflexivity.
    + subst.
      (* E1不成立，因为value不能继续归约 *)
      exfalso.
      apply value__normal in H1.
      apply H1.
      exists t1'.
      exact E1.
  - intros t'' h1.
    inversion h1.
    + subst.
      (* t2 既是 value 又能继续归约，矛盾。 *)
      solve_by_value_nf.
    + subst.
      (* v1 既是 value 又能继续归约，矛盾。 *)
      solve_by_value_nf.
    + subst.
      f_equal.
      apply IHE1.
      assumption.
  - intros t'' h1.
    inversion h1.
    + subst.
      reflexivity.
    + subst.
      inversion H3.
  - intros t'' h1.
    inversion h1.
    + subst.
      reflexivity.
    + subst.
      inversion H3.
  - intros t'' h1.
    inversion h1.
    + subst.
      inversion E1.
    + subst.
      inversion E1.
    + subst.
      f_equal.
      apply IHE1.
      assumption.




  (* generalize dependent t''.
  induction E1; intros t'' E2; inversion E2; subst; clear E2;
    try f_equal; try solve_by_value_nf; eauto.
  - inversion H3.
  - inversion E1.
  - inversion H3.
  - inversion H3.
  - inversion E1.
  - inversion E1. *)
Qed.

Lemma step_preserves_halting :
  forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  destruct STM as [start | start middle final Hfirst Hrest].
  (* 零步归约： t'' 就是 t*)
  + exfalso; apply value__normal in V; eauto.
  (* 一步或多步归约：
     存在中间程序 t'
     Hstep : t --> t'
     Hmulti : t' -->* t'' *)
  + rewrite (step_deterministic _ _ _ ST Hfirst).
    exists final.
    split.
    * exact Hrest.
    * exact V.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0.
  split.
  + apply multi_step with (y := t').
    * exact ST.
    * exact STM.
  + exact V.
Qed.

(* 程序一步归约后仍然满足R性质 *)
Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
  induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
  - (* Bool *)
    split. eapply preservation; eauto.
    split. apply (step_preserves_halting _ _ E); eauto.
    auto.
  - (* Arrow *)
    split. eapply preservation; eauto.
    split. apply (step_preserves_halting _ _ E); eauto.
    intros.
    eapply IHT2.
    apply  ST_App1. apply E.
    apply RRt; auto.
    
Qed.

(* 程序多步归约后仍然满足R性质 *)
Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> R T t -> R T t'.
Proof.
  intros T t t' STM.
  induction STM;intros.
  - assumption.
  - apply IHSTM.
    eapply step_preserves_R.
    apply H.
    exact H0.
Qed.


Lemma step_preserves_R' : forall T t t',
  <{ empty |-- t \in T }> -> (t --> t') -> R T t' -> R T t.
Proof.
  induction T; intros t t' H H0 H1.
  - (* Bool *)
    split.
    exact H.
    split.
    assert (H2: halts t').
    {
      apply R_halts in H1.
      exact H1.
    }
    eapply (proj2 (step_preserves_halting t t' H0)).
    exact H2.
    auto.
  - (* Arrow *)
    split.
    exact H.
    split.
    assert (H2: halts t').
    {
      apply R_halts in H1.
      exact H1.
    }
    eapply (proj2 (step_preserves_halting t t' H0)).
    exact H2.
    intros.
    eapply IHT2.
    + eapply T_App.
      * exact H.
      * exact (R_typable_empty H2).
    + apply ST_App1.
      apply H0.
    + 
      (* 只需要H1和H2 *)
      unfold R in H1.
      fold R in H1. (*先unfold再fold是为了只展开一层R*)
      destruct H1 as [_ [_ Hfun]].
      apply Hfun.
      exact H2.
Qed.

Lemma multistep_preserves_R' : forall T t t',
  <{ empty |-- t \in T }> -> (t -->* t') -> R T t' -> R T t.
Proof.
  intros.
  induction H0.
  - exact H1.
  - assert (R T y0).
    {
      apply IHmulti.
      + apply (preservation x0 y0 T H H0).
      + exact H1.
    }
    eapply step_preserves_R'.
    exact H.
    apply H0.
    apply H3.
Qed.


(* 不是之前的类型环境Gamma *)
Definition env := list (string * tm).

Fixpoint msubst (ss:env) (t:tm) : tm :=
match ss with
| nil => t
(* 按照 env 列表从头到尾依次替换 *)
| ((x,s)::ss') => msubst ss' <{ [x:=s]t }>
end.

(** We need similar machinery to talk about repeated extension of a
    typing context using a list of (identifier, type) pairs, which we
    call a _type assignment_. *)
(* tass 是 type assignment 的缩写 *)
Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) :=
  match xts with
  | nil => Gamma
  (* 按照tass从尾到头依次update Gamma *)
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.

(** We will need some simple operations that work uniformly on
    environments and type assigments *)
(* 在列表 l 中查找名字 k，返回它映射的内容。如果有多个相同的 k，返回列表中最靠前的那一个 *)
Fixpoint lookup {X:Set} (k : string) (l : list (string * X))
              : option X :=
  match l with
    | nil => None
    | (j,x) :: l' =>
      if String.eqb j k then Some x else lookup k l'
  end.
(* 从列表 l 中删除所有名字为 k 的项 *)
Fixpoint drop {X:Set} (n:string) (nxs:list (string * X))
            : list (string * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') =>
        if String.eqb n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.

(** An _instantiation_ combines a type assignment and a value
    environment with the same domains, where corresponding elements are
    in R. *)
(* 定义 tass 和 env 合法对应 *)
Inductive instantiation :  tass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T t c e,
    value t -> R T t ->
    instantiation c e ->
    instantiation ((x,T)::c) ((x,t)::e).

(* 显然 *)
Lemma vacuous_substitution : forall  t x,
~ appears_free_in x t  ->
forall t', <{ [x:=t']t }> = t.
Proof with eauto.
  intros.
  generalize dependent x0.
  induction t;intros.
  - simpl.
    assert (Hneq : x0 <> s).
    {
      intro Heq.
      subst s.
      apply H.
      apply afi_var.
    }
    rewrite (false_eqb_string x0 s Hneq).
    reflexivity.
  - simpl.
    assert (Hnot1 : ~ appears_free_in x0 t1).
    {
      intro Hfree1.
      apply H.
      apply afi_app1.
      exact Hfree1.
    }

    assert (Hnot2 : ~ appears_free_in x0 t2).
    {
      intro Hfree2.
      apply H.
      apply afi_app2.
      exact Hfree2.
    }
    clear H.
    rewrite (IHt1 x0 Hnot1).
    rewrite (IHt2 x0 Hnot2).
    reflexivity.
  - simpl.
    destruct (eqb_spec x0 s) as [Heq | Hneq].
    + reflexivity.
    + rewrite IHt.
      reflexivity.
      intro.
      apply H.
      apply afi_abs.
      auto.
      assumption.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    rewrite IHt3.
    reflexivity.
    + intro.
      apply H.
      apply afi_test2.
      assumption.
    + intro.
      apply H.
      apply afi_test1.
      assumption.
    + intro.
      apply H.
      apply afi_test0.
      assumption.
Qed.

(* 显然，因为t没有自由变量 *)
Lemma subst_closed: forall t,
    closed t  ->
    forall x t', <{ [x:=t']t }> = t.
Proof.
  intros.
  unfold closed in H.
  apply vacuous_substitution.
  auto.
Qed.

(* 加closed v，是为了防止x作为自由变量出现在v里 *)
Lemma subst_not_afi : forall t x v,
   closed v ->  ~ appears_free_in x <{ [x:=v]t }>.
Proof. 
  intros.
  unfold closed in H.
  assert (~ appears_free_in x0 v).
  {
    auto.
  }
  clear H.
  intro.
  apply H0.
  clear H0.
  revert H.
  induction t.
  - intro.
    destruct (eqb_spec x0 s) as [Heq | Hneq].
    + subst.
      simpl in H.
      rewrite String.eqb_refl in H.
      assumption.
    + simpl in H.
      rewrite (false_eqb_string x0 s Hneq) in H.
      (* 显然H不成立，因为x0<>s *)
      inversion H.
      subst.
      exfalso.
      apply Hneq.
      reflexivity.
  - intro.
    simpl in H.
    inversion H;subst.
    + eauto.
    + eauto.
  - intro.
    apply IHt.
    clear IHt.
    simpl in H.
    destruct (eqb_spec x0 s) as [Heq | Hneq].
    + subst.
      (* 显然H不成立 *)
      exfalso.
      inversion H.
      subst.
      contradiction.
    + inversion H.
      subst.
      assumption.
  - intro.
    (* 显然H不成立 *)
    inversion H.
  - intro.
    (* 显然H不成立 *)
    inversion H.
  - intro.
    inversion H;subst.
    + auto.
    + auto.
    + auto.
 
Qed.

(* 显然，因为v里没有自由变量x0 *)
Lemma duplicate_subst : forall t' x t v,
 closed v -> <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
  intros.
  apply vacuous_substitution.
  apply subst_not_afi.
  assumption.

Qed.

Lemma swap_subst : forall t x x1 v v1,
   x <> x1 ->
   closed v -> closed v1 ->
   <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof.
  intros.
  induction t;intros;subst.
  - 
    (* 分4种情况 *)
    destruct (eqb_spec x0 s) as [Hx0 | Hx0];
    destruct (eqb_spec x1 s) as [Hx1 | Hx1].
    + subst.
      (* H不成立 *)
      contradiction.
    + subst.
      simpl.
      rewrite String.eqb_refl.
      rewrite (false_eqb_string x1 s Hx1).
      simpl.
      rewrite String.eqb_refl.
      apply subst_closed.
      assumption.
    + subst.
      simpl.
      rewrite (false_eqb_string x0 s H).
      rewrite String.eqb_refl.
      simpl.
      rewrite String.eqb_refl.
      symmetry.
      apply subst_closed.
      assumption.
    + simpl.
      rewrite (false_eqb_string x0 s Hx0).
      rewrite (false_eqb_string x1 s Hx1).
      simpl.
      rewrite (false_eqb_string x1 s Hx1).
      rewrite (false_eqb_string x0 s Hx0).
      reflexivity.

  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - simpl.
    (* 分4种情况 *)
    destruct (eqb_spec x0 s) as [Hx0 | Hx0];
    destruct (eqb_spec x1 s) as [Hx1 | Hx1];subst.
    + 
      (* H不成立 *)
      contradiction.
    + simpl.
      rewrite (false_eqb_string x1 s Hx1).
      rewrite String.eqb_refl.
      reflexivity.
    + simpl.
      rewrite String.eqb_refl.
      rewrite (false_eqb_string x0 s Hx0).
      reflexivity.
    + simpl.
      rewrite (false_eqb_string x0 s Hx0).
      rewrite (false_eqb_string x1 s Hx1).
      rewrite IHt.
      reflexivity.
  - simpl.
    auto.
  - simpl.
    auto.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    rewrite IHt3.
    reflexivity.

Qed.

(** *** Properties of Multi-Substitutions *)
(* 显然 *)
Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof.
  intros.
  induction ss.
  - auto.
  - destruct a as [x0 s].
    simpl.
    rewrite (subst_closed t H x0 s).
    apply IHss.

Qed.

(** Closed environments are those that contain only closed terms. *)
(* closed env *)
Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

(* 一次普通替换 [x:=v] 和一组多重替换 msubst env，在替换程序都封闭时，可以交换执行顺序。 *)
Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
  msubst env <{ [x:=v]t }> = <{ [x:=v] $(msubst (drop x env) t) }> .
Proof.
  intros env0.
  induction env0.
  - reflexivity.
  - destruct a as [x1 t1].
    intros.
    simpl in H0.
    destruct H0.
    simpl.
    (* 分x1=x0和x1<>x0讨论 *)
    destruct (eqb_spec x1 x0) as [Heq | Hneq].
    + subst.
      rewrite (duplicate_subst t x0 t1 v H).
      apply IHenv0.
      assumption.
      assumption.
    + assert (Hrev : x0 <> x1).
      {
        auto.
      }
      rewrite (swap_subst t x0 x1 v t1 Hrev H H0).
      simpl.
      apply IHenv0.
      assumption.
      assumption.
      
Qed.
(* 对一个变量 x 执行多重替换，等价于就是在替换表 ss 中查找 x返回的结果 *)
Lemma msubst_var:  forall ss x, closed_env ss ->
  msubst ss (tm_var x) =
  match lookup x ss with
  | Some t => t
  | None => tm_var x
end.
Proof.
  intros ss x0.
  induction ss.
  - intros.
    auto.
  - intros.
    destruct a as [x1 t1].
    simpl.
    (* 分x1=x0和x1<>x0讨论 *)
    destruct (eqb_spec x1 x0) as [Heq | Hneq].
    + subst.
      simpl in H.
      destruct H as [Ht1 Hss].
      apply msubst_closed.
      assumption.
    + apply IHss.
      simpl in H.
      destruct H as [Ht1 Hss].
      assumption.
Qed.
(* x是非自由变量，所以ss msubst不了它。所以等价于(drop x ss)直接替换t *)
Lemma msubst_abs: forall ss x T t,
msubst ss <{ \ x : T, t }> = <{ \x : T, $(msubst (drop x ss) t) }>.
Proof.
  intros ss x0.
  induction ss.
  - intros.
    reflexivity.
  - intros.
    destruct a as [x1 t1].
    simpl.
    (* 分x1=x0和x1<>x0讨论 *)
    destruct (eqb_spec x1 x0) as [Heq | Hneq].
    + subst.
      apply IHss.
    + rewrite (IHss T <{ [x1 := t1] t }>).
      simpl.
      reflexivity.

Qed.

(* subst的定义中<{ t1 t2 }> => <{ [x:=s] t1 [x:=s] t2 }>分支的多步版本 *)
Lemma msubst_app : forall ss t1 t2,
  msubst ss <{ t1 t2 }> = <{ $(msubst ss t1) $(msubst ss t2) }>.
Proof.
induction ss; intros.
  reflexivity.
  destruct a.
  simpl.
  apply IHss.
Qed.

(* 显然 *)
Lemma msubst_if : forall ss t1 t2 t3,
msubst ss <{ if t1 then t2 else t3 }> =
<{ if $(msubst ss t1)
   then $(msubst ss t2)
   else $(msubst ss t3) }>.
Proof.
  induction ss; intros.
  - auto.
  - destruct a.
    simpl.
    apply IHss.
Qed.

(* 显然 *)
Lemma mupdate_lookup : forall (c : tass) (x:string),
    lookup x c = (mupdate empty c) x.
Proof.
  intros.
  induction c.
  - auto.
  - destruct a as [x1 T1].
    simpl.
    destruct (eqb_spec x1 x0) as [Heq | Hneq].
    + subst.
      symmetry.
      apply update_eq.
    + rewrite update_neq.
      apply IHc.
      apply Hneq.

Qed.

(* 显然 *)
Lemma mupdate_drop : forall (c: tass) Gamma x x',
      mupdate Gamma (drop x c) x'
    = if String.eqb x x' then Gamma x' else mupdate Gamma c x'.
Proof.
  intros.
  induction c.
  - destruct (eqb_spec x0 x') as [Heq | Hneq].
    + subst. reflexivity.
    + reflexivity.
  - destruct (eqb_spec x0 x') as [Heq | Hneq].
    + subst.
      destruct a as [x1 T1].
      simpl.
      destruct (eqb_spec x1 x') as [Heq | Hneq].
      * subst.
        assumption.
      * simpl.
        rewrite update_neq.
        assumption.
        assumption.
    + destruct a as [x1 T1].
      simpl.
      destruct (eqb_spec x1 x0).
      * subst.
        rewrite update_neq.
        assumption.
        assumption.
      * simpl.
        destruct (eqb_spec x1 x').
        --subst.
          rewrite update_eq.
          rewrite update_eq.
          reflexivity.
        --rewrite update_neq.
          rewrite update_neq.
          assumption.
          assumption.
          assumption. 
           
Qed.

(** *** Properties of Instantiations *)

(** These are strightforward. *)

Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {T},
      lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
  intros c e H.
  induction H; intros.
  - 
    (* H不成立 *)
    simpl in H.
    discriminate H.
  - simpl.
    destruct (eqb_spec x0 x1).
    + subst.
      eauto.
    + eapply IHinstantiation.
      apply String.eqb_neq in n.
      simpl in H2.
      rewrite n in H2.
      exact H2.

Qed.

(* 这个有点意思 *)
Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
Proof.
  intros.
  induction H.
  - simpl.
    auto.
  - simpl.
    split.
    + apply typable_empty__closed with (T := T).
      apply R_typable_empty.
      assumption.
    + assumption.
Qed.
(*  如果类型表 c 和替换表 e 是合法对应的，那么同一个变量 x 在 c 中对应类型 T、在 e 中对应程序 t 时，就有 R T t。 *)
Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
Proof.
  intros c e H.
  induction H;intros.
  - 
    (* H不成立 *)
    simpl in H.
    discriminate H.
  - simpl in H2.
    simpl in H3.
    destruct (String.eqb_spec x0 x1).
    + subst.
      injection H2 as H4.
      injection H3 as H5.
      subst.
      exact H0.
    + apply (IHinstantiation x1 t0 T0).
      exact H2.
      exact H3.


Qed.
(* 如果类型表 c 和程序替换表 env 合法对应，那么从两张表中同时删除变量 x 后，它们仍然合法对应。 *)
Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e H.
  induction H; intros.
  - simpl.
    exact V_nil.
  - simpl.
    destruct (eqb_spec x0 x1).
    + subst.
      eauto.
    + apply V_cons.
      assumption.
      assumption.
      eauto.
Qed.

(** *** Congruence Lemmas on Multistep *)

(** We'll need just a few of these; add them as the demand arises. *)

Lemma multistep_App2 : forall v t t',
  value v -> (t -->* t') -> <{ v t }> -->* <{ v t' }>.
Proof.
  intros v t t' Hv Hsteps.
  induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2.
      exact Hv.
      exact H.
    + exact IHHsteps.
Qed.

Lemma multistep_If : forall t t' t2 t3,
  t -->* t' ->
  <{ if t then t2 else t3 }> -->* <{ if t' then t2 else t3 }>.
Proof.
  intros t t' t2 t3 Hsteps.
  induction Hsteps.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_If.
      exact H.
    + exact IHHsteps.
Qed.

(* 条件和两个分支都满足 R 时，整个 if 也满足 R。 *)
Lemma R_if : forall T t1 t2 t3,
  R <{{ Bool }}> t1 ->
  R T t2 ->
  R T t3 ->
  R T <{ if t1 then t2 else t3 }>.
Proof.
  intros T t1 t2 t3 HRcond HRthen HRelse.

  assert (HTif : <{ empty |-- if t1 then t2 else t3 \in T }>).
  {
    apply T_If.
    - apply R_typable_empty.
      exact HRcond.
    - apply R_typable_empty.
      exact HRthen.
    - apply R_typable_empty.
      exact HRelse.
  }

  destruct (R_halts HRcond) as [v [Hsteps Hv]].
  assert (HRv : R <{{ Bool }}> v).
  {
    apply (multistep_preserves_R <{{ Bool }}> t1 v).
    - exact Hsteps.
    - exact HRcond.
  }

  destruct (canonical_forms_bool v (R_typable_empty HRv) Hv)
    as [Heq | Heq].
  - subst v.
    assert (HRtrue : R T <{ if true then t2 else t3 }>).
    {
      eapply step_preserves_R'.
      - apply T_If.
        + apply T_True.
        + apply R_typable_empty.
          exact HRthen.
        + apply R_typable_empty.
          exact HRelse.
      - apply ST_IfTrue.
      - exact HRthen.
    }
    apply (multistep_preserves_R'
             T
             <{ if t1 then t2 else t3 }>
             <{ if true then t2 else t3 }>).
    + exact HTif.
    + apply multistep_If.
      exact Hsteps.
    + exact HRtrue.
  - subst v.
    assert (HRfalse : R T <{ if false then t2 else t3 }>).
    {
      eapply step_preserves_R'.
      - apply T_If.
        + apply T_False.
        + apply R_typable_empty.
          exact HRthen.
        + apply R_typable_empty.
          exact HRelse.
      - apply ST_IfFalse.
      - exact HRelse.
    }
    apply (multistep_preserves_R'
             T
             <{ if t1 then t2 else t3 }>
             <{ if false then t2 else t3 }>).
    + exact HTif.
    + apply multistep_If.
      exact Hsteps.
    + exact HRfalse.
Qed.

(* 原来程序 t 依赖 Gamma 和 c。用 e 把 c 中的变量全部替换成具体程序后，新程序不再依赖 c，只依赖 Gamma，并且类型仍然是 S。 *)
Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, <{$(mupdate Gamma c) |-- t \in S}> ->
     <{Gamma |-- $(msubst e t) \in S}>.
Proof.
    intros c e H.
    induction H;intros.
    - simpl.
      simpl in H.
      assumption.
    - simpl.
      simpl in H2.
      apply IHinstantiation.
      eapply substitution_preserves_typing.
      exact H2.
      apply R_typable_empty.
      assumption.
Qed.

Lemma msubst_R : forall c env t T,
  <{$(mupdate empty c) |-- t \in T}> ->
  instantiation c env ->
  R T (msubst env t).
Proof.
  intros.
  generalize dependent env0.
  remember (mupdate empty c) as Gamma eqn:HGamma.
  assert (Hlookup : forall x, Gamma x = lookup x c).
  {
    intro x.
    rewrite HGamma.
    symmetry.
    apply mupdate_lookup.
  }
  clear HGamma.
  generalize dependent c.
  induction H; intros.
  - assert (lookup x0 c =Some T1).
    {
      rewrite <-(Hlookup x0).
      exact H.
    }
    eapply instantiation_R.
    exact H0.
    exact H1.
    destruct (instantiation_domains_match H0 H1).
    rewrite H2.
    rewrite msubst_var.
    (* 显然左右相同 *)
    rewrite H2.
    reflexivity.
    (* 证明一下这个条件 *)
    apply (instantiation_env_closed c env0).
    exact H0.
  - 
    (* 最难的一个分支 *)
    unfold R.
    fold R.
    repeat split.
    + 
      eapply msubst_preserves_typing.
      exact H0.
      apply T_Abs.
      eapply context_invariance.
      exact H.
      intros.
      unfold update, t_update.
      destruct (String.eqb x0 x1).
      reflexivity.
      rewrite (Hlookup x1).
      apply mupdate_lookup.
    + rewrite msubst_abs.
      apply value_halts.
      apply v_abs.
    + intros.
      destruct (R_halts H1) as [v [Hsteps Hv]].
      assert (HRv : R T2 v).
      {
        eapply multistep_preserves_R.
        - exact Hsteps.
        - exact H1.
      }
      assert (Hbody :
      R T1 (msubst ((x0, v) :: env0) t1)).
      {
        apply (IHhas_type ((x0, T2) :: c)).
        - intro y.
          unfold update, t_update.
          simpl.
          destruct (String.eqb x0 y).
          + reflexivity.
          + apply Hlookup.
        - apply V_cons.
          + exact Hv.
          + exact HRv.
          + exact H0.
      }
      assert (Hclosedv : closed v).
      {
        apply typable_empty__closed with (T := T2).
        apply R_typable_empty.
        exact HRv.
      }
      assert (Hclosedenv : closed_env env0).
      {
        apply (instantiation_env_closed c env0).
        exact H0.
      }
      assert (Hbeta :
      <{ $(msubst env0 <{ \ x0 : T2, t1 }>) v }>
        --> msubst ((x0, v) :: env0) t1).
      {
        rewrite msubst_abs.
        simpl.
        rewrite (subst_msubst env0 x0 v t1 Hclosedv Hclosedenv).
        apply ST_AppAbs.
        exact Hv.
      }
      assert (HtypedFun :
      <{ empty |-- $(msubst env0 <{ \ x0 : T2, t1 }>)
         \in T2 -> T1 }>).
      {
        eapply msubst_preserves_typing.
        - exact H0.
        - apply T_Abs.
          eapply context_invariance.
          + exact H.
          + intros y _.
            unfold update, t_update.
            destruct (String.eqb x0 y).
            * reflexivity.
            * rewrite (Hlookup y).
              apply mupdate_lookup.
      }
      assert (HRappv :
      R T1 <{ $(msubst env0 <{ \ x0 : T2, t1 }>) v }>).
      {
        eapply step_preserves_R'.
        - apply T_App with (T2 := T2).
          + exact HtypedFun.
          + apply R_typable_empty.
            exact HRv.
        - exact Hbeta.
        - exact Hbody.
      }
      eapply multistep_preserves_R'.
      * apply T_App with (T2 := T2).
        -- exact HtypedFun.
        -- apply R_typable_empty.
          exact H1.
    
      * apply
          (multistep_App2
            (msubst env0 <{ \ x0 : T2, t1 }>)
            t0
            v).
        -- rewrite msubst_abs.
          apply v_abs.
        -- exact Hsteps.
    
      * exact HRappv.
  - rewrite msubst_app.
    pose proof
      (IHhas_type1 c Hlookup env0 H1)
      as HRfun.
    pose proof
      (IHhas_type2 c Hlookup env0 H1)
      as HRarg.
    unfold R in HRfun.
    fold R in HRfun.
    destruct HRfun as [_ [_ Happly]].
    apply Happly.
    exact HRarg.
  - assert (HclosedTrue : closed <{ true }>).
    {
      unfold closed.
      intros x Hfree.
      inversion Hfree.
    }
    rewrite (msubst_closed <{ true }> HclosedTrue env0).
    unfold R.
    repeat split.
    + apply T_True.
    + apply value_halts. apply v_true.
  - assert (HclosedFalse : closed <{ false }>).
    {
      unfold closed.
      intros x Hfree.
      inversion Hfree.
    }
    rewrite (msubst_closed <{ false }> HclosedFalse env0).
    repeat split.
    + apply T_False.
    + apply value_halts. apply v_false.
  - assert (R <{{ Bool }}> (msubst env0 t1)).
    {
      eapply IHhas_type1.
      exact Hlookup.
      exact H2.
    }
    assert (R T1 (msubst env0 t2)).
    {
      eapply IHhas_type2.
      exact Hlookup.
      exact H2.
    }
    assert (R T1 (msubst env0 t3)).
    {
      eapply IHhas_type3.
      exact Hlookup.
      exact H2.
    }
    rewrite msubst_if.
    apply R_if.
    assumption.
    assumption.
    assumption.
    
Qed.

Theorem normalization : forall t T, <{empty |-- t \in T}> -> halts t.
Proof.
  intros.
  (* 把停机加强为R *)
  apply (@R_halts T t).
  eapply (msubst_R nil nil).
  - auto.
  - apply V_nil.

Qed.

End STLCNorm.
