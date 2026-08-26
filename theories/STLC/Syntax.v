Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From AutoProof Require Import Smallstep.

Import ListNotations.

Module STLC.

(** atom 是自由变量的名字。这里为了自包含，先用 nat 当变量名。
Rocq 会把 atom 展开成 nat，所以目前atom等价于nat
*)
Definition atom := nat.

(** Types: booleans and functions. *)
Inductive ty : Type :=
  | Ty_Bool : ty
  (*
    标准 lambda 演算中的函数每次只接收一个参数。
    Ty_Arrow T1 T2 表示函数类型：输入类型是 T1，输出类型是 T2。
  *)
  | Ty_Arrow : ty -> ty -> ty.

(** Terms. tm 就是程序。 *)
Inductive tm : Type :=
  (*
    locally nameless 的核心：
    - tm_bvar n 是被 lambda 绑定的变量，用 de Bruijn index 表示；
    - tm_fvar x 是自由变量，仍然用名字表示。
  *)
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  (* 调用函数。app 函数 参数 *)
  | tm_app : tm -> tm -> tm
  (*
    定义函数。LN 里 lambda 不再存参数名；
    lambda : T, bvar 0 表示 fun x : T => x。
  *)
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  (* if-then-else。if 条件 then 为真时的程序 else 为假时的程序 *)
  | tm_if : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "x" := x
  (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.
(** $(...) = 在自定义语法中嵌入普通 Rocq 表达式。 *)
Notation "$( t )" := t
  (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "( T )" := T
  (in custom stlc_ty at level 0, T custom stlc_ty) : stlc_scope.

Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "$( x )" := x
  (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom stlc_tm at level 0, n constr at level 0) : stlc_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom stlc_tm at level 200,
   T custom stlc_ty,
   t custom stlc_tm at level 200,
   left associativity) : stlc_scope.
Notation "'if' t1 'then' t2 'else' t3" :=
  (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm,
   t3 custom stlc_tm at level 200,
   left associativity) : stlc_scope.

(* 
locally nameless 里最核心的操作之一。
open_rec k u t：在程序 t 里，把绑定变量 bvar k 替换成程序 u。
k 是相对于当前子项 t 的深度（绑定变量相对于当前 t 的编码），不是绑定变量在整个原始项里的编码。（这个很重要）
*)
Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  (* 防止变量捕获。 S k就是k+1，S表示后继。
  *)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
  end.
(* open t u：把 t 当作某个 lambda 的函数体，去掉这层 lambda，并把原来由这层 lambda 绑定的位置换成参数 v。。  *)
Definition open (t u : tm) : tm := open_rec 0 u t.

Reserved Notation "'[' x ':=' s ']' t"
  (in custom stlc_tm at level 5,
   x constr at level 0,
   s custom stlc_tm,
   t custom stlc_tm at next level,
   right associativity).

(* subst x s t: 把t中的x替换为s
subst 只替换自由变量 fvar x；绑定变量 bvar 不靠名字替换，所以不会变量捕获。 *)
Fixpoint subst (x : atom) (s : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
  | tm_abs T t1 => tm_abs T (subst x s t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst x s t1) (subst x s t2) (subst x s t3)
  end
where "'[' x ':=' s ']' t" := (subst x s t)
  (in custom stlc_tm).

(* free_vars t 返回程序 t 中所有自由变量名。 *)
Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => free_vars t1 ++ free_vars t2 ++ free_vars t3
  end.

(* lc_at k t 表示：t 在 外面的k 层 lambda 之内是局部闭合的，没有裸 bvar。 
locally closed at。
就是在定义一个命题：程序里有没有“找不到主人”的绑定变量 bvar。
*)
Inductive lc_at : nat -> tm -> Prop :=
  | lc_bvar : forall k i,
      (* 
      有 k 层 lambda 时，合法索引是：
      0, 1, ..., k - 1
      所以必须满足：
      i < k
       *)
      i < k ->
      lc_at k (tm_bvar i)
  | lc_fvar : forall k x,
      lc_at k (tm_fvar x)
  | lc_app : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_app t1 t2)
  | lc_abs : forall k T t1,
      (* 显然 *)
      lc_at (S k) t1 ->
      lc_at k (tm_abs T t1)
  | lc_true : forall k,
      lc_at k tm_true
  | lc_false : forall k,
      lc_at k tm_false
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k t3 ->
      lc_at k (tm_if t1 t2 t3).

(* locally_closed t 表示 t 是一个合法完整程序；closed t 进一步要求 t 没有自由变量。 *)
Definition locally_closed (t : tm) : Prop := lc_at 0 t.
Definition closed (t : tm) : Prop := locally_closed t /\ free_vars t = [].

Hint Constructors lc_at : core.

(**
  Values for call-by-value evaluation.
  value t 表示命题：程序 t 是一个已经计算完成的值。
*)
Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

(* 将 value 的构造器加入提示库，使 auto 能自动尝试使用它们。 *)
Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

(* step t1 t2 表示 t1 能经过一步归约变成 t2。 *)
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed (tm_abs T t) ->
      value v ->
      tm_app (tm_abs T t) v --> open t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed t2 ->
      tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_IfTrue : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed t2 ->
      locally_closed t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* context是一个记录自由变量类型的表。 

*)
Definition context := atom -> option ty.

Definition empty : context := fun _ => None.

(* 在已有环境 Gamma 中，记录自由变量 x 的类型是 T。 *)
(* 
context 本身就是一个函数：
  Definition context := atom -> option ty.
返回一个新的 context，也就是返回一个新函数 *)
Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else Gamma y.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty,
   right associativity) : stlc_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty) : stlc_scope.
Notation "'empty'" := empty
  (in custom stlc_tm) : stlc_scope.

Lemma update_eq : forall Gamma x T,
  update Gamma x T x = Some T.
Proof.
  intros. unfold update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_neq : forall Gamma x y T,
  x <> y ->
  update Gamma x T y = Gamma y.
Proof.
  intros. unfold update.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma update_shadow : forall Gamma x T1 T2,
  update (update Gamma x T1) x T2 = update Gamma x T2.
Proof.
  intros. apply functional_extensionality. intros y.
  unfold update.
  destruct (Nat.eqb x y); reflexivity.
Qed.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
  (at level 0,
   Gamma custom stlc_tm at level 200,
   t custom stlc_tm,
   T custom stlc_ty).

(**
  has_type Gamma t T 表示：在类型环境 Gamma 下，程序 t 的类型是 T。

  lambda 分支用 fresh x 打开函数体，这是 LN 处理绑定变量的标准写法。
*)
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      <{ Gamma |-- fvar x \in T }>
  | T_Abs : forall (L : list atom) Gamma T1 T2 t1,
      (forall x, ~ In x L ->
        <{ x |-> T1 ; Gamma |-- $(open t1 (tm_fvar x)) \in T2 }>) ->
      <{ Gamma |-- lambda : T1, $(t1) \in T1 -> T2 }>
  | T_App : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- $(t1) \in T1 -> T2 }> ->
      <{ Gamma |-- $(t2) \in T1 }> ->
      <{ Gamma |-- $(tm_app t1 t2) \in T2 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.
(* 返回一个肯定不在 L 中的新变量名 *)
Definition fresh (L : list atom) : atom := S (max_atom L).

Lemma in_le_max_atom : forall x L,
  In x L -> x <= max_atom L.
Proof.
  induction L; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. lia.
    + specialize (IHL H). lia.
Qed.

Lemma fresh_notin : forall L,
  ~ In (fresh L) L.
Proof.
  unfold fresh. intros L H.
  pose proof (in_le_max_atom _ _ H). lia.
Qed.

End STLC.
