(** The syntax of STLC, following Software Foundations [Stlc]. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From AutoProof Require Import Maps.
From AutoProof Require Import Smallstep.
Set Default Goal Selector "!".

Module STLC.

(** Types: booleans and functions. *)
Inductive ty : Type :=
  | Ty_Bool : ty
  (*
    标准 λ 演算中的函数每次只接收一个参数. 
    这里等价于| Arrow (input : ty) (output : ty) : ty.
  *)
  | Ty_Arrow : ty -> ty -> ty.

(** Terms.  tm就是程序 *)
Inductive tm : Type :=
  | tm_var : string -> tm
  (*
    调用函数。app 函数 参数
  *)
  | tm_app : tm -> tm -> tm
  (*
    定义函数。abs 参数名 参数类型 函数体
  *)
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  (*
    if-then-else。test 条件 为真时的程序 为假时的程序
  *)
  | tm_if : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x
  (in custom stlc_ty at level 0, x global) : stlc_scope.
Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "( t )" := t
  (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.

(* $(...) = 在自定义语法中嵌入普通 Rocq 表达式 *)
Notation "$( t )" := t
  (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.

Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z)
  (in custom stlc_tm at level 200,
   x custom stlc_tm,
   y custom stlc_tm,
   z custom stlc_tm at level 200,
   left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0).
Notation "$( x )" := x
  (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" := (tm_abs x t y)
  (in custom stlc_tm at level 200,
   x global,
   t custom stlc_ty,
   y custom stlc_tm at level 200,
   left associativity).

Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(** Values for call-by-value evaluation. 
一个“是否已经算完”的判断。
对于任意程序 t：
value t
表示命题：
程序 t 是一个已经计算完成的值。
*)
Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{ \x:T2, t1 }>
  | v_true :
      value <{ true }>
  | v_false :
      value <{ false }>.

(** 将 [value] 的构造器加入标准提示库，使 [auto] 能自动尝试使用它们。 *)
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t"
  (in custom stlc_tm at level 5,
   x global,
   s custom stlc_tm,
   t custom stlc_tm at next level,
   right associativity).

(*Fixpoint 是 Rocq 中定义递归函数的关键字。大致相当于 Lean 中允许递归的 def.
x：要查找的变量名字
s：要替换成的程序
t：被检查、被修改的整个程序
*)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  (* 
  例如：[x:=tru] (\x:Bool. x) 变为(\x:Bool. x)；
  [x:=tru] (\y:Bool. x) 变为 \y:Bool. tru。 
  *)
  | <{ \y:T, t1 }> =>
      if String.eqb x y then t else <{ \y:T, [x:=s] t1 }>
  | <{ t1 t2 }> =>
      <{ [x:=s] t1 [x:=s] t2 }>
  | <{ true }> =>
      <{ true }>
  | <{ false }> =>
      <{ false }>
  | <{ if t1 then t2 else t3 }> =>
      <{ if [x:=s] t1 then [x:=s] t2 else [x:=s] t3 }>
  end

where "'[' x ':=' s ']' t" := (subst x s t)
  (in custom stlc_tm).

Reserved Notation "t '-->' t'" (at level 40).

(** step t1 t2 表示 t1 能经过一步归约变成 t2。 *)
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
      value v ->
      <{ (\x:T, t) v }> --> <{ [x:=v] t }>
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ t1 t2 }> --> <{ t1' t2 }>
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ v1 t2 }> --> <{ v1 t2' }>
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{ if t1 then t2 else t3 }> --> <{ if t1' then t2 else t3 }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.
(* 在已有环境 m 中，记录 x 的类型是 v。 *)
Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty,
   right associativity) : stlc_scope.
(* 意思是从空环境开始，记录 x 的类型是 v。 *)
Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty) : stlc_scope.
Notation "'empty'" := empty
  (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
  (at level 0,
   Gamma custom stlc_tm at level 200,
   t custom stlc_tm,
   T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
      <{ Gamma |-- t1 \in Bool }> ->
      <{ Gamma |-- t2 \in T1 }> ->
      <{ Gamma |-- t3 \in T1 }> ->
      <{ Gamma |-- if t1 then t2 else t3 \in T1 }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

End STLC.
