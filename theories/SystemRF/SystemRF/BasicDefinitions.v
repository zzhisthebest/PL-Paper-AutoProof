Require Import Nat.
Require Import ZArith.

Definition index := nat.
(* 变量名字 *)
Definition var_name := nat. (* can change this atoms later *)

Declare Scope systemrf_scope.
Delimit Scope systemrf_scope with systemrf.
Open Scope systemrf_scope.

Declare Custom Entry systemrf_ty.
Declare Custom Entry systemrf_tm.

(* primitive operation（内置运算） *)
Inductive prim : Set :=
    | And 
    | Or 
    | Not 
    (* 判断两个Bool是否相同 *)
    | Eqv 
    | Imp
    (* 整数“小于等于”运算 *)
    | Leq 
    (* Leq 已经接收了第一个参数 n，正在等待第二个参数 *)
    | Leqn (n : Z)
    (* 整数“等于”运算 *)
    | Eq  
    (* Eq 已经接收了第一个参数 n，正在等待第二个参数 *)
    | Eqn (n : Z)
    (* 
    多态的小于等于。
    在当前 SystemRF 实现里，Leql 实际只支持实例化为 Int：
    Leql[Int]  --> Leq
    *)
    | Leql 
    (* 
    多态相等比较。
    例如：
    Eql [Bool] true false   = false
    Eql [Int]  3    3       = true
    *)
    | Eql.           (* Leql and Eql are polymorphic *)

(* 
basic 表示精化类型底下的“基础类型”。

例如：

{x : Int | x > 0}

这里：

- Int 是 basic
- x > 0 是精化条件
- 整个 {x : Int | x > 0} 才是 type
*)
Inductive basic : Set :=
    | TBool 
    | TInt  
    (* bound type variable，也就是“被绑定的类型变量”。 *)
    | BTV   (i : index)
    (* free type variable，也就是“自由类型变量”。 *)
    | FTV   (a : var_name).

    (* 判断：b是具体类型，不包含任何类型变量。 *)
    Definition isConcreteBasic (b : basic) : Prop :=
        match b with
        | TBool => True
        | TInt  => True
        | _     => False
        end.

    Definition isBTV (b : basic) : Prop := 
        match b with
        | (BTV _) => True
        | _       => False
        end.  

(* ONLY types with Base kind may have non-trivial refinements. Star kinded type variables 
     may only have the refinement { x : [] }. *)
Inductive kind : Set := 
    | Base         (* B, base kind *)
    | Star.        (* *, star kind *)

(* 对程序的定义 *)
Inductive expr : Set :=  
    (* Boolean constant *)
    | Bool_constant (b : bool)                 (* True, False *)
    (* Integer constant *)
    | Int_constant (n : Z)                  (* 0, 1, 2, *)
    | Prim (p : prim)               (* built-in primitive functions *)
    | BV (i : index)                (* BOUND Variables: bound to a Lambda, Let or :t *)
    | FV (x : var_name)                (* FREE Variables: bound in an environment *)
    | Lambda (e : expr)             (* \x.e          abstractions    (x is nameless) *)
    (* 把参数e2传给函数e1 *)
    | App (e1 : expr) (e2 : expr)   (* e e'          applications *)
    | LambdaT (k : kind) (e : expr) (* /\a:k.e  type abstractions    (a is nameless) *)
    | AppT (e : expr) (t : type)    (* e [bt]   type applications *)
    | Let (e1 : expr) (e2 : expr)   (* let x = e1 in e2              (x is nameless) *)
    (* e : t。声称程序 e 具有类型 t。类型标注只用于类型检查，不改变程序最终的计算结果。*)
    | Annot (e : expr) (t : type)   
    | If (e0 e1 e2 : expr)          (* if e0 then e1 else e2 *)
    | Error

(* 相当于之前的inductive ty:=... *)
with type : Set :=
    (* 精化类型：
    {x : b | ps}
    例如：
    {x : Int | x > 0} *)
    (* TRefn TBool PEmpty就是普通的Bool类型 *)
    | TRefn   (b : basic) (ps : preds)   
    (* dependent function type：x : tx -> t。输入类型是 tx，返回类型是 t，
       并且 t 可以引用输入值 x。例如 add1 的类型可以写成
       x : Int -> {y : Int | y = x + 1}。普通的 Int -> Bool 是 t 不引用 x 的特殊情况。 *)
    | TFunc   (tx : type) (t : type)     
    (* 存在类型：
    exists x : tx, t
    表示存在某个 tx 类型的值 x，使最终结果具有类型 t。 *)
    | TExists (tx : type) (t : type)  
    (* 多态类型：
    forall X : k, t
    例如：
    forall X : Star, X -> X
    其中绑定类型变量 X 在 t 中使用 BTV 0 表示。
    与之前system f不同之处：system f是forall X, t.也就是多了个k参数。
    *)
    | TPoly   (k : kind)  (t : type)     

(* preds 是 predicate list，也就是精化条件列表；PEmpty 表示没有条件，相当于空列表 []；PCons p ps 表示把条件 p 放到条件列表 ps 的最前面。例如条件列表 [x > 0, x < 10] 表示为 PCons “x > 0” (PCons “x < 10” PEmpty)。 *)
with preds : Set :=               (* i.e. [expr] *)
    | PEmpty
    | PCons (p : expr) (ps : preds).

Scheme expr_mutind  := Induction for expr  Sort Set
with   type_mutind  := Induction for type  Sort Set
with   preds_mutind := Induction for preds Sort Set.
Combined Scheme syntax_mutind from expr_mutind, type_mutind, preds_mutind.

Notation "T" := T
  (in custom systemrf_ty at level 0, T constr at level 0) : systemrf_scope.
Notation "<{{ T }}>" := T
  (T custom systemrf_ty at level 200) : systemrf_scope.
Notation "( T )" := T
  (in custom systemrf_ty at level 0, T custom systemrf_ty) : systemrf_scope.
Notation "$( T )" := T
  (in custom systemrf_ty at level 0, T constr) : systemrf_scope.
Notation "'Bool'" := (TRefn TBool PEmpty)
  (in custom systemrf_ty at level 0) : systemrf_scope.
Notation "'Int'" := (TRefn TInt PEmpty)
  (in custom systemrf_ty at level 0) : systemrf_scope.
Notation "T1 '->' T2" := (TFunc T1 T2)
  (in custom systemrf_ty at level 99, right associativity) : systemrf_scope.
Notation "'exists' T1 ',' T2" := (TExists T1 T2)
  (in custom systemrf_ty at level 200,
   T1 custom systemrf_ty,
   T2 custom systemrf_ty at level 200) : systemrf_scope.
Notation "'forall' ':' k ',' T" := (TPoly k T)
  (in custom systemrf_ty at level 200,
   k constr at level 0,
   T custom systemrf_ty at level 200) : systemrf_scope.

Notation "t" := t
  (in custom systemrf_tm at level 0, t constr at level 0) : systemrf_scope.
Notation "<{ t }>" := t
  (t custom systemrf_tm at level 200) : systemrf_scope.
Notation "( t )" := t
  (in custom systemrf_tm at level 0, t custom systemrf_tm) : systemrf_scope.
Notation "$( t )" := t
  (in custom systemrf_tm at level 0, t constr, only parsing) : systemrf_scope.
Notation "'bvar' i" := (BV i)
  (in custom systemrf_tm at level 0, i constr at level 0) : systemrf_scope.
Notation "'fvar' x" := (FV x)
  (in custom systemrf_tm at level 0, x constr at level 0) : systemrf_scope.
Notation "'true'" := (Bool_constant true)
  (in custom systemrf_tm at level 0) : systemrf_scope.
Notation "'false'" := (Bool_constant false)
  (in custom systemrf_tm at level 0) : systemrf_scope.
Notation "'Eql'" := (Prim Eql)
  (in custom systemrf_tm at level 0) : systemrf_scope.
Notation "t1 t2" := (App t1 t2)
  (in custom systemrf_tm at level 10, left associativity) : systemrf_scope.
Notation "t '[' T ']'" := (AppT t T)
  (in custom systemrf_tm at level 10,
   t custom systemrf_tm,
   T custom systemrf_ty) : systemrf_scope.
Notation "'lambda' ',' t" := (Lambda t)
  (in custom systemrf_tm at level 200,
   t custom systemrf_tm at level 200) : systemrf_scope.
Notation "'type_lambda' ':' k ',' t" := (LambdaT k t)
  (in custom systemrf_tm at level 200,
   k constr at level 0,
   t custom systemrf_tm at level 200) : systemrf_scope.
Notation "'let' t1 'in' t2" := (Let t1 t2)
  (in custom systemrf_tm at level 200,
   t1 custom systemrf_tm,
   t2 custom systemrf_tm at level 200) : systemrf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (If t1 t2 t3)
  (in custom systemrf_tm at level 200,
   t1 custom systemrf_tm,
   t2 custom systemrf_tm,
   t3 custom systemrf_tm at level 200) : systemrf_scope.
Notation "t ':' T" := (Annot t T)
  (in custom systemrf_tm at level 100,
   t custom systemrf_tm,
   T custom systemrf_ty) : systemrf_scope.

    Definition isTRefn (t : type) : Prop  := 
        match t with
        | (TRefn _ _) => True
        | _           => False
        end.
    
    Definition isTFunc (t : type) : Prop  :=
        match t with 
        | (TFunc _ _) => True
        | _           => False
        end.
    
    Definition isTExists (t : type) : Prop  := 
        match t with
        | (TExists _ _) => True
        | _             => False
        end.
    
    Definition isTPoly (t : type) : Prop  :=
        match t with
        | (TPoly _ _) => True
        | _           => False
        end.  

(* 相当于之前的value *)
Definition isValue (e: expr) : Prop :=
    match e with
    | Bool_constant _          => True
    | Int_constant _          => True
    | Prim _        => True
    | FV _          => True
    | BV _          => True
    | Lambda   _    => True
    | LambdaT   k e => True
    | _             => False         
    end.
(* 判断：类型内部没有出现 forall，也就是没有 TPoly。 *)
Fixpoint isMono (t0 : type) : Prop := 
    match t0 with         
    | (TRefn b ps)     => True  
    | (TFunc  t_x t)   => isMono t_x /\ isMono t
    | (TExists  t_x t) => isMono t_x /\ isMono t
    | (TPoly  k   t)   => False
    end.
(* 判断： t 中没有 TExists*)
Fixpoint noExists (t0 : type) : Prop := 
    match t0 with         
    | (TRefn b ps)     => True  
    | (TFunc  t_x t)   => noExists t_x /\ noExists t
    | (TExists  t_x t) => False
    | (TPoly  k   t)   => noExists t
    end.
(* locally closed：程序 e 位于 j_x 层程序 binder 和 j_a 层类型 binder 中时，所有绑定变量索引都合法。 *)
Fixpoint isLC_at (j_x : index) (j_a : index) (e : expr) : Prop  :=
    match e with
    | (Bool_constant _)         => True
    | (Int_constant _)         => True
    | (Prim _)       => True
    | (BV i)         => i < j_x
    | (FV _)         => True
    | (Lambda e')    => isLC_at (j_x + 1) j_a e'
    | (App e1 e2)    => isLC_at j_x j_a e1    /\ isLC_at j_x j_a e2 
    | (LambdaT k e') => isLC_at j_x (j_a + 1) e'
    | (AppT e' t)    => isLC_at j_x j_a e'    /\ isLCT_at j_x j_a t 
    (* let x = ex in e' 只在 e' 中绑定变量 x，因此检查 ex 时 binder 数量不变，
    检查 e' 时使用 j_x + 1。例如 let x = 3 in x 表示为 Let (Int_constant 3) (BV 0)，
    在 e' 中有一层 binder，所以 BV 0 满足 0 < 1。 *)
    | (Let ex e')    => isLC_at j_x j_a ex    /\ isLC_at (j_x+1) j_a e'  
    | (Annot e' t)   => isLC_at j_x j_a e'    /\ isLCT_at j_x j_a t 
    | (If e0 e1 e2)  => isLC_at j_x j_a e0    /\ isLC_at j_x j_a e1 /\ isLC_at j_x j_a e2
    | Error          => True
    end


(* 检查的是类型是否 locally closed。 *)
with isLCT_at (j_x : index) (j_a : index) (t0 : type) : Prop := 
    match t0 with
    | (TRefn   b  rs) =>  (* b : basic *) 
                          match b with
                          (* TRefn b rs 表示：{x : b | rs}
                          它会为 predicates rs 新绑定一个程序变量 x。因此进入 rs 时，程序 binder 深度必须加一 *)
                          | (BTV i) => i < j_a /\ isLCP_at (j_x+1) j_a rs
                          | _       =>            isLCP_at (j_x+1) j_a rs
                          end
    (* j_x+1是因为x占据了一层binder *)
    | (TFunc   t_x t) => isLCT_at j_x j_a t_x /\ isLCT_at (j_x+1) j_a t
    | (TExists t_x t) => isLCT_at j_x j_a t_x /\ isLCT_at (j_x+1) j_a t
    (* j_a+1是因为X占据了一层binder *)
    | (TPoly   k   t) =>                         isLCT_at j_x (j_a+1) t
    end
(* 检查refinement predicate列表 ps 是否 locally closed。 因为每个refinement predicate都是一个expr*)
with isLCP_at (j_x : index) (j_a : index) (ps0 : preds) : Prop := 
    match ps0 with
    | PEmpty       => True
    | (PCons p ps) => isLC_at j_x j_a p /\ isLCP_at j_x j_a ps
    end.

Definition isLC  (e  : expr)  : Prop := isLC_at  0 0 e.
Definition isLCT (t  : type)  : Prop := isLCT_at 0 0 t.
Definition isLCP (ps : preds) : Prop := isLCP_at 0 0 ps.

Fixpoint open_at (j : index) (y : var_name) (e : expr) : expr := 
    match e with
    | (Bool_constant b)             => Bool_constant b
    | (Int_constant n)             => Int_constant n
    | (Prim c)           => Prim c
    | (BV i)             => if j =? i then FV y else BV i 
    | (FV x)             => FV x
    | (Lambda e')        => Lambda (open_at (j+1) y e')
    | (App e1 e2)        => App   (open_at j y e1)  (open_at j y e2)
    | (LambdaT k e')     => LambdaT k (open_at j y e')  
    | (AppT e' t)        => AppT  (open_at j y e')  (openT_at j y t)
    | (Let ex e')        => Let   (open_at j y ex) (open_at (j+1) y e')
    | (Annot e' t)       => Annot (open_at j y e')  (openT_at j y t)
    | (If e0 e1 e2)      => If (open_at j y e0) (open_at j y e1) (open_at j y e2)
    | Error              => Error
    end

with openT_at (j : index) (y : var_name) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (openP_at (j+1) y ps)
    | (TFunc   t_z t) => TFunc   (openT_at j y t_z) (openT_at (j+1) y t)
    | (TExists t_z t) => TExists (openT_at j y t_z) (openT_at (j+1) y t)
    | (TPoly   k   t) => TPoly k (openT_at j y t) 
    end

with openP_at (j : index) (y : var_name) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (open_at j y p) (openP_at j y ps)
    end.

Definition unbind  (y : var_name) (e : expr)   : expr  :=  open_at 0 y e. 
Definition unbindT (y : var_name) (t : type)   : type  :=  openT_at 0 y t.
(* 把 predicate list ps 中最外层绑定的程序变量 BV 0，替换成自由变量 FV y。 *)
Definition unbindP (y : var_name) (ps : preds) : preds :=  openP_at 0 y ps.


Fixpoint open_tv_at (j : index) (a' : var_name) (e0 : expr) : expr :=
    match e0 with
    | (Bool_constant b)                       => Bool_constant b
    | (Int_constant n)                       => Int_constant n
    | (Prim p)                     => Prim p
    | (BV i)                       => BV i    (* looking for type vars *)
    | (FV y)                       => FV y
    | (Lambda e)                   => Lambda    (open_tv_at j a' e)  
    | (App e e')                   => App       (open_tv_at j a' e)  (open_tv_at j a' e')
    | (LambdaT k e)                => LambdaT k (open_tv_at (j+1) a' e)
    | (AppT e t)                   => AppT      (open_tv_at j a' e)  (open_tvT_at j a' t)
    | (Let e1 e2  )                => Let       (open_tv_at j a' e1) (open_tv_at  j a' e2) 
    | (Annot e t)                  => Annot     (open_tv_at j a' e)  (open_tvT_at j a' t)
    | (If e0 e1 e2)                => If (open_tv_at j a' e0) (open_tv_at j a' e1) (open_tv_at  j a' e2) 
    | Error                        => Error
    end

with open_tvT_at (j : index) (a' : var_name) (t0 : type) : type  :=
    match t0 with
    | (TRefn b  ps)     => match b with 
          | (BTV i)  => if j =? i then TRefn (FTV a') (open_tvP_at j a' ps) 
                                  else TRefn b        (open_tvP_at j a' ps)
          | _        =>                TRefn b        (open_tvP_at j a' ps) 
          end
    | (TFunc   t_z t)   => TFunc    (open_tvT_at j a' t_z) (open_tvT_at j a' t)
    | (TExists t_z t)   => TExists  (open_tvT_at j a' t_z) (open_tvT_at j a' t)
    | (TPoly   k  t)    => TPoly k  (open_tvT_at (j+1) a' t)
    end

with open_tvP_at (j : index) (a' : var_name) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (open_tv_at j a' p) (open_tvP_at j a' ps)
    end.

Definition unbind_tv  (a' : var_name) (e : expr) : expr  :=  open_tv_at 0 a' e.
Definition unbind_tvT (a' : var_name) (t : type) : type  :=  open_tvT_at 0 a' t.
Definition unbind_tvP (a' : var_name) (ps : preds) : preds := open_tvP_at 0 a' ps.


(* deBruijn index shifting : only used to define push, not in the actual proof *)
Fixpoint shift_at (j k : index) (e : expr) : expr := 
    match e with
    | (Bool_constant b)             => Bool_constant b
    | (Int_constant n)             => Int_constant n
    | (Prim c)           => Prim c
    | (BV i)             => if i <=? j then BV (i+1) else BV i 
    | (FV x)             => FV x
    | (Lambda e')        => Lambda (shift_at (j+1) k e')
    | (App e1 e2)        => App   (shift_at j k e1)  (shift_at j k e2)
    | (LambdaT k0 e')    => LambdaT k0 (shift_at j (k+1) e')  
    | (AppT e' t)        => AppT  (shift_at j k e')  (shiftT_at j k t)
    | (Let ex e')        => Let   (shift_at j k ex)  (shift_at (j+1) k e')
    | (Annot e' t)       => Annot (shift_at j k e')  (shiftT_at j k t)
    | (If e0 e1 e2)      => If (shift_at j k e0) (shift_at j k e1) (shift_at j k e2)
    | Error              => Error
    end

with shiftT_at (j k : index) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (shiftP_at (j+1) k ps)
    | (TFunc   t_z t) => TFunc   (shiftT_at j k t_z) (shiftT_at (j+1) k t)
    | (TExists t_z t) => TExists (shiftT_at j k t_z) (shiftT_at (j+1) k t)
    | (TPoly   k0  t) => TPoly k0 (shiftT_at j (k+1) t) 
    end

with shiftP_at (j k : index) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (shift_at j k p) (shiftP_at j k ps)
    end.

Definition shiftP (ps : preds) : preds := shiftP_at 0 0 ps.

  (*- TERM-LEVEL SUBSTITUTION -*)
Fixpoint subFV (x : var_name) (v_x : expr) (e0 : expr) : expr :=
    match e0 with
    | (Bool_constant b)                    => Bool_constant b
    | (Int_constant n)                    => Int_constant n
    | (Prim p)                  => Prim p
    | (BV i)                    => BV i
    | (FV y)                    => if x =? y then v_x else FV y
    | (Lambda   e)              => Lambda    (subFV x v_x e)
    | (App e e')                => App   (subFV x v_x e)  (subFV x v_x e')
    | (LambdaT   k e)           => LambdaT   k (subFV x v_x e)
    | (AppT e bt)               => AppT  (subFV x v_x e) (tsubFV x v_x bt)
    | (Let   e1 e2)             => Let   (subFV x v_x e1) (subFV x v_x e2)
    | (Annot e t)               => Annot (subFV x v_x e) (tsubFV x v_x t) 
    | (If e0 e1 e2)             => If (subFV x v_x e0) (subFV x v_x e1) (subFV x v_x e2)
    | Error                     => Error
    end

with tsubFV (x : var_name) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn  b r)     => TRefn b   (psubFV x v_x r)
    | (TFunc  t_z t)   => TFunc    (tsubFV x v_x t_z) (tsubFV x v_x t)
    | (TExists  t_z t) => TExists  (tsubFV x v_x t_z) (tsubFV x v_x t)
    | (TPoly  k   t)   => TPoly    k                  (tsubFV x v_x t)
    end

with psubFV (x : var_name) (v_x : expr) (ps0 : preds) : preds :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subFV x v_x p) (psubFV x v_x ps)
    end.

Fixpoint strengthen (qs : preds) (rs : preds) : preds :=
    match qs with
    | PEmpty       => rs 
    | (PCons p ps) => PCons p (strengthen ps rs)
    end.

(* When substituting in for a type variable, say a{x:p}[t_a/a], where t_a is not a refined
--     basic type, then we need to express "t_a {x:p}" by pushing the refinement down into t_a.
--     For example a{x:p}[ ( \exists y:Int{y:q}. a'{z:r} )/a] becomes roughly speaking
--             \exists Int{y:q}. a'{z:r `And` p} *)
Fixpoint push (p : preds) (t0 : type) : type := 
    match t0 with
    | (TRefn   b     r)  => TRefn   b     (strengthen p r)
    | (TFunc     t_y t)  => TFunc     t_y t
    | (TExists   t_y t)  => TExists   t_y (push (shiftP p) t)
        (* wanted: match texists_not_usertype t_y t pf with end *)
    | (TPoly     k   t)  => TPoly     k   t
    end.    

Fixpoint subFTV (a : var_name) (t_a : type) (e0 : expr) : expr :=
    match e0 with
    | (Bool_constant b)                    => Bool_constant b
    | (Int_constant n)                    => Int_constant n
    | (Prim p)                  => Prim p
    | (BV i)                    => BV i
    | (FV y)                    => FV y
    | (Lambda   e)              => Lambda     (subFTV a t_a e)
    | (App e e')                => App   (subFTV a t_a e)  (subFTV a t_a e')
    | (LambdaT    k e)          => LambdaT    k (subFTV a t_a e)
    | (AppT e t)                => AppT  (subFTV a t_a e) (tsubFTV a t_a t)
    | (Let   e1 e2)             => Let   (subFTV a t_a e1) (subFTV a t_a e2)
    | (Annot e t)               => Annot (subFTV a t_a e) (tsubFTV a t_a t) 
    | (If e0 e1 e2)             => If (subFTV a t_a e0) (subFTV a t_a e1) (subFTV a t_a e2)
    | Error                     => Error
    end

with tsubFTV (a : var_name) (t_a : type) (t0 : type) : type  :=
    match t0 with
    | (TRefn b   r)        => match b with
          | (FTV a')   => if a =? a' then push      (psubFTV a t_a r) t_a
                                     else TRefn b   (psubFTV a t_a r)
          | _          =>                 TRefn b   (psubFTV a t_a r)
          end
    | (TFunc     t_z t)    => TFunc      (tsubFTV a t_a t_z) (tsubFTV a t_a t)
    | (TExists   t_z t)    => TExists    (tsubFTV a t_a t_z) (tsubFTV a t_a t)
    | (TPoly      k  t)    => TPoly      k                   (tsubFTV a t_a t)
    end

with psubFTV (a : var_name) (t_a : type) (ps0 : preds) : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subFTV a t_a p) (psubFTV a t_a ps)
    end.

Fixpoint subBV_at (j : index) (v : expr) (e0 : expr) : expr :=
    match e0 with
    | (Bool_constant b)             => Bool_constant b
    | (Int_constant n)             => Int_constant n
    | (Prim c)           => Prim c
    | (BV i)             => if j =? i then v else BV i
    | (FV x)             => FV x
    | (Lambda e)         => Lambda (subBV_at (j+1) v e)
    | (App e e')         => App   (subBV_at j v e)  (subBV_at j v e')
    | (LambdaT k e)      => LambdaT k (subBV_at j v e) 
    | (AppT e t)         => AppT  (subBV_at j v e)  (tsubBV_at j v t)
    | (Let ex e)         => Let   (subBV_at j v ex) (subBV_at (j+1) v e)
    | (Annot e t)        => Annot (subBV_at j v e)  (tsubBV_at j v t)
    | (If e0 e1 e2)      => If (subBV_at j v e0) (subBV_at j v e1) (subBV_at j v e2)
    | Error              => Error
    end

with tsubBV_at (j : index) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (psubBV_at (j+1) v_x ps)  
    | (TFunc   t_z t) => TFunc   (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
    | (TExists t_z t) => TExists (tsubBV_at j v_x t_z) (tsubBV_at (j+1) v_x t)
    | (TPoly   k  t)  => TPoly k (tsubBV_at j v_x t)  
    end

with psubBV_at (j : index) (v_x : expr) (ps0 : preds) : preds  := 
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subBV_at j v_x p) (psubBV_at j v_x ps)
    end.

Definition subBV  (v : expr) (e : expr)   : expr  :=  subBV_at 0 v e.
Definition tsubBV (v_x : expr) (t : type) : type  :=  tsubBV_at 0 v_x t.
Definition psubBV (v : expr) (ps : preds) : preds :=  psubBV_at 0 v ps.

Fixpoint subBTV_at (j : index) (t_a : type) (e0 : expr) : expr :=
    match e0 with
    | (Bool_constant b)                       => Bool_constant b
    | (Int_constant n)                       => Int_constant n
    | (Prim p)                     => Prim p
    | (BV i)                       => BV i 
    | (FV y)                       => FV y
    | (Lambda   e)                 => Lambda    (subBTV_at j t_a e)  
    | (App e e')                   => App       (subBTV_at j t_a e)  (subBTV_at j t_a e')
    | (LambdaT  k e)               => LambdaT k (subBTV_at (j+1) t_a e)
    | (AppT e t)                   => AppT      (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    | (Let   e1 e2)                => Let       (subBTV_at j t_a e1) (subBTV_at j t_a e2) 
    | (Annot e t)                  => Annot     (subBTV_at j t_a e) (tsubBTV_at j t_a t)
    | (If e0 e1 e2)                => If (subBTV_at j t_a e0) (subBTV_at j t_a e1) (subBTV_at j t_a e2)
    | Error                        => Error
    end

with tsubBTV_at (j : index) (t_a : type) (t0 : type) : type :=
    match t0 with
    | (TRefn b   ps)     => match b with
          | (BTV i) => if j =? i then push (psubBTV_at j t_a ps) t_a 
                                 else TRefn b (psubBTV_at j t_a ps) (* TExists y t_y (push x r[t_a/a] t')  *)
          | _       =>                TRefn b (psubBTV_at j t_a ps)    
          end
    | (TFunc   t_z t)    => TFunc    (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  
    | (TExists t_z t)    => TExists  (tsubBTV_at j t_a t_z) (tsubBTV_at j t_a t)  
    | (TPoly   k  t)     => TPoly k  (tsubBTV_at (j+1) t_a t)
    end

with psubBTV_at (j : index) (t_a : type) (ps0 : preds) : preds :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subBTV_at j t_a p) (psubBTV_at j t_a ps)
    end.

Definition subBTV  (t : type)   (e : expr)   : expr  :=  subBTV_at 0 t e.
Definition tsubBTV (t_a : type) (t : type)   : type  :=  tsubBTV_at 0 t_a t.
Definition psubBTV (t_a : type) (ps : preds) : preds :=  psubBTV_at 0 t_a ps.


(* BARE TYPES: i.e. System F types. These still contain type polymorphism and type variables, 
     but all the refinements, dependent arrow binders, and existentials have been erased. *)
(* 擦除 refinement information 后的普通 System F 类型 *)
Inductive ftype : Set :=
    | FTBasic (b : basic)                (* b: Bool, Int, FTV a, BTV a *)
    | FTFunc  (t1 : ftype) (t2 : ftype)  (* bt -> bt' *)
    | FTPoly  (k : kind) (t : ftype).    (* \forall a:k. bt *)

    Definition isBaseF (t : ftype) : Prop  :=
        match t with
        | (FTBasic b)     => True
        | _               => False
        end.
    (* 不包含任何类型变量的具体基础类型 *)
    Definition isClosedBaseF (t : ftype) : Prop  :=
        match t with
        | (FTBasic TBool) => True
        | (FTBasic TInt)  => True
        | _               => False
        end.

(* 删除 ty 中的 refinement predicates 及仅用于 refinement 的依赖信息，
    返回对应的普通 System F 类型。 *)
Fixpoint erase (t0 : type) : ftype :=
    match t0 with
    (* 这个是基础分支，其余三个是递归分支 *)
    | (TRefn b r)     => FTBasic b
    | (TFunc t_x t)   => FTFunc (erase t_x) (erase t)
    | (TExists t_x t) => (erase t)
    | (TPoly  k  t)   => FTPoly k (erase t)
    end.

Fixpoint isMonoF (t0 : ftype) : Prop := 
    match t0 with         
    | (FTBasic b)      => True  
    | (FTFunc  t_x t)  => isMonoF t_x /\ isMonoF t
    | (FTPoly  k   t)  => False
    end.  (* is this needed? *)

Fixpoint isLCFT_at (j : index) (t0 : ftype) : Prop :=
    match t0 with
    | (FTBasic b)      => match b with
                          | (BTV i)   => i < j
                          | _         => True
                          end
    | (FTFunc t_x t)   => isLCFT_at j t_x /\ isLCFT_at j t
    | (FTPoly   k t)   => isLCFT_at (j+1) t
    end.

Definition isLCFT (t : ftype) : Prop  :=  isLCFT_at 0 t.

Fixpoint openFT_at (j : index) (a' : var_name) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)    => match b with   (* TODO put arg on left *)
                        | (BTV i) => if j =? i then FTBasic (FTV a') else FTBasic b
                        | _       => FTBasic b
                        end
    | (FTFunc t_x t) => FTFunc (openFT_at j a' t_x) (openFT_at j a' t)
    | (FTPoly k   t) => FTPoly k (openFT_at (j+1) a' t)
    end.

Definition unbindFT (a' : var_name) (t : ftype) : ftype := openFT_at 0 a' t.

Fixpoint ftsubFV (a : var_name) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic b)     => match b with
                         | (FTV a')  => if a =? a' then t_a else FTBasic b
                         | _         => FTBasic b
                         end
    | (FTFunc t_z t)  => FTFunc (ftsubFV a t_a t_z) (ftsubFV a t_a t)
    | (FTPoly   k t)  => FTPoly k (ftsubFV a t_a t)
    end.

Fixpoint ftsubBV_at (j : index) (t_a : ftype) (t0 : ftype) : ftype :=
    match t0 with
    | (FTBasic   b)   =>  match b with
                          | (BTV i) => if j =? i then t_a else FTBasic b
                          | _       => FTBasic b
                          end
    | (FTFunc t_z t)  => FTFunc (ftsubBV_at j t_a t_z) (ftsubBV_at j t_a t)
    | (FTPoly  k  t)  => FTPoly k (ftsubBV_at (j+1) t_a t)
    end.
 
Definition ftsubBV (t_a : ftype) (t : ftype) : ftype  :=  ftsubBV_at 0 t_a t.
