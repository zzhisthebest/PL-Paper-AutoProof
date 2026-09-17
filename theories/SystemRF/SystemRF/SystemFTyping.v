Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions. 
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.

Require Import ZArith.

(*-------------------------------------------------------------------------
----- | REFINEMENT TYPES of BUILT-IN PRIMITIVES
-------------------------------------------------------------------------*)
(* 表示布尔常量 b 的精确 refinement type：
  tybc true  = { x : Bool | x = true }
  tybc false = { x : Bool | x = false } *)
Definition tybc (b:bool) : type := (*Set_emp (free t) && Set_emp (freeTV t) *)
    TRefn TBool (PCons (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) 
                                 (Bool_constant b)) (BV 0))  PEmpty).

Definition tyic (n:Z) : type := (* Set_emp (free t) && Set_emp (freeTV t) *)
    TRefn TInt  (PCons (App (App (AppT (Prim Eql) (TRefn TInt  PEmpty))
                                 (Int_constant n)) (BV 0))  PEmpty).

Definition refn_pred (c:prim) : expr := (* Set_emp (fv p) && Set_emp (ftv p) *)
    match c with 
    | And      => App (App (Prim Eqv) 
                           (App (App (Prim And) (BV 2)) (BV 1))) (BV 0)
    | Or       => App (App (Prim Eqv) 
                           (App (App (Prim Or)  (BV 2)) (BV 1))) (BV 0)
    | Not      => App (App (Prim Eqv) (App (Prim Not) (BV 1))) (BV 0)
    | Eqv      => App (App (Prim Eqv) 
                           (App (App (Prim Eqv) (BV 2)) (BV 1))) (BV 0)
    | Imp      => App (App (Prim Eqv)
                           (App (App (Prim Imp) (BV 2)) (BV 1))) (BV 0)
    | Leq      => App (App (Prim Eqv) 
                           (App (App (Prim Leq) (BV 2)) (BV 1))) (BV 0)
    | (Leqn n) => App (App (Prim Eqv) 
                           (App (App (Prim Leq) (Int_constant n)) (BV 1))) (BV 0)
    | Eq       => App (App (Prim Eqv) 
                           (App (App (Prim Eq)  (BV 2)) (BV 1))) (BV 0)
    | (Eqn n)  => App (App (Prim Eqv) 
                           (App (App (Prim Eq)  (Int_constant n)) (BV 1))) (BV 0)
    | Leql     => App (App (Prim Eqv) 
                           (App (App (AppT (Prim Leql) (TRefn (BTV 0) PEmpty)) 
                                     (BV 2)) (BV 1))) (BV 0)
    | Eql      => App (App (Prim Eqv) 
                           (App (App (AppT (Prim Eql)  (TRefn (BTV 0) PEmpty)) 
                                     (BV 2)) (BV 1))) (BV 0)
    end.

(* 定义内置运算接收的第一个程序参数的type *)
(* 
 以：
  Leql[Int] 3 5
  为例，它依次接收：
  Int    类型参数
  3      第一个程序参数
  5      第二个程序参数
  primitive_input_type Leql 描述的是 3 的类型，不是类型参数 Int。
*)
Definition primitive_input_type (c:prim ) : type := (* Set_emp (free t) && Set_emp (freeTV t) *)
    match c with 
    | And     => TRefn TBool   PEmpty 
    | Or      => TRefn TBool   PEmpty
    | Eqv     => TRefn TBool   PEmpty
    | Imp     => TRefn TBool   PEmpty
    | Not     => TRefn TBool   PEmpty
    | Leq      => TRefn TInt    PEmpty
    (* _ 对应 Leq 已经接收并保存在 Leqn 里的第一个整数参数。 *)
    | Leqn _   => TRefn TInt    PEmpty 
    | Eq       => TRefn TInt    PEmpty
    | Eqn _    => TRefn TInt    PEmpty
    | Leql     => TRefn (BTV 0) PEmpty
    | Eql      => TRefn (BTV 0) PEmpty
    end.
(* 内置运算 c 接收一个程序参数以后，剩余部分的类型。 *)
Definition primitive_remaining_type (c:prim) : type := (*Set_emp (free t) && Set_emp (freeTV t) *)
    match c with
    (* And 的完整类型是：
       (x : Bool) -> (y : Bool) -> {result : Bool | result = And x y}。
       接收第一个参数 x 后，剩余类型是：
       (y : Bool) -> {result : Bool | result = And x y}。 *)
    | And      => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred And) PEmpty))
    | Or       => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Or)  PEmpty))
    | Not      =>                             TRefn TBool (PCons (refn_pred Not) PEmpty)
    | Eqv      => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Eqv) PEmpty))
    | Imp      => TFunc (TRefn TBool PEmpty) (TRefn TBool (PCons (refn_pred Imp) PEmpty))
    | Leq      => TFunc (TRefn TInt  PEmpty) (TRefn TBool (PCons (refn_pred Leq) PEmpty))
    | (Leqn n) =>                             TRefn TBool (PCons (refn_pred (Leqn n)) PEmpty)
    | Eq       => TFunc (TRefn TInt  PEmpty) (TRefn TBool (PCons (refn_pred Eq)  PEmpty)) 
    | (Eqn n)  =>                             TRefn TBool (PCons (refn_pred (Eqn n)) PEmpty)
    | Leql     => TFunc (TRefn (BTV 0) PEmpty) (TRefn TBool (PCons (refn_pred Leql) PEmpty))
    | Eql      => TFunc (TRefn (BTV 0) PEmpty) (TRefn TBool (PCons (refn_pred Eql) PEmpty))
    end.

(* 内置运算 c 的类型。
  例如：
  primitive_type And
  = (x : Bool) -> (y : Bool) -> {result : Bool | result = And x y}
*)
Definition primitive_type (c:prim) : type := (*Set_emp (free t) && Set_emp (freeTV t) *)
    match c with
    | And      => TFunc (primitive_input_type And)      (primitive_remaining_type And)
    | Or       => TFunc (primitive_input_type Or)       (primitive_remaining_type Or)
    | Not      => TFunc (primitive_input_type Not)      (primitive_remaining_type Not)
    | Eqv      => TFunc (primitive_input_type Eqv)      (primitive_remaining_type Eqv)
    | Imp      => TFunc (primitive_input_type Imp)      (primitive_remaining_type Imp)
    | Leq      => TFunc (primitive_input_type Leq)      (primitive_remaining_type Leq)
    | (Leqn n) => TFunc (primitive_input_type (Leqn n)) (primitive_remaining_type (Leqn n))
    | Eq       => TFunc (primitive_input_type Eq)       (primitive_remaining_type Eq)
    | (Eqn n)  => TFunc (primitive_input_type (Eqn n))  (primitive_remaining_type (Eqn n))
    | Leql     => TPoly Base (TFunc (primitive_input_type Leql) (primitive_remaining_type Leql))
    | Eql      => TPoly Base (TFunc (primitive_input_type Eql)  (primitive_remaining_type Eql))
    end.

Definition erase_ty (c:prim) : ftype := (* Set_emp (ffreeTV t) && t == erase (primitive_type c) && isLCFT t *)
    match c with
    | And      => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Or       => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Not      => FTFunc (FTBasic TBool) (FTBasic TBool)
    | Eqv      => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Imp      => FTFunc (FTBasic TBool) (FTFunc (FTBasic TBool) (FTBasic TBool))
    | Leq      => FTFunc (FTBasic TInt)  (FTFunc (FTBasic TInt)  (FTBasic TBool))
    | (Leqn n) => FTFunc (FTBasic TInt)  (FTBasic TBool)
    | Eq       => FTFunc (FTBasic TInt)  (FTFunc (FTBasic TInt)  (FTBasic TBool))
    | (Eqn n)  => FTFunc (FTBasic TInt)  (FTBasic TBool)
    | Leql     => FTPoly Base (FTFunc (FTBasic (BTV 0))
                                      (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))
    | Eql      => FTPoly Base (FTFunc (FTBasic (BTV 0)) 
                                      (FTFunc (FTBasic (BTV 0)) (FTBasic TBool)))
    end.

Lemma erase_ty_ffreeTV : forall (c:prim), ffreeTV (erase_ty c) = empty.
Proof. destruct c; simpl; reflexivity. Qed. 

(*-----------------------------------------------------------------------------
----- | JUDGEMENTS : the Bare-Typing Relation
-----------------------------------------------------------------------------*)

(* HasFtype g e ty 表示：在普通 System F 环境 g : fenv 中，
   程序 e : expr 具有普通类型 ty : ftype。 *)
Inductive HasFtype : fenv -> expr -> ftype -> Prop := 
    | FTBC   : forall (g:fenv) (b:bool),  HasFtype g (Bool_constant b) (FTBasic TBool)
    | FTIC   : forall (g:fenv) (n:Z),   HasFtype g (Int_constant n) (FTBasic TInt)
    | FTVar  : forall (g:fenv) (x:var_name) (b:ftype),
          bound_inF x b g -> HasFtype g (FV x) b
    | FTPrm  : forall (g:fenv) (c:prim), HasFtype g (Prim c) (erase_ty c)
    | FTAbs  : forall (g:fenv) (b:ftype) (k:kind) (e:expr) (b':ftype) (nms:names),
          WFFT g b k 
              -> (forall (y:var_name), ~ In y nms -> HasFtype (FCons y b g) (unbind y e) b' )
              -> HasFtype g (Lambda e) (FTFunc b b')
    | FTApp  : forall (g:fenv) (e:expr) (b:ftype) (b':ftype) (e':expr),
          HasFtype g e (FTFunc b b') -> HasFtype g e' b -> HasFtype g (App e e') b'
    | FTAbsT : forall (g:fenv) (k:kind) (e:expr) (b:ftype) (nms:names),
          (forall (a':var_name), ~ In a' nms
                    -> HasFtype (FConsT a' k g) (unbind_tv a' e) (unbindFT a' b) )
              -> HasFtype g (LambdaT k e) (FTPoly k b)
    | FTAppT : forall (g:fenv) (e:expr) (k:kind) (t':ftype) (rt:type),
          HasFtype g e (FTPoly k t') -> isMono rt
              -> noExists rt -> Subset (free rt) (vbindsF g) 
                             -> Subset (freeTV rt) (tvbindsF g) -> isLCT rt
              -> WFFT g (erase rt) k -> HasFtype g (AppT e rt) (ftsubBV (erase rt) t')
    | FTLet  : forall (g:fenv) (e_x:expr) (b:ftype) (e:expr) (b':ftype) (nms:names),
          HasFtype g e_x b 
              -> (forall (y:var_name), ~ In y nms -> HasFtype (FCons y b g) (unbind y e) b' )
              -> HasFtype g (Let e_x e) b'
    | FTAnn  : forall (g:fenv) (e:expr) (b:ftype) (t1:type),
          erase t1 = b  -> Subset (free t1) (vbindsF g) 
                        -> Subset (freeTV t1) (tvbindsF g) -> isLCT t1 
              -> HasFtype g e b -> HasFtype g (Annot e t1) b
    | FTIf   : forall (g : fenv) (e0 e1 e2 : expr) (t : ftype),
          HasFtype g e0 (FTBasic TBool) -> HasFtype g e1 t -> HasFtype g e2 t
              -> HasFtype g (If e0 e1 e2) t.

(* PredicatesHaveBoolType g ps 表示在环境 g 中，ps 里的每个 predicate 都具有 Bool 类型。 *)
Inductive PredicatesHaveBoolType : fenv -> preds -> Prop := 
    | PFTEmp  : forall (g:fenv), PredicatesHaveBoolType g PEmpty
    | PFTCons : forall (g:fenv) (p:expr) (ps:preds),
          HasFtype g p (FTBasic TBool) -> PredicatesHaveBoolType g ps -> PredicatesHaveBoolType g (PCons p ps).
