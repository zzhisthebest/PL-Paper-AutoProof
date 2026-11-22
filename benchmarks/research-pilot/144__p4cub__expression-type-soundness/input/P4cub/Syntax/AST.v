Require Import Coq.PArith.BinPos Coq.ZArith.BinInt.

Require Export Poulet4.P4cub.Syntax.P4Field.

Import String.

Variant paramarg (A B : Set) : Set :=
  | PAIn    (a : A)
  | PAOut   (b : B)
  | PAInOut (b : B)  .

Arguments PAIn {_} {_}.

Arguments PAOut {_} {_}.

Arguments PAInOut {_} {_}.

Definition paramarg_map {A B C D : Set}
           (f : A -> C) (g : B -> D)
           (pa : paramarg A B) : paramarg C D :=
  match pa with
  | PAIn    a => PAIn      (f a)
  | PAOut   b => PAOut     (g b)
  | PAInOut b => PAInOut   (g b)
  end.

Definition paramarg_map_same
           {A B : Set} (f : A -> B)
  : paramarg A A -> paramarg B B :=
  paramarg_map f f.

Variant pred_paramarg {A B : Set}
  (P : A -> Prop) (Q : B -> Prop) : paramarg A B -> Prop :=
  | pred_PAIn a : P a -> pred_paramarg P Q (PAIn a)
  | pred_PAOut b : Q b -> pred_paramarg P Q (PAOut b)
  | pred_PAInOut b : Q b -> pred_paramarg P Q (PAInOut b).

Definition pred_paramarg_same {A : Set} (P : A -> Prop)
  : paramarg A A -> Prop := pred_paramarg P P.

Variant rel_paramarg {A1 A2 B1 B2 : Set}
  (R : A1 -> A2 -> Prop) (Q : B1 -> B2 -> Prop)
  : paramarg A1 B1 -> paramarg A2 B2 -> Prop :=
  | rel_paramarg_PAIn a1 a2 :
    R a1 a2 -> rel_paramarg R Q (PAIn a1) (PAIn a2)
  | rel_paramarg_PAOut b1 b2 :
    Q b1 b2 -> rel_paramarg R Q (PAOut b1) (PAOut b2)
  | rel_paramarg_PAInOut b1 b2 :
    Q b1 b2 -> rel_paramarg R Q (PAInOut b1) (PAInOut b2).

Definition rel_paramarg_same {A B : Set} (R : A -> B -> Prop) :
  paramarg A A -> paramarg B B -> Prop :=
  rel_paramarg R R.

Definition paramarg_elim {A : Set} (p : paramarg A A) : A :=
    match p with
    | PAIn a | PAOut a | PAInOut a => a
    end.

Record arrow (A B C : Set) : Set :=
  { paramargs : list (A * paramarg B C);
    rtrns : option C }.

Arguments paramargs {_} {_} {_}.

Arguments rtrns {_} {_} {_}.

Module Typ.

Inductive t : Set :=
  | Bool
  | VarBit (max_width: N)
  | Bit    (width : N)
  | Int    (width : positive)
  | Error
  | Array  (size : N) (typ : t)
  | Struct (isheader : bool) (fields : list t)
  | Var    (type_name : nat)                   .

Definition param : Set := paramarg Typ.t Typ.t.

Definition params : Set :=
    list (  string * param).

Definition arrowT : Set := arrow   string Typ.t Typ.t.

End Typ.

Module Una.

Variant t : Set :=
    | Not
    | BitNot
    | Minus
    | IsValid
    | SetValidity (validity : bool)  .

End Una.

Module Bin.

Variant t : Set :=
  | Plus
  | PlusSat
  | Minus
  | MinusSat
  | Times
  | Shl
  | Shr
  | Le
  | Ge
  | Lt
  | Gt
  | Eq
  | NotEq
  | BitAnd
  | BitXor
  | BitOr
  | PlusPlus
  | And
  | Or        .

End Bin.

Module Lst.

Variant t : Set :=
    | Struct
    | Array  (element_type : Typ.t)
    | Header (b : bool).

End Lst.

Module Exp.

Inductive t : Set :=
  | Bool   (b : bool)
  | VarBit (max_width : N) (width : N) (val : Z)
  | Bit    (width : N) (val : Z)
  | Int    (width : positive) (val : Z)
  | Var    (type : Typ.t) (original_name : string) (x : nat)
  | Slice  (hi lo : positive) (arg : t)
  | Cast   (type : Typ.t) (arg : t)
  | Uop    (result_type : Typ.t) (op : Una.t) (arg : t)
  | Bop    (result_type : Typ.t) (op : Bin.t) (lhs rhs : t)
  | Lists  (flag : Lst.t) (es : list t)
  | Index  (elem_type : Typ.t) (array index : t)
  | Member (result_type : Typ.t) (mem : nat) (arg : t)
  | Error  (err : string)                                    .

Definition arg : Set := paramarg Exp.t Exp.t.

Definition args : Set := list arg.

End Exp.

Module Lbl.

Variant t : Set :=
    | Start
    | Accept
    | Reject
    | Name (st : nat)  .

End Lbl.

Module Pat.

Inductive t : Set :=
  | Wild
  | Mask  (p1 p2 : t)
  | Range (p1 p2 : t)
  | Bit   (width : N) (val : Z)
  | Int   (width : positive) (val : Z)
  | Lists (ps : list t)                 .

End Pat.

Module Trns.

Variant t : Set :=
  | Direct (st : Lbl.t)
  | Select (discriminee : Exp.t)
      (default : Lbl.t)
      (cases : list (Pat.t * Lbl.t))

.

End Trns.

Module Call.

Variant t : Set :=
    | Funct  (function_name : string) (type_args : list Typ.t)
        (returns : option Exp.t)
    | Action (action_name : string)
        (control_plane_args : list Exp.t)
    | Method (extern_instance_name method_name : string)
        (type_args : list Typ.t) (returns : option Exp.t)
    | Inst   (instance_name : string) (ext_args : list string)  .

End Call.

Module Stm.

Inductive t : Set :=


  | Skip
  | Ret (e : option Exp.t)
  | Exit
  | Trans (trns : Trns.t)
  | Asgn (lhs rhs : Exp.t)
  | App (call : Call.t) (args : Exp.args)
  | Invoke (lhs : option Exp.t) (table_name : string)


  | LetIn (original_name : string) (init : Typ.t  + Exp.t)
      (tail : t)
  | Seq (head tail : t)
  | Cond (guard : Exp.t) (tru fls : t)  .

End Stm.

Module Ctrl.

Variant t : Set :=
    | Var (original_name : string) (expr : Typ.t + Exp.t)
  | Action (action_name : string)
      (control_plane_params : list (string * Typ.t))
      (data_plane_params : Typ.params)
      (body : Stm.t)
  | Table (table_name : string)
      (key : list (Exp.t * string))
      (actions :
        list
          (string
           * Exp.args  ))
      (default_action : option (string * list Exp.t))      .

End Ctrl.

Module Cnstr.

Variant t : Set :=
    | Control
    | Parser   .

End Cnstr.

Module InstTyp.

Variant t : Set :=
    | Ctr (flag : Cnstr.t)
        (extern_params : list string)
        (parameters : Typ.params)
    | Package
    | Extern (extern_name : string)  .

End InstTyp.

Module Top.

Definition constructor_params : Set := list (string * InstTyp.t).

Definition constructor_args : Set := list string.

Variant t : Set :=
    | Instantiate
        (constructor_name instance_name : string)
        (type_args : list Typ.t)
        (cargs : constructor_args)
        (expr_cargs : list Exp.t)
    | Extern
        (extern_name : string)
        (type_params : nat)
        (cparams : constructor_params)
        (expr_cparams : list Typ.t)
        (methods : Field.fs
                     string
                     (nat
                      * list string
                      * Typ.arrowT  ))

    | Control
        (control_name : string)
        (cparams : constructor_params)
        (expr_cparams : list Typ.t)
        (eparams : list (string * string))
        (params : Typ.params)
        (body : list Ctrl.t)
        (apply_blk : Stm.t)
    | Parser
        (parser_name : string)
        (cparams : constructor_params)
        (expr_cparams : list Typ.t)
        (eparams : list (string * string))
        (params : Typ.params)
        (start : Stm.t)
        (states : list Stm.t)

    | Funct
        (function_name : string)
        (type_params : nat)
        (signature : Typ.arrowT)
        (body : Stm.t)  .

Definition prog : Set := list t.

End Top.
