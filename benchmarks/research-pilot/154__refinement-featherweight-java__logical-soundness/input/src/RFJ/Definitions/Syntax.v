Require Import RFJ.Lists.

Require Import RFJ.Utils.

Require Import Nat.

Require Import ZArith.

Notation "'[' X ']'" := (list X) (at level 40).

Definition index := nat.

Definition vname := nat.

Definition ClassName := nat.

Definition InterfaceName := nat.

Definition FieldName := nat.

Definition MethodName := nat.

Definition LblName := nat.

Parameter this: vname.

Parameter v: vname.

Inductive nomtype: Type :=
| TClass: ClassName -> nomtype
| TInterface: InterfaceName -> nomtype.

Inductive fjtype : Type :=
  | TAny
  | TBool
  | TInt
  | TNom: nomtype -> fjtype.

Inductive UnOp :=
  | Not.

Inductive BinOp :=
  | And
  | Or
  | Eq.

Inductive expr : Type :=
  | Bc (b : bool)
  | Ic (n : Z)
  | BV (i : index)
  | FV (x : vname)
  | ExpUnOp (o:UnOp) (e:expr)
  | ExpBinOp (o:BinOp) (e1:expr) (e2:expr)
  | ExpFieldAccess : expr -> FieldName -> expr
  | ExpMethodInvoc : expr -> MethodName -> expr -> expr
  | ExpNew : ClassName -> [expr] -> expr
  | ExpLet (e1 : expr) (e2 : expr)


with type:Type :=
  | TRefn   (b : fjtype) (ps : preds)


with preds : Type :=
  | PEmpty: preds
  | PCons (p : expr) (ps : preds).

Scheme expr_mutind  := Induction for expr  Sort Prop
with   type_mutind  := Induction for type  Sort Prop
with   preds_mutind := Induction for preds Sort Prop.

Definition syntax_mutind' := fun (P : expr -> Prop) (P0 : type -> Prop) (P1 : preds -> Prop)
(f0: forall b : bool, P (Bc b))
(f1: forall n : Z, P (Ic n))
(f2: forall i : index, P (BV i))
(f3: forall x : vname, P (FV x))
(f4: (forall (o : UnOp) (e : expr), P e -> P (ExpUnOp o e)))
(f5: (forall (o : BinOp) (e1 : expr), P e1 -> forall e2 : expr, P e2 -> P (ExpBinOp o e1 e2)))
(f6: (forall e : expr, P e -> forall (m : MethodName) (e0 : expr), P e0 -> P (ExpMethodInvoc e m e0)))
(f7: forall e : expr, P e -> forall f6 : FieldName, P (ExpFieldAccess e f6))
(f8: forall (c : ClassName) (l : [expr]), Forall P l -> P (ExpNew c l))
(f9: (forall e1 : expr, P e1 -> forall e2 : expr, P e2 -> P (ExpLet e1 e2)))
(g0: forall (b : fjtype) (ps : preds), P1 ps -> P0 (TRefn b ps))
(h0: P1 PEmpty)
(h1: (forall p : expr, P p -> forall ps : preds, P1 ps -> P1 (PCons p ps)))
=>
(conj (fix f (e:expr) : P e :=
match e with
| Bc b => f0 b
| Ic n => f1 n
| BV i => f2 i
| FV x => f3 x
| ExpUnOp o e => f4 o e (f e)
| ExpBinOp o e0 e1 => f5 o e0 (f e0) e1 (f e1)
| ExpFieldAccess e0 ff => f7 e0 (f e0) ff
| ExpMethodInvoc e m e0 => f6 e (f e) m e0 (f e0)
| ExpNew c es => f8 c es ((fix list_Forall_ind (es' : [expr]):
Forall (P) es':=
match es' with
| nil => @Forall_nil expr P
| (e::es'') => @Forall_cons expr P e es'' (f e) (list_Forall_ind es'')
end) es)
| ExpLet e1 e2 => f9 e1 (f e1) e2 (f e2)
end)

(conj (fix g (t:type) : P0 t :=
match t with
| TRefn b ps => g0 b ps (h ps)
end
with h (ps:preds) : P1 ps :=
(match ps with
| PEmpty => h0
| PCons p ps' => h1 p (f p) ps' (h ps')
end)
with f (e:expr) : P e :=
(match e with
| Bc b => f0 b
| Ic n => f1 n
| BV i => f2 i
| FV x => f3 x
| ExpUnOp o e => f4 o e (f e)
| ExpBinOp o e0 e1 => f5 o e0 (f e0) e1 (f e1)
| ExpFieldAccess e0 ff => f7 e0 (f e0) ff
| ExpMethodInvoc e m e0 => f6 e (f e) m e0 (f e0)
| ExpNew c es => f8 c es ((fix list_Forall_ind (es' : [expr]):
Forall (P) es':=
match es' with
| nil => @Forall_nil expr P
| (e::es'') => @Forall_cons expr P e es'' (f e) (list_Forall_ind es'')
end) es)
| ExpLet e1 e2 => f9 e1 (f e1) e2 (f e2)
end) for g
)

(fix h (ps:preds) : P1 ps :=
(match ps with
| PEmpty => h0
| PCons p ps' => h1 p (f p) ps' (h ps')
end)
with f (e:expr) : P e :=
(match e with
| Bc b => f0 b
| Ic n => f1 n
| BV i => f2 i
| FV x => f3 x
| ExpUnOp o e => f4 o e (f e)
| ExpBinOp o e0 e1 => f5 o e0 (f e0) e1 (f e1)
| ExpFieldAccess e0 ff => f7 e0 (f e0) ff
| ExpMethodInvoc e m e0 => f6 e (f e) m e0 (f e0)
| ExpNew c es => f8 c es ((fix list_Forall_ind (es' : [expr]):
Forall (P) es':=
match es' with
| nil => @Forall_nil expr P
| (e::es'') => @Forall_cons expr P e es'' (f e) (list_Forall_ind es'')
end) es)
| ExpLet e1 e2 => f9 e1 (f e1) e2 (f e2)
end) for h
))
).

Fixpoint erase (t0 : type) : fjtype :=
  match t0 with
  | (TRefn b r)     => b
  end.

Fixpoint isValue (e: expr) : Prop :=
  match e with
  | Bc _          => True
  | Ic _          => True
  | ExpNew c es => (fix f (es': [expr]) := match es' with | nil => True | e::es''=> isValue e /\ (f es'') end) es
  | _             => False
  end.

Fixpoint isLC_at (j_x : index) (e : expr) {struct e}: Prop  :=
  match e with
  | (Bc _)         => True
  | (Ic _)         => True
  | (BV i)         => i < j_x
  | (FV _)         => True
  | (ExpUnOp _ e1)         => isLC_at j_x e1
  | (ExpBinOp _ e1 e2)         => isLC_at j_x e1 /\ isLC_at j_x e2
  | (ExpMethodInvoc e1 m e2)         => isLC_at j_x e1 /\ isLC_at j_x e2
  | (ExpFieldAccess e1 f) => isLC_at j_x e1
  | (ExpNew c es) => (fix f (es': [expr]) := match es' with | nil => True | e::es''=> isLC_at j_x e /\ (f es'') end) es
  | (ExpLet ex e')    => isLC_at j_x ex    /\ isLC_at (j_x+1) e'
  end

with isLCT_at (j_x : index) (t0 : type) {struct t0}: Prop :=
  match t0 with
  | (TRefn   b  rs) =>  match b with
                        | _       =>            isLCP_at (j_x+1) rs
                        end
  end

with isLCP_at (j_x : index) (ps0 : preds) {struct ps0}: Prop :=
  match ps0 with
  | PEmpty       => True
  | (PCons p ps) => isLC_at j_x p /\ isLCP_at j_x ps
  end.

Definition isLC  (e  : expr)  : Prop := isLC_at  0 e.

Definition isLCT (t  : type)  : Prop := isLCT_at 0 t.

Definition isLCP (ps : preds) : Prop := isLCP_at 0 ps.

Fixpoint open_at (j : index) (y : vname) (e : expr) {struct e} : expr :=
    match e with
    | (Bc b)             => Bc b
    | (Ic n)             => Ic n
    | (BV i)             => if j =? i then FV y else BV i
    | (FV x)             => FV x
    | (ExpUnOp op e')        => ExpUnOp op (open_at j y e')
    | (ExpBinOp op e1 e2)        => ExpBinOp op  (open_at j y e1)  (open_at j y e2)
    | (ExpMethodInvoc e1 m e2)        => ExpMethodInvoc (open_at j y e1) m (open_at j y e2)
    | (ExpFieldAccess e1 f) => ExpFieldAccess (open_at j y e1) f
    | (ExpNew c es) => ExpNew c ((fix f (es': [expr]) := match es' with | nil => nil | e::es''=> (open_at j y e) :: (f es'') end) es)
    | (ExpLet ex e')        => ExpLet   (open_at j y ex) (open_at (j+1) y e')
    end

with openT_at (j : index) (y : vname) (t0 : type)  {struct t0} : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (openP_at (j+1) y ps)
    end

with openP_at (j : index) (y : vname) (ps0 : preds)  {struct ps0} : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (open_at j y p) (openP_at j y ps)
    end.

Fixpoint open_many (l:[vname]) (e : expr)  : expr :=
  match l with
  | nil => e
  | v::l' => open_many l' (open_at ((length l) - 1) v e)
  end.

Definition unbind  (y : vname) (e : expr)   : expr  :=  open_at 0 y e.

Definition unbindT (y : vname) (t : type)   : type  :=  openT_at 0 y t.

Definition unbindP (y : vname) (ps : preds) : preds :=  openP_at 0 y ps.

Fixpoint subFV (x : vname) (v_x : expr) (e0 : expr) : expr :=
  match e0 with
  | (Bc b)                    => Bc b
  | (Ic n)                    => Ic n
  | (BV i)                    => BV i
  | (FV y)                    => if x =? y then v_x else FV y
  | (ExpUnOp op e)              => ExpUnOp op (subFV x v_x e)
  | (ExpBinOp op e e')                => ExpBinOp op (subFV x v_x e)  (subFV x v_x e')
  | (ExpMethodInvoc e m e')                => ExpMethodInvoc (subFV x v_x e) m (subFV x v_x e')
  | (ExpFieldAccess e1 f) => ExpFieldAccess (subFV x v_x e1) f
  | (ExpNew c es) => ExpNew c ((fix f (es': [expr]) := match es' with | nil => nil | e::es''=> (subFV x v_x e) :: (f es'') end) es)
  | (ExpLet   e1 e2)             => ExpLet   (subFV x v_x e1) (subFV x v_x e2)
  end

with tsubFV (x : vname) (v_x : expr) (t0 : type) : type :=
    match t0 with
    | (TRefn  b r)     => TRefn b   (psubFV x v_x r)
    end

with psubFV (x : vname) (v_x : expr) (ps0 : preds) : preds :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subFV x v_x p) (psubFV x v_x ps)
    end.

Fixpoint strengthen (qs : preds) (rs : preds) : preds :=
    match qs with
    | PEmpty       => rs
    | (PCons p ps) => PCons p (strengthen ps rs)
    end.

Fixpoint subBV_at (j : index) (v : expr)  (e : expr) {struct e} : expr :=
  match e with
  | (Bc b)             => Bc b
  | (Ic n)             => Ic n
  | (BV i)             => if j =? i then v else BV i
  | (FV x)             => FV x
  | (ExpUnOp op e)         => ExpUnOp op (subBV_at j v e)
  | (ExpBinOp op e e')         => ExpBinOp op (subBV_at j v e)  (subBV_at j v e')
  | (ExpMethodInvoc e m e')         => ExpMethodInvoc (subBV_at j v e) m (subBV_at j v e')
  | (ExpFieldAccess e1 f) => ExpFieldAccess (subBV_at j v e1) f
  | (ExpNew c es) => ExpNew c ((fix f (es': [expr]) := match es' with | nil => nil | e::es''=> (subBV_at j v e) :: (f es'') end) es)
  | (ExpLet ex e)         => ExpLet   (subBV_at j v ex) (subBV_at (j+1) v e)
  end
with tsubBV_at (j : index) (v_x : expr) (t0 : type)  {struct t0} : type :=
    match t0 with
    | (TRefn b ps)    => TRefn b (psubBV_at (j+1) v_x ps)
    end

with psubBV_at (j : index) (v_x : expr) (ps0 : preds)  {struct ps0} : preds  :=
    match ps0 with
    | PEmpty       => PEmpty
    | (PCons p ps) => PCons (subBV_at j v_x p) (psubBV_at j v_x ps)
    end.

Fixpoint subBV_many (l:[expr]) (e : expr)  : expr :=
  match l with
  | nil => e
  | v::l' => subBV_many l' (subBV_at ((length l) - 1) v e)
  end.

Fixpoint tsubBV_many (l:[expr]) (t : type)  : type :=
  match l with
  | nil => t
  | v::l' => tsubBV_many l' (tsubBV_at ((length l) - 1) v t)
  end.

Definition subBV  (v : expr) (e : expr)   : expr  :=  subBV_at 0 v e.

Definition tsubBV (v_x : expr) (t : type) : type  :=  tsubBV_at 0 v_x t.

Definition psubBV (v : expr) (ps : preds) : preds :=  psubBV_at 0 v ps.

Definition eqlPred2 e1 e2:= ExpBinOp (Eq) e1 e2.

Definition eqlPred (e : expr) :=  ExpBinOp (Eq) e (BV 0).

Fixpoint self (t0 : type) (e : expr) : type :=
  match t0 with
  | (TRefn b ps)      =>  TRefn b (PCons  (eqlPred e)  ps)
  end.

Inductive RefFieldDecl :=
| RefFDecl : type -> FieldName -> RefFieldDecl.

#[export] Instance RefFieldRef: Referable RefFieldDecl :={
  ref fdecl :=
    match fdecl with
    | RefFDecl _ fn => fn end
}.

Definition ReffieldType (f: RefFieldDecl): type :=
  match f with RefFDecl t _ => t end.

Definition ReffieldName (f: RefFieldDecl): FieldName :=
  match f with RefFDecl _ n => n end.

Inductive Argument :=
| Arg : vname -> Argument.

Inductive Assignment :=
  | Assgnmt : expr -> expr -> Assignment.

Inductive Constructor :=
  | KDecl : ClassName -> [RefFieldDecl] -> [vname] -> [Assignment] -> Constructor.

Inductive MethodDecl :=
| MDecl : type -> MethodName -> preds -> type -> MethodDecl.

#[export] Instance MDeclRef : Referable MethodDecl :={
  ref mdecl :=
    match mdecl with
   | MDecl _ var _ _ => var end
}.

Inductive MethodDefn :=
| MDefn : MethodDecl -> expr -> MethodDefn.

#[export] Instance MDefnRef : Referable MethodDefn :={
  ref mdecl :=
    match mdecl with
   | MDefn (MDecl _ var _ _) _ => var end
}.

Inductive RefClassDecl:=
| RefCDecl: ClassName -> ClassName -> [InterfaceName] ->
  forall (fDecls:[RefFieldDecl]), NoDup (refs fDecls) -> Constructor ->
  forall (mDefns:[MethodDefn]), NoDup (refs mDefns) -> RefClassDecl.

Inductive RefInterfaceDecl:=
| RefIDecl: InterfaceName ->
  forall (mDecls:[MethodDecl]), NoDup (refs mDecls) -> RefInterfaceDecl.

#[export] Instance RefCDeclRef : Referable RefClassDecl :={
  ref cdecl :=
    match cdecl with
    | RefCDecl var _ _ _ _ _ _ _ => var end
}.

#[export] Instance RefIDeclRef : Referable RefInterfaceDecl :={
  ref cdecl :=
    match cdecl with
   | RefIDecl var _ _ => var end
}.

Parameter Object: ClassName.

Parameter RefCT: [RefClassDecl].

Parameter RefIT: [RefInterfaceDecl].
