Require Import Relations Decidable.

Require Import RFJ.Lists.

Require Import RFJ.Utils.Referable.

Require Import Forall2.

Require Import ZArith.

Require Import Bool.

Require Export Definitions.Syntax.

Require Export Definitions.Names.

Inductive isCompat : UnOp -> expr -> Set :=
    | isCpt_Not  : forall b, isCompat Not (Bc b).

Inductive isCompat2 : BinOp -> expr -> expr -> Set :=
| isCpt_And  : forall b1 b2, isCompat2 And (Bc b1) (Bc b2)
| isCpt_Or   : forall b1 b2, isCompat2 Or  (Bc b1) (Bc b2)
| isCpt_Eq  : forall v1 v2, isValue v1 -> isValue v2 -> isCompat2 Eq v1 v2.

Fixpoint veq v1 v2 :=
    match v1, v2 with
    | (Ic n1), (Ic n2) => Z.eqb n1 n2
    | (Bc n1), (Bc n2) => Bool.eqb n1 n2
    | (ExpNew c1 es1), (ExpNew c2 es2) => andb (c1 =? c2) ((fix ff es1' es2' :=
                                                    match es1' with
                                                    | nil => (match es2' with | nil => true | e2:: es2'' => false end)
                                                    | e1 :: es1'' => (match es2' with | nil => false | e2:: es2'' => andb (veq e1 e2) (ff es1'' es2'') end)
                                                    end) es1 es2)
    | _, _ => false
    end.

Definition udelta (c : UnOp) (v : expr) (pf : isCompat c v) : expr :=
  match pf with
  | isCpt_Not b    => match b with
                      | true  => Bc false
                      | false => Bc true
                      end
  end.

Definition udelta' (c : UnOp) (v : expr) : option expr :=
  match v with
  |(Bc b) => match b with
            | true  => Some (Bc false)
            | false => Some (Bc true)
            end
  | _     => None
  end.

Definition bdelta (c : BinOp) (v1 : expr) (v2 : expr) (pf : isCompat2 c v1 v2) : expr :=
  match pf with
  | isCpt_And b1 b2   => Bc (andb b1 b2)
  | isCpt_Or b1 b2    => Bc (orb b1 b2)
  | isCpt_Eq v1 v2 p1 p2 => Bc (veq v1 v2)

  end.

Definition bdelta' (c : BinOp) (v1 : expr) (v2 : expr) : option expr :=
  match c, v1, v2 with
  | And      , (Bc b1), (Bc b2) => Some  (Bc (andb b1 b2))
  | Or       , (Bc b1), (Bc b2) => Some  (Bc (orb b1 b2))
  | Eq       , _, _             => Some (Bc (veq v1 v2))
  | _        , _, _         => None
  end.

Inductive Reffields : ClassName -> [RefFieldDecl] -> Prop :=
| RefF_Obj : Reffields Object nil
| RefF_Decl : forall C D Is fs  noDupfs K mds noDupMds fs',
    find C RefCT = Some (RefCDecl C D Is fs noDupfs K mds noDupMds) ->
    Reffields D fs' ->
    NoDup (refs (fs' ++ fs)) ->
    Reffields C (fs'++fs).

Reserved Notation "'mtype(' m ',' D ')' '=' ps '~>' c '~>' c0" (at level 40, c at next level).

Inductive m_type: MethodName -> ClassName -> preds -> type -> type -> Prop:=
  | mty_ok : forall C D Is m ps rt t e Fs K Ms noDupfs noDupMds,
              find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds)->
              find m Ms = Some (MDefn (MDecl rt m ps t) e) ->
              mtype(m, C) = ps ~> t ~> rt
  | mty_no_override: forall ps C D Is m rt t Fs K Ms noDupfs noDupMds,
              find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) ->
              find m Ms = None ->
              mtype(m, D) = ps ~> t ~> rt ->
              mtype(m, C) = ps ~> t ~> rt
  where "'mtype(' m ',' D ')' '=' ps '~>' cs '~>' c0"
        := (m_type m D ps cs c0).

Reserved Notation "'mtypei(' m ',' I ')' '=' ps '~>' c '~>' c0" (at level 40, c at next level).

Inductive m_type_i: MethodName -> InterfaceName -> preds -> type -> type -> Prop:=
| mty_ok_i : forall I Ms m rt t ps noDupMds,
            find I RefIT = Some (RefIDecl I Ms noDupMds)->
            find m Ms = Some (MDecl rt m ps t) ->
            mtypei(m, I) = ps ~> t ~> rt
where "'mtypei(' m ',' I ')' '=' ps '~>' cs '~>' c0"
      := (m_type_i m I ps cs c0).

Inductive m_body: MethodName -> ClassName -> expr -> Prop:=
  | mbdy_ok : forall C D Is m ps rt t e Fs K Ms noDupfs noDupMds,
              find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds)->
              find m Ms = Some (MDefn (MDecl rt m ps t) e) ->
              m_body m C e
  | mbdy_no_override: forall C D Is m e Fs K Ms noDupfs noDupMds,
              find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds)->
              find m Ms = None ->
              m_body m D e ->
              m_body m C e.

Notation "'mbody(' m ',' D ')' '=' e" := (m_body m D e) (at level 40).

Reserved Notation "e '~~>' e1" (at level 60).

Inductive Step : expr -> expr -> Prop :=
| EUnOp1 : forall (c:UnOp) (e e': expr) ,
      Step e e' -> Step (ExpUnOp c e) (ExpUnOp c e')
| EUnOp2 : forall (c:UnOp) (w : expr) (pf : isCompat c w),
      isValue w -> Step (ExpUnOp c w) (udelta c w pf)
| EBinOp1 : forall (c:BinOp) (e e' e1 : expr),
      Step e e' -> Step (ExpBinOp c e e1) (ExpBinOp c e' e1)
| EBinOp2 : forall (c:BinOp) (e e' v : expr),
      isValue v -> Step e e' -> Step (ExpBinOp c v e) (ExpBinOp c v e')
| EBinOp3 : forall (c:BinOp) (v1 v2: expr) (pf : isCompat2 c v1 v2),
      isValue v1 -> isValue v2 -> Step (ExpBinOp c v1 v2) (bdelta c v1 v2 pf)
| Refc_Invok1: forall m e1 e2 e1',
      e1 ~~> e1' ->
      ExpMethodInvoc e1 m e2 ~~> ExpMethodInvoc e1' m e2
| Refc_Invok2: forall m v e e',
    isValue v -> e ~~> e' ->
    ExpMethodInvoc v m e ~~> ExpMethodInvoc v m e'
| Refc_Invok3: forall C e m v es,
    mbody(m, C) = e -> isValue v -> isValue (ExpNew C es) ->
    ExpMethodInvoc (ExpNew C es) m v ~~> (subBV_at 1 (ExpNew C es) (subBV v e))
| Refc_Field : forall C Fs es fi ei i,
      Reffields C Fs ->
      nth_error Fs i = Some fi ->
      nth_error es i = Some ei->
      isValue (ExpNew C es) ->
      ExpFieldAccess (ExpNew C es) (ref fi) ~~> ei
| RefRC_Field : forall e0 e0' f,
      e0 ~~> e0' ->
      ExpFieldAccess e0 f ~~> ExpFieldAccess e0' f
| RefRC_New_Arg : forall C ei' es es' ei i,
      Step ei ei' ->
      nth_error es i = Some ei ->
      nth_error es' i = Some ei' ->
      (forall j, j <> i -> nth_error es j = nth_error es' j) ->
      length es = length es' ->
      ExpNew C es ~~> ExpNew C es'
| ELet  : forall (e_x e_x' e : expr),
      Step e_x e_x' -> Step (ExpLet e_x e) (ExpLet e_x' e)
| ELetV : forall (v : expr) (e : expr),
      isValue v -> Step (ExpLet v e) (subBV v e)
  where "e '~~>' e1" := (Step e e1).

Inductive EvalsTo : expr -> expr -> Prop :=
  | Refl     : forall (e : expr),  EvalsTo e e
  | AddStep  : forall (e1 e2 e3 : expr),
        Step e1 e2 -> EvalsTo e2 e3 -> EvalsTo e1 e3.
