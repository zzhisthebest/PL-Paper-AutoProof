Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.

Require Import Stdlib.Init.Sumbool.

Require Import Coq.Program.Equality.

Module Usage.

Parameter usage : Set.

Parameter Irr : usage.

Parameter Lin : usage.

Parameter qeqb  : usage -> usage -> bool.

Parameter qleb  : usage -> usage -> bool.

Parameter qplus : usage -> usage -> usage.

Parameter qmul  : usage -> usage -> usage.

Definition t := usage.

Definition eq := @Logic.eq usage.

Definition eqb  := qeqb.

Parameter q_eq_dec : forall (A : usage) (B : usage), { A = B } + { not (A = B) }.

Instance equ  : @EqDec_eq usage := q_eq_dec.

Parameter eqb_eq : forall (n m : usage), qeqb n m = true <-> n = m.

Definition eq_equiv : Equivalence (@Logic.eq usage) := eq_equivalence.

Definition eq_dec := q_eq_dec.

Include BackportEq.

Definition size_usage : usage -> nat := fun _ => 1%nat.

Declare Scope usage_scope.

Bind Scope usage_scope with usage.

Local Open Scope usage_scope.

Infix "=?" := qeqb (at level 70) : usage_scope.

Infix "<=?" := qleb (at level 70) : usage_scope.

Notation "q1 <= q2" := (is_true (qleb q1 q2)) (at level 70)  : usage_scope.

Notation "0" := Irr : usage_scope.

Notation "1" := Lin : usage_scope.

Notation "x + y"  := (qplus x y) : usage_scope.

Notation "x * y " := (qmul x y)  : usage_scope.

Parameter qplus_0_l : forall x, 0 + x = x.

Parameter qmul_0_l : forall x, 0 * x = 0.

Parameter qplus_comm : forall (n m : usage), n + m = m + n.

Parameter qplus_assoc : forall (n m p : usage), n + (m + p) = (n + m) + p.

Parameter qmul_1_l : forall n, 1*n = n.

Parameter qmul_assoc : forall n m p, n*(m*p) = (n*m)*p.

Parameter distr_l : forall n m p, (n + m)*p = n*p + m*p.

Parameter qmul_0_r : forall x, x * 0 = 0.

Parameter qmul_1_r : forall n, n*1 = n.

Parameter distr_r : forall n m p, p * (n + m) = p * n + p * m.

Definition leb  := qleb.

Definition le n m := is_true (qleb n m).

Parameter leb_le : forall (n m : usage), (n <=? m) = true <-> n <= m.

Parameter qleb_refl : forall n, is_true (n <=? n).

Parameter qleb_trans: forall m n p, is_true (n <=? m) -> is_true (m <=? p) -> is_true (n <=? p).

Parameter po_semiring1 : forall a b c , a <= b -> a + c <= b + c.

Parameter po_semiring2 : forall a b c , a <= b -> a * c <= b * c.

Parameter po_semiring3 : forall a b c , a <= b -> c * a <= c * b.

End Usage.

Export Usage.

Section UsageCtx.

Variables A : Type.

Local Open Scope usage_scope.

Definition sort_mul (q: usage) (s : usage * A) : usage * A :=
  match s with
  | (q1 , A) => (qmul q q1, A)
  end.

Definition ctx_mul (q : usage) G :=
  map (sort_mul q) G.

Definition add_usage (q : usage) (D: list (var * A)) : list (var * (usage * A)) :=
  map (fun x => (q, x)) D.

Definition ungrade (G: list (var * (usage * A))) : list (var * A) :=
  map snd G.

Fixpoint ctx_plus (G1 G2 : list (var * (usage * A))) : list (var * (usage * A)) :=
  match G1, G2 with
  | nil , nil => nil
  | cons (x , (q1 , A)) G1' , cons (_, (q2, _)) G2' => cons (x, (q1 + q2, A)) (ctx_plus G1' G2')
  | _ , _ => nil
  end.

Inductive ctx : list (atom * A) -> list (atom * (usage * A)) -> Prop :=
 | ctx_nil :
     ctx nil nil
 | ctx_cons : forall D (x:atom) G (q:usage) a,
     ctx D G ->
      ~ AtomSetImpl.In x (dom  D)  ->
     ctx (x ~ a ++ D ) (x ~ (q,a) ++ G).

Inductive ctx_sub : list (atom * A) -> list (atom * (usage * A))-> list (atom * (usage * A)) -> Prop :=
 | CS_Empty :  ctx_sub  nil   nil   nil
 | CS_ConsTm : forall D (x:atom) (a:A) G1 (q1:usage) G2 q2,
     ( q1  <=  q2 )  ->
     ctx_sub D G1 G2 ->
      ~ AtomSetImpl.In  x  (dom  D)  ->
     ctx_sub (x ~ a ++ D) (x ~ (q1 ,a) ++ G1) (x ~ (q2,a) ++ G2).

End UsageCtx.

Section UsageList.

Local Open Scope usage_scope.

Fixpoint oplus (G1 G2 : list usage) : list usage :=
  match G1, G2 with
  | nil , nil => nil
  | cons q1  G1' , cons q2 G2' => cons (q1 + q2) (oplus G1' G2')
  | _ , _ => nil
  end.

Definition ozero {A} (G : list A) : list usage :=
  List.map (fun _ => 0) G.

Definition Qs {A} (h : list (atom * (usage * A))) : list usage :=
  List.map (fun x => match x with | (_,(u, _)) => u end) h.

End UsageList.

Arguments sort_mul {_}.

Arguments ctx_mul {_}.

Arguments ctx_plus {_}.

Arguments ctx {_}.

Arguments ctx_sub {_}.

Arguments add_usage {_}.

Arguments ungrade {_}.
