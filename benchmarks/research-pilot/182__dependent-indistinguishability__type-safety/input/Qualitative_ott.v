Require Import Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export Qual.grade_sig.

Require Export Qual.sort_sig.

From mathcomp Require Import ssreflect ssrbool.

Local Open Scope order_scope.

Local Close Scope bool_scope.

Definition tmvar : Set := var.

Definition qualityvar : Set := atom.

Inductive tm : Type :=
 | a_TyUnit : tm
 | a_TmUnit : tm
 | a_Pi (psi:grade) (A:tm) (B:tm)
 | a_Abs (psi:grade) (A:tm) (a:tm)
 | a_App (a:tm) (psi:grade) (b:tm)
 | a_Type (s:sort)
 | a_Var_b (_:nat)
 | a_Var_f (x:tmvar)
 | a_CEq (psi:grade) (a:tm) (b:tm) (psi0:grade) (A:tm)
 | a_Refl : tm
 | a_Transp (a:tm) (b:tm)
 | a_T (psi:grade) (A:tm)
 | a_Box (psi:grade) (a:tm)
 | a_Unbox (psi:grade) (a:tm)
 | a_SSigma (psi:grade) (A:tm) (B:tm)
 | a_SPair (a:tm) (psi:grade) (b:tm)
 | a_Proj1 (psi:grade) (a:tm)
 | a_Proj2 (psi:grade) (a:tm)
 | a_Bool : tm
 | a_True : tm
 | a_False : tm
 | a_If (a:tm) (b0:tm) (b1:tm).

Definition econtext : Type := list ( atom * grade ).

Inductive headform : Type :=
 | h_Abs : headform
 | h_Pi (psi:grade)
 | h_Type (s:sort)
 | h_CEq (psi:grade) (psi0:grade)
 | h_Refl : headform
 | h_T (psi:grade)
 | h_Box (psi:grade)
 | h_SSigma (psi:grade)
 | h_SPair : headform
 | h_TyUnit : headform
 | h_TmUnit : headform
 | h_Bool : headform
 | h_True : headform
 | h_False : headform.

Definition context : Type := list ( atom * (grade * tm) ).

Fixpoint open_tm_wrt_tm_rec (k:nat) (a5:tm) (a_6:tm) {struct a_6}: tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit
  | a_TmUnit => a_TmUnit
  | (a_Pi psi A B) => a_Pi psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_Abs psi A a) => a_Abs psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 a)
  | (a_App a psi b) => a_App (open_tm_wrt_tm_rec k a5 a) psi (open_tm_wrt_tm_rec k a5 b)
  | (a_Type s) => a_Type s
  | (a_Var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => a5
        | inright _ => a_Var_b (nat - 1)
      end
  | (a_Var_f x) => a_Var_f x
  | (a_CEq psi a b psi0 A) => a_CEq psi (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) psi0 (open_tm_wrt_tm_rec k a5 A)
  | a_Refl => a_Refl
  | (a_Transp a b) => a_Transp (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
  | (a_T psi A) => a_T psi (open_tm_wrt_tm_rec k a5 A)
  | (a_Box psi a) => a_Box psi (open_tm_wrt_tm_rec k a5 a)
  | (a_Unbox psi a) => a_Unbox psi (open_tm_wrt_tm_rec k a5 a)
  | (a_SSigma psi A B) => a_SSigma psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_SPair a psi b) => a_SPair (open_tm_wrt_tm_rec k a5 a) psi (open_tm_wrt_tm_rec k a5 b)
  | (a_Proj1 psi a) => a_Proj1 psi (open_tm_wrt_tm_rec k a5 a)
  | (a_Proj2 psi a) => a_Proj2 psi (open_tm_wrt_tm_rec k a5 a)
  | a_Bool => a_Bool
  | a_True => a_True
  | a_False => a_False
  | (a_If a b0 b1) => a_If (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b0) (open_tm_wrt_tm_rec k a5 b1)
end.

Definition open_tm_wrt_tm a5 a_6 := open_tm_wrt_tm_rec 0 a_6 a5.

Fixpoint close_tm_wrt_tm_rec (k:nat) (a5:var) (a_6:tm) {struct a_6}: tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit
  | a_TmUnit => a_TmUnit
  | (a_Pi psi A B) => a_Pi psi (close_tm_wrt_tm_rec k a5 A) (close_tm_wrt_tm_rec (S k) a5 B)
  | (a_Abs psi A a) => a_Abs psi (close_tm_wrt_tm_rec k a5 A) (close_tm_wrt_tm_rec (S k) a5 a)
  | (a_App a psi b) => a_App (close_tm_wrt_tm_rec k a5 a) psi (close_tm_wrt_tm_rec k a5 b)
  | (a_Type s) => a_Type s
  | (a_Var_b nat) =>
       if (lt_dec nat k)
         then a_Var_b nat
         else a_Var_b (S nat)
  | (a_Var_f x) => if (a5 === x) then (a_Var_b k) else (a_Var_f x)
  | (a_CEq psi a b psi0 A) => a_CEq psi (close_tm_wrt_tm_rec k a5 a) (close_tm_wrt_tm_rec k a5 b) psi0 (close_tm_wrt_tm_rec k a5 A)
  | a_Refl => a_Refl
  | (a_Transp a b) => a_Transp (close_tm_wrt_tm_rec k a5 a) (close_tm_wrt_tm_rec k a5 b)
  | (a_T psi A) => a_T psi (close_tm_wrt_tm_rec k a5 A)
  | (a_Box psi a) => a_Box psi (close_tm_wrt_tm_rec k a5 a)
  | (a_Unbox psi a) => a_Unbox psi (close_tm_wrt_tm_rec k a5 a)
  | (a_SSigma psi A B) => a_SSigma psi (close_tm_wrt_tm_rec k a5 A) (close_tm_wrt_tm_rec (S k) a5 B)
  | (a_SPair a psi b) => a_SPair (close_tm_wrt_tm_rec k a5 a) psi (close_tm_wrt_tm_rec k a5 b)
  | (a_Proj1 psi a) => a_Proj1 psi (close_tm_wrt_tm_rec k a5 a)
  | (a_Proj2 psi a) => a_Proj2 psi (close_tm_wrt_tm_rec k a5 a)
  | a_Bool => a_Bool
  | a_True => a_True
  | a_False => a_False
  | (a_If a b0 b1) => a_If (close_tm_wrt_tm_rec k a5 a) (close_tm_wrt_tm_rec k a5 b0) (close_tm_wrt_tm_rec k a5 b1)
end.

Definition close_tm_wrt_tm a_6 a5 := close_tm_wrt_tm_rec 0 a_6 a5.

Inductive lc_tm : tm -> Prop :=
 | lc_a_TyUnit :
     (lc_tm a_TyUnit)
 | lc_a_TmUnit :
     (lc_tm a_TmUnit)
 | lc_a_Pi : forall (psi:grade) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi psi A B))
 | lc_a_Abs : forall (psi:grade) (A a:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     (lc_tm (a_Abs psi A a))
 | lc_a_App : forall (a:tm) (psi:grade) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a psi b))
 | lc_a_Type : forall (s:sort),
     (lc_tm (a_Type s))
 | lc_a_Var_f : forall (x:tmvar),
     (lc_tm (a_Var_f x))
 | lc_a_CEq : forall (psi:grade) (a b:tm) (psi0:grade) (A:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm A) ->
     (lc_tm (a_CEq psi a b psi0 A))
 | lc_a_Refl :
     (lc_tm a_Refl)
 | lc_a_Transp : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_Transp a b))
 | lc_a_T : forall (psi:grade) (A:tm),
     (lc_tm A) ->
     (lc_tm (a_T psi A))
 | lc_a_Box : forall (psi:grade) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Box psi a))
 | lc_a_Unbox : forall (psi:grade) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Unbox psi a))
 | lc_a_SSigma : forall (psi:grade) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_SSigma psi A B))
 | lc_a_SPair : forall (a:tm) (psi:grade) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_SPair a psi b))
 | lc_a_Proj1 : forall (psi:grade) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Proj1 psi a))
 | lc_a_Proj2 : forall (psi:grade) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Proj2 psi a))
 | lc_a_Bool :
     (lc_tm a_Bool)
 | lc_a_True :
     (lc_tm a_True)
 | lc_a_False :
     (lc_tm a_False)
 | lc_a_If : forall (a b0 b1:tm),
     (lc_tm a) ->
     (lc_tm b0) ->
     (lc_tm b1) ->
     (lc_tm (a_If a b0 b1)).

Fixpoint fv_tm (a5:tm) : vars :=
  match a5 with
  | a_TyUnit => {}
  | a_TmUnit => {}
  | (a_Pi psi A B) => (fv_tm A) \u (fv_tm B)
  | (a_Abs psi A a) => (fv_tm A) \u (fv_tm a)
  | (a_App a psi b) => (fv_tm a) \u (fv_tm b)
  | (a_Type s) => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_CEq psi a b psi0 A) => (fv_tm a) \u (fv_tm b) \u (fv_tm A)
  | a_Refl => {}
  | (a_Transp a b) => (fv_tm a) \u (fv_tm b)
  | (a_T psi A) => (fv_tm A)
  | (a_Box psi a) => (fv_tm a)
  | (a_Unbox psi a) => (fv_tm a)
  | (a_SSigma psi A B) => (fv_tm A) \u (fv_tm B)
  | (a_SPair a psi b) => (fv_tm a) \u (fv_tm b)
  | (a_Proj1 psi a) => (fv_tm a)
  | (a_Proj2 psi a) => (fv_tm a)
  | a_Bool => {}
  | a_True => {}
  | a_False => {}
  | (a_If a b0 b1) => (fv_tm a) \u (fv_tm b0) \u (fv_tm b1)
end.

Fixpoint subst_tm (a5:tm) (x5:tmvar) (a_6:tm) {struct a_6} : tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit
  | a_TmUnit => a_TmUnit
  | (a_Pi psi A B) => a_Pi psi (subst_tm a5 x5 A) (subst_tm a5 x5 B)
  | (a_Abs psi A a) => a_Abs psi (subst_tm a5 x5 A) (subst_tm a5 x5 a)
  | (a_App a psi b) => a_App (subst_tm a5 x5 a) psi (subst_tm a5 x5 b)
  | (a_Type s) => a_Type s
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => (if eq_var x x5 then a5 else (a_Var_f x))
  | (a_CEq psi a b psi0 A) => a_CEq psi (subst_tm a5 x5 a) (subst_tm a5 x5 b) psi0 (subst_tm a5 x5 A)
  | a_Refl => a_Refl
  | (a_Transp a b) => a_Transp (subst_tm a5 x5 a) (subst_tm a5 x5 b)
  | (a_T psi A) => a_T psi (subst_tm a5 x5 A)
  | (a_Box psi a) => a_Box psi (subst_tm a5 x5 a)
  | (a_Unbox psi a) => a_Unbox psi (subst_tm a5 x5 a)
  | (a_SSigma psi A B) => a_SSigma psi (subst_tm a5 x5 A) (subst_tm a5 x5 B)
  | (a_SPair a psi b) => a_SPair (subst_tm a5 x5 a) psi (subst_tm a5 x5 b)
  | (a_Proj1 psi a) => a_Proj1 psi (subst_tm a5 x5 a)
  | (a_Proj2 psi a) => a_Proj2 psi (subst_tm a5 x5 a)
  | a_Bool => a_Bool
  | a_True => a_True
  | a_False => a_False
  | (a_If a b0 b1) => a_If (subst_tm a5 x5 a) (subst_tm a5 x5 b0) (subst_tm a5 x5 b1)
end.

Definition labels : context -> econtext :=
  map (fun '(u , s) => u).

Definition subst_ctx (a : tm) (x:var) : context -> context :=
  map (fun '(g, A) => (g, (subst_tm a x A))).

Definition tm_to_headform (a : tm) : option headform :=
  match a with
  | a_Abs _ _ _ => Some h_Abs
  | a_Pi psi _ _ => Some (h_Pi psi)
  | a_Type s => Some (h_Type s)
  | a_CEq psi _ _ psi0 _ => Some (h_CEq psi psi0)
  | a_Refl => Some h_Refl
  | a_Box psi _ => Some (h_Box psi)
  | a_T psi _ => Some (h_T psi)
  | a_SPair _ _ _ => Some h_SPair
  | a_SSigma psi _ _ => Some (h_SSigma psi)
  | a_TyUnit => Some h_TyUnit
  | a_TmUnit => Some h_TmUnit
  | a_Bool => Some h_Bool
  | a_True => Some h_True
  | a_False => Some h_False
  | _ => None
  end.

Definition Consistent (a b : tm) : Prop :=
  match tm_to_headform a, tm_to_headform b with
  | Some h1, Some h2 => h1 = h2
  | _, _ => True
  end.

Definition Value (a : tm) : bool :=
  match a with
  | a_SPair _ _ _ => true
  | a_SSigma _ _ _ => true
  | a_Pi _ _ _ => true
  | a_Abs _ _ _ => true
  | a_Type _ => true
  | a_CEq _ _ _ _ _ => true
  | a_Refl => true
  | a_Box psi _ => true
  | a_T psi _ => true
  | a_TyUnit => true
  | a_TmUnit => true
  | a_Bool => true
  | a_True => true
  | a_False => true
  | _ => false
  end.

Inductive P_sub : econtext -> econtext -> Prop :=
 | P_Empty :
     P_sub  nil   nil
 | P_Cons : forall (P1:econtext) (x:tmvar) (psi1:grade) (P2:econtext) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     P_sub P1 P2 ->
      ~ AtomSetImpl.In  x  (dom  P1 )  ->
      ~ AtomSetImpl.In  x  (dom  P2 )  ->
     P_sub  (  ( x ~ psi1 )  ++ P1 )   (  ( x ~ psi2 )  ++ P2 ) .

Inductive P_meet : econtext -> econtext -> econtext -> Prop :=
 | PM_Empty :
     P_meet  nil   nil   nil
 | PM_Cons : forall (P1:econtext) (x:tmvar) (psi1:grade) (P2:econtext) (psi2:grade) (P3:econtext),
     P_meet P1 P2 P3 ->
     P_meet  (  (  ( x ~ psi1 )  ++ P1 )  )   (  (  ( x ~ psi2 )  ++ P2 )  )   (  (  ( x ~  ( psi1  `&`  psi2 )  )  ++ P3 )  ) .

Inductive ctx_sub : context -> context -> Prop :=
 | CS_Empty :
     ctx_sub  nil   nil
 | CS_ConsTm : forall (W1:context) (x:tmvar) (psi1:grade) (A:tm) (W2:context) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     ctx_sub W1 W2 ->
      ~ AtomSetImpl.In  x  (dom  W1 )  ->
      ~ AtomSetImpl.In  x  (dom  W2 )  ->
     ctx_sub  (  ( x ~( psi1 , A ))  ++ W1 )   (  ( x ~( psi2 , A ))  ++ W2 ) .

Inductive GDefEq : econtext -> grade -> tm -> tm -> Prop :=
 | GE_Var : forall (P:econtext) (psi:grade) (x:tmvar) (psi0:grade),
      uniq  P  ->
      ( psi0  <=  psi )  ->
      binds  x   psi0   P  ->
     GDefEq P psi (a_Var_f x) (a_Var_f x)
 | GE_Type : forall (P:econtext) (psi:grade) (s:sort),
      uniq  P  ->
     GDefEq P psi (a_Type s) (a_Type s)
 | GE_Sym : forall (P:econtext) (psi:grade) (b a:tm),
     GDefEq P psi a b ->
     GDefEq P psi b a
 | GE_Trans : forall (P:econtext) (psi:grade) (a b b0:tm),
     GDefEq P psi a b0 ->
     GDefEq P psi b0 b ->
     GDefEq P psi a b
 | GE_App : forall (P:econtext) (psi:grade) (b0:tm) (psi0:grade) (a0 b1 a1:tm),
     GDefEq P psi b0 b1 ->
     CGDefEq P psi psi0 a0 a1 ->
     GDefEq P psi (a_App b0 psi0 a0) (a_App b1 psi0 a1)
 | GE_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (A0 b0 A1 b1:tm),
     lc_tm A0 ->
     lc_tm A1 ->
      ( forall x , x \notin  L  -> GDefEq  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b0 (a_Var_f x) )   ( open_tm_wrt_tm b1 (a_Var_f x) )  )  ->
     GDefEq P psi (a_Abs psi0 A0 b0) (a_Abs psi0 A1 b1)
 | GE_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A0 B0 A1 B1:tm),
     GDefEq P psi A0 A1 ->
      ( forall x , x \notin  L  -> GDefEq  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm B0 (a_Var_f x) )   ( open_tm_wrt_tm B1 (a_Var_f x) )  )  ->
     GDefEq P psi (a_Pi psi0 A0 B0) (a_Pi psi0 A1 B1)
 | GE_AppAbs : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b0 a0 b1 A:tm),
     GDefEq P psi a (a_Abs psi0 A a0) ->
     CGDefEq P psi psi0 b0 b1 ->
     GDefEq P psi (a_App a psi0 b0)  (open_tm_wrt_tm  a0   b1 )
 | GE_Refl : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GDefEq P psi a_Refl a_Refl
 | GE_Transp : forall (P:econtext) (psi:grade) (a0 b0 a1 b1:tm),
     GDefEq P psi a0 a1 ->
     GDefEq P psi b0 b1 ->
     GDefEq P psi (a_Transp a0 b0) (a_Transp a1 b1)
 | GE_CEq : forall (P:econtext) (psi psi0:grade) (a0 b0:tm) (psi1:grade) (A0 a1 b1 A1:tm),
     lc_tm A0 ->
     lc_tm A1 ->
     GDefEq P psi a0 a1 ->
     GDefEq P psi b0 b1 ->
      ( psi0  <=  psi )  ->
     GDefEq P psi (a_CEq psi0 a0 b0 psi1 A0) (a_CEq psi0 a1 b1 psi1 A1)
 | GE_TranspRefl : forall (P:econtext) (psi:grade) (a0 b0 b1:tm),
     GDefEq P psi a0 a_Refl ->
     GDefEq P psi b0 b1 ->
     GDefEq P psi (a_Transp a0 b0) b1
 | GE_T : forall (P:econtext) (psi psi0:grade) (A B:tm),
     GDefEq P psi A B ->
     GDefEq P psi (a_T psi0 A) (a_T psi0 B)
 | GE_Box : forall (P:econtext) (psi psi0:grade) (a b:tm),
     CGDefEq P psi psi0 a b ->
     GDefEq P psi (a_Box psi0 a) (a_Box psi0 b)
 | GE_Unbox : forall (P:econtext) (psi psi0:grade) (a b:tm),
     GDefEq P psi a b ->
      ( psi0  <=  psi )  ->
     GDefEq P psi (a_Unbox psi0 a) (a_Unbox psi0 b)
 | GE_UnboxBox : forall (P:econtext) (psi psi0:grade) (a b:tm),
     GDefEq P psi a (a_Box psi0 b) ->
      ( psi0  <=  psi )  ->
     GDefEq P psi (a_Unbox psi0 a) b
 | GE_Proj1Cong : forall (P:econtext) (psi psi0:grade) (a0 a1:tm),
     GDefEq P psi a0 a1 ->
      ( psi0  <=  psi )  ->
     GDefEq P psi (a_Proj1 psi0 a0) (a_Proj1 psi0 a1)
 | GE_Proj2Cong : forall (P:econtext) (psi psi0:grade) (a0 a1:tm),
     GDefEq P psi a0 a1 ->
     GDefEq P psi (a_Proj2 psi0 a0) (a_Proj2 psi0 a1)
 | GE_Proj1Beta : forall (P:econtext) (psi psi0:grade) (b a1 a2:tm),
     GDefEq P psi b (a_SPair a1 psi0 a2) ->
      ( psi0  <=  psi )  ->
     GDefEq P psi (a_Proj1 psi0 b) a1
 | GE_Proj2Beta : forall (P:econtext) (psi psi0:grade) (b a2 a1:tm),
     GDefEq P psi b (a_SPair a1 psi0 a2) ->
     GDefEq P psi (a_Proj2 psi0 b) a2
 | GE_SPair : forall (P:econtext) (psi:grade) (a0:tm) (psi0:grade) (b0 a1 b1:tm),
     CGDefEq P psi psi0 a0 a1 ->
     GDefEq P psi b0 b1 ->
     GDefEq P psi (a_SPair a0 psi0 b0) (a_SPair a1 psi0 b1)
 | GE_SSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A0 B0 A1 B1:tm),
     GDefEq P psi A0 A1 ->
      ( forall x , x \notin  L  -> GDefEq  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm B0 (a_Var_f x) )   ( open_tm_wrt_tm B1 (a_Var_f x) )  )  ->
     GDefEq P psi (a_SSigma psi0 A0 B0) (a_SSigma psi0 A1 B1)
 | GE_TyUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GDefEq P psi a_TyUnit a_TyUnit
 | GE_TmUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GDefEq P psi a_TmUnit a_TmUnit
 | GE_Bool : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GDefEq P psi a_Bool a_Bool
 | GE_True : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GDefEq P psi a_True a_True
 | GE_False : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GDefEq P psi a_False a_False
 | GE_If : forall (P:econtext) (psi:grade) (a0 b0 b1 a1 b2 b3:tm),
     GDefEq P psi a0 a1 ->
     GDefEq P psi b0 b2 ->
     GDefEq P psi b1 b3 ->
     GDefEq P psi (a_If a0 b0 b1) (a_If a1 b2 b3)
 | GE_IfTrue : forall (P:econtext) (psi:grade) (a0 b0 b1 b2 b3:tm),
     GDefEq P psi a0 a_True ->
     GDefEq P psi b0 b2 ->
     GDefEq P psi b1 b3 ->
     GDefEq P psi (a_If a0 b0 b1) b2
 | GE_IfFalse : forall (P:econtext) (psi:grade) (a0 b0 b1 b3 b2:tm),
     GDefEq P psi a0 a_False ->
     GDefEq P psi b0 b2 ->
     GDefEq P psi b1 b3 ->
     GDefEq P psi (a_If a0 b0 b1) b3
with CGDefEq : econtext -> grade -> grade -> tm -> tm -> Prop :=
 | CGE_Leq : forall (P:econtext) (psi psi0:grade) (a b:tm),
      ( psi0  <=  psi )  ->
     GDefEq P psi a b ->
     CGDefEq P psi psi0 a b
 | CGE_NLeq : forall (P:econtext) (psi psi0:grade) (a b:tm),
     lc_tm a ->
     lc_tm b ->
      not ( psi0  <=  psi )  ->
      uniq  P  ->
     CGDefEq P psi psi0 a b.

Inductive DefEq : econtext -> tm -> tm -> Prop :=
 | E_One : forall (P:econtext) (a b:tm) (psi:grade),
     GDefEq P psi a b ->
     DefEq P a b
 | E_Trans : forall (P:econtext) (a b b0:tm),
     DefEq P a b0 ->
     DefEq P b0 b ->
     DefEq P a b.

Inductive Ctx : context -> Prop :=
 | Ctx_Empty :
     Ctx  nil
 | Ctx_Cons : forall (W:context) (x:tmvar) (psi0:grade) (A:tm) (psi:grade) (s:sort),
     Ctx W ->
     Typing W psi A (a_Type s) ->
      ~ AtomSetImpl.In  x  (dom  W )  ->
     Ctx  (  ( x ~( psi0 , A ))  ++ W )
with Typing : context -> grade -> tm -> tm -> Prop :=
 | T_Type : forall (W:context) (psi:grade) (s1 s2:sort),
     Ctx W ->
      axiom  s1   s2  ->
     Typing W psi (a_Type s1) (a_Type s2)
 | T_Var : forall (W:context) (psi:grade) (x:tmvar) (A:tm) (psi0:grade),
     Ctx W ->
      ( psi0  <=  psi )  ->
      binds  x  ( psi0 ,  A )  W  ->
     Typing W psi (a_Var_f x) A
 | T_Pi : forall (L:vars) (W:context) (psi psi0:grade) (A B:tm) (s3 s1 s2:sort),
     Typing W psi A (a_Type s1) ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~( psi0 , A ))  ++ W )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  (a_Type s2) )  ->
      rule_pi  s1   s2   s3  ->
     Typing W psi (a_Pi psi0 A B) (a_Type s3)
 | T_Abs : forall (L:vars) (W:context) (psi psi0:grade) (A b B:tm) (psi1:grade) (s:sort),
      ( forall x , x \notin  L  -> Typing  (  ( x ~( psi0 , A ))  ++ W )  psi  ( open_tm_wrt_tm b (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Typing W psi1  ( (a_Pi psi0 A B) )  (a_Type s) ->
     Typing W psi (a_Abs psi0 A b) (a_Pi psi0 A B)
 | T_App : forall (W:context) (psi:grade) (b:tm) (psi0:grade) (a B A:tm),
     Typing W psi b (a_Pi psi0 A B) ->
     Typing W psi0 a A ->
     Typing W psi (a_App b psi0 a)  (open_tm_wrt_tm  B   a )
 | T_Conv : forall (W:context) (psi:grade) (a B A:tm) (psi0:grade) (s:sort),
     Typing W psi a A ->
     Typing W psi0 B (a_Type s) ->
     DefEq  (labels  W )  A B ->
     Typing W psi a B
 | T_Refl : forall (W:context) (psi psi0:grade) (a:tm) (psi1:grade) (A:tm) (psi2:grade) (s:sort),
     Typing W psi2  (a_CEq psi0 a a psi1 A)  (a_Type s) ->
     Typing W psi a_Refl  (a_CEq psi0 a a psi1 A)
 | T_CEq : forall (W:context) (psi psi0:grade) (a b:tm) (psi1:grade) (A:tm) (s2:sort) (psi2:grade) (s1:sort),
     Typing W psi1 a A ->
     Typing W psi1 b A ->
     Typing W psi2 A (a_Type s1) ->
      rule_eq  s1   s2  ->
      ( psi1  <=  psi0 )  ->
      ( psi0  <=  psi )  ->
     Typing W psi  (a_CEq psi0 a b psi1 A)  (a_Type s2)
 | T_Transp : forall (L:vars) (W:context) (psi:grade) (a b B a1:tm) (psi0:grade) (A:tm) (psi1:grade) (s:sort) (a0:tm) (psi2:grade) (s1:sort),
      ( forall x , x \notin  L  -> Typing  (  ( x ~( psi1 , A ))  ++ W )  psi0  ( open_tm_wrt_tm B (a_Var_f x) )  (a_Type s) )  ->
     Typing W psi a  (a_CEq psi0 a0 a1 psi1 A)  ->
     Typing W psi b  (open_tm_wrt_tm  B   a0 )  ->
      Typing W psi2 A (a_Type s1)  ->
     Typing W psi (a_Transp a b)  (open_tm_wrt_tm  B   a1 )
 | T_T : forall (W:context) (psi psi0:grade) (A:tm) (s2 s1:sort),
     Typing W psi A (a_Type s1) ->
      rule_t  s1   s2  ->
     Typing W psi (a_T psi0 A) (a_Type s2)
 | T_Box : forall (W:context) (psi psi0:grade) (a A:tm) (psi1:grade) (s:sort),
     Typing W psi0 a A ->
     Typing W psi1 (a_T psi0 A) (a_Type s) ->
     Typing W psi (a_Box psi0 a) (a_T psi0 A)
 | T_Unbox : forall (W:context) (psi psi0:grade) (a A:tm),
     Typing W psi a (a_T psi0 A) ->
      ( psi0  <=  psi )  ->
     Typing W psi (a_Unbox psi0 a) A
 | T_SSigma : forall (L:vars) (W:context) (psi psi0:grade) (A B:tm) (s3 s1 s2:sort),
     Typing W psi A (a_Type s1) ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~( psi0 , A ))  ++ W )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  (a_Type s2) )  ->
      rule_sig  s1   s2   s3  ->
     Typing W psi (a_SSigma psi0 A B) (a_Type s3)
 | T_SPair : forall (W:context) (psi:grade) (a:tm) (psi0:grade) (b A B:tm) (psi1:grade) (s:sort),
     Typing W psi1 (a_SSigma psi0 A B) (a_Type s) ->
     Typing W psi0 a A ->
     Typing W psi b  (open_tm_wrt_tm  B   a )  ->
     Typing W psi (a_SPair a psi0 b) (a_SSigma psi0 A B)
 | T_Proj1 : forall (W:context) (psi psi0:grade) (a A B:tm),
     Typing W psi a (a_SSigma psi0 A B) ->
      ( psi0  <=  psi )  ->
     Typing W psi (a_Proj1 psi0 a) A
 | T_Proj2 : forall (W:context) (psi psi0:grade) (a B A:tm),
     Typing W psi a (a_SSigma psi0 A B) ->
     Typing W psi0 (a_Proj1 psi0 a) A ->
     Typing W psi (a_Proj2 psi0 a)  (open_tm_wrt_tm  B   (a_Proj1 psi0 a) )
 | T_TyUnit : forall (W:context) (psi:grade) (s:sort),
     Ctx W ->
      rule_unit  s  ->
     Typing W psi a_TyUnit (a_Type s)
 | T_TmUnit : forall (W:context) (psi psi0:grade) (s:sort),
     Typing W psi0 a_TyUnit (a_Type s) ->
     Typing W psi a_TmUnit a_TyUnit
 | T_Bool : forall (W:context) (psi:grade) (s:sort),
     Ctx W ->
      rule_bool  s  ->
     Typing W psi a_Bool (a_Type s)
 | T_True : forall (W:context) (psi psi0:grade) (s:sort),
     Typing W psi0 a_Bool (a_Type s) ->
     Typing W psi a_True a_Bool
 | T_False : forall (W:context) (psi psi0:grade) (s:sort),
     Typing W psi0 a_Bool (a_Type s) ->
     Typing W psi a_False a_Bool
 | T_If : forall (W:context) (psi:grade) (a b0 b1 A:tm),
     Typing W psi a a_Bool ->
     Typing W psi b0 A ->
     Typing W psi b1 A ->
     Typing W psi (a_If a b0 b1) A.

Inductive Red : tm -> tm -> Prop :=
 | R_App : forall (a0:tm) (psi0:grade) (b a1:tm),
     lc_tm b ->
     Red a0 a1 ->
     Red (a_App a0 psi0 b) (a_App a1 psi0 b)
 | R_AppAbs : forall (psi0:grade) (A a b:tm),
     lc_tm A ->
     lc_tm (a_Abs psi0 A a) ->
     lc_tm b ->
     Red (a_App  ( (a_Abs psi0 A a) )  psi0 b)  (open_tm_wrt_tm  a   b )
 | R_Transp : forall (a b a0:tm),
     lc_tm b ->
     Red a a0 ->
     Red (a_Transp a b) (a_Transp a0 b)
 | R_TranspRefl : forall (a:tm),
     lc_tm a ->
     Red (a_Transp a_Refl a) a
 | R_Unbox : forall (psi0:grade) (a a0:tm),
     Red a a0 ->
     Red (a_Unbox psi0 a) (a_Unbox psi0 a0)
 | R_UnboxBox : forall (psi0:grade) (a:tm),
     lc_tm a ->
     Red (a_Unbox psi0  ( (a_Box psi0 a) ) ) a
 | R_Proj1Cong : forall (psi:grade) (a a':tm),
     Red a a' ->
     Red (a_Proj1 psi a) (a_Proj1 psi a')
 | R_Proj2Cong : forall (psi:grade) (a a':tm),
     Red a a' ->
     Red (a_Proj2 psi a) (a_Proj2 psi a')
 | R_Proj1Beta : forall (psi:grade) (a1 a2:tm),
     lc_tm a2 ->
     lc_tm a1 ->
     Red (a_Proj1 psi (a_SPair a1 psi a2)) a1
 | R_Proj2Beta : forall (psi:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
     Red (a_Proj2 psi (a_SPair a1 psi a2)) a2
 | R_If : forall (a b0 b1 a':tm),
     lc_tm b0 ->
     lc_tm b1 ->
     Red a a' ->
     Red (a_If a b0 b1) (a_If a' b0 b1)
 | R_IfTrue : forall (b0 b1:tm),
     lc_tm b1 ->
     lc_tm b0 ->
     Red (a_If a_True b0 b1) b0
 | R_IfFalse : forall (b0 b1:tm),
     lc_tm b0 ->
     lc_tm b1 ->
     Red (a_If a_False b0 b1) b1.

Inductive Reds : tm -> tm -> Prop :=
 | Rs_Refl : forall (a:tm),
     lc_tm a ->
     Reds a a
 | Rs_Step : forall (a0 a1 b:tm),
     Red a0 b ->
     Reds b a1 ->
     Reds a0 a1.

Inductive CPar : econtext -> grade -> grade -> tm -> tm -> Prop :=
 | CPar_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     Par P psi a1 a2 ->
     CPar P psi psi0 a1 a2
 | CPar_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not ( psi0  <=  psi )  ->
      uniq  P  ->
     CPar P psi psi0 a1 a2
with Par : econtext -> grade -> tm -> tm -> Prop :=
 | Par_Var : forall (P:econtext) (psi:grade) (x:tmvar) (psi0:grade),
      uniq  P  ->
      ( psi0  <=  psi )  ->
      binds  x   psi0   P  ->
     Par P psi (a_Var_f x) (a_Var_f x)
 | Par_Type : forall (P:econtext) (psi:grade) (s:sort),
      uniq  P  ->
     Par P psi (a_Type s) (a_Type s)
 | Par_Pi : forall (L:vars) (P:econtext) (psi psi1:grade) (A1 B1 A2 B2:tm),
     Par P psi A1 A2 ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi1 )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     Par P psi (a_Pi psi1 A1 B1) (a_Pi psi1 A2 B2)
 | Par_AppBeta : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b' A:tm),
     Par P psi a  ( (a_Abs psi0 A a') )  ->
     CPar P psi psi0 b b' ->
     Par P psi (a_App a psi0 b)  (open_tm_wrt_tm  a'   b' )
 | Par_App : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     Par P psi a a' ->
     CPar P psi psi0 b b' ->
     Par P psi (a_App a psi0 b) (a_App a' psi0 b')
 | Par_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 b1 A2 b2:tm),
     lc_tm A1 ->
     lc_tm A2 ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     Par P psi (a_Abs psi0 A1 b1) (a_Abs psi0 A2 b2)
 | Par_Refl : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Par P psi a_Refl a_Refl
 | Par_Transp : forall (P:econtext) (psi:grade) (a0 b0 a1 b1:tm),
     Par P psi a0 a1 ->
     Par P psi b0 b1 ->
     Par P psi (a_Transp a0 b0) (a_Transp a1 b1)
 | Par_CEq : forall (P:econtext) (psi psi0:grade) (a0 b0:tm) (psi1:grade) (A0 a1 b1 A1:tm),
     lc_tm A0 ->
     lc_tm A1 ->
     Par P psi a0 a1 ->
     Par P psi b0 b1 ->
      ( psi0  <=  psi )  ->
     Par P psi (a_CEq psi0 a0 b0 psi1 A0) (a_CEq psi0 a1 b1 psi1 A1)
 | Par_TranspRefl : forall (P:econtext) (psi:grade) (a0 b0 b1:tm),
     Par P psi a0 a_Refl ->
     Par P psi b0 b1 ->
     Par P psi (a_Transp a0 b0) b1
 | Par_T : forall (P:econtext) (psi psi0:grade) (A B:tm),
     Par P psi A B ->
     Par P psi (a_T psi0 A) (a_T psi0 B)
 | Par_Box : forall (P:econtext) (psi psi0:grade) (a b:tm),
     CPar P psi psi0 a b ->
     Par P psi (a_Box psi0 a) (a_Box psi0 b)
 | Par_Unbox : forall (P:econtext) (psi psi0:grade) (a b:tm),
     Par P psi a b ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Unbox psi0 a) (a_Unbox psi0 b)
 | Par_UnboxBox : forall (P:econtext) (psi psi0:grade) (a b:tm),
     Par P psi a (a_Box psi0 b) ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Unbox psi0 a) b
 | Par_Proj1Cong : forall (P:econtext) (psi psi0:grade) (a0 a1:tm),
     Par P psi a0 a1 ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Proj1 psi0 a0) (a_Proj1 psi0 a1)
 | Par_Proj2Cong : forall (P:econtext) (psi psi0:grade) (a0 a1:tm),
     Par P psi a0 a1 ->
     Par P psi (a_Proj2 psi0 a0) (a_Proj2 psi0 a1)
 | Par_Proj1Beta : forall (P:econtext) (psi psi0:grade) (b a1 a2:tm),
     Par P psi b (a_SPair a1 psi0 a2) ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Proj1 psi0 b) a1
 | Par_Proj2Beta : forall (P:econtext) (psi psi0:grade) (b a2 a1:tm),
     Par P psi b (a_SPair a1 psi0 a2) ->
     Par P psi (a_Proj2 psi0 b) a2
 | Par_SPair : forall (P:econtext) (psi:grade) (a0:tm) (psi0:grade) (b0 a1 b1:tm),
     CPar P psi psi0 a0 a1 ->
     Par P psi b0 b1 ->
     Par P psi (a_SPair a0 psi0 b0) (a_SPair a1 psi0 b1)
 | Par_SSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A0 B0 A1 B1:tm),
     Par P psi A0 A1 ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm B0 (a_Var_f x) )   ( open_tm_wrt_tm B1 (a_Var_f x) )  )  ->
     Par P psi (a_SSigma psi0 A0 B0) (a_SSigma psi0 A1 B1)
 | Par_TyUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Par P psi a_TyUnit a_TyUnit
 | Par_TmUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Par P psi a_TmUnit a_TmUnit
 | Par_Bool : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Par P psi a_Bool a_Bool
 | Par_True : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Par P psi a_True a_True
 | Par_False : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Par P psi a_False a_False
 | Par_If : forall (P:econtext) (psi:grade) (a0 b0 b1 a1 b2 b3:tm),
     Par P psi a0 a1 ->
     Par P psi b0 b2 ->
     Par P psi b1 b3 ->
     Par P psi (a_If a0 b0 b1) (a_If a1 b2 b3)
 | Par_IfTrue : forall (P:econtext) (psi:grade) (a0 b0 b1 b2 b3:tm),
     Par P psi a0 a_True ->
     Par P psi b0 b2 ->
     Par P psi b1 b3 ->
     Par P psi (a_If a0 b0 b1) b2
 | Par_IfFalse : forall (P:econtext) (psi:grade) (a0 b0 b1 b3 b2:tm),
     Par P psi a0 a_False ->
     Par P psi b0 b2 ->
     Par P psi b1 b3 ->
     Par P psi (a_If a0 b0 b1) b3.

Inductive EPar : econtext -> tm -> tm -> Prop :=
 | EP_One : forall (P:econtext) (a b:tm) (psi:grade),
     Par P psi a b ->
     EPar P a b.

Inductive EMPar : econtext -> tm -> tm -> Prop :=
 | EMP_One : forall (P:econtext) (a b:tm),
     EPar P a b ->
     EMPar P a b
 | EMP_Step : forall (P:econtext) (a a' b:tm),
     EPar P a b ->
     EMPar P b a' ->
     EMPar P a a'.

Inductive EJoins : econtext -> tm -> tm -> Prop :=
 | EJ_ejoins : forall (P:econtext) (a1 a2 b:tm),
     EMPar P a1 b ->
     EMPar P a2 b ->
     EJoins P a1 a2.

Inductive MultiPar : econtext -> grade -> tm -> tm -> Prop :=
 | MP_One : forall (P:econtext) (psi:grade) (a b:tm),
     Par P psi a b ->
     MultiPar P psi a b
 | MP_Step : forall (P:econtext) (psi:grade) (a a' b:tm),
     Par P psi a b ->
     MultiPar P psi b a' ->
     MultiPar P psi a a'.

Inductive Joins : econtext -> grade -> tm -> tm -> Prop :=
 | join : forall (P:econtext) (psi:grade) (a1 a2 b:tm),
     MultiPar P psi a1 b ->
     MultiPar P psi a2 b ->
     Joins P psi a1 a2.

Inductive CMultiPar : econtext -> grade -> grade -> tm -> tm -> Prop :=
 | CMP_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     MultiPar P psi a1 a2 ->
     CMultiPar P psi psi0 a1 a2
 | CMP_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not ( psi0  <=  psi )  ->
      uniq  P  ->
     CMultiPar P psi psi0 a1 a2.

Inductive CJoins : econtext -> grade -> grade -> tm -> tm -> Prop :=
 | CJ_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     Joins P psi a1 a2 ->
     CJoins P psi psi0 a1 a2
 | CJ_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not ( psi0  <=  psi )  ->
      uniq  P  ->
     CJoins P psi psi0 a1 a2.
