From Stdlib Require Import PeanoNat Lia Wf_nat.

From OLlibs Require Import Logic_Datatypes_more List_more.

From InterPT Require Export lformulas.

Export LogicNotations ListNotations.

Set Default Proof Using "Type".

Set Implicit Arguments.

Unset Printing Use Implicit Types.

Reserved Notation "l ⎹ bp ⊦ a" (at level 65, format "l ⎹ bp ⊦  a").

Inductive lprove {bp : bool} : list lform -> lform -> Type :=
| lidentity a : [a]⎹bp⊦ a
| ltop_right l : l⎹bp⊦ 𝖳
| lwith_left1 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ a ∧ b :: l2⎹bp⊦ c
| lwith_left2 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ b ∧ a :: l2⎹bp⊦ c
| lwith_right a b l : l⎹bp⊦ a -> l⎹bp⊦ b -> l⎹bp⊦ a ∧ b
| lmap_left a b c l1 l2 l3 : (bp = true -> l1 = [] /\ length l2 = 1%nat) ->
    l2⎹bp⊦ a -> l1 ++ b :: l3⎹bp⊦ c -> l1 ++ b / a :: l2 ++ l3⎹bp⊦ c
| lmap_right a b l : l · a⎹bp⊦ b -> l⎹bp⊦ b / a
| lzero_left a l1 l2 : l1 ++ 0 :: l2⎹bp⊦ a
| lplus_left a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ b :: l2⎹bp⊦ c -> l1 ++ a ∨ b :: l2⎹bp⊦ c
| lplus_right1 a b l : l⎹bp⊦ a -> l⎹bp⊦ a ∨ b
| lplus_right2 a b l : l⎹bp⊦ a -> l⎹bp⊦ b ∨ a
| lone_left a l1 l2 : l1 ++ l2⎹bp⊦ a -> l1 ++ 1 :: l2⎹bp⊦ a
| lone_right : nil⎹bp⊦ 1
| lfrl_left a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2⎹bp⊦ c -> l1 ++ lfrl x a :: l2⎹bp⊦ c
| lfrl_right a x l : map fupz l⎹bp⊦ subs x (dvar 0) (fupz a) -> l⎹bp⊦ lfrl x a
| lexs_left a x c l1 l2 : map fupz l1 ++ subs x (dvar 0) (fupz a) :: map fupz l2⎹bp⊦ fupz c ->
   l1 ++ lexs x a :: l2⎹bp⊦ c
| lexs_right a x b l : closed b -> l⎹bp⊦ subs x b a -> l⎹bp⊦ lexs x a
where "l ⎹ bp ⊦ a" := (@lprove bp l a).

Arguments lidentity {_ _}, [_] _, _ _.

Arguments ltop_right {_ _}, [_] _, _ _.

Arguments lwith_left1 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.

Arguments lwith_left2 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.

Arguments lwith_right [_ _ _ _] _ _, [_] _ _ _ _ _, _ _ _ _ _ _.

Arguments lmap_left [_ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _] _ _ _, [_] _ _ _ _ _ _ _ _ _, _ _ _ _ _ _ _ _ _ _.

Arguments lmap_right [_ _ _ _] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lzero_left {_ _ _ _}, [_] _ _ _, _ _ _ _.

Arguments lplus_left [_ _ _ _ _ _] _ _, [_] _ _ _ _ _ _ _, _ _ _ _ _ _ _ _.

Arguments lplus_right1 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lplus_right2 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lone_left [_ _ _ _] _, [_ _] _ _ _, [_] _ _ _ _, _ _ _ _ _.

Arguments lone_right {_}, _.

Arguments lfrl_left [_ _ _ _ _ _ _ _] _, [_ _ _ _ _ _ _] _ _, _ _ _ _ _ _ _ _.

Arguments lfrl_right [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lexs_left [_ _ _ _ _ _] _, [_ _] _ [_ _] _, [_] _ _ _ _ _, _ _ _ _ _ _.

Arguments lexs_right [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _ _.

Section WithParameter.

Variable bp : bool.

Notation lprove := (@lprove bp).

Notation "l ⊦ a" := (lprove l a) (at level 65, format "l  ⊦  a").

Fixpoint lweight l b (pi : l ⊦ b) := S
match pi with
| lidentity | ltop_right | lzero_left | lone_right => 0
| lwith_left1 pi1 | lwith_left2 pi1 | lmap_right pi1 | lplus_right1 pi1 | lplus_right2 pi1
| lone_left pi1 | lfrl_left pi1 | lfrl_right pi1 | lexs_left pi1 | lexs_right pi1 => lweight pi1
| lwith_right pi1 pi2 | lplus_left pi1 pi2 => max (lweight pi1) (lweight pi2)
| lmap_left pi1 pi2 => lweight pi1 + lweight pi2
end.

Theorem lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.

End WithParameter.
