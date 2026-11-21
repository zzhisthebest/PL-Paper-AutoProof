Require Import String Arith Lia Bool List Nat.

Require Import terms types.

Open Scope string_scope.

Open Scope nat_scope.

Set Default Proof Using "Type".

Definition omega21_ty := program_type omega21.

Definition omega22_ty := program_type omega22.

Definition omega2_ty := (Fork (Stem omega21_ty) omega22_ty).

Definition eval_ty := quant 1 (Funty (Var 0) (Asf (Var 0))).

Definition eager_ty := quant 2 (Funty (Funty (Var 0) (Var 1)) (Funty (Var 0) (Var 1))).

Definition bfff_aug uty := Fork (Stem (Fork Leaf eval_ty)) (Asf uty).

Definition bffs_aug uty := Fork (Stem (Fork Leaf eager_ty)) (bfff_aug uty).

Inductive subtype : dtype -> dtype -> Prop :=

| sub_zero : forall ty, subtype ty ty
| sub_trans : forall ty1 ty2 ty3, subtype ty1 ty2 -> subtype ty2 ty3 -> subtype ty1 ty3

| sub_stem : forall uty1 uty2, subtype uty1 uty2 -> subtype (Stem uty1) (Stem uty2)
| sub_fork : forall uty1 uty2 vty1 vty2, subtype uty1 uty2 -> subtype vty1 vty2 ->
                                         subtype (Fork uty1 vty1) (Fork uty2 vty2)
| sub_asf : forall uty1 uty2, subtype uty1 uty2 -> subtype (Asf uty1) (Asf uty2)
| sub_funty : forall uty1 uty2 vty1 vty2, subtype uty2 uty1 -> subtype vty1 vty2 ->
                                          subtype (Funty uty1 vty1) (Funty uty2 vty2)
| sub_quant : forall vty1 vty2,  subtype vty1 vty2 -> subtype (Quant vty1) (Quant vty2)

| sub_quant_stem: forall uty, subtype (Quant (Stem uty)) (Stem (Quant uty))
| sub_quant_fork: forall uty vty, subtype (Quant (Fork uty vty)) (Fork (Quant uty) (Quant vty))
| sub_quant_asf: forall uty, subtype (Quant (Asf uty)) (Asf (Quant uty))
| sub_dist: forall uty vty, subtype (Quant (Funty uty vty)) (Funty (Quant uty) (Quant vty))

| sub_inst : forall ty u,  subtype (Quant ty) (subst ty u)
| sub_lift: forall ty, subtype ty (Quant (lift 1 ty))

| sub_leaf_fun:forall uty,  subtype Leaf (Funty uty (Stem uty))
| sub_stem_fun: forall uty vty, subtype (Stem uty) (Funty vty (Fork uty vty))

| sub_fork_leaf: forall uty vty, subtype (Fork Leaf uty) (Funty vty uty)
| sub_fork_stem: forall uty vty wty,
    subtype (Fork (Stem (Funty uty (Funty vty wty))) (Funty uty vty)) (Funty uty wty)
| sub_fork_fork_leaf: forall uty vty wty,
    subtype (Fork (Fork uty vty) wty) (Funty Leaf uty)
| sub_fork_fork_stem:
    forall uty vty1 vty2 wty,
      subtype (Fork (Fork uty (Funty vty1 vty2)) wty) (Funty (Stem vty1) vty2)
| sub_fork_fork_fork:
    forall uty vty wty1 wty2 wty3,
      subtype (Fork (Fork uty vty) (Funty wty1 (Funty wty2 wty3))) (Funty (Fork wty1 wty2) wty3)

| sub_recursion:
    forall k uty vty,
      subtype omega2_ty
              (Funty
                 omega2_ty
                 (Funty
                    (Funty (quant k (Funty uty vty)) (quant k (Funty uty vty)))
                    (quant k (Funty uty vty))))
| sub_tree: forall ty uty,
    covariant ty ->
    subtype (Fork
               (Fork
                  (subst ty Leaf)
                  (quant 1 (Funty (Var 0) (subst (lift_rec ty 1 1) (Stem (Var 0))))))
               (quant
                  2
                  (Funty
                     (Var 1)
                     (Funty (Var 0) (subst (lift_rec ty 1 2) (Fork (Var 1) (Var 0)))))
            ))
            (Funty uty (subst ty uty))
| sub_to_asf: forall ty, subtype ty (Asf ty)
| sub_from_asf: forall uty vty, subtype (Asf (Funty uty vty)) (Funty uty vty)
| sub_bffs: forall uty vty, subtype (Fork (Stem (bffs_aug uty)) (Asf vty)) (Asf (Fork (Stem uty) vty))
| sub_bfff : forall uty vty wty, subtype (Fork (Fork uty (Asf vty)) (bfff_aug wty))
                                         (Asf (Fork (Fork uty vty) wty))
.
