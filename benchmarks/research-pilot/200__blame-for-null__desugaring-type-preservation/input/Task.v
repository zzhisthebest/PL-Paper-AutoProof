From Stdlib Require Import List.
Require Import Metalib.Metatheory.
Require Import Definitions.

Notation "G '⊢' t ':' T" := (typing G t T) (at level 40, t at level 59).

Notation "##" := mod_non_nullable.

Notation "??" := mod_safe.

Notation "!!" := mod_unsafe.

Notation "G '⊢e' t ':' T" := (typingE G t T) (at level 40, t at level 59).

Notation "G '⊢i' t ':' T" := (typingI G t T) (at level 40, t at level 59).

Notation "### T '→' U" := (typE_nonnull_arrow T U) (at level 40).

Notation "??? T '→' U" := (typE_safe_arrow T U) (at level 40).

Notation "!!! T '→' U" := (typI_unsafe_arrow T U) (at level 40).

Fixpoint desugarTe (Te : typE) : typ :=
  match Te with
  | typE_null => typ_null
  | typE_nonnull_arrow Se Ue => typ_mod_arrow ## (desugarTe Se) (desugarTe Ue)
  | typE_safe_arrow Se Ue => typ_mod_arrow ?? (desugarTe Se) (desugarTe Ue)
  end.

Fixpoint desugarTi (Ti : typI) : typ :=
  match Ti with
  | typI_null => typ_null
  | typI_unsafe_arrow Si Ui => typ_mod_arrow !! (desugarTi Si) (desugarTi Ui)
  end.

Definition fresh_label (existing : list blame_label) : blame_label := MetatheoryAtom.Atom.fresh existing.

Definition E_l := fresh_label nil.

Definition I_l := fresh_label (E_l :: nil).

Definition E_intl := fresh_label (E_l :: I_l :: nil).

Definition I_intl := fresh_label (E_l :: I_l :: E_intl :: nil).

Definition E_lab := label_name E_l.

Definition I_lab := label_name I_l.

Definition E_int := label_name E_intl.

Definition I_int := label_name I_intl.

Fixpoint desugar t :=
  match t with
  | tei_var_b n =>
    t_var_b n
  | tei_var_f x =>
    t_var_f x
  | tei_null _ =>
    t_null
  | tei_abs_exp T t =>
    t_abs (desugarTe T) (desugar t)
  | tei_abs_imp Ti t Ui =>
    t_cast (t_abs (desugarTi Ti) (desugar t))
           (typ_mod_arrow ## (desugarTi Ti) (desugarTi Ui))
           I_int
           (typ_mod_arrow !! (desugarTi Ti) (desugarTi Ui))
  | tei_app t u _ =>
    t_app (desugar t) (desugar u)
  | tei_app_safe s t u m =>
    t_app_safe (desugar s) (desugar t) (desugar u)
  | tei_cast_exp t Te Ue =>
    t_cast (desugar t) (desugarTe Te) E_int (desugarTe Ue)
  | tei_cast_imp t Ti p Ui =>
    t_cast (desugar t) (desugarTi Ti) p (desugarTi Ui)
  | tei_import_exp Te t Ti u =>
    t_app (t_abs (desugarTe Te) (desugar u))
          (t_cast (desugar t) (desugarTi Ti) I_lab (desugarTe Te))
  | tei_import_imp Ti t Te u =>
    t_app (t_abs (desugarTi Ti) (desugar u))
          (t_cast (desugar t) (desugarTe Te) E_lab (desugarTi Ti))
  end.

Notation dGe Ge :=
  (map desugarTe Ge).

Notation dGi Gi :=
  (map desugarTi Gi).

Theorem desugar_typing:
  (forall Ge tei Te,
      Ge ⊢e tei : Te ->
      dGe Ge ⊢ desugar tei : desugarTe Te) /\
  (forall Gi tei Ti,
      Gi ⊢i tei : Ti ->
      dGi Gi ⊢ desugar tei : desugarTi Ti).
