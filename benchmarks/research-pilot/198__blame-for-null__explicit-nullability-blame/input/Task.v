From Stdlib Require Import List.
Require Import Metalib.Metatheory.
Require Import Blame.

Notation "G '⊢e' t ':' T" := (typingE G t T) (at level 40, t at level 59).

Notation "G '⊢i' t ':' T" := (typingI G t T) (at level 40, t at level 59).

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

Notation dTe Te := (desugarTe Te).

Notation dTi Ti := (desugarTi Ti).

Definition fresh_label (existing : list blame_label) : blame_label := MetatheoryAtom.Atom.fresh existing.

Definition E_l := fresh_label nil.

Definition I_l := fresh_label (E_l :: nil).

Definition E_intl := fresh_label (E_l :: I_l :: nil).

Definition I_intl := fresh_label (E_l :: I_l :: E_intl :: nil).

Definition E_lab := label_name E_l.

Definition I_lab := label_name I_l.

Definition E_int := label_name E_intl.

Definition I_int := label_name I_intl.

Definition EIlabels := E_lab ::
                       I_lab ::
                       ~~E_lab ::
                       ~~I_lab ::
                       E_int ::
                       I_int ::
                       ~~E_int ::
                       ~~I_int ::
                       nil.

Notation SafeLabels :=
  (~~I_lab :: E_lab :: I_int :: ~~I_int :: E_int :: ~~E_int :: nil).

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

Fixpoint labels t :=
  match t with
  | tei_var_b _ => nil
  | tei_var_f _ => nil
  | tei_null _ => nil
  | tei_abs_exp _ t => labels t
  | tei_abs_imp _ t _ => labels t
  | tei_app t u _ => labels t ++ labels u
  | tei_app_safe s t u _ => labels s ++ labels t ++ labels u
  | tei_cast_exp t Te Ue => labels t
  | tei_cast_imp t Ti p Ui => p :: labels t
  | tei_import_exp Te t Ti u => labels t ++ labels u
  | tei_import_imp Ti t Te u => labels t ++ labels u
  end.

Definition disjoint {A} (l1 l2 : list A) :=
  forall x, In x l1 -> ~(In x l2).

Notation sfors t ls := (forall l, In l ls -> sfor t l).

Theorem explicit_cant_be_blamed :
  (forall Ge t Te,
      Ge ⊢e t : Te ->
      disjoint EIlabels (labels t) ->
      sfors (desugar t) SafeLabels) /\
  (forall Gi t Ti,
      Gi ⊢i t : Ti ->
      disjoint EIlabels (labels t) ->
      sfors (desugar t) SafeLabels).
