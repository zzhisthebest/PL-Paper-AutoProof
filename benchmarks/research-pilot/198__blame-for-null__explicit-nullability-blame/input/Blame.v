Require Export Definitions.
Require Import Metalib.Metatheory.

Notation "t '⦂' S '=>' U '@@' p" := (t_cast t S p U) (at level 40).

Notation "M '{{{' T '→' U '}}}'" := (typ_mod_arrow M T U) (at level 40).

Notation "##" := mod_non_nullable.

Notation "??" := mod_safe.

Notation "!!" := mod_unsafe.

Notation Null := typ_null.

Notation "### T '→' U" := (typE_nonnull_arrow T U) (at level 40).

Notation "??? T '→' U" := (typE_safe_arrow T U) (at level 40).

Notation "!!! T '→' U" := (typI_unsafe_arrow T U) (at level 40).

Definition neglabel_fun (l: label) : label :=
  match l with
  | (label_name l') => (label_not_label l')
  | (label_not_label l') => label_name l'
  end.

Inductive null_mod : modality -> Prop :=
| null_mod_safe : null_mod ??
| null_mod_unsafe : null_mod !!.

Inductive psub : typ -> typ -> Prop :=
| psub_null_refl : psub Null Null
| psub_null M S T : null_mod M -> psub Null (M {{{S → T}}})
| psub_arrow_nn M S T S' T' : nsub S' S -> psub T T' -> psub (## {{{S → T}}}) (M {{{S' → T'}}})
| psub_arrow_nullable M M' S T S' T' : null_mod M -> null_mod M' -> nsub S' S -> psub T T' -> psub (M {{{S → T}}}) (M' {{{S' → T'}}})

with nsub : typ -> typ -> Prop :=
     | nsub_null_refl : nsub Null Null
     | nsub_null S T : nsub Null (?? {{{S → T}}})
     | nsub_arrow_nn M S T S' T' : psub S' S -> nsub T T' -> nsub (## {{{S → T}}}) (M {{{S' → T'}}})
     | nsub_arrow_nullable M S T S' T': psub S' S -> nsub T T' -> nsub (!! {{{S → T}}}) (M {{{S' → T'}}})
     | nsub_arrow_nullable_safe M S T S' T': (M = ## \/ M = ??) -> psub S' S -> nsub T T' -> nsub (typ_mod_arrow ?? S T) (typ_mod_arrow M S' T').

Notation "T '≺+' U" := (psub T U) (at level 40).

Notation "T '≺-' U" := (nsub T U) (at level 40).

Notation "~~ p" := (neglabel_fun p) (at level 40).

Inductive sfor : trm -> label -> Prop :=
| sfor_varb n p : sfor (t_var_b n) p
| sfor_var x p : sfor (t_var_f x) p
| sfor_null p : sfor t_null p
| sfor_abs T s p : sfor s p -> sfor (t_abs T s) p
| sfor_app t1 t2 p : sfor t1 p -> sfor t2 p ->  sfor (t_app t1 t2) p
| sfor_safe_app t1 t2 t3 p : sfor t1 p -> sfor t2 p -> sfor t3 p -> sfor (t_app_safe t1 t2 t3) p
| sfor_cast_pos S T p s : S ≺+ T -> sfor s p -> sfor (s ⦂ S => T @@ p) p
| sfor_cast_neg S T p s : S ≺- T -> sfor s p -> sfor (s ⦂ S => T @@ (neglabel_fun p)) p
| sfor_cast_diff S T p q s : sfor s p -> p <> q -> p <> (neglabel_fun q) -> sfor (s ⦂ S => T @@ q) p.
