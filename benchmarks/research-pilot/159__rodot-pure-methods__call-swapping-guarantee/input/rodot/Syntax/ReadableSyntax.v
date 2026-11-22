Require Import LibExtra AbstractSyntax.

Declare Custom Entry term_custom.

Notation "'❪' e '❫'" := e (e custom term_custom at level 2, only parsing).

Notation "'$' v" := (avar_f v) (in custom term_custom at level 1, only parsing).

Notation "'#' n" := (avar_b n) (in custom term_custom at level 1, only parsing).

Notation "'Let' x '=' t1 'In' t2 " := (trm_let t1 (close x t2))  (in custom term_custom at level 0, x ident, only parsing, right associativity).

Notation "'Lit' x '=' l 'In' t " := (trm_lit l (close x t))  (in custom term_custom at level 0, x ident, only parsing, right associativity).

Notation "'Read' x '․' a " := (trm_read x a)  (in custom term_custom at level 0, x at level 1, only parsing).

Notation "'Write' x1 '․' a '=' x2 " := (trm_write x1 a x2)  (in custom term_custom at level 0, x1 at level 1, x2 at level 1, only parsing).

Notation "'Call' x1 '․' m x2" := (trm_call x1 m x2)  (in custom term_custom at level 0, x1 at level 1, x2 at level 1, only parsing).

Notation "'λ' '⟮' z '∶' T '⟯' t " := (lit_fun T (close z t)) (in custom term_custom at level 2, only parsing).

Notation "'ν' '⟮' s '∶' T '⟯' ds " := (lit_obj (close s T) (close s ds)) (in custom term_custom at level 2, only parsing).

Notation "'μ' T " := (typ_bnd T) (in custom term_custom at level 2, only parsing).

Notation "'μ' '⟮' r '∶' T '⟯' " := (typ_bnd (close r T)) (in custom term_custom at level 2, only parsing).

Notation "x1 '․' A '⟮' x2 '⟯' " := (typ_sel x1 A x2) (in custom term_custom at level 2, only parsing).

Notation "x1 '․ⁿ' A '⟮' x2 '⟯' " := (typ_sel x1 (typ_label_normal A) x2) (in custom term_custom at level 2, only parsing).

Notation "'⊤'" := (typ_top) (in custom term_custom at level 2, only parsing).

Notation "'⊥'" := (typ_bot) (in custom term_custom at level 2, only parsing).

Notation "'𝖭'" := (typ_nocap) (in custom term_custom at level 1, only parsing).

Notation "'𝖬'" := (typ_label_refcap typ_refcap_mutability) (in custom term_custom at level 2, only parsing).

Notation "T1 '∧' T2" := (typ_and T1 T2) (in custom term_custom at level 3, only parsing, left associativity).

Notation "T1 '∨' T2" := (typ_or T1 T2) (in custom term_custom at level 3, only parsing, left associativity).

Notation "'❴ᵗ' A '∶' TL '..' TU  '❵'" := (typ_rcd (dec_typ A TL TU)) (in custom term_custom at level 2, only parsing).

Notation "'❴ⁿ' A '∶' TL '..' TU  '❵'" := (typ_rcd (dec_typ (typ_label_normal A) TL TU)) (in custom term_custom at level 2, only parsing).

Notation "'❴ᶜ' A '∶' TL '..' TU  '❵'" := (typ_rcd (dec_typ (typ_label_refcap A) TL TU)) (in custom term_custom at level 2, only parsing).

Notation "'❴ᶠ' a '∶' TL '..' TU  '❵'" := (typ_rcd (dec_fld a TL TU)) (in custom term_custom at level 2, only parsing).

Notation "'❴ᵐ' m '∶' TC ',' TZ '→' TR  '❵'" := (typ_rcd (dec_met m TC TZ TR)) (in custom term_custom at level 2, only parsing).

Notation "'❴ᵗ' A '⟮' r '⟯' '∶' TL '..' TU '❵'" := (typ_rcd (dec_typ A (close r TL) (close r TU))) (in custom term_custom at level 2, only parsing).

Notation "'❴ᵐ' m '⟮' r '∶' TC ',' z '∶' TZ '⟯' '∶' TR '❵'" := (typ_rcd (dec_met m (close z TC) TZ (close_met z r TR))) (in custom term_custom at level 2, only parsing).

Notation "'❴ᵗ' A '=' T '❵'" := (def_typ A T) (in custom term_custom at level 2, only parsing).

Notation "'❴ⁿ' A '=' T '❵'" := (def_typ (typ_label_normal A) T) (in custom term_custom at level 2, only parsing).

Notation "'❴ᶜ' A '=' T '❵'" := (def_typ (typ_label_refcap A) T) (in custom term_custom at level 2, only parsing).

Notation "'❴ᶠ' A '=' x '❵'" := (def_fld A x) (in custom term_custom at level 2, only parsing).

Notation "'❴ᵐ' m '=' t  '❵'" := (def_met m t) (in custom term_custom at level 2, only parsing).

Notation "'❴ᵗ' A '⟮' r '⟯' '=' T '❵'" := (def_typ A (close r T)) (in custom term_custom at level 2, only parsing).

Notation "'❴ᵐ' m '⟮' r ',' z '⟯' '=' t '❵'" := (def_met m (close_met z r t)) (in custom term_custom at level 2, only parsing).

Notation "T1 '⋏' T2" := (defs_cons T1 T2) (in custom term_custom at level 3, only parsing, left associativity).

Notation "∅" := (defs_nil) (in custom term_custom at level 3, only parsing, left associativity).

Notation "{ x }" := x (in custom term_custom at level 0, x constr, only parsing).

Notation "x" := x (in custom term_custom at level 0, x ident, only parsing).
