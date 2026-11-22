Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Require Import Vars Types Context.

Inductive objctx: Set :=

| objctx_empty: objctx
| objctx_lit(x: var)(T: typ): objctx
| objctx_heap(y: var)(T: typ): objctx
.

Notation ctx_met G xz TZ xc TC := (G § xz / v_par ~ TZ § xc / v_recv ~ (open xz TC)).

Notation open_met xz xc T := (open xz (open_rec 1 xc T)) (only parsing).

Notation close_met z r T := (close z (close_rec 1 r T)) (only parsing).

Definition ctx_obj(G: ctx)(Go: objctx) :=
  match Go with
  | objctx_empty => G
  | objctx_lit x T => G § x / v_self ~ open x T
  | objctx_heap y T => G
  end.

Notation ctx_met_refined G xz TZ xc TC TC2 := (G § xz / v_par ~ TZ § xc / v_recv ~ (typ_and (open xz TC) TC2)).

Notation ctx_met_refined_heap G xz TZ xc TC y T := (ctx_met_refined G xz TZ xc TC (typ_and (open y T) (open xc T))).

Definition subst_objctx vSrc vDst Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit x (subst_var vSrc vDst T)
  | objctx_heap y T => objctx_heap (subst_var vSrc vDst y) (subst_var vSrc vDst T)
  end.

Notation "G '/[§§' x '->' y ']'" :=
  (subst_objctx x y G) (x at level 69, at level 7, left associativity) : syntax_scope.

Definition subst_objctx_pvars xs ys Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit x (subst_pvars xs ys T)
  | objctx_heap y T => objctx_heap (subst_pvars xs ys y) (subst_pvars xs ys T)
  end.

Definition subst_objctx_varx vsSrc vsDst Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit x (subst_vars vsSrc vsDst T)
  | objctx_heap y T => objctx_heap (subst_vars vsSrc vsDst y) (subst_vars vsSrc vsDst T)
  end.

Definition objctx_dom Go :=
  match Go with
  | objctx_empty => \{}
  | objctx_lit x T => \{ x }
  | objctx_heap y T => \{}
  end.

Definition objctx_keys Go: list var :=
  match Go with
  | objctx_empty => nil
  | objctx_lit x T => x::nil
  | objctx_heap y T => nil
  end.

Definition objctx_fv Go :=
  match Go with
  | objctx_empty => \{}
  | objctx_lit x T => fv T
  | objctx_heap y T => \{y} \u (fv T)
  end.

Notation "G '§§&' Go" := (ctx_obj G Go)  (at level 28, left associativity).

Fixpoint objctx_seal_rec n y G {struct G} :=
  match G with
  | objctx_empty => objctx_empty
  | objctx_heap x T => objctx_heap x (seal_rec (S n) y T)
  | objctx_lit x T => objctx_lit x (seal_rec (S n) y T)
  end.

Instance ObjctxSealable: Sealable objctx := objctx_seal_rec.
