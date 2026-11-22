Set Implicit Arguments.

Require Import LibExtra Vars Terms Stack Heap Env SyntaxClasses.

Inductive config: Type := config_mk (t:trm) (s:stack) (S:heap) (e:renv) (Lv: fset var): config.

Notation "t ; s ; Sigma ; e ; Lv" :=
  (config_mk t s Sigma e Lv) (at level 39, s, Sigma, e at level 38, Lv at level 38) : syntax_scope.

Definition config_heap C := (
  match C with
  _ ; _ ; Sc ; _ ; _ => Sc
  end ).

Definition config_env C := (
  match C with
  _ ; _ ; _ ; e ; _ => e
  end ).

Definition config_fv C := (
  match C with
  _ ; _ ; _ ; _ ; Lv => Lv
  end ).

Notation fv_renv e := ((@dom var e) \u (fv_env e)).

Notation fv_config c :=
  match c with
  | (t ; s ; Sigma ; e ; Lv) =>
    (@fv trm _ t) \u (@fv stack _ s) \u (fv_heap Sigma)
      \u (fv_renv e) \u Lv
  end.

Notation fresh_in_config l c := (fresh (fv_config c) (length l) l).

Definition nothing_fresh_in_config A {AF: FreeVar A} (a:A) c :=
  (fv a) \c fv_config c.

Notation vars_conf xs C := (
    from_list xs \c fv_config C
  ) (only parsing).

Definition vars_conf_unique xs C := (
    fresh \{} (length xs) xs /\
    vars_conf xs C
  ).
