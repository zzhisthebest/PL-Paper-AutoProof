From stdpp Require Export prelude fin_maps fin_map_dom.

Notation "m '>>=' f" := (mbind f m) (at level 60, right associativity) : stdpp_scope.

Notation "x <- y ; z" := (y >>= (λ x : _, z))
  (at level 20, y at level 30, z at level 200, only parsing) : stdpp_scope.

Notation "' x <- y ; z" := (y >>= (λ x : _, z))
  (at level 20, x pattern, y at level 30, z at level 200, only parsing) : stdpp_scope.
