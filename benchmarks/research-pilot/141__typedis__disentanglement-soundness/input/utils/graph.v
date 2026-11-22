From Coq.ssr Require Import ssreflect.

From stdpp Require Import strings binders gmap gmultiset sets ssreflect.

Definition graph (K:Type) `{Countable K} := (gset (K*K)).

Section Graph.

Context `{Countable K}.

Implicit Type G : graph K.

Implicit Type x y : K.

Definition edge G x y := (x,y) ∈ G.

Definition reachable G x y := rtc (edge G) x y.

Definition edges (x:K) (X:gset K) : gset (K*K) := set_map (fun y => (x,y)) X.

Definition graph_upd G x (X:gset K) := (edges x X) ∪ G.

Definition vertices G : gset K := set_fold (fun '(x,y) acc => {[x;y]} ∪ acc) ∅ G.

Definition graph_fork (G:graph K) (t v w:K) :=
  graph_upd G t {[v;w]}.

Definition graph_join (G:graph K) (t v w:K) :=
  graph_upd (graph_upd G t {[w]}) v {[w]}.

End Graph.

Inductive direction := Left | Right.

Definition path := list direction.
