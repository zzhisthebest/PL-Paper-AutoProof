Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import PreTyping Typing GeneralTyping.

Require Import Effects Initialization InitLookup.

Implicit Types (i : init_typ) (t : trm) (l : lit).

Inductive all_comm_unspec : inits -> Prop :=
| all_comm_unspec_nil : all_comm_unspec nil
| all_comm_unspec_cons : forall i is',
    (i = committed) \/ (i = unspecified) ->
    all_comm_unspec is' ->
    all_comm_unspec (cons i is').

Inductive well_committed : CommitTyping trm :=

| commit_var : forall Gamma Delta x,
    binds x committed Delta ->
    Gamma ⸴ Delta ⊢c (trm_var (avar_f x))

| commit_all_elim : forall Gamma Delta x z,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⸴ Delta ⊢c trm_var (avar_f z) ->
    Gamma ⸴ Delta ⊢c trm_app (avar_f x) (avar_f z)

| commit_new : forall Gamma Delta x avs Ts is' T,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T ->
    all_comm_unspec is' ->
    Gamma ⸴ Delta ⊢c avs ->
    Gamma ⸴ Delta ⊢c trm_new (avar_f x) avs

| commit_rcd_elim : forall Gamma Delta x a,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⸴ Delta ⊢c trm_sel (avar_f x) a

| commit_fld_asn : forall Gamma Delta x i y a,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⸴ Delta ⊢c trm_var (avar_f y) ->
    Gamma ⸴ Delta ⊢c trm_asn (avar_f x) a (avar_f y)

| commit_let : forall L Gamma Delta t u T,
    Gamma ⸴ Delta ⊢c t ->
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x u) ->
    Gamma ⸴ Delta ⊢c trm_let T t u

| commit_llit : forall L Gamma Delta l u T,
    Gamma ⸴ Delta ⊢c l ->
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x u) ->
    Gamma ⸴ Delta ⊢c trm_lit T l u

with well_committed_avars : CommitTyping avars :=
     | committed_nil : forall Gamma Delta,
         Gamma ⸴ Delta ⊢c nil

     | committed_cons : forall Gamma Delta x avs,
         Gamma ⸴ Delta ⊢c (trm_var (avar_f x)) ->
         Gamma ⸴ Delta ⊢c avs ->
         Gamma ⸴ Delta ⊢c (cons (avar_f x) avs)

with well_committed_lit : CommitTyping lit :=

     | commit_all_intro : forall L Gamma Delta T t,
         (forall x, x \notin L ->
               Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x t) ->
         Gamma ⸴ Delta ⊢c lit_fun T t

     | commit_con_intro : forall L Gamma Delta Ts is' T i ds t,
         length is' = length_s Ts ->
         (forall x ys,
             length ys = length_s Ts ->
             fresh L (S (length ys)) (cons x ys) ->
             has_effs (open_vars (cons x ys) t) (def_eff x ds)) ->
         (forall x ys,
             length ys = length_s Ts ->
             fresh L (S (length ys)) (cons x ys) ->
             (Gamma & (ys ~** (to_list Ts))
              & (x ~ open_vars (cons x ys) T) ⸴ Delta
              & (ys ~** is') & (x ~ free) ⸴ (from_list ys) \u \{ x}
                                          ⊢i (open_vars (cons x ys) t) ∶ i)) ->
         Gamma ⸴ Delta ⊢c lit_con Ts is' T ds t

with well_init : InitTyping trm :=

| init_var_binds : forall Gamma Delta vs x i,

    init_var Delta vs x i ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ i

| init_commit : forall Gamma Delta t vs,
    Gamma ⸴ Delta ⊢c t ->
    Gamma ⸴ Delta ⸴ vs ⊢i t ∶ committed

| init_new_free : forall Gamma Delta vs x avs Ts is' T,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T ->
    Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_new (avar_f x) avs ∶ free

| init_fld_asn_ac : forall Gamma Delta vs x i y a,
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ i ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f y) ∶ committed ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_asn (avar_f x) a (avar_f y) ∶ committed

| init_fld_asn_ff : forall Gamma Delta vs x y a,
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ free ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f y) ∶ free ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_asn (avar_f x) a (avar_f y) ∶ free

| init_let : forall L Gamma Delta vs t u T i i',
    Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ i ⸴ vs \u \{ x} ⊢i open x u ∶ i') ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_let T t u ∶ i'

| init_llit : forall L Gamma Delta vs l u T i,
    Gamma ⸴ Delta ⊢c l ->
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ committed ⸴ vs ⊢i open x u ∶ i) ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_lit T l u ∶ i

with well_inits : InitTypings avars :=
     | well_inits_nil : forall Gamma Delta vs,
         Gamma ⸴ Delta ⸴ vs ⊢i nil :: nil

     | well_inits_cons : forall Gamma Delta vs x i avs is',
         Gamma ⸴ Delta ⸴ vs ⊢i (trm_var (avar_f x)) ∶ i ->
         Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
         Gamma ⸴ Delta ⸴ vs ⊢i (cons (avar_f x) avs) :: (cons i is').

Existing Instance well_committed.

Existing Instance well_committed_avars.

Existing Instance well_init.

Existing Instance well_inits.

Existing Instance well_committed_lit.

Scheme well_committed_mut        := Induction for well_committed Sort Prop
with   well_committed_avars_mut  := Induction for well_committed_avars Sort Prop
with   well_committed_lit_mut    := Induction for well_committed_lit Sort Prop
with   well_init_mut             := Induction for well_init Sort Prop
with   well_inits_mut            := Induction for well_inits Sort Prop.

Combined Scheme well_init_mut_ind from
         well_committed_mut, well_committed_avars_mut, well_committed_lit_mut,
         well_init_mut, well_inits_mut.
