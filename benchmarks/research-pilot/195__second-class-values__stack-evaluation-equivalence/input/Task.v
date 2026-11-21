Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

Require Export stlc1.

Require Export stlc2.

Inductive equiv_val : stack vl_stack -> vl -> vl_stack -> Prop :=
  | equiv_const : forall b st, equiv_val st (vbool b) (vbool_stack b)
  | equiv_abs : forall H1 H2 idx lS i t c1 c2 H fr,
                      get_stack_frame lS i = Some (fr, idx) ->
                      equiv_env lS (Def H1 H2 idx) (H, (fr, idx)) ->
                      equiv_val lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2)
with equiv_env : stack vl_stack -> venv -> venv_stack -> Prop :=
  | eqv_forall : forall lS H1 H1s H2 H2s H20,
                      Forall2(fun v vs => equiv_val lS v vs) H1 H1s ->
                      Forall2(fun v vs => equiv_val lS v vs) H2 H2s ->
                      equiv_env lS (Def H1 (H2++H20) (length H20)) (H1s, (H2s, length H20))
.

Definition eqv_nested_ind := fun
  (Pv : stack vl_stack -> vl -> vl_stack -> Prop)
  (Pe : stack vl_stack -> venv -> venv_stack -> Prop)
  (fconst : forall (b : bool) (st : stack vl_stack),
       Pv st (vbool b) (vbool_stack b))
  (fabs : forall (H1 H2 : list vl) (idx : nat) (lS : stack vl_stack)
          (i : st_ptr) (t : tm) (c1 c2 : class) (H : heap vl_stack)
          (fr : list vl_stack),
        get_stack_frame lS i = Some (fr, idx) ->
        Pe lS (Def H1 H2 idx) (H, (fr, idx)) ->
        Pv lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2))
  (fenv : forall (lS : stack vl_stack) (H1 : list vl)
         (H1s : list vl_stack) (H2 : list vl) (H2s : list vl_stack)
         (H20 : list vl),
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H1 H1s ->
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H2 H2s ->
       Pe lS (Def H1 (H2 ++ H20) (length H20)) (H1s, (H2s, length H20)))
=>
  fix F (s : stack vl_stack) (v : vl) (v0 : vl_stack) (e : equiv_val s v v0): Pv s v v0 :=
match e in (equiv_val s0 v1 v2) return (Pv s0 v1 v2) with
| equiv_const x x0 => fconst x x0
| equiv_abs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 x9 =>
  fabs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 (
         match x9 in (equiv_env s0 v1 v2) return (Pe s0 v1 v2) with
           | eqv_forall x x0 x1 x2 x3 x4 x5 x6 =>
             fenv x x0 x1 x2 x3 x4
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x0 x1 x5)
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x2 x3 x6)
         end)
end.

Inductive equiv_opt: stack vl_stack -> option (vl) -> option (vl_stack) -> Prop :=
| e_stuck : forall lS, equiv_opt lS None None
| e_val : forall lS v v_stack, equiv_val lS v v_stack -> equiv_opt lS (Some v) ((Some v_stack)).

Inductive equiv_res: stack vl_stack -> option (option vl) -> option (option vl_stack) -> Prop :=
| e_time : forall lS, equiv_res lS None None
| e_res : forall lS v v_stack, equiv_opt lS v v_stack -> equiv_res lS ((Some v)) ((Some v_stack)).

Definition get_fenv (vs : option (option vl_stack)) :=
  match vs with
  | Some (Some (vabs_stack h _ _ _ _)) => h
  | _ => []
  end.

Theorem teval_equiv : forall k n t env v lS lS' fr env_stack v_stack st,
     teval k env t n = v ->
     teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t n = (v_stack, st) ->

     equiv_env (fr::lS) env (env_stack,fr) ->
     fc_env env_stack -> sc_env (lS' ++ fr::lS) ->
     equiv_res st v v_stack.
