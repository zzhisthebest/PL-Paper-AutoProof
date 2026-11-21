Require Export stlc1.

Definition stack_frame (X : Type) := prod (list X) nat.

Definition stack (X : Type) := list (stack_frame X).

Definition heap (X : Type) := list X.

Definition env_stack (X : Type) := prod (heap X) (stack_frame X).

Inductive st_ptr : Type :=
| S0 : nat -> st_ptr
| Si : nat -> st_ptr
.

Inductive vl_stack : Type :=
| vbool_stack : bool -> vl_stack
| vabs_stack  : heap vl_stack -> st_ptr -> class -> tm -> class -> vl_stack
.

Definition venv_stack := env_stack vl_stack.

Definition index_heap {X : Type} (n : id) (l : env_stack X) : option X := index n (fst l).

Definition index_stack {X : Type} (n : id) (l : env_stack X) : option X :=
match l with
| (_, ([], _))          => None
| (_, (h, off)) => if off <=? n then index (n - off) h else None
end.

Section index_examples.

Let ts_0 := TBool.

Let ts_1 := TFun TBool First TBool Second.

Let ts_2 := TFun TBool Second TBool First.

Let ts_3 := TFun TBool Second TBool Second.

Let th_0 := TFun TBool First TBool First.

Let th_1 := TBool.

Let estack : env_stack ty := ([th_1; th_0], ([ts_3; ts_2; ts_1; ts_0], 2)).

End index_examples.

Definition lookup_stack {X : Type} (n : var) (h: heap X) (st : stack X) : option X :=
match n with
| V First i => index i h
| V Second i =>
  match st with
  | (fr,off)::_ => if off <=? i then index (i - off) fr else None
  | _ => None
  end
end.

Definition expand_env_stack {X : Type} (env : env_stack X) (x : X) (n : class) :=
match env, n with
| (h, (l,off)), First  => (x::h, (l,off))
| (h, (l,off)), Second =>  (h, (x::l, off))
end
.

Definition get_stack_frame {X : Type} (st : stack X) (ptr: st_ptr) :=
  match ptr with
    | S0 idx => Some (nil, idx)
    | Si idx =>  index idx st

end.

Inductive wf_val : class -> vl_stack -> Prop :=
| wf_val_const : forall bool c, wf_val c (vbool_stack bool)
| wf_val_closureF : forall tm vheap class idx retcl,
      fc_env vheap ->
      wf_val First (vabs_stack vheap (S0 idx) class tm retcl)
| wf_val_closureS : forall tm vheap class i retcl,
      fc_env vheap ->
      wf_val Second (vabs_stack vheap i class tm retcl)
with fc_env : heap vl_stack -> Prop :=
| heap_nil : fc_env []
| heap_cons : forall v vheap,
     wf_val First v ->
     fc_env vheap ->
     fc_env (v::vheap)
with sc_env : stack vl_stack -> Prop :=
| stack_nil : sc_env []
| stack_cons : forall vstack fr idx,
     sc_env vstack ->
     Forall(fun v => wf_val Second v) fr ->
     sc_env ((fr, idx)::vstack).

Inductive wf : class -> option (option vl_stack) -> Prop :=
| wf_opt : forall v c, wf_val c v -> wf c (Some (Some v))
| wf_timeout: forall c, wf c None
| wf_stuck: forall c, wf c (Some None)
.

Definition fc_val v := wf_val First v.

Definition bind_prod {X Y : Type} (vl : option X) (lS : Y) : option (X * Y) :=
  match vl with
  | None => None
  | Some v => Some (v, lS)
  end.

Fixpoint stack_split (st : stack vl_stack) (n : nat) : option (stack vl_stack * stack vl_stack) :=
  match st with
  | [] => None
  | fr::lS =>
    if length st =? n then Some ([], st)
    else match (stack_split lS n) with
    | None => None
    | Some (l1, l2) => Some (fr::l1, l2)
    end
  end.

Definition stack_split_opt (v : option (option (vl_stack * stack vl_stack))) (n : nat) :=
  match v with
  | None => None
  | Some None => Some None
  | Some (Some (v, st)) =>
    match stack_split st n with
    | None => Some None
    | Some (l1, l2) => Some (Some (v, l2))
    end
  end.

Fixpoint teval_stack (k : nat) (st_max : nat) (st_over : stack vl_stack)(env: heap vl_stack)(t: tm)(n: class){struct k}: (option (option vl_stack) * stack vl_stack) :=
  match k with
  | 0 => (None, st_over)
  | S k' =>
    match stack_split st_over st_max with
    | None => (Some None, st_over)
    | Some (_, st) =>
      match t, n with
      | ttrue, _ => (Some (Some (vbool_stack true)), st_over)
      | tfalse, _ => (Some (Some (vbool_stack false)), st_over)
      | tvar (V First i),  First  => (Some (lookup_stack (V First i) env st), st_over)
      | tvar (V Second i), First  => (Some None, st_over)
      | tvar i, Second        => (Some (lookup_stack i env st), st_over)
      | tabs m y retcl, First =>
                                    match st with
                                    | [] => (Some None, st_over)
                                    | (fr, idx)::_ => (Some (Some (vabs_stack env (S0 (idx + length fr)) m y retcl)), st_over)
                                    end
      | tabs m y retcl, Second      => match st with
                                      | [] => (Some None, st_over)
                                      | _::st1 =>
                                        (Some (Some (vabs_stack env (Si (length st1)) m y retcl)), st_over)
                                    end
      | tapp ef ex, _   =>
          match teval_stack k' st_max st_over env ef Second, n with
            | (None, _), _ => (None, st_over)
            | (Some None, _), _ => (Some None, st_over)
            | (Some (Some (vbool_stack _)), _), _ => (Some None, st_over)
            | (Some (Some (vabs_stack _ _ _ _ Second)), _), First => (Some None, st_over)
            | (Some (Some (vabs_stack env2 i m ey retcl)), st'), _ =>
              match teval_stack k' st_max st' env ex m with
                | (None, _) => (None, st_over)
                | (Some None, _) => (Some None, st_over)
                | (Some (Some vx), st'') =>
                  match get_stack_frame st' i with
                    | None => (Some None, st_over)
                    | Some fr =>
                      let (env',fr') := expand_env_stack (expand_env_stack (env2,fr) (vabs_stack env2 i m ey retcl) Second) vx m in
                      let frames := fr'::st'' in
                      let (v, st''') := teval_stack k' (length (frames)) frames env' ey retcl in
                      match (v, retcl) with
                      | (Some (Some v), Second) => (Some (Some v), st''')
                      | _ => (v, st_over)
                      end
                  end
              end
        end
      end
    end
  end.

Definition tid := (tabs Second (tvar (V Second 0)) Second).

Definition term := (tapp (tapp tid tid) tid).

Definition ssss : stack vl_stack := ([], 0) :: (@nil (stack_frame vl_stack)).

Definition with_st (res : option (option (vl_stack * stack vl_stack))) (st : stack vl_stack) :=
  match res with
  | None => None
  | Some None => Some None
  | Some (Some (v, s)) => Some (Some (v, st))
  end.

Definition mts := (@nil (stack_frame vl_stack)).
