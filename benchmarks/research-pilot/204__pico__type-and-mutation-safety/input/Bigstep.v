From Stdlib Require Import Lia.

From Stdlib Require Import List.

From Stdlib Require String.

Require Import Stdlib.Sets.Ensembles.

Require Import Stdlib.Classes.RelationClasses.

Import ListNotations.

Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers Reachability.

Definition get_this_var_mapping (vm : var_mapping) : option Loc :=
  match vm with
  | [] => None
  | ι :: _ =>
    match ι with
    | Null_a => None
    | Iot loc => Some loc
    end
  end.

Definition r_muttype (h: heap) (ι: Loc) : option q_r :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rqtype (rt_type o))
  end.

Definition r_basetype (h: heap) (ι: Loc) : option class_name :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rctype (rt_type o))
  end.

Definition r_type (h: heap) (ι: Loc) : option runtime_type :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rt_type o)
  end.

Definition update_field (h: heap) (ι: Loc) (f: var) (v: value) : heap :=
  match runtime_getObj h ι with
  | None => h
  | Some o =>
      let new_fields := update f v o.(fields_map) in
      let new_obj := (set_fields_map o (new_fields))
      in update ι new_obj h
  end.

Definition vpa_mutability_runtime_bound_agree (q1: q_r)(q2 : q_c) : bool :=
  match (q1, q2) with
    | (Imm_r, RDM_c) => true
    | (Mut_r, RDM_c) => true
    | (Imm_r, Imm_c) => true
    | (Mut_r, Mut_c) => true
    | (_, _) => false
    end.

Definition wf_rtypeuse (CT: class_table) (q: q_r) (c: class_name) : Prop :=
  match (bound CT c) with
  | None => False
  | Some q' => c < dom CT /\ vpa_mutability_runtime_bound_agree q q'
  end.

Definition qualifier_typable_context (qr: q_r) (qs: q) (qcontext: q_r): Prop :=
  match qr with
  | Imm_r =>
    match vpa_mutability_runtime qcontext qs with
    | Imm => True
    | RO => True
    | Lost => True
    | _ => False
    end
  | Mut_r =>
    match vpa_mutability_runtime qcontext qs with
    | Mut => True
    | RO => True
    | Lost => True
    | _ => False
    end
  end.

Definition qualifier_typable_heap (qr: q_r) (qs: q): Prop :=
  match qr with
  | Imm_r =>
    match qs with
    | Imm => True
    | RO => True
    | _ => False
    end
  | Mut_r =>
    match qs with
    | Mut => True
    | RO => True
    | _ => False
    end
  end.

Definition wf_obj (CT: class_table) (h: heap) (ι: Loc) : Prop :=
  match runtime_getObj h ι with
  | None => False
  | Some o =>

      wf_rtypeuse CT (rt_type o).(rqtype) (rt_type o).(rctype) /\

      exists field_defs, CollectFields CT (rt_type o).(rctype) field_defs /\
      List.length (fields_map o) = List.length field_defs /\
      Forall2 (fun v fdef =>
        match v with
        | Null_a => True
        | Iot loc =>
          match runtime_getObj h loc with
          | Some _ =>

            exists rqt, r_type h loc = Some rqt /\
            base_subtype CT (rctype rqt) (f_base_type (ftype fdef)) /\
            qualifier_typable_heap (rqtype rqt) (vpa_mutability_rec_fld (rqtype (rt_type o)) (mutability (ftype fdef)))
          | None => False
          end
        end) (fields_map o) field_defs
  end.

Definition wf_renv (CT: class_table) (rΓ: r_env) (h: heap) : Prop :=

  dom rΓ.(vars) > 0 /\
  (exists iot, get_this_var_mapping rΓ.(vars) = Some iot /\ iot < dom h) /\
  Forall (fun value =>
    match value with
    | Null_a => True
    | Iot loc =>
        match runtime_getObj h loc with
        | None => False
        | Some _ => True
        end
    end) rΓ.(vars).

Definition wf_heap (CT: class_table) (h: heap) : Prop :=
    forall (ι : Loc),
    ι < (List.length h) ->
    wf_obj CT h ι.

Definition wf_r_typable (CT: class_table) (h: heap) (ι: Loc)
  (sqt: qualified_type) (qcontext: q_r) : Prop :=
  match r_type h ι with
  | Some rqt =>
      base_subtype CT (rctype rqt) (sctype sqt) /\
      qualifier_typable_context (rqtype rqt) (sqtype sqt) qcontext
  | _ => False
  end.

Definition wf_r_config (CT: class_table) (sΓ: s_env) (rΓ: r_env) (h: heap) : Prop :=

  wf_class_table CT /\

  wf_heap CT h /\

  wf_renv CT rΓ h /\

  wf_senv CT sΓ /\

  List.length sΓ = List.length rΓ.(vars) /\
  forall ι qcontext,
  get_this_var_mapping (vars rΓ) = Some ι ->
  (r_muttype h ι) = Some qcontext ->
  forall i, i < List.length sΓ ->
  forall sqt,

    nth_error sΓ i = Some sqt ->
    match runtime_getVal rΓ i with
    | Some (Iot loc) => wf_r_typable CT h loc sqt qcontext
    | Some Null_a => True
    | None => False
    end.

Inductive eval_result :=
| OK : eval_result
| MUTATIONEXP: eval_result
| NPE : eval_result.

Definition runtime_vpa_assignability (q1: q_r) (a1: a) : a :=
  match q1, a1 with
    | _, Assignable => Assignable
    | Mut_r, RDA => Assignable
    | _, _ => Final
  end.

Definition reachable_locations_from_initial_env
  (h : heap) (rΓ : r_env) : Ensembles.Ensemble Loc :=
  fun l_target =>
    exists x l_root ,
      runtime_getVal rΓ x = Some (Iot l_root) /\
      reachable h l_root l_target.

Inductive eval_expr : class_table -> r_env -> heap -> expr -> value -> eval_result -> r_env -> heap -> Prop :=

  | EBS_Null : forall CT rΓ h,
      eval_expr CT rΓ h ENull Null_a OK rΓ h


  | EBS_Val : forall CT rΓ h x v
      (Hval : runtime_getVal rΓ x = Some v),
      eval_expr CT rΓ h (EVar x) v OK rΓ h


  | EBS_Field : forall CT rΓ h x f v o v1
      (Hval   : runtime_getVal rΓ x = Some (Iot v))
      (Hobj   : runtime_getObj h v = Some o)
      (Hfield : getVal o.(fields_map) f = Some v1),
      eval_expr CT rΓ h (EField x f) v1 OK rΓ h


  | EBS_Field_NPE : forall CT rΓ h x f
      (Hnull : runtime_getVal rΓ x = Some (Null_a)),
      eval_expr CT rΓ h (EField x f) Null_a NPE rΓ h
  .

Inductive eval_stmt : class_table -> r_env -> heap -> stmt -> eval_result -> r_env -> heap -> Prop :=

  | SBS_Skip : forall CT rΓ h,
      eval_stmt CT rΓ h SSkip OK rΓ h


  | SBS_Local : forall CT rΓ h T x
      (Hnone : runtime_getVal rΓ x = None),
      eval_stmt CT rΓ h (SLocal T x) OK
      (set_vars rΓ (rΓ.(vars)++[Null_a]) )
      h


  | SBS_Assign : forall CT rΓ h x e v1 v2
      (Hval   : runtime_getVal rΓ x = Some v1)
      (Heval  : eval_expr CT rΓ h e v2 OK rΓ h),
      eval_stmt CT rΓ h (SVarAss x e) OK
      (set_vars rΓ (update x v2 rΓ.(vars)))
      h

  | SBS_Assign_NPE : forall CT rΓ h x e v1 v2
      (Hval   : runtime_getVal rΓ x = Some v1)
      (Heval  : eval_expr CT rΓ h e v2 NPE rΓ h),
      eval_stmt CT rΓ h (SVarAss x e) NPE
      rΓ
      h


  | SBS_FldWrite : forall CT rΓ h x f y loc_x o a vf val_y h'
      (Hval_x  : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hobj    : runtime_getObj h loc_x = Some o)
      (Hfield  : getVal o.(fields_map) f = Some vf)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
      (Hval_y  : runtime_getVal rΓ y = Some val_y)
      (Hruntime_assignable : runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable)
      (Hupdate : h' = update_field h loc_x f val_y),
      eval_stmt CT rΓ h (SFldWrite x f y) OK rΓ h'


  | SBS_FldWrite_NPE : forall CT rΓ h x f y
      (Hnull : runtime_getVal rΓ x = Some (Null_a)),
      eval_stmt CT rΓ h (SFldWrite x f y) NPE rΓ h

  | SBS_FldWrite_MUTATIONEXP : forall CT rΓ h x f y loc_x o a vf val_y
      (Hval_x  : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hobj    : runtime_getObj h loc_x = Some o)
      (Hfield  : getVal o.(fields_map) f = Some vf)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
      (Hval_y  : runtime_getVal rΓ y = Some val_y)
      (Hfinal  : runtime_vpa_assignability (rqtype (rt_type o)) a = Final),
      eval_stmt CT rΓ h (SFldWrite x f y) MUTATIONEXP rΓ h


  | SBS_New : forall CT rΓ h x (q_c:q_c) c ys l1 qthisr vals o qadapted rΓ' h'
      (Hthis    : runtime_getVal rΓ 0 = Some (Iot l1))
      (Hargs    : runtime_lookup_list rΓ ys = Some vals)
      (Hmut     : r_muttype h l1 = Some qthisr)
      (Hadapt   : vpa_mutability_object_creation qthisr q_c = qadapted)
      (Hobj     : o = mkObj (mkruntime_type qadapted c) (vals))
      (Hheap    : h' = h++[o])
      (Henv     : rΓ' = (set_vars rΓ (update x (Iot (dom h)) rΓ.(vars)))),
      eval_stmt CT rΓ h (SNew x q_c c ys) OK rΓ' h'


  | SBS_Call : forall CT rΓ h x y m zs vals ly cy mdef mbody mstmt mret retval h' rΓ' rΓ'' rΓ'''
      (Hval_y      : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase       : r_basetype h ly = Some cy)
      (Hfind       : FindMethodWithName CT cy m mdef /\ mbody = Syntax.mbody mdef)
      (Hstmt       : mstmt = mbody.(mbody_stmt))
      (Hret        : mret = mbody.(mreturn))
      (Hargs       : runtime_lookup_list rΓ zs = Some vals)
      (Hframe      : rΓ' = mkr_env (Iot ly :: vals))
      (Heval_body  : eval_stmt CT rΓ' h mstmt OK rΓ'' h')
      (Hretval     : runtime_getVal rΓ'' mret = Some retval)
      (Henv        : rΓ''' = (set_vars rΓ (update x retval rΓ.(vars)))),
      eval_stmt CT rΓ h (SCall x m y zs) OK rΓ''' h'


  | SBS_Call_NPE : forall CT rΓ h x y m zs
      (Hnull : runtime_getVal rΓ y = Some (Null_a)),
      eval_stmt CT rΓ h (SCall x m y zs) NPE rΓ h

  | SBS_Call_NPE_Body : forall CT rΓ h x y m zs vals ly cy mdef mbody mstmt mret h' rΓ' rΓ''
      (Hval_y     : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase      : r_basetype h ly = Some cy)
      (Hfind      : FindMethodWithName CT cy m mdef /\ mbody = Syntax.mbody mdef)
      (Hstmt      : mstmt = mbody.(mbody_stmt))
      (Hret       : mret = mbody.(mreturn))
      (Hargs      : runtime_lookup_list rΓ zs = Some vals)
      (Hframe     : rΓ' = mkr_env (Iot ly :: vals))
      (Heval_body : eval_stmt CT rΓ' h mstmt NPE rΓ'' h'),
      eval_stmt CT rΓ h (SCall x m y zs) NPE rΓ'' h'

  | SBS_Call_MUTATIONEXP_Body : forall CT rΓ h x y m zs vals ly cy mdef mbody mstmt mret h' rΓ' rΓ''
      (Hval_y     : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase      : r_basetype h ly = Some cy)
      (Hfind      : FindMethodWithName CT cy m mdef /\ mbody = Syntax.mbody mdef)
      (Hstmt      : mstmt = mbody.(mbody_stmt))
      (Hret       : mret = mbody.(mreturn))
      (Hargs      : runtime_lookup_list rΓ zs = Some vals)
      (Hframe     : rΓ' = mkr_env (Iot ly :: vals))
      (Heval_body : eval_stmt CT rΓ' h mstmt MUTATIONEXP rΓ'' h'),
      eval_stmt CT rΓ h (SCall x m y zs) MUTATIONEXP rΓ'' h'

  | SBS_Seq : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt CT rΓ h s1 OK rΓ' h')
      (Heval2 : eval_stmt CT rΓ' h' s2 OK rΓ'' h''),
      eval_stmt CT rΓ h (SSeq s1 s2) OK rΓ'' h''

  | SBS_Seq_NPE_first : forall CT rΓ h s1 s2 rΓ' h'
      (Heval1 : eval_stmt CT rΓ h s1 NPE rΓ' h'),
      eval_stmt CT rΓ h (SSeq s1 s2) NPE rΓ' h'

  | SBS_Seq_NPE_second : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt CT rΓ h s1 OK rΓ' h')
      (Heval2 : eval_stmt CT rΓ' h' s2 NPE rΓ'' h''),
      eval_stmt CT rΓ h (SSeq s1 s2) NPE rΓ'' h''

  | SBS_Seq_MUTATIONEXP_first : forall CT rΓ h s1 s2 rΓ' h'
      (Heval1 : eval_stmt CT rΓ h s1 MUTATIONEXP rΓ' h'),
      eval_stmt CT rΓ h (SSeq s1 s2) MUTATIONEXP rΓ' h'

  | SBS_Seq_MUTATIONEXP_second : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt CT rΓ h s1 OK rΓ' h')
      (Heval2 : eval_stmt CT rΓ' h' s2 MUTATIONEXP rΓ'' h''),
      eval_stmt CT rΓ h (SSeq s1 s2) MUTATIONEXP rΓ'' h''
  .
