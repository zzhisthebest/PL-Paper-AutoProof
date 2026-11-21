Require Import Syntax Subtyping ViewpointAdaptation Helpers.

From Stdlib Require String.

From Stdlib Require Import List.

Import ListNotations.

Inductive CollectFields : class_table -> class_name -> list field_def -> Prop :=

  | CF_NotFound : forall CT C
      (Hnone : find_class CT C = None),
      CollectFields CT C []


  | CF_Object : forall CT C def
      (Hfind  : find_class CT C = Some def)
      (Hsuper : super (signature def) = None),
      CollectFields CT C []


  | CF_Inherit : forall CT C def parent parent_fields own_fields
      (Hfind        : find_class CT C = Some def)
      (Hsuper       : super (signature def) = Some parent)
      (Hparent_cf   : CollectFields CT parent parent_fields)
      (Hown_fields  : own_fields = Syntax.fields (body def)),
      CollectFields CT C (parent_fields ++ own_fields).

Inductive FieldLookup : class_table -> class_name -> var -> field_def -> Prop :=
  | FL_Found : forall CT C fields f fdef
      (Hcf  : CollectFields CT C fields)
      (Hget : gget fields f = Some fdef),
      FieldLookup CT C f fdef.

Definition sf_def_rel (CT: class_table) (C: class_name) (f: var) (fdef: field_def) : Prop :=
  FieldLookup CT C f fdef.

Definition sf_assignability_rel (CT: class_table) (C: class_name) (f: var) (a: a) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ assignability (ftype fdef) = a.

Definition sf_mutability_rel (CT: class_table) (C: class_name) (f: var) (qf: q_f) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ mutability (ftype fdef) = qf.

Definition constructor_def_lookup (CT : class_table) (C : class_name) : option constructor_def :=
  match find_class CT C with
  | Some def => Some (constructor (body def))
  | None => None
  end.

Definition constructor_sig_lookup (CT : class_table) (C : class_name) : option constructor_sig :=
  match constructor_def_lookup CT C with
  | Some ctor => Some (csignature ctor)
  | None => None
  end.

Definition eq_method_name (m1 m2 : method_name) : bool :=
  match m1, m2 with
  | n1, n2 => Nat.eqb n1 n2
  end.

Definition gget_method (methods : list method_def) (m : method_name) : option method_def :=
  find (fun mdef => eq_method_name (mname (msignature mdef)) m) methods.

Definition override (parent_methods own_methods : list method_def) : list method_def :=
  own_methods ++ filter (fun pmdef =>
    negb (existsb (fun omdef =>
      eq_method_name (mname (msignature pmdef)) (mname (msignature omdef)))
    own_methods)) parent_methods.

Inductive CollectMethods : class_table -> class_name -> list method_def -> Prop :=

  | CM_NotFound : forall CT C
      (Hnone : find_class CT C = None),
      CollectMethods CT C []


  | CM_Object : forall CT C def
      (Hfind  : find_class CT C = Some def)
      (Hsuper : super (signature def) = None)
      (Hdom   : C < dom CT),
      CollectMethods CT C (methods (body def))


  | CM_Inherit : forall CT C def parent parent_methods own_methods merged
      (Hfind          : find_class CT C = Some def)
      (Hsuper         : super (signature def) = Some parent)
      (Hdom_C         : C < dom CT)
      (Hdom_parent    : parent < dom CT)
      (Hordering      : cname (signature def) > parent)
      (Hparent_cm     : CollectMethods CT parent parent_methods)
      (Hown_methods   : own_methods = methods (body def))
      (Hmerged        : merged = override parent_methods own_methods),
      CollectMethods CT C merged.

Definition wf_stypeuse (CT : class_table) (q_use: q) (c: class_name) : Prop :=
  match bound CT c with
  | Some q_bound =>



                  q_subtype (vpa_mutability_bound q_use q_bound) q_use /\
                   c < dom CT
  | None => False
  end.

Definition qf2q (qf : q_f) : q :=
  match qf with
  | Mut_f => Mut
  | Imm_f => Imm
  | RDM_f => RDM
  | RO_f => RO
  end.

Definition wf_field (CT : class_table) (fdef: field_def) : Prop :=
  wf_stypeuse CT (qf2q (mutability (ftype fdef)))
    (f_base_type (ftype fdef)).

Definition wf_senv (CT : class_table) (sΓ : s_env) : Prop :=

  dom sΓ > 0 /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) sΓ.

Inductive FindMethodWithName : class_table -> class_name -> method_name -> method_def -> Prop :=

  | FOM_Here : forall CT C def own_methods m mdef
      (Hfind       : find_class CT C = Some def)
      (Hown        : own_methods = methods (body def))
      (Hget_method : gget_method own_methods m = Some mdef),
      FindMethodWithName CT C m mdef


  | FOM_Super : forall CT C def parent m mdef own_methods
      (Hfind       : find_class CT C = Some def)
      (Hown        : own_methods = methods (body def))
      (Hnot_here   : gget_method own_methods m = None)
      (Hsuper      : super (signature def) = Some parent)
      (Hparent_fmn : FindMethodWithName CT parent m mdef),
      FindMethodWithName CT C m mdef.

Inductive expr_has_type : class_table -> s_env -> method_scope -> expr -> qualified_type -> Prop :=


  | ET_Null : forall CT Γ mt q class_name
      (Hwf  : wf_senv CT Γ)
      (Hdom : class_name < dom CT),
      expr_has_type CT Γ mt ENull (Build_qualified_type q class_name)


  | ET_Var : forall CT Γ mt x T
      (Hwf  : wf_senv CT Γ)
      (Hget : static_getType Γ x = Some T),
      expr_has_type CT Γ mt (EVar x) T


  | ET_Field_abstract_state : forall CT Γ mt x T fDef f
      (Hwf      : wf_senv CT Γ)
      (Hget_x   : static_getType Γ x = Some T)
      (Hfld_def : sf_def_rel CT (sctype T) f fDef)
      (Hmt      : mt = AbstractState \/ mt = ConcreteState),
      expr_has_type CT Γ mt (EField x f)
        (Build_qualified_type
          (vpa_mutability_stype_fld_abstract_state (sqtype T) (mutability (ftype fDef)))
          (f_base_type (ftype fDef)))


  | ET_Field_readonly_state : forall CT Γ mt x T fDef f
      (Hwf      : wf_senv CT Γ)
      (Hget_x   : static_getType Γ x = Some T)
      (Hfld_def : sf_def_rel CT (sctype T) f fDef)
      (Hmt      : mt = ReadonlyState \/ mt = TransitiveState),
      expr_has_type CT Γ mt (EField x f)
        (Build_qualified_type
          (vpa_mutability_stype_fld_readonly_state (sqtype T) (mutability (ftype fDef)))
          (f_base_type (ftype fDef)))
.

Definition qc2q (qi : q_c) : q :=
  match qi with
    | RDM_c => RDM
    | Imm_c => Imm
    | Mut_c => Mut
    end.

Definition vpa_mutability_constructor_param (qc : q_c) (T : qualified_type) : qualified_type :=
  Build_qualified_type
    (vpa_mutability_qq_abstract_state (qc2q qc) (sqtype T))
    (sctype T).

Definition vpa_mutability_override (qc : q_c) (T : qualified_type) : qualified_type :=
  Build_qualified_type
    (vpa_mutability_qq_abstract_state (qc2q qc) (sqtype T))
    (sctype T).

Definition method_override_compatible
    (CT : class_table) (qc : q_c)
    (overrider overridden : method_sig) : Prop :=
  mname overrider = mname overridden /\
  mscope overrider = mscope overridden /\
  qualified_type_subtype CT
    (mret overrider)
    (vpa_mutability_override qc (mret overridden)) /\
  Forall2
    (fun overridden_param overrider_param =>
      qualified_type_subtype CT
        (vpa_mutability_override qc overridden_param)
        overrider_param)
    (mparams overridden) (mparams overrider) /\
  q_subtype
    (sqtype (vpa_mutability_override qc (mreceiver overridden)))
    (sqtype (mreceiver overrider)).

Inductive method_signature_refinement
    (CT : class_table) : method_sig -> method_sig -> Prop :=
  | msr_refl : forall msig,
      method_signature_refinement CT msig msig
  | msr_override : forall qc overrider overridden,
      bound CT (sctype (mreceiver overrider)) = Some qc ->
      base_subtype CT
        (sctype (mreceiver overrider))
        (sctype (mreceiver overridden)) ->
      wf_senv CT (mreceiver overrider :: mparams overrider) ->
      method_override_compatible CT qc overrider overridden ->
      method_signature_refinement CT overrider overridden
  | msr_trans : forall child middle parent,
      method_signature_refinement CT child middle ->
      method_signature_refinement CT middle parent ->
      method_signature_refinement CT child parent.

Definition is_nonmutable_qualifier (qualifier : q) : Prop :=
  qualifier = RO \/ qualifier = Lost \/ qualifier = RDM \/ qualifier = Imm.

Definition signature_has_no_mutable_roots (msig : method_sig) : Prop :=
  is_nonmutable_qualifier (sqtype (mreceiver msig)) /\
  Forall
    (fun T => is_nonmutable_qualifier (sqtype T))
    (mparams msig).

Definition get_this_qualified_type (sΓ : s_env) : option qualified_type :=
  match sΓ with
  | [] => None
  | T_this :: _ =>
      Some T_this
  end.

Inductive stmt_typing : class_table -> s_env -> method_scope -> stmt -> s_env -> Prop :=

  | ST_Skip : forall CT sΓ mt
      (Hwf : wf_senv CT sΓ),
      stmt_typing CT sΓ mt SSkip sΓ


  | ST_Local : forall CT sΓ mt T x sΓ'
      (Hwf       : wf_senv CT sΓ)
      (Hwf_T     : wf_stypeuse CT (sqtype T) (sctype T))
      (Hnone     : static_getType sΓ x = None)
      (Henv'     : sΓ' = sΓ ++ [T])
      (Hget_x    : static_getType sΓ' x = Some T),
      stmt_typing CT sΓ mt (SLocal T x) sΓ'


  | ST_VarAss : forall CT sΓ mt x e Te Tthis Tx
      (Hwf      : wf_senv CT sΓ)
      (Htype_e  : expr_has_type CT sΓ mt e Te)
      (Hthis    : get_this_qualified_type sΓ = Some Tthis)
      (Hnot_rcv : x <> 0)
      (Hget_x   : static_getType sΓ x = Some Tx)
      (Hsub     : qualified_type_subtype CT Te Tx),
      stmt_typing CT sΓ mt (SVarAss x e) sΓ


  | ST_FldWrite_abstract_state : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_abstract_state (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ AbstractState (SFldWrite x f y) sΓ


  | ST_FldWrite_concrete_state : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_abstract_state (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability_cs_ts (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ ConcreteState (SFldWrite x f y) sΓ


  | ST_FldWrite_readonly_state : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_readonly_state (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ ReadonlyState (SFldWrite x f y) sΓ


  | ST_FldWrite_transitive_state : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_readonly_state (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability_cs_ts (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ TransitiveState (SFldWrite x f y) sΓ


  | S_New : forall CT sΓ mt x Tx (qc:q_c) C args argtypes Tthis consig
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hconsig     : constructor_sig_lookup CT C = Some consig)
      (Hnot_rcv    : x <> 0)
      (Hqc         : vpa_mutability_bound (qc2q qc) (cqualifier consig) = qc2q qc)
      (Harg_sub    : Forall2 (fun arg T => qualified_type_subtype CT arg T)
                       argtypes (map (vpa_mutability_constructor_param qc) consig.(cparams)))
      (Hresult_sub : qualified_type_subtype CT (Build_qualified_type (qc2q qc) C) Tx),
      stmt_typing CT sΓ mt (SNew x qc C args) sΓ


  | ST_Call : forall CT sΓ mt x m y args argtypes Tthis Tx Ty mdef
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfind_m     : FindMethodWithName CT (sctype Ty) m mdef)
      (Hnot_rcv    : x <> 0)
      (Hret_sub    : qualified_type_subtype CT (vpa_mutability_tt_abstract_state Ty (mret (msignature mdef))) Tx)
      (Hrcv_sub    : qualified_type_subtype CT Ty
                       (vpa_mutability_tt_abstract_state Ty
                         (mreceiver (msignature mdef)))
                     \/ (sqtype Ty = RO /\
                         mdef.(msignature).(mreceiver).(sqtype) = RDM /\
                         base_subtype CT (sctype Ty)
                           mdef.(msignature).(mreceiver).(sctype)))
      (Harg_sub    : Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_mutability_tt_abstract_state Ty T))
                       argtypes (mparams (msignature mdef)))
      (Hscope      : mt = AbstractState \/
                     (mt = ConcreteState /\ method_scope_subtype mdef.(msignature).(mscope) ConcreteState)),
      stmt_typing CT sΓ mt (SCall x m y args) sΓ


  | ST_Call_readonly_state : forall CT sΓ mt x m y args argtypes Tthis Tx Ty mdef
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfind_m     : FindMethodWithName CT (sctype Ty) m mdef)
      (Hnot_rcv    : x <> 0)
      (Hmt_not_abs : mdef.(msignature).(mscope) <> AbstractState)
      (Hmt_not_cs  : mdef.(msignature).(mscope) <> ConcreteState)
      (Hret_sub    : qualified_type_subtype CT (vpa_mutability_tt_readonly_state Ty (mret (msignature mdef))) Tx)
      (Hrcv_sub    : qualified_type_subtype CT Ty
                       (vpa_mutability_tt_readonly_state Ty
                         (mreceiver (msignature mdef)))
                     \/ (sqtype Ty = RO /\
                         mdef.(msignature).(mreceiver).(sqtype) = RDM /\
                         base_subtype CT (sctype Ty)
                           mdef.(msignature).(mreceiver).(sctype)))
      (Harg_sub    : Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_mutability_tt_readonly_state Ty T))
                       argtypes (mparams (msignature mdef)))
      (Hmt_not_abs2 : mt <> AbstractState)
      (Hmt_not_cs2  : mt <> ConcreteState)
      (Hmt_sub     : method_scope_subtype mdef.(msignature).(mscope) mt),
      stmt_typing CT sΓ mt (SCall x m y args) sΓ


  | ST_Seq : forall CT sΓ mt s1 sΓ' s2 sΓ''
      (Hwf    : wf_senv CT sΓ)
      (Htype1 : stmt_typing CT sΓ mt s1 sΓ')
      (Htype2 : stmt_typing CT sΓ' mt s2 sΓ''),
      stmt_typing CT sΓ mt (SSeq s1 s2) sΓ''
.

Definition wf_constructor_object (CT : class_table) (C : class_name) (ctor : constructor_def) : Prop :=
  parent_lookup CT C = None /\
  constructor_def_lookup CT C = Some ctor /\
  let sig := csignature ctor in
  let q_c := cqualifier sig in
  Some q_c = bound CT C /\
  cparams sig = [] /\
  CollectFields CT C [].

Definition wf_constructor (CT : class_table) (c : class_name) (ctor : constructor_sig) : Prop :=

  bound CT c = Some (cqualifier ctor) /\


  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (cparams ctor) /\


  exists field_defs,
    CollectFields CT c field_defs /\
    length (cparams ctor) = length field_defs /\


  Forall2 (fun param_type field_def =>
    qualified_type_subtype CT
      (vpa_mutability_constructor_param (cqualifier ctor) param_type)
      {| sqtype := vpa_mutability_constructor_fld (cqualifier ctor) (mutability (ftype field_def));
         sctype := f_base_type (ftype field_def) |})
    (cparams ctor) field_defs.

Definition wf_method (CT : class_table) (C : class_name) (mdef : method_def) : Prop :=
  let mscope := mdef.(msignature).(mscope) in
  let msig := msignature mdef in
  let methodbody := mbody mdef in
  let mbodystmt := mbody_stmt methodbody in
  let sΓ := msig.(mreceiver) :: msig.(mparams) in
  wf_stypeuse CT (sqtype (mret msig)) (sctype (mret msig)) /\
  exists sΓ' mbodyrettype,
    stmt_typing CT sΓ mscope mbodystmt sΓ' /\
    let mbodyretvar := mreturn methodbody in
    mbodyretvar < dom sΓ' /\
    nth_error sΓ' mbodyretvar = Some mbodyrettype /\
    qualified_type_subtype CT mbodyrettype (mret msig) /\
    (forall parent_def parent mdef_parent qc,
      find_class CT C = Some parent_def ->
      super (signature parent_def) = Some parent ->
      bound CT C = Some qc ->
      FindMethodWithName CT parent (mname msig) mdef_parent ->
      method_override_compatible CT qc msig (msignature mdef_parent)) /\
    sctype (mreceiver msig) = C /\
    (readonly_state_method_scope mscope ->
      signature_has_no_mutable_roots msig).

Inductive wf_class : class_table -> class_def -> Prop :=


| WFObjectDef : forall CT cdef class_name
    (Hno_super    : cdef.(signature).(super) = None)
    (Hrdm         : cdef.(signature).(class_qualifier) = RDM_c)
    (Hno_fields   : cdef.(body).(Syntax.fields) = [])
    (Hno_methods  : cdef.(body).(methods) = [])
    (Hcname       : cdef.(signature).(cname) = class_name)
    (Hwf_ctor     : wf_constructor_object CT class_name cdef.(body).(constructor))
    (Hwf_fields   : Forall (wf_field CT) cdef.(body).(Syntax.fields))
    (Hnodup       : NoDup (map (fun mdef => mname (msignature mdef)) cdef.(body).(methods))),
    wf_class CT cdef


| WFOtherDef : forall CT cdef superC thisC
    (Hsuper    : cdef.(signature).(super) = Some superC)
    (Hcname    : cdef.(signature).(cname) = thisC)
    (Hordering : thisC > superC),
    let sig := cdef.(signature) in
    let bod := cdef.(body) in
    let C := cname sig in
    let qC := class_qualifier sig in
    (wf_constructor CT C (csignature (constructor bod)) /\
    Forall (wf_method CT C) (methods bod) /\
    NoDup (map (fun mdef => mname (msignature mdef)) (methods bod)) /\
    match bound CT superC with
    | Some q_super =>
        exists fs, CollectFields CT C fs /\
        (qC = q_super \/ q_super = RDM_c) /\
        Forall (wf_field CT) fs
    | None =>
        CollectFields CT C []
    end) ->
    wf_class CT cdef
.

Definition wf_class_table (CT : class_table) : Prop :=
  let object_class_at_zero :=
    exists obj_def, find_class CT 0 = Some obj_def /\
                    super (signature obj_def) = None in
  let non_object_classes_extend_object :=
    forall i def, i > 0 -> find_class CT i = Some def ->
                  super (signature def) <> None in
  let class_name_matches_index :=
    forall i def, find_class CT i = Some def ->
                  cname (signature def) = i in
  Forall (wf_class CT) CT /\
  object_class_at_zero /\
  non_object_classes_extend_object /\
  class_name_matches_index.

Definition is_mut_or_ro (qualifier : q) : Prop :=
  qualifier = Mut \/ qualifier = RO.

Definition is_rdm_or_bot (qualifier : q) : Prop :=
  qualifier = RDM \/ qualifier = Bot.

Definition is_concrete_or_rdm_or_bot (qualifier : q) : Prop :=
  qualifier = Mut \/ qualifier = Imm \/ qualifier = RDM \/ qualifier = Bot.

Definition is_mut_or_bot (qualifier : q) : Prop :=
  qualifier = Mut \/ qualifier = Bot.

Definition is_imm_or_bot (qualifier : q) : Prop :=
  qualifier = Imm \/ qualifier = Bot.
