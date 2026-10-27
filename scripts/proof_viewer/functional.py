"""Functional classification for the five additional archived cases.

Definitions are anchored per language. Lemmas are routed by the objects in
their statements, especially the conclusion, not by spelling of lemma names.
This is navigation metadata, not a claim about proof correctness.
"""
import re

PROOFS = {'Lemma', 'Theorem', 'Corollary', 'Proposition'}

COMMON = {
    'syntax': '''atom ty tm open_rec open open_ty_rec open_ty open_tm_rec open_tm
        open_tm_ty_rec open_tm_ty ty_subst tm_ty_subst tm_subst lc_ty_at
        locally_closed_ty lc_tm_at locally_closed_tm lc_at locally_closed''',
    'infra': 'context ty_context lookup_context empty update',
    'typing': 'wf_ty has_type subtype',
    'operational': 'value numeric_value numeral step multi evaluates',
    'target': 'strongly_normalizing normalization polymorphic_identity_theorem_for_free type_safety noninterference',
}

DEFINITIONS = {
 '004': {
    'syntax': '''fvs subst_f lc fvars subst subst_env fv occurs max_fvar subst_tm
        subst_all lcb lc_env env_lc lc_b ids rho_id''',
    'infra': '''max_list extend list_max fresh sum_list env_update max_atom_list
        maxlist extend_rho update_subst subst_update update_tm upd update_env
        cons_env cons_tm max_atom''',
    'operational': '''fstep neutral not_val_form valueb step_inv value_dec
        is_abs not_abs non_abs contra_value_step contra_abs_step ns_all val_shape''',
    'lr': '''V E sem_env C env_ok CR CR_ok R LR env_sat ctx_ok value_cond
        valuation env_match R_env env_sem RR rel sem env_rel sem_ctx''',
    'target': 'sn_f sn',
 },
 '034': {
    'syntax': '''ftv_ty ftv_tm fvars_tm no_ftv_ty no_ftv_tm closed_ty closed_tm
        tysub tmsub ty_subst_env tm_subst_env ctx_ftv tm_subst_all erase erased lc
        etm eopen_rec eopen esubst fta tm_fv tm_occ etm_fv eocc subst_tm fv_tm fv_ty
        fv_context utm uopen_rec uopen usubst usubst_all FV_tm FV_ty
        sktm sk open_sk_rec open_sk sksubst lc_sk_at lc_sk ty_bound ty_free free_sk
        tm_fvars ty_fvars ctx_fvars canon tsubst_ty tsubst_tm subst_env
        ut open_ut_rec open_ut subst_ut free_ut lc_ut_at lc_ut free_ty free_gamma
        fvars_ty subst_all erase_tm fvars_context open_e_rec open_e subst_e fv_e lc_e_at lc_e use_ih E''',
    'infra': '''list_max fresh_atom extend_ty extend_tm max_list fresh extend_sigma
        insert_rel upd_b bcons eupd incl_atoms xi_upd upd_tau upd_env replace_at
        update_ut update_sigma max_atom_list cons_env set_env update_rho consB updB updA''',
    'operational': '''e_numeric_value ev_value estep value_form neutral unum
        uvalue unumeral ustep umulti numeric_sk value_sk sstep stuck_sk
        numeric_ut value_ut numeral_ut is_nat is_val natrec_result evalue numeric_value_e numeral_e''',
    'lr': '''LR SemTy C_ty sem_nat sem_arrow sem_ty cand candidate no_cand Vt Rt
        candidate_rho candidates_env cand_xi Rel top nth_rel cand_stack R sem_ctx
        default_cand sn_cand rho_valid db_valid nth_cand C env benv is_cand R_cand
        top_cand Cand good_cand env_good xi_good mk_cand nat_cand arrow_V arrow_cand
        cons_cand interp cand_equiv insert_cand all_cand R_ty term_env IsCand lr cand_val env_rel''',
    'target': 'SN eSN sn usn SN_sk SN_ut sn_e',
 },
 '055': {
    'syntax': '''fv_ty fv_tm_ann context_fv tsubst subst_all ty_apply tm_apply free_ty
        free_ty_tm free_tm_tm free_ty_ctx fv_tm fv_tm_ty fv_context ty_subst_env
        tm_ty_subst_env tm_subst_env apply_env fvs_ty fvs_tm subst_map tsub trel
        fta_ty fta_tm ftv_tm fbv_ty subst_ty_env subst_tm_ty_env subst_tm_env
        fta_context ty_fv tm_fv tm_ty_fv ctx_ty_fv fvs_context ty_subst_all
        tm_ty_subst_all tm_subst_all fvars_tm ctx_fv norm_ty norm_tm ty_atoms tm_atoms
        closed_tyenv ty_size L_ok close ctx_fv_ty ty_fvars tm_fvars tm_ty_fvars ctx_ty_fvars
        tysubst id_ty id_tm size_ty atoms_ty atoms_tm ctx_atoms ctx_vars tysub
        tmsubst_ty tmsubst_fv idty lc_ty lc_tm free_ty_vars_ty free_ty_vars_tm
        free_tm_vars context_free_ty_vars context_dom inst atoms_context
        ty_inst tm_ty_inst tm_rho_inst fv_ctx''',
    'infra': '''max_list fresh_from tvar_update tmenv_update fresh upd tyenv tmenv
        upd_tm extend_ty extend_tm fresh_atom update_sub update_tyenv update_tmenv
        set_at_rel max_atom_list insert_at update_sigma update_xi update_theta
        tm_env ty_env upd_ty tenv extend replace_at lmax upd_rho''',
    'typing': 'ctx_wf',
    'lr': '''SemPred BEnv FEnv bshift bupd V R emp_rel VR VRV TR PRel lookup_rel
        benv_agree benv_pequiv env_rel VRel DefaultRel Adm E rel stack empty_stack
        push_stack set_stack empty_rho extend_rho V_ty E_ty RelTy TyRelEnv BRelEnv nth_rel
        Sem RelSem ValSem rel_iff envB_agree pred semty adm default_semty sem Rel bot_rel
        Vty Rty predenv extend_pred sem_ty bvar_env fvar_env extend_b upd_b upd_f C upd_rel
        rel_bot E_def pty pfv rstack Vb rels_agree_below rel_env value_rel env_value_rel
        rel_val erel env_equiv rho_equiv_on default_sem_ty nth_sem mk_sem sty upd_sem env_ok lvl''',
    'core': 'FundStmt',
 },
 '073': {
    'syntax': '''fv_ty fv_tm ftv_tm qualifier Pred_Ne Pred_Gt Pred_Ge Pred_Implies
        open_pred_tm_rec open_qualifier_tm_rec open_pred_tm open_qualifier_tm
        open_pred_ty_rec open_qualifier_ty_rec pred_subst qualifier_subst pred_ty_subst
        qualifier_ty_subst lc_pred_at lc_qualifier_at predicate_closed rty erase
        open_rty_tm_rec open_rty_tm open_rty_ty_rec open_rty_ty rty_subst rty_ty_subst
        lc_rty_at locally_closed_rty erase_context ty_tsubst tm_tsubst q_tsubst r_tsubst
        tm_msubst q_msubst r_msubst tm_subst_all q_subst_all r_subst_all fv_q ftv_q fv_r ftv_r
        fv_rcontext ftv_rcontext lc_tenv lc_menv rty_nodes tsubst qsubst ty_subst_atoms
        tm_ty_subst_atoms q_ty_subst_atoms rty_subst_env rty_ty_subst_atoms subst_all
        rty_subst_all rty_size closed_ty closed_sigma q_ftv q_fv rty_ftv rty_fv
        rcontext_fv qual_env rty_env fv_qual ftv_qual fv_rty ftv_rty subst_ty_d subst_tm_d
        subst_q_d ty_fsubst tm_fsubst qual_fsubst rty_fsubst ty_inst tm_inst qual_inst qinst
        lc_tm_ty lc_qual_ty tsubst_tm tysubst_ty tysubst_tm tsubst_qual tysubst_qual
        tsubst_rty tysubst_rty close_ty close_tm close_qual close_rty open_qualifier_ty
        rank tenv_good type_ok term_ok mty mtm mqual mrty lc_ty_any lc_tm_any keys_rcontext
        dom_rcontext sty stm squal srty lc_sigma lc_tau subst_env subst_pred_env erase_tm
        erase_pred closed_env ty_subst_env tm_ty_subst_env qual_ty_subst_env rty_ty_subst_env
        tysub_ok pred_ftv_nil pred_fv_nil subst_tm subst_ty subst_tm_ty subst_qual_tm
        subst_qual_ty subst_rty_tm subst_rty_ty lc0_tm lc0_ty lc0_tm_env lc0_ty_env size_rty
        RIntTrue RIntNeZero occurs_free atoms_rcontext fvs_rcontext ftvs_rcontext atoms_context id_tm id_ty env_ok_base''',
    'infra': '''max_atom fresh rcontext lookup_rcontext empty_rcontext update_rcontext
        tenv menv upd_tenv upd_menv env tyenv upd_tm upd_ty ty_env tm_env set_nth
        nth_ty_def nth_tm_def upd_te tcons tycons fresh2 concat_lists upd solve_incl_atom''',
    'typing': 'predicate_wf qualifier_wf wf_rty entails has_rtype',
    'core': 'Pfun P0fun',
    'operational': '''integer_operator eval_integer_operator predicate_multistep
        solve_contr solve_head_contra close_step_contra close_step_goal env_good''',
    'lr': '''atom_interpretation interpret_qualifier operational_atoms predicate_holds
        qualifier_holds value_shape semF sem valok shape semVf semV semT env_ok
        CV V ET envT_ok envM_ok qsem vty0 vty base_val Vf T satisfies_context
        cshape psem canon ctx_interp NotStuck Safe''',
    'target': 'safe safe_multi',
 },
 '100': {
    'infra': '''label flows_to join security wf_security security_le public secret
        protect_security max_list fresh_from env env_update env_id gamma_plug fresh
        extend flowb set_security extend_env upd solve_notin extend_rho id_rho flows_to_b
        max_atom update_env fresh_atom sum_list is_low list_max id_env sec_trans''',
    'syntax': '''security_of ty_protect subst fv closed erase_type erase_security
        program_context plug subst_env env_lc context_fv subst_all fv_context
        context_atoms fvsC ctx_atoms subst_rho fvs_context fv_ctx subst_atoms range_lc subst_fn''',
    'typing': 'context_wf context_has_type',
    'operational': 'protect_value sec_of_tm eval value_sec value_security top_security vsec',
    'lr': '''obs_sec W LRterm env_related low_annotated RV R env_rel VRp VR TR
        EnvRel IR Vp E V vis VpS ER hidden_at bound_at Rp value_rel term_rel ann val_rel interp''',
    'core': 'P',
    'target': '''ground transparent_at transparent same_result all_ir_low all_visible all_low
        all_ind_flows all_ir_flows nested_le all_indirect_flows all_ind_low all_sec_below''',
 },
}


def anchors(case):
    labels = {n: group for group, names in COMMON.items() for n in names.split()}
    for group, names in DEFINITIONS[case].items():
        labels.update({n: group for n in names.split()})
    return labels


WORD = re.compile(r"[^\W\d]\w*'?", re.UNICODE)


def statement(declaration):
    return re.split(r'\b(?:Proof|Admitted|Abort)\b', declaration['code'], maxsplit=1)[0]


def bound_names(text):
    """Names bound in common Rocq binder lists, not global definition names."""
    names = set()
    for m in re.finditer(r'\b(?:forall|exists|fun)\s+([^,:(){}]+)', text):
        names.update(WORD.findall(m[1]))
    for m in re.finditer(r"[({]\s*([\w\s']+)\s*:", text):
        names.update(WORD.findall(m[1]))
    return names


def conclusion(text):
    """Strip outer quantifiers and implications; keep nested premises intact."""
    depth, start, i = 0, 0, 0
    while i < len(text):
        char = text[i]
        if char in '({[':
            depth += 1
        elif char in ')}]':
            depth -= 1
        elif depth == 0:
            if char == ',':
                start = i+1
            elif text[i:i+2] == '->' and (i == 0 or text[i-1] not in '<-'):
                start = i+2
                i += 1
        i += 1
    return text[start:]


def infer_labels(declarations, case):
    labels = anchors(case)
    # Constructors/projections have the role of the definition introducing them.
    objects = dict(labels)
    objects.update({n: 'infra' for n in '''In incl nth nth_error length fold_right max
        Nat eqb list app map Forall exists_fresh nat S'''.split()})
    for d in declarations:
        if d['kind'] == 'Inductive':
            for name in re.findall(r'\|\s*([^\W\d]\w*)', d['code']):
                objects[name] = labels.get(d['name'], 'unknown')
        elif d['kind'] == 'Record':
            for name in re.findall(r'(?:\{|;)\s*([^\W\d]\w*)\s*:', d['code']):
                objects[name] = labels.get(d['name'], 'unknown')
    # A short LR name such as R or T is only a global here when that run
    # actually declares it. Never import an absent LR from another run.
    actual = {d['name'] for d in declarations if d['kind'] not in PROOFS}
    for name in list(objects):
        if name in labels and name not in actual:
            objects.pop(name)
    for d in declarations:
        name = d['name']
        if d['kind'] not in PROOFS:
            labels[name] = labels.get(name, 'unknown')
            continue
        if name in {'normalization', 'polymorphic_identity_theorem_for_free', 'never_stuck', 'type_safety', 'noninterference'}:
            labels[name] = 'target'
            continue
        text = statement(d)
        text = re.sub(r'^\s*\w+\s+'+re.escape(name)+r'\b', '', text, count=1)
        bound = bound_names(text)
        refs = set(WORD.findall(text))-bound
        goal = conclusion(text)
        goal_refs = set(WORD.findall(goal))-bound
        groups = {objects[n] for n in refs if n in objects}
        goal_groups = {objects[n] for n in goal_refs if n in objects}
        typing = 'typing' in groups or '|--' in text
        canonical = case == '073' and goal_refs & {'shape','canon','cshape','base_val','vty0','vty','value_shape','CV'}
        if typing and canonical:
            block = 'typing'
        elif 'core' in groups or (refs & {'has_type','has_rtype','subtype','entails'} or '|--' in text) and 'lr' in goal_groups:
            block = 'core'
        elif 'target' in goal_groups and 'lr' not in goal_groups:
            block = 'target'
        elif case == '100' and 'lr' in groups and 'lr' not in goal_groups and 'erase_security' in goal_refs and '=' in goal:
            block = 'target'
        elif 'lr' in groups:
            block = 'lr'
        elif typing:
            block = 'typing'
        elif 'operational' in groups or '-->' in text or '-->*' in text:
            block = 'operational'
        elif 'target' in groups:
            block = 'target'
        else:
            # Merely mentioning tm/ty in a binder does not make a generic
            # environment/list lemma a syntax lemma.
            substantive = refs-{'tm', 'ty', 'atom', 'etm', 'utm', 'ut', 'sktm', 'rty',
                                'qualifier', 'context', 'ty_context', 'rcontext'}
            cats = {objects[n] for n in substantive if n in objects}
            if 'syntax' in cats:
                block = 'syntax'
            elif 'infra' in cats or '=?' in text:
                block = 'infra'
            elif refs & {'tm', 'ty'}:
                block = 'syntax'
            else:
                block = 'unknown'
        labels[name] = block
    return labels
