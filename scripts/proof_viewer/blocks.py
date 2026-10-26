"""Reviewed functional labels for the 001 pilot, not a keyword classifier.

The lists record decisions made from the declarations in the 20 final files.
Unknown declarations stay unclassified. The original source is never rewritten.
"""
import re

BLOCKS = [
    ('infra', '通用基础设施', '名字、列表、映射与环境操作。'),
    ('syntax', 'Syntax', '语法、自由变量、打开、替换与局部封闭。'),
    ('operational', 'Operational semantics', 'value、归约、求值及执行过程的性质。'),
    ('typing', 'Typing', '类型判断及其性质，包括 typing 推出局部封闭。'),
    ('lr', '语义解释与 LR', 'LR、语义环境及其辅助引理；不含单独提取目标性质的桥接引理。'),
    ('core', '核心证明', '从 typing 推出 LR 的 fundamental theorem 及其分支。'),
    ('target', '目标性质与最终证明', 'SN 的定义、SN 辅助引理、LR 推出 SN，以及最终 normalization。'),
    ('unknown', '待确认', '尚未人工确认功能的声明。'),
]

# Explicit names are identifiers for reviewed declarations, not naming heuristics.
NAMES = {
    'infra': '''context empty update max_atom max_atom_spec fresh fresh_notin
      fresh_notin_app_l fresh_notin_app_r subst_update In_max_atom extend
      atom_max in_atom_max fresh_not_in fresh_pair update_eq max_list in_max_list
      fresh_atom max_list_spec extend_eq extend_neq update_neq max_list_ge
      max_list_ub subst_update_same subst_update_diff le_fold_max fresh_not_in_app_l
      fresh_not_in_app_r lt_of_lt_succ_neq upd_sigma In_fold_right_add_le
      In_le_fold_max env env_update fresh_notin_left fresh_notin_right env_lookup
      in_le_fold_max fresh_gt fresh_in1 fresh_in2 fresh_in3 fresh_bound
      fresh_bound_ge fresh_atom_notin upd_env upd_env_eq upd_env_neq fresh_spec
      exists_fresh upd upd_same upd_neq max_atoms in_max_atoms in_max_atom
      update_env update_env_same update_env_other max_atoms_spec fresh_atom_spec
      extend_same extend_other list_bounded fresh_exists list_max in_list_max
      env_update_eq env_update_neq fold_right_max_bound fresh_fresh''',
    'syntax': '''atom ty tm open_rec open lc_at locally_closed fvars subst_id substf
      substf_id lc_at_mono open_rec_lc lc_open_rec lc_open_fvar_inv lc_subst
      subst_open_rec_fvar subst_fvar subst_fvar_id lc_at_bvar_inv lc_at_app_inv
      lc_at_abs_inv lc_at_weaken lc_open_rec_inv open_rec_lc_id subst_fvar_open_rec
      subst_fvar_open fv subst_fvar_agree lc_at_dec subst lc_at_open_rec
      subst_open_rec lc_app_pres lc_app_inv lc_abs_inv lc_at_open open_rec_lc_at
      lc_at_subst subst_open_fvar free_atom fv_spec fresh_both tsubst tsubst_id
      lc_at_open_rec_id lc_at_0_open_rec lc_at_open_rec_inv tsubst_open_rec_fvar
      tsubst_open_fvar lc_open lc_open_inv subst_open_gen subst_lc subst_agree
      fv_open_rec lc_at_S lc_bvar_inv lc_at_le lc_open_rec_id open_rec_id id_sigma
      fv_list fv_in_fv_list fresh_not_fv tsubst_ids tsubst_update_same
      tsubst_open_rec tsubst_lc tsubst_update_open lc_mono lc_open_fvar env_lc
      subst_env subst_env_lc subst_env_open_rec subst_env_id fv_app_notin_1
      fv_app_notin_2 open_lc tsubst_open_gen tsubst_open substenv env_atoms
      substenv_nil lc_substenv substenv_open_rec lc_env subst_tm subst_tm_id
      lc_at_open_inv open_rec_lc_gen open_rec_lc_inv subst_extend_fresh is_abs
      subst_open_fresh subst_tm_fvar subst_tm_open_rec subst_tm_upd_notin
      subst_tm_update_notin lc_open_rec_gen lc_subst_tm ids subst_ids occurs_free
      subst_ext subst_open idenv subst_tm_idenv subst_tm_lc_at fvs subst_tm_open_fvar
      subst_update_notin update_env_lc lc_open_back subst_open_comm subst_env_update_ext''',
    'operational': '''multi value step step_lc abs_no_step true_no_step false_no_step
      step_abs_inv step_true_inv step_false_inv value_app_inv lc_step step_app_inv
      value_lc value_no_step app_not_value value_abs_lc value_dec step_app_cases
      no_step_abs no_step_true no_step_false step_abs_app_inv step_app_nonvalue
      abs_not_step value_multistep value_app multi_app_l multi_app_decomp
      app_multistep_value multi_app_abs_decomp app_abs_multistep_value value_app_false
      step_abs_false inert inert_not_value inert_no_step step_app_abs_inv
      multi_trans multi_stuck multi_first_step value_not_app step_true_false
      step_false_false step_lc_preserve step_det value_multi_eq step_preserves_lc
      multi_preserves_lc value_app_absurd app_multi_value_inv value_abs lc_at_step
      step_lc_fwd step_lc_back value_step_absurd fvar_not_value fvar_no_step
      multi_app_r value_multi_self multi_inv multi_fvar multi_app1 multi_app2
      contra_value solve_step_absurd''',
    'typing': 'has_type typing_lc has_type_lc lc_typing',
    'lr': '''Red Red_lc Red_step Red_backward abs_app_red Red_app Red_nonvalue
      Red_abs_app Red_var valuation R R_step_fwd R_of_neutral R_abs_app R_app_value
      R_app good lrel lrel_step lrel_intro_nonvalue lrel_app lrel_app_abs env_rel
      env_rel_update tr tr_lc tr_app tr_step tr_closure_nonvalue tr_abs_app env_sem
      TermRel ValRel TermRel_lc TermRel_value_red TermRel_step TermRel_multistep
      TermRel_app_abs env_sat sem_ty LR LR_lc LR_app inert_LR fvar_LR LR_step
      LR_of_reducts LR_abs_app env_ok env_ok_update_fvar env_ok_update Vclause
      R_iff R_lc R_vclause R_step R_multi R_abs R_app_aux anti_red_app SN_app_abs_gen
      ctx_sat upd_sigma_sat ctx_sat_empty env_ty LR_step_back LR_neutral_intro
      abs_app_LR LR_step_forward LR_of_red_nonabs LR_app_aux env_sem_cons
      env_sem_empty C C_lc C_app C_step C_neutral C_beta_aux C_beta sat R_props
      R_fwd R_expand R_abs_app_aux LR_back LR_fvar env_sem_lc env_sem_ty
      env_sem_update VR_value VR_lc LR_pack VR_LR LR_to_VR LR_arrow_app LR_stuck
      LR_neutral_expand V R_V R_true R_false R_fvar R_app_abs_val R_app_abs
      V_reducts_app_aux env_good env_good_extend R_intro_neutral abs_app abs_intro
      env_CR update_env_R CV V_Bool V_Arrow C_Bool C_Arrow C_halts V_lc C_intro
      C_elim V_value_C V_Arrow_apply sem_type''',
    'core': 'fundamental fundamental_aux',
    'target': '''strongly_normalizing normalization Red_sn SN_no_step SN_step SN_abs
      SN_true SN_false R_SN lrel_sn sn_step tr_sn sn_abs_app TermRel_SN
      TermRel_app_SN SN_app_of_value_reds SN_app_abs SN_multistep LR_SN inert_SN
      value_sn multi_sn R_sn SN_ind' sn_abs sn_true sn_false LR_sn SN_value SN_multi
      sn_app_value sn_app SN C_sn SN_ind value_SN SN_app_of_R_arrow sn_value
      sn_back_step sn_multi_back''',
}
LABELS = {name: block for block, names in NAMES.items() for name in names.split()}
assert len(LABELS) == sum(len(names.split()) for names in NAMES.values())


def mask_comments(text):
    """Blank nested comments and strings, keeping offsets/newlines."""
    out = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if not quoted and pair == '(*':
            depth += 1
            out[i:i+2] = '  '
            i += 2
        elif depth and pair == '*)':
            depth -= 1
            out[i:i+2] = '  '
            i += 2
        elif depth or quoted:
            if text[i] == '"' and not depth:
                if pair == '""':
                    out[i:i+2] = '  '
                    i += 2
                    continue
                quoted = False
            if text[i] != '\n':
                out[i] = ' '
            i += 1
        else:
            if text[i] == '"':
                quoted = True
                out[i] = ' '
            i += 1
    return ''.join(out)


def sections(snapshot):
    """Extract declaration bodies, excluding following comments/notations."""
    lines = snapshot['text'].splitlines()
    clean = mask_comments(snapshot['text']).splitlines()
    ds = list(snapshot['declarations'])
    for m in re.finditer(r'(?m)^\s*Ltac\s+(\w+)', '\n'.join(clean)):
        ds.append(dict(kind='Ltac', name=m[1], line='\n'.join(clean).count('\n', 0, m.start(1))+1))
    ds.sort(key=lambda d: d['line'])
    result = []
    for i, d in enumerate(ds):
        start = d['line'] - 1
        limit = ds[i+1]['line'] - 1 if i+1 < len(ds) else len(lines)
        body = '\n'.join(clean[start:limit])
        is_proof = d['kind'] in {'Lemma', 'Theorem', 'Corollary', 'Proposition'}
        end = re.search(r'\b(?:Qed|Defined|Admitted|Abort)\s*\.', body) if is_proof else re.search(r'\.(?=\s|$)', body)
        # A mutually recursive Fixpoint is one declaration group.
        count = body[:end.end()].count('\n') + 1 if end else limit-start
        stop = start + count
        code = '\n'.join(clean[start:stop])
        proof = re.search(r'\bProof\b', code)
        result.append(dict(**d, end=stop, code=code,
                           proofLine=start+code[:proof.start()].count('\n')+1 if proof else None))
    return result


def classify(run):
    initial = {d['name']: d for d in sections(run['snapshots'][run['initial']])}
    result = sections(run['snapshots'][run['final']])
    normalize = lambda s: re.sub(r'\s+', '', s)
    for d in result:
        original = initial.get(d['name'])
        d['block'] = LABELS.get(d['name'], 'unknown')
        if original and normalize(original['code']) == normalize(d['code']):
            d['origin'] = 'original'
            d['addedLines'] = 0
        elif original:
            d['origin'] = 'modified'
            # In this pilot the supplied target statement receives a proof.
            # Other modified supplied declarations are explicitly not treated as new.
            offset = d['proofLine']-d['line'] if d['proofLine'] else 0
            d['addedLines'] = sum(bool(line.strip()) for line in d['code'].splitlines()[offset:])
        else:
            d['origin'] = 'new'
            d['addedLines'] = sum(bool(line.strip()) for line in d['code'].splitlines())
        del d['code']
    return result
