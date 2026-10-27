import unittest

from build import declarations
from blocks import sections, classify
from functional import infer_labels


class FunctionalTests(unittest.TestCase):
    def labels(self, text, case):
        return infer_labels(sections(dict(text=text, declarations=declarations(text))), case)

    def test_statements_not_lemma_names_determine_group(self):
        text = '''Definition subst_tm := 0.
Definition LR := 0.
Inductive has_type : Prop := typed.
Inductive strongly_normalizing : Prop := sn.
Lemma first : forall t, subst_tm t = t. Proof. Admitted.
Lemma second : forall t, LR t -> LR t. Proof. Admitted.
Lemma third : forall t, has_type t -> LR t. Proof. Admitted.
Lemma fourth : forall t, LR t -> strongly_normalizing t. Proof. Admitted.
Lemma fifth : forall t, has_type t -> subst_tm t = t. Proof. Admitted.
'''
        labels = self.labels(text, '004')
        self.assertEqual([labels[n] for n in ['first','second','third','fourth','fifth']],
                         ['syntax','lr','core','target','typing'])

    def test_shadowed_or_absent_lr_is_not_a_global_reference(self):
        text = '''Definition R := 0.
Definition fv_tm := 0.
Lemma local : forall (R : ty) t, fv_tm t = []. Proof. Admitted.
Lemma absent : forall t, E t = t. Proof. Admitted.
'''
        labels = self.labels(text, '055')
        self.assertEqual(labels['local'], 'syntax')
        self.assertNotEqual(labels['absent'], 'lr')

    def test_mixed_lr_characterization_is_not_only_target_property(self):
        text = r'''Definition LR := 0.
Inductive strongly_normalizing : Prop := sn.
Lemma expand : forall t, LR t <-> strongly_normalizing t /\ LR t. Proof. Admitted.
'''
        self.assertEqual(self.labels(text, '004')['expand'], 'lr')

    def test_case_specific_objects_and_no_alpha_conversion(self):
        text = '''Definition E := 0.
Lemma helper : forall t, E t = t. Proof. Admitted.
'''
        self.assertEqual(self.labels(text, '034')['helper'], 'syntax')
        self.assertEqual(self.labels(text, '055')['helper'], 'lr')
        snap = dict(text=text, declarations=declarations(text))
        run = dict(snapshots=[dict(text='', declarations=[]), snap], initial=0, final=1)
        result = classify(run, self.labels(text, '034'), alpha=False)
        self.assertTrue(all('alpha' not in d for d in result))
        self.assertEqual(run['snapshots'][1]['text'], text)

    def test_refinement_semantic_safety_and_final_theorem(self):
        text = '''Definition Safe := 0.
Inductive has_rtype : Prop := rt.
Lemma fundamental : forall t, has_rtype t -> Safe t. Proof. Admitted.
Theorem never_stuck : forall t, has_rtype t -> Safe t. Proof. Admitted.
'''
        labels = self.labels(text, '073')
        self.assertEqual(labels['Safe'], 'lr')
        self.assertEqual(labels['fundamental'], 'core')
        self.assertEqual(labels['never_stuck'], 'target')


if __name__ == '__main__':
    unittest.main()
