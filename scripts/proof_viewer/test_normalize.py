import unittest

from normalize import normalize_statement


class NormalizeTests(unittest.TestCase):
    def normal(self, body):
        result = normalize_statement('Lemma example : '+body+'.')
        self.assertEqual(result['status'], 'normalized')
        return result['text']

    def test_alpha_renaming(self):
        self.assertEqual(self.normal('forall t T, has_type empty t T -> strongly_normalizing t'),
                         self.normal('forall e A, has_type empty e A -> strongly_normalizing e'))

    def test_scope_and_shadowing(self):
        self.assertEqual(self.normal('forall x, (forall x, P x) -> Q x'),
                         self.normal('forall a, (forall b, P b) -> Q a'))
        self.assertNotEqual(self.normal('forall x, (forall y, P x) -> Q x'),
                            self.normal('forall x, (forall y, P y) -> Q x'))

    def test_dependent_binders_and_lambda(self):
        self.assertEqual(self.normal('forall (A : Type) (x : A), (fun y : A => y) x = x'),
                         self.normal('forall (B : Type) (z : B), (fun q : B => q) z = z'))

    def test_binder_type_uses_outer_scope(self):
        self.assertEqual(self.normal('forall (x : Type), forall (x : x), P x'),
                         self.normal('forall (A : Type), forall (y : A), P y'))

    def test_exists_and_implicit_binders(self):
        self.assertEqual(self.normal('forall {A : Type}, exists (x : A), P x'),
                         self.normal('forall {B : Type}, exists (y : B), P y'))

    def test_globals_and_meaningful_changes_remain(self):
        self.assertNotEqual(self.normal('forall t, P t'), self.normal('forall t, Q t'))
        self.assertNotEqual(self.normal('forall t u, R t u'), self.normal('forall t u, R u t'))
        self.assertIn('M.x', self.normal('forall x, P M.x x'))
        self.assertIn('x1', self.normal('forall t, P x1 t'))
        self.assertIn('_x1', self.normal('forall t, P x1 t'))
        self.assertEqual(self.normal('forall x1, P x1'), self.normal('forall t, P t'))
        self.assertIn('\\in', self.normal('forall t T, <{ empty |-- t \\in T }>'))

    def test_unsupported_is_not_guessed(self):
        for s in ['forall x, match x with Some y => P y | None => True end',
                  'forall x, let y := x in P y',
                  'forall x, { y : nat | P x y }',
                  'forall x, (f (x := x)) = x']:
            result = normalize_statement('Lemma example : '+s+'.')
            self.assertEqual(result, dict(status='unsupported', text=None))

    def test_other_families(self):
        for first, second in [
            ('forall D G t T, has_type D G t T -> E T t',
             'forall Delta Gamma e A, has_type Delta Gamma e A -> E A e'),
            ('forall rho T v1 v2, value_relation rho T v1 v2 -> P v1 v2',
             'forall env A left right, value_relation env A left right -> P left right'),
            ('forall R v, denotes R v -> value v',
             'forall ty term, denotes ty term -> value term'),
            ('forall k T t, flows_to k Low -> has_type empty t T -> Q t',
             'forall label A e, flows_to label Low -> has_type empty e A -> Q e'),
        ]:
            self.assertEqual(self.normal(first), self.normal(second))

    def test_notation_and_record_projection(self):
        self.assertIn('-->s', self.normal('forall t u, t -->s u -> P t'))
        self.assertEqual(self.normal('forall k reader, P k.(reader) reader'),
                         self.normal('forall q x, P q.(reader) x'))


if __name__ == '__main__':
    unittest.main()
