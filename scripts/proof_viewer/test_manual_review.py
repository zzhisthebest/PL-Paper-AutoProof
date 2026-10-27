import unittest

from manual_review import apply_review


class ManualReviewTests(unittest.TestCase):
    def test_review_keeps_original_command(self):
        command = 'orig_prefix = orig[:193]'
        step = {'traceLine': 151, 'input': {'command': command}}
        apply_review({'case': '001__example', 'repeat': 17}, [step], lambda text: 0)
        self.assertEqual(step['input']['command'], command)
        self.assertEqual(step['reviewedCommand'], 'true')
        self.assertTrue(step['reviewNote'])

    def test_changed_source_rejects_old_correction(self):
        step = {'traceLine': 151, 'input': {'command': 'different command'}}
        with self.assertRaises(AssertionError):
            apply_review({'case': '001__example', 'repeat': 17}, [step], lambda text: 0)
