import unittest

from problem_times import attach_problem_times, case_overview, compile_analysis


class ProblemTimesTests(unittest.TestCase):
    def test_pilot_accounts_for_whole_run_without_overlap(self):
        for case, repeat in [('001', 7), ('001', 12), ('034', 8)]:
            run = dict(repeat=repeat, seconds=500,
                       timeline=[{'elapsedSeconds': i + 1} for i in range(210)])
            attach_problem_times(run, case)
            data = run['problemTimes']
            self.assertEqual(sum(x['seconds'] for x in data['problems'] + data['other']), 500)
            self.assertEqual(data['problems'], sorted(data['problems'], key=lambda p: -p['seconds']))

    def test_unreviewed_run_has_no_chart(self):
        run = dict(repeat=1)
        attach_problem_times(run, '001')
        self.assertNotIn('problemTimes', run)

    def test_overview_counts_runs_not_repeated_problems(self):
        p = dict(category='tactic', title='explicit parameters', seconds=5,
                 ranges=[{'after': 2}], resolution='resolved')
        runs = [dict(repeat=1, seconds=100, problemTimes=dict(analyzed=True, problems=[p,p])),
                dict(repeat=2, seconds=200, problemTimes=dict(analyzed=True, problems=[p])),
                dict(repeat=3, seconds=300)]
        overview = case_overview(runs)
        self.assertEqual(overview['analyzed'], 2)
        self.assertEqual(overview['seconds'], 300)
        category = overview['categories'][0]
        self.assertEqual(category['runs'], 2)
        self.assertEqual(len(category['occurrences']), 3)
        self.assertEqual(category['seconds'], 15)

    def test_reject_overlapping_problems(self):
        run = dict(seconds=10, timeline=[{'elapsedSeconds': i+1, 'lines':[i+1]} for i in range(10)])
        item = dict(title='p', outcome='o', intervals=[[1,5]])
        with self.assertRaisesRegex(AssertionError, 'overlap'):
            compile_analysis(run, dict(problems=[item,item], phases=[]))
