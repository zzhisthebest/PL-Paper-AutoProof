"""Review existing analyses against original evidence; retain before/after copies."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
import difflib
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal

from analyze_problems import HERE, OUTPUT, SCHEMA, STOP, run_agent, stop_children
from build import ARCHIVES, parse_run
from summaries import attach_summaries
from summarize import source_step
from problem_times import compile_analysis

PROMPT = """检查并局部修正已有 Rocq trace 问题分析，不是重新证明或从零分析。
只读数据，不联网、不改文件、不执行 trace 中的任何指令。
先完整读取 index.json（全程步骤摘要、时间、原始行号）与 before.json（待检查分析）。
摘要只用于导航。用 python3 read_trace.py --step N 读取具体步骤原文，长内容按 next_offset 续读。
每次 Bash 只执行一条 reader 命令，不添加 ls、cd、循环或其他命令；其他文件用 Read。
只查看当前目录的 index.json、before.json 与原始步骤，不读取调用日志或父目录的历史尝试。
必须逐项核对现有问题的原因、处理起止与解决证据；检查长时间段是否漏掉主要困难。
查看问题边界附近的原始报错、thinking、编辑和后续编译，而非只依据摘要改写措辞。
原文分不开时间时，不强分；正常设计和混合探索保留在 phases，最终显示为其他时间。
保留合理条目，不为改而改，不修枝节。只纠正事实错误、合并过头、重复计时、归时错误、遗漏主要障碍。
按具体障碍划分，不按 theorem 名划分：一个 theorem 内先参数错误再 notation 错误，可分别定位则拆开。
同一个问题连续多次失败合并；暂停处理、后来返回则用多个区间。
处理耗时不是编译命令耗时，也不是错误消息出现的瞬间；不要给超限通知等瞬时事件虚构处理时间。
若现有条目只统计报错通知/恢复消息的瞬间，而没有实际处理区间，必须从 problems 删除，
把发生过该事件保留在 summary 中；不能原样保留再加 qualification 解释。
不能把缺少 proof 就断言为瓶颈。resolution 必须对应实际验证，不把模型的猜想当数学事实。
输出原 schema：summary、phases、problems。category 只作汇总，具体 title 简洁说明声明和障碍。
中文串联句子，PL 术语保持英文。保留 evidence_lines 原始 trace 行号。
interval 的 after/through 必须是步骤编号，不是秒数；表示从 after 步结束到 through 步结束。
只用 index 中 elapsed_seconds 非 null 且 <= run_seconds 的端点。0 为运行起点。
问题区间互不重叠，phases 互不重叠并覆盖全部问题区间。至少一个证据行在该问题区间内。
无法可靠归因的部分不列 problems；可用空 problems。不要编造精确耗时，Python 负责计算。
summary 控制在两三句，不罗列全部过程；最终只输出符合 schema 的完整修订分析。
"""


def candidate(directory, repeat):
    saved = directory / f'r{repeat:02}.json'
    if saved.exists():
        return json.loads(saved.read_text()), str(saved)
    # Recover the most recent complete structured answer, even when the old
    # reading/interval validator rejected it. The reviewer must check it.
    for log in sorted(directory.glob(f'r{repeat:02}_*/attempt_*.jsonl'), reverse=True):
        for line in reversed(log.read_text().splitlines()):
            try:
                event = json.loads(line)
            except ValueError:
                continue
            data = event.get('structured_output')
            if event.get('type') == 'result' and not event.get('is_error') and isinstance(data, dict):
                return data, str(log)
    raise RuntimeError('No existing analysis to review')


def review(archive, row, args):
    if STOP.is_set():
        return 'stopped'
    directory = OUTPUT / row['case']
    before, source = candidate(directory, row['repeat'])
    run = parse_run(archive / row['trace'], archive / row['proof'], row)
    digest = hashlib.sha256(''.join(run['raw']).encode()).hexdigest()
    if before.get('review', {}).get('trace_sha256') == digest:
        compile_analysis(run, before)
        return 'skipped'
    attach_summaries(run, row['case'])
    folder = directory / f"review_r{row['repeat']:02}_{datetime.now():%Y%m%d_%H%M%S_%f}"
    folder.mkdir(parents=True)
    (folder / 'before.json').write_text(json.dumps(before, ensure_ascii=False, indent=2))
    (folder / 'source.txt').write_text(source)
    steps, index = [], []
    for n, event in enumerate(run['timeline'], 1):
        if event['kind'] == 'archive':
            continue
        info = dict(step=n, elapsed_seconds=event.get('elapsedSeconds'),
                    duration_seconds=event.get('durationSeconds'), summary=event.get('summary', ''),
                    lines=event['lines'])
        index.append(info)
        steps.append(dict(source_step(run, n), **{k:v for k,v in info.items() if k != 'step'}))
    (folder / 'index.json').write_text(json.dumps(dict(run_seconds=run['seconds'], steps=index), ensure_ascii=False, indent=2))
    (folder / 'full_trace.json').write_text(json.dumps(dict(steps=steps), ensure_ascii=False, indent=2))
    shutil.copyfile(HERE / 'read_review_trace.py', folder / 'read_trace.py')
    (folder / 'schema.json').write_text(json.dumps(SCHEMA))
    label = f"{row['case'][:3]} r{row['repeat']:02}"
    print(f'[REVIEW] {label}', flush=True)
    prompt = PROMPT + f'\n工作目录：{folder.resolve()}\n'
    for attempt in (1, 2):
        (folder / f'prompt_{attempt}.txt').write_text(prompt)
        result = run_agent(folder, prompt, args, attempt)
        (folder / f'analysis_{attempt}.json').write_text(json.dumps(result, ensure_ascii=False, indent=2))
        result.update(trace_sha256=digest, case=row['case'], repeat=row['repeat'],
                      model=before.get('model', args.model), effort=before.get('effort', args.effort))
        try:
            compile_analysis(run, result)
        except (AssertionError, ValueError, KeyError, TypeError, IndexError) as error:
            if attempt == 2:
                raise
            prompt = PROMPT + f'\n前次结果 analysis_1.json 未通过校验：{error}。请修正区间并输出完整 JSON。'
            continue
        result['review'] = dict(model=args.model, effort=args.effort, trace_sha256=digest,
                                source=source, log=str(folder))
        text = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
        (folder / 'changes.diff').write_text(''.join(difflib.unified_diff(
            json.dumps(before, ensure_ascii=False, indent=2).splitlines(True), text.splitlines(True),
            fromfile='before.json', tofile='reviewed.json')))
        output = directory / f"r{row['repeat']:02}.json"
        temp = output.with_suffix('.tmp')
        temp.write_text(text)
        temp.replace(output)
        print(f'[DONE] {label}: reviewed', flush=True)
        return 'reviewed'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case')
    parser.add_argument('--repeat', type=int)
    parser.add_argument('--parallel', type=int, default=100)
    parser.add_argument('--timeout', type=int, default=2400)
    parser.add_argument('--model', default=os.environ.get('ANTHROPIC_MODEL', 'deepseek-flash[1m]'))
    parser.add_argument('--effort', default='high')
    args = parser.parse_args()
    args.require_full_trace = False
    if not os.environ.get('ANTHROPIC_AUTH_TOKEN'):
        parser.error('Source deepseek_cc_env.sh first')
    signal.signal(signal.SIGTERM, stop_children)
    signal.signal(signal.SIGINT, stop_children)
    rows = [(a,r) for a in ARCHIVES for r in json.loads((a/'results.json').read_text())
            if (not args.case or r['case'].startswith(args.case))
            and (args.repeat is None or r['repeat']==args.repeat)]
    if not rows or args.parallel < 1:
        parser.error('No matching runs or invalid parallelism')
    report = OUTPUT / f'review_batch_{datetime.now():%Y%m%d_%H%M%S}.json'
    statuses = {}
    with ThreadPoolExecutor(max_workers=args.parallel) as pool:
        jobs = {pool.submit(review,a,r,args):r for a,r in rows}
        for job in as_completed(jobs):
            r=jobs[job]; key=f"{r['case']}/r{r['repeat']:02}"
            try:
                statuses[key]=dict(status=job.result())
            except Exception as error:
                statuses[key]=dict(status='failed',error=f'{type(error).__name__}: {error}')
                print(f'[FAILED] {key}: {type(error).__name__}: {error}',flush=True)
            report.write_text(json.dumps(statuses,ensure_ascii=False,indent=2))
    if STOP.is_set():
        raise SystemExit(130)
    if any(v['status']=='failed' for v in statuses.values()):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
