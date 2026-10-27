"""Walk every replay step in Chromium, using the viewer's actual controls.

Checks presentation against embedded snapshots, not the correctness of the
original proofs or arbitrary Shell reconstruction. Findings are saved as JSON.
"""
import argparse
import concurrent.futures
import json
from pathlib import Path
from playwright.sync_api import sync_playwright


CHECK_STEP = r"""() => {
 const r=DATA.runs[state.history],e=r.timeline[state.event], issues=[];
 const add=message=>issues.push({case:DATA.case,run:r.repeat,step:state.event+1,
                               trace:e.lines,message});
 if(document.querySelector('.error-location')||document.querySelector('#history-code .focus'))
  add('Unexpected error navigation/highlight in playback');
 const checkFile=(path)=>{
  const f=e.files.find(f=>f.path===path);
  if(!f){add('Displayed file missing from event');return}
  const partial=f.partial&&(!f.snapshotLine||f.partial.traceLine>f.snapshotLine)?f.partial:null;
  const text=partial?partial.text:f.snapshot==null?null:r.snapshots[f.snapshot].text;
  if(f.snapshotLine>e.end)add('Snapshot from future trace');
  if(text===null){if(document.getElementById('history-code'))add('Code shown without snapshot');return}
  const box=document.getElementById('history-code');
  if(!box){add('Snapshot exists but code panel missing: '+path);return}
  // Verify both sides of the rendered diff, including folded unchanged rows.
  const mode=document.querySelector('[data-mode].active')?.dataset.mode;
  if(mode==='diff'){
   const old=e.before==null?null:r.snapshots[e.before].text.split('\n');
   const current=text.split('\n'), oldSeen=[],newSeen=[];
   for(const row of box.querySelectorAll('.row')){
    const nums=row.querySelectorAll('.ln'),src=row.querySelector('.src')?.textContent;
    const a=Number(nums[0]?.textContent)||0,b=Number(nums[1]?.textContent)||0;
    if(a){oldSeen.push(a);if(!old||src!==(old[a-1]||' '))add('Diff old line mismatch: '+path+':'+a)}
    if(b){newSeen.push(b);if(src!==(current[b-1]||' '))add('Diff new line mismatch: '+path+':'+b)}
   }
   if(old && (oldSeen.length!==old.length||oldSeen.some((n,i)=>n!==i+1)))add('Diff lost or reordered old lines');
   if(newSeen.length!==current.length||newSeen.some((n,i)=>n!==i+1))add('Diff lost or reordered new lines');
  }
  document.querySelector('[data-mode="after"]')?.click();
  const rows=[...box.querySelectorAll('.row')],lines=text.split('\n'),start=partial?.start||1;
  if(rows.length!==lines.length)add('After view line count mismatch: '+path);
  for(let i=0;i<Math.min(rows.length,lines.length);i++){
   if(rows[i].querySelector('.src')?.textContent!==(lines[i]||' ')
      ||Number(rows[i].dataset.line)!==i+start){add('After view content/line mismatch: '+path+':'+(i+start));break}
  }
 };
 if(document.getElementById('replay-file')?.value!==e.file)add('Wrong default file');
 checkFile(e.file);
 // Also inspect a secondary file whenever its snapshot/partial record changes,
 // and every referenced compiler-error file, not only the default selection.
 const previous=state.event?r.timeline[state.event-1].files:[];
 for(const f of e.files){
  const old=previous.find(x=>x.path===f.path);
  if(f.path!==e.file && (!old||old.snapshot!==f.snapshot||old.partial?.traceLine!==f.partial?.traceLine
                       ||e.errors.some(x=>x.path===f.path))){
   const select=document.getElementById('replay-file');select.value=f.path;
   select.dispatchEvent(new Event('change'));checkFile(f.path);
  }
 }
 const raw=document.getElementById('raw-records');
 if(raw){raw.open=true;raw.ontoggle();const shown=[...document.querySelectorAll('.raw-record pre')].map(x=>x.textContent);
  if(JSON.stringify(shown)!==JSON.stringify(e.lines.map(n=>r.raw[n-1])))add('Raw records missing or modified')}
 return {issues,missing:e.files.find(f=>f.path===e.file)?.snapshot==null,
         stale:!!e.files.find(f=>f.path===e.file)?.stale,step:state.event+1};
}"""


def check_case(html, index):
    report = dict(case_index=index, runs=[], errors=[])
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, args=['--no-sandbox'])
        page = browser.new_page(viewport={'width': 1600, 'height': 1000})
        page.on('pageerror', lambda e: report['errors'].append(str(e)))
        try:
            page.goto(html.as_uri(), timeout=120000)
            page.wait_for_function('typeof DATA!=="undefined" && DATA && !$("case-select").disabled', timeout=120000)
            page.select_option('#case-select', str(index))
            page.wait_for_function('(i)=>!$("case-select").disabled && DATA.case===CASES[i].case', arg=index, timeout=120000)
            report['case'] = page.evaluate('DATA.case')
            page.click('#history-tab')
            for run in range(page.locator('#history-run option').count()):
                page.select_option('#history-run', str(run))
                count = page.evaluate('DATA.runs[state.history].timeline.length')
                result = dict(run=run+1, total=count, visited=0, missing=0, stale=0, issues=[])
                report['runs'].append(result)
                for step in range(count):
                    try:
                        checked = page.evaluate(CHECK_STEP)
                        result['issues'].extend(checked['issues'])
                        result['missing'] += checked['missing']
                        result['stale'] += checked['stale']
                        result['visited'] += 1
                        if checked['step'] != step+1:
                            raise AssertionError('Next button did not advance one step')
                        if step+1<count:
                            # Actual Next button handler: no direct state jump.
                            page.evaluate('document.getElementById("next").click()')
                    except Exception as e:
                        result['issues'].append(dict(step=step+1,message=str(e)))
                        # Continue auditing later steps even if one cannot render.
                        page.evaluate('(i)=>{state.event=i;showHistory()}', step+1 if step+1<count else step)
                print(f"{report['case'][:3]} r{run+1:02}: {result['visited']}/{count} steps, {len(result['issues'])} findings", flush=True)
        finally:
            browser.close()
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('html',type=Path)
    parser.add_argument('--output',type=Path,default=Path('/tmp/proof-viewer-playback-audit.json'))
    parser.add_argument('--workers',type=int,default=3)
    args=parser.parse_args()
    reports=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(check_case,args.html.resolve(),i):i for i in range(6)}
        for f in concurrent.futures.as_completed(futures):
            try:reports.append(f.result())
            except Exception as e:reports.append(dict(case_index=futures[f],fatal=str(e)))
            args.output.write_text(json.dumps(reports,ensure_ascii=False,indent=2))
    runs=[r for c in reports for r in c.get('runs',[])]
    print(json.dumps(dict(runs=len(runs),steps=sum(r['visited'] for r in runs),
                          findings=sum(len(r['issues']) for r in runs),report=str(args.output))))


if __name__=='__main__':
    main()
