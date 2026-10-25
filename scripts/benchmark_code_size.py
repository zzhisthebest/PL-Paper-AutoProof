"""统计 108 道题的题面与一轮完整 baseline 的最终文件规模。"""
import json
from pathlib import Path
from statistics import median

from count_code_lines import code_lines

ROOT = Path(__file__).resolve().parents[1]
TAG = "gpt6luna_high_difficulty_v4_full_r1"
FAMILIES = {
    "stlc": "STLC — Strong Normalization",
    "system-f-normalization": "System F — Strong Normalization",
    "system-f-parametricity": "System F — Polymorphic Identity",
    "system-f-refinement": "System F + Refinement Types — Type Safety",
    "secure-stlc": "Secure STLC — Noninterference",
}


def size(path):
    text = path.read_text()
    return len(text.splitlines()), code_lines(text)


def family(case):
    if case["language"] == "system-f":
        suffix = "normalization" if case["target"] == "strong-normalization" else "parametricity"
        return "system-f-" + suffix
    return case["language"]


def span(values):
    return f"{min(values):,}–{max(values):,}"


def main():
    cases = json.loads((ROOT / "benchmarks/case-names.json").read_text())
    rows = []
    for case in cases:
        name = case["name"]
        source = ROOT / "benchmarks" / name / "input/Task.v.orig"
        result_dir = ROOT / "benchmarkResults" / name
        results = json.loads((result_dir / f"results_{TAG}.json").read_text())
        result = results.get(name, results.get(case["old_name"]))
        final = result_dir / f"proofs_{TAG}/Task.v"
        input_raw, input_code = size(source)
        final_raw, final_code = size(final)
        rows.append({
            "id": case["id"], "case": name, "family": FAMILIES[family(case)],
            "features": case["features"], "difficulty": case["difficulty"],
            "input_physical_lines": input_raw, "input_code_lines": input_code,
            "status": result["status"],
            "final_physical_lines": final_raw, "final_code_lines": final_code,
            "input_path": str(source.relative_to(ROOT)),
            "final_path": str(final.relative_to(ROOT)),
        })

    lines = [
        "# Benchmark 代码规模：108 道题逐题统计",
        "",
        "## 统计口径",
        "",
        "- 题面：当前 benchmark 的 `input/Task.v.orig`，包括定义、已提供引理和待证明目标。",
        f"- 最终文件：统一取 GPT-6 Luna high 的全量实验 `{TAG}`；每题预算 3600 秒，75 题成功、33 题超时。",
        "- 总行数：文件的物理行数；代码行数：去掉注释（含嵌套注释）和空行后，仍有内容的行数。",
        "- 最终文件包含题面与模型补写的代码，不是纯 proof 行数；超时文件仅代表未完成产物，不能称为完整证明规模。",
        "- 当前题面与历史运行输入可能不同，因此不把两者相减当作模型新增行数。",
        "- 108 张卡片对应 36 个语言／feature／目标组合，每个组合有 Hard、Medium、Easy 三个难度；不是 108 个独立性质。",
        "- 以下没有重复计算 `Task.v` 与 `Task.v.orig`，也没有把整个 `theories/` 的无关文件相加。行数受排版和证明风格影响，不等于证明难度。",
        "",
        "## 五类任务汇总",
        "",
        "下表均为去掉注释与空行后的代码行数；完整文件仅统计成功运行。不同难度的成功样本不是严格配对样本。",
        "",
        "| 类别 | 组合数／卡片数 | Hard 题面范围 | Medium 题面范围 | Easy 题面范围 | 成功数 | 完整文件范围 | 完整文件中位数 |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for name in FAMILIES.values():
        group = [r for r in rows if r["family"] == name]
        inputs = [span([r["input_code_lines"] for r in group if r["difficulty"] == level])
                  for level in ("hard", "medium", "easy")]
        completed = [r["final_code_lines"] for r in group if r["status"] == "proved"]
        lines.append(f"| {name} | {len(group)//3}／{len(group)} | " + " | ".join(inputs)
                     + f" | {len(completed)}/{len(group)} | {span(completed)} | {median(completed):,.0f} |")

    lines += ["", "## 逐题明细", "",
              "点击编号查看当前题面；点击最终代码行数查看模型最后提交的文件。**超时行不是完成的证明。**", ""]
    for name in FAMILIES.values():
        lines += [f"### {name}", "",
                  "| 编号 | Features | 难度 | 题面总行数 | 题面代码行数 | 结果 | 最终总行数 | 最终代码行数 |",
                  "|---|---|---|---:|---:|---|---:|---:|"]
        for r in rows:
            if r["family"] != name:
                continue
            status = "成功" if r["status"] == "proved" else "超时（未完成）"
            lines.append(f"| [{r['id']}](../{r['input_path']}) | {r['features']} | {r['difficulty'].title()} | "
                         f"{r['input_physical_lines']:,} | {r['input_code_lines']:,} | {status} | "
                         f"{r['final_physical_lines']:,} | [{r['final_code_lines']:,}](../{r['final_path']}) |")
        lines.append("")

    report = ROOT / "docs/benchmark-code-size.md"
    report.write_text("\n".join(lines))
    (report.with_suffix(".json")).write_text(json.dumps(
        {"baseline_tag": TAG, "cases": rows}, ensure_ascii=False, indent=2) + "\n")
    print(report)
    print("\n".join(lines[15:25]))


if __name__ == "__main__":
    main()
