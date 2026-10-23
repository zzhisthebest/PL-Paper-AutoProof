"""用一张数值热力图展示 36 个任务、108 张卡片的代码规模。"""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager
import numpy as np
import seaborn as sns

ROOT = Path(__file__).resolve().parents[2]
rows = json.loads((ROOT / "docs/benchmark-code-size.json").read_text())["cases"]
names = {
    "STLC — Strong Normalization": "STLC-N",
    "System F — Strong Normalization": "System F-N",
    "System F — Polymorphic Identity": "System F-P",
    "System F + Refinement Types — Type Safety": "Refinement",
    "Security STLC — Noninterference": "Security",
}
levels = ["hard", "medium", "easy"]
groups = {}
for row in rows:
    groups.setdefault((row["family"], row["features"]), {})[row["difficulty"]] = row

values, labels = [], []
for (family, features), group in groups.items():
    inputs = [group[level]["input_code_lines"] for level in levels]
    completed = [group[level]["final_code_lines"] if group[level]["status"] == "proved"
                 else np.nan for level in levels]
    values.append(inputs + completed)
    labels.append(f"{group['hard']['id']}–{group['easy']['id']}  {names[family]} · {features}")
values = np.array(values)

font_manager.fontManager.addfont("/usr/share/fonts/truetype/droid/DroidSansFallbackFull.ttf")
sns.set_theme(style="white")
plt.rcParams["font.family"] = ["DejaVu Sans", "Droid Sans Fallback"]
fig, ax = plt.subplots(figsize=(14, 17))
ax.set_facecolor("#eeeeee")
sns.heatmap(values, annot=True, fmt=".0f", cmap="YlGnBu", vmin=0, vmax=4500,
            linewidths=0.5, linecolor="white", yticklabels=labels,
            xticklabels=["Hard", "Medium", "Easy"] * 2,
            annot_kws={"fontsize": 10}, cbar=False, ax=ax)
for i, j in zip(*np.where(np.isnan(values))):
    ax.text(j + 0.5, i + 0.5, "×", ha="center", va="center", color="#888888", fontsize=13)
for boundary in [8, 16, 24, 32]:
    ax.axhline(boundary, color="#34495e", linewidth=2)
ax.axvline(3, color="white", linewidth=7)
ax.xaxis.tick_top()
ax.tick_params(axis="both", length=0, labelsize=10)
ax.set_yticklabels(labels, rotation=0)
ax.text(1.5, -1.2, "当前题面：定义 + 已提供代码", ha="center", fontsize=13, color="#253342")
ax.text(4.5, -1.2, "成功后的完整文件：定义 + 证明", ha="center", fontsize=13, color="#253342")
fig.suptitle("36 个任务 × 3 个难度：代码规模总览", x=0.035, ha="left", y=0.985,
             fontsize=22, fontweight="bold")
fig.text(0.035, 0.955, "数字 = 去除注释与空行后的代码行数；颜色越深，代码越多。灰色 × = 超时，没有完成的证明。",
         fontsize=12, color="#536170")
fig.text(0.035, 0.048,
         "N = Strong Normalization；P = Polymorphic Identity；Refinement = Type Safety；Security = Noninterference。",
         fontsize=10, color="#536170")
fig.text(0.035, 0.028,
         "右侧统一取 GPT-6 Luna high、每题 3600 秒的全量实验（75/108 成功）；左侧为当前题面，不能直接相减。",
         fontsize=10, color="#536170")
fig.subplots_adjust(left=0.45, right=0.98, top=0.89, bottom=0.075)
output = ROOT / "docs/benchmark-code-size.png"
fig.savefig(output, dpi=180)
print(output)
