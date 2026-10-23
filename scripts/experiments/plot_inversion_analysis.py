"""绘制两道 STLC Hard 题各 20 次独立运行的耗时分布。"""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager
import numpy as np
import pandas as pd
import seaborn as sns

root = Path(__file__).resolve().parents[2]
folder = root / "benchmarkResults/feature_inversion_analysis_20_repeats"
records = json.loads((folder / "results.json").read_text())
labels = {"001": "001 · 无额外 feature", "004": "004 · +if"}
rows = pd.DataFrame([
    {"题目": labels[r["case"][:3]], "分钟": r["time_s"] / 60,
     "状态": r["status"]}
    for r in records
])
order = list(labels.values())
successes = rows[rows["状态"] == "proved"]

font_manager.fontManager.addfont("/usr/share/fonts/truetype/droid/DroidSansFallbackFull.ttf")
sns.set_theme(style="whitegrid", font_scale=1.1)
plt.rcParams["font.family"] = ["DejaVu Sans", "Droid Sans Fallback"]
fig, ax = plt.subplots(figsize=(9, 6.8))
colors = ["#357CA5", "#D18A46"]

# 小提琴是平滑后的分布估计；cut=0 避免画出实际范围以外的尾部。
sns.violinplot(data=successes, x="题目", y="分钟", order=order,
               hue="题目", hue_order=order, palette=colors, legend=False,
               inner=None, cut=0, density_norm="width", linewidth=1.2,
               ax=ax)

# 每个点是一条真实记录，轻微左右错开，避免重叠。
rng = np.random.default_rng(42)
for i, label in enumerate(order):
    group = rows[rows["题目"] == label]
    times = group.loc[group["状态"] == "proved", "分钟"]
    ax.scatter(i + rng.uniform(-0.09, 0.09, len(times)), times,
               s=39, facecolor="white", edgecolor=colors[i], linewidth=1.2,
               zorder=3)
    median = times.median()
    ax.plot([i - 0.15, i + 0.15], [median, median], color="#253342",
            linewidth=2.5, zorder=4)
    ax.annotate(f"中位数 {median:.2f} 分钟", (i + 0.18, median),
                xytext=(10, 0), textcoords="offset points", va="center",
                fontsize=10, color="#253342")
    ax.text(i, 1.025, f"成功 {len(times)}/{len(group)}",
            transform=ax.get_xaxis_transform(), ha="center", fontsize=12)
    failed = group[group["状态"] != "proved"]
    if not failed.empty:
        ax.scatter(i + rng.uniform(-0.09, 0.09, len(failed)), failed["分钟"],
                   marker="x", color="#B04444", s=65, zorder=4)

ax.set(xlabel="", ylabel="完成证明的耗时（分钟）", ylim=(0, None))
ax.set_xlim(-0.65, 1.8)
sns.despine(ax=ax, left=True)
fig.suptitle("STLC Hard：有无 if 的重复运行对照", x=0.12, ha="left",
             y=0.98, fontsize=19, fontweight="bold")
fig.text(0.12, 0.918,
         "DeepSeek Flash · Claude Code · 每题 20 次 · 单次预算 60 分钟",
         fontsize=11, color="#566574")
fig.text(0.12, 0.065,
         "圆点：一次成功运行    横线：中位数    宽度：耗时的集中程度（平滑估计）",
         fontsize=10, color="#566574")
fig.text(0.12, 0.03,
         "运行顺序：先 +if 的 20 次并行，再 none 的 20 次并行。两组均无超时。",
         fontsize=10, color="#566574")
fig.subplots_adjust(left=0.12, right=0.97, top=0.83, bottom=0.15)
fig.savefig(folder / "runtime_distribution.png", dpi=180)
print(folder / "runtime_distribution.png")
