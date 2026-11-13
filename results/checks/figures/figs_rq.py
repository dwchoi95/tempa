"""Section 4 figures and Appendix A's Figure on the three builds (no model call):
  fig_rq1            RR_{RPS<=tau} of Refactory, PyDex, TEMPA, per model (RQ1)
  fig_growth         model cost of one assignment against its buggy submissions (RQ2)
  fig_ablation       RR_{RPS<=tau} of TEMPA's stage variants, per model (RQ3)
  fig_rq4_a          held-out failures against the amplified tests m (RQ3)
  fig_rules_compact  rules' share of the repairs per assignment, and recurring mistakes (RQ4)
  fig_rq2            RR_{RPS<=0.25} with no model, Python against TRL rules, three builds (Appendix A)
    python3 -I results/checks/figures/figs_rq.py [rq1|growth|ablation|rq4|rules_compact|rq2]
"""
import os, sys
from pathlib import Path
import numpy as np, pandas as pd
ROOT = Path(__file__).resolve().parents[3]; sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.experiments import figures as F  # noqa
from matplotlib.transforms import Bbox

TEMPA = "TEMPA"
TOOLS = [("Refactory", "Refactory", F.ORANGE, "--", F.FILL["Refactory"]),
         ("PyDex", "PyDex", F.GREEN, ":", F.FILL["PyDex"]),
         ("TEMPA_LF", TEMPA, F.BLUE, "-", F.FILL["TEMPA_LF"])]

def panels(fig, axes, name):
    fig.canvas.draw()
    r, inch = fig.canvas.get_renderer(), fig.dpi_scale_trans.inverted()
    boxes = [ax.get_tightbbox(r).transformed(inch) for ax in axes]
    y0, y1 = min(b.y0 for b in boxes) - 0.01, max(b.y1 for b in boxes) + 0.01
    for s, b in zip("abc", boxes):
        print(f"    {name}_{s}: {(b.width + 0.02) / F.W:.3f} of the text")
        F._save(fig, f"{name}_{s}", bbox_inches=Bbox([[b.x0 - 0.01, y0], [b.x1 + 0.01, y1]]))

def rq1():
    """RR_{RPS<=tau} against tau, one curve per tool and model; the legend gives each
    tool's mean RPS over its repairs and its share of repairs with RPS > 1."""
    plt = F._mpl()
    from matplotlib.lines import Line2D
    rows = pd.read_csv(ROOT / "results/checks/rows/oos/A1_rows.csv", keep_default_na=False)
    rows["rps"] = pd.to_numeric(rows.rps, errors="coerce")
    rows["held"] = rows.held.astype(str) == "True"; rows["fixed"] = rows.fixed.astype(str) == "True"
    C = {"Refactory": F.ORANGE, "PyDex": F.GREEN, "TEMPA_LF": F.BLUE}
    MS = [m for m, _ in F.MODELS]
    series = [("Refactory", MS[0], C["Refactory"])] + [(arm, m, C[arm] if i == 0 else F._tint(C[arm], 0.5))
              for arm in ("PyDex", "TEMPA_LF") for i, m in enumerate(MS)]
    NAME = {("Refactory", MS[0]): "Refactory", ("PyDex", MS[0]): r"PyDex$_{\mathrm{claude}}$", ("PyDex", MS[1]): r"PyDex$_{\mathrm{gpt}}$",
            ("TEMPA_LF", MS[0]): r"TEMPA$_{\mathrm{claude}}$", ("TEMPA_LF", MS[1]): r"TEMPA$_{\mathrm{gpt}}$"}
    fig, b = plt.subplots(figsize=(2.75, 2.0))
    taus = np.linspace(0, 1, 401); hs, labs = [], []
    for arm, m, col in series:
        d = rows[(rows.arm == arm) & (rows.model == m)]
        rep = d.rps[d.fixed].dropna().values
        v = np.sort(d.rps[d.fixed & d.held].dropna().values)
        y = 100 * np.searchsorted(v, taus, side="right") / len(d)
        ls = {"Refactory": "-.", "PyDex": "--", "TEMPA_LF": "-"}[arm]   # dash by tool, shade by model (grayscale)
        h, = b.plot(taus, y, ls=ls, color=col, lw=1.4 if arm == "TEMPA_LF" else 1.1)
        hs.append(h); labs.append(f"{NAME[(arm, m)]}  {np.mean(rep):.3f}  {100 * np.mean(rep > 1):.1f}%")
    b.axvline(0.25, color="0.45", lw=0.7, ls=":", zorder=0)
    b.set_xlim(0, 1); b.set_ylim(0, 100); b.set_yticks([0, 25, 50, 75, 100])
    b.set_xticks([0, 0.25, 0.5, 0.75, 1]); b.set_xticklabels(["0", ".25", ".5", ".75", "1"])
    b.set_xlabel(r"RPS bound $\tau$"); b.set_ylabel(r"RR$_{\mathrm{RPS} \leq \tau}$ (%)")
    b.grid(alpha=0.3, lw=0.4)
    b.legend(hs, labs, loc="lower right", fontsize=5.8, handlelength=2.2, labelspacing=0.2, borderaxespad=0.1,
             title="mean RPS, RPS > 1", title_fontsize=5.8)
    fig.tight_layout(); F._save(fig, "fig_rq1"); plt.close(fig)


def growth():
    """Model cost of one assignment against its number of buggy submissions: TEMPA's
    mean build per assignment plus its calls, against PyDex with and without prompt
    caching; circles where TEMPA's line crosses PyDex's with caching."""
    import json
    plt = F._mpl()
    from src.experiments.tables import ORDER
    MS = [m for m, _ in F.MODELS]
    sizes = [int(F._cell(F._summary("", p), "TEMPA_L", MS[0])["N"]) for p in ORDER]
    x = np.logspace(0, 3, 300)
    fig, ax = plt.subplots(figsize=(2.45, 1.8))
    for i, (m, short) in enumerate(zip(MS, ("claude", "gpt"))):
        per, build = {}, 0.0
        for arm in ("PyDex", "PyDex_PC", "TEMPA_LF"):
            api = n = 0.0
            for pid in ORDER:
                c = F._cell(F._summary("", pid), arm, m)
                api += float(c["$API"]); n += int(c["N"])
                if arm == "TEMPA_LF":
                    amp = ROOT / "benchmark" / pid / "amplified" / m / "cost.json"
                    build += (float(c["$Build"]) + (json.loads(amp.read_text())["usd"] if amp.exists() else 0.0)) / len(ORDER)
            per[arm] = api / n
        g = F.GREEN if i == 0 else F._tint(F.GREEN, 0.5); bl = F.BLUE if i == 0 else F._tint(F.BLUE, 0.5)
        ax.plot(x, per["PyDex"] * x, ":", color=g, lw=1.3, label=rf"PyDex$_{{\mathrm{{{short}}}}}$ w/o cache")   # dotted: apart from TEMPA in grayscale
        ax.plot(x, per["PyDex_PC"] * x, "--", color=g, lw=0.9, label=rf"PyDex$_{{\mathrm{{{short}}}}}$ w/ cache")
        ax.plot(x, build + per["TEMPA_LF"] * x, "-", color=bl, lw=1.5, label=rf"TEMPA$_{{\mathrm{{{short}}}}}$")
        ns = build / (per["PyDex"] - per["TEMPA_LF"])
        ax.plot(ns, per["PyDex"] * ns, "o", ms=3.5, mfc="white", mec="black", mew=0.8, zorder=5)
        ax.annotate(f"$N^*={ns:.0f}$", (ns, per["PyDex"] * ns), fontsize=6, xytext=(-31, 3) if i == 0 else (4, -9),
                    textcoords="offset points", ha="left")
        print(f"    {m}: N* {ns:.2f}, ratio at 1000 {per['PyDex'] * 1000 / (build + per['TEMPA_LF'] * 1000):.1f} (w/ cache {per['PyDex_PC'] * 1000 / (build + per['TEMPA_LF'] * 1000):.1f})")
    ax.plot(sizes, [0.0012] * len(sizes), "|", color="black", ms=5, mew=0.7)
    ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlim(1, 1000); ax.set_ylim(0.0008, 20000)
    ax.set_xlabel("buggy submissions per assignment (log)"); ax.set_ylabel("model cost (\\$, log)")
    ax.grid(alpha=0.3, lw=0.4)
    ax.legend(loc="upper left", ncol=2, fontsize=5.5, handlelength=1.8, labelspacing=0.2, columnspacing=0.8, borderaxespad=0.3, framealpha=0.9)
    fig.tight_layout(); F._save(fig, "fig_growth", bbox_inches="tight"); plt.close(fig)


def rq2():
    plt = F._mpl()
    fig, ax = plt.subplots(figsize=(2.5, 1.55))
    data = {"Python": {"cs": [1362, 1299, 1291], "gm": [1089, 1085, 1199]},
            "TRL": {"cs": [1188, 1197, 1211], "gm": [1182, 1125, 1173]}}
    builds = ["main", "rebuild 1", "rebuild 2"]
    y = 0; ticks = []; labels = []
    for form in ("Python", "TRL"):
        for i, bname in enumerate(builds):
            cs, gm = 100 * data[form]["cs"][i] / 2970, 100 * data[form]["gm"][i] / 2970
            ax.plot([gm, cs], [y, y], color="0.6", lw=1.0, zorder=1)
            ax.scatter([cs], [y], color=F.BLUE, s=14, zorder=2, label="claude" if y == 0 else None)
            ax.scatter([gm], [y], color=F.SKY, s=14, marker="s", zorder=2, label="gpt" if y == 0 else None)
            ax.text(max(cs, gm) + 0.45, y, f"{abs(cs - gm):.1f}", va="center", fontsize=6)
            ticks.append(y); labels.append(f"{form}, {bname}"); y += 1
        y += 0.6
    ax.set_yticks(ticks, labels); ax.invert_yaxis()
    ax.set_xlim(35.4, 47.8); ax.set_xlabel(r"RR$_{\mathrm{RPS} \leq 0.25}$ (%), no model")
    ax.grid(axis="x", alpha=0.3, lw=0.4); ax.set_axisbelow(True)
    ax.legend(loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=2, fontsize=6, handletextpad=0.2, columnspacing=1.0, borderaxespad=0.1)
    fig.tight_layout(); F._save(fig, "fig_rq2"); plt.close(fig)

def rq4():
    """Held-out failures of TEMPA^-fallback on R1-R5 against m, per model
    (results/sensitivity.csv, default budget b = 1000)."""
    plt = F._mpl()
    d = pd.read_csv(ROOT / "results/sensitivity.csv"); d = d[d.b == 1000]
    g = d.groupby(["n", "model"])[["repaired", "overfit"]].sum()
    pct = (100 * g.overfit / g.repaired).unstack()
    fig, ax = plt.subplots(figsize=(2.3, 1.4))
    for (m, _), label, col, ls, mk in zip(F.MODELS, ("claude", "gpt"), (F.BLUE, F.SKY), ("-", "--"), ("o", "s")):
        ax.plot(pct.index, pct[m].values, ls=ls, marker=mk, ms=3, color=col, lw=1.2, label=label)
    ax.set_xticks(list(pct.index)); ax.set_xlabel(r"amplified tests $m$"); ax.set_ylabel("held-out failures (%)")
    ax.set_ylim(0, 6.5); ax.grid(alpha=0.3, lw=0.4)
    ax.legend(loc="upper right", fontsize=6, borderaxespad=0.1)
    fig.tight_layout(); F._save(fig, "fig_rq4_a"); plt.close(fig)
    print("   ", pct.round(2).to_dict())

def ablation():
    """Each stage variant's RR_{RPS<=tau} minus TEMPA's, against tau, one panel per model;
    PyDex for reference (it leaves the range below). The legend keeps RR_{RPS<=0.25}."""
    plt = F._mpl()
    d = pd.read_csv(ROOT / "results/checks/rows/stages/stage_rows.csv", keep_default_na=False)
    a1 = pd.read_csv(ROOT / "results/checks/rows/oos/A1_rows.csv", keep_default_na=False)
    d = pd.concat([d, a1[a1.arm == "PyDex"][d.columns]], ignore_index=True)
    d["rps"] = pd.to_numeric(d.rps, errors="coerce")
    d["held"] = d.held.astype(str) == "True"; d["fixed"] = d.fixed.astype(str) == "True"
    V = [("TEMPA", "TEMPA", F.BLUE, "-", None),          # marker per variant: apart in grayscale
         ("rand", "rand", F.ORANGE, (0, (1, 1)), "o"),
         ("built-in", "built-in", "#7F7F7F", "--", "s"),
         ("Refazer", "Refazer", F.PURPLE, ":", "^"),
         ("Python", "Python", "#C0392B", (0, (4, 1, 1, 1)), "x"),
         ("block", "block", "#B8860B", (0, (2, 1)), "D"),
         ("-fallback", "−fallback", F.SKY, "-.", "v"),
         ("PyDex", "PyDex", F.GREEN, (0, (5, 1.5, 1, 1.5, 1, 1.5)), "+")]
    fig, axes = plt.subplots(1, 2, figsize=(F.W, 1.8), sharey=True)
    taus = np.linspace(0, 1, 401)
    def curve(arm, m):
        x = d[(d.arm == arm) & (d.model == m)]
        v = np.sort(x.rps[x.fixed & x.held].dropna().values)
        return 100 * np.searchsorted(v, taus, side="right") / len(x)
    for ax, (m, _), short in zip(axes, F.MODELS, ("claude", "gpt")):
        base = curve("TEMPA", m)
        for i, (arm, lab, col, ls, mk) in enumerate(V):
            y = curve(arm, m)
            ax.plot(taus, y - base, ls=ls, color=col, lw=1.0, marker=mk, ms=2.6, mew=0.7, mfc="white" if mk and mk in "osD^v" else col,
                    markevery=(5 * i, 50), label=f"{lab}  {y[100]:.1f}")
        ax.axvline(0.25, color="0.45", lw=0.7, ls=":", zorder=0)
        ax.set_title(short, fontsize=7)
        ax.set_xlim(0, 1); ax.set_ylim(-8, 20); ax.set_yticks([-5, 0, 5, 10, 15])
        ax.set_xticks([0, 0.25, 0.5, 0.75, 1]); ax.set_xticklabels(["0", ".25", ".5", ".75", "1"])
        ax.set_xlabel(r"RPS bound $\tau$"); ax.grid(alpha=0.3, lw=0.4)
        ax.legend(loc="upper right", ncol=2, fontsize=6.4, handlelength=2.0, labelspacing=0.15, columnspacing=0.6,
                  handletextpad=0.3, borderaxespad=0.3, framealpha=0.9)
    axes[0].set_ylabel("Difference from TEMPA (points)")
    fig.tight_layout(w_pad=1.2); F._save(fig, "fig_ablation"); plt.close(fig)


def rules_compact():
    """(top) per assignment and model, the share of the repaired programs that rules repair,
    and over all assignments; (bottom) the kinds of mistake the used rules repair
    (recurring.json): filled, a builder's rule; open, a built-in rule only."""
    import json
    from src.experiments._common import ORDER
    plt = F._mpl()
    MS = [m for m, _ in F.MODELS]
    ids = ["R1", "R2", "R3", "R4", "R5", "C1", "C2", "C3", "C4", "C5", "C6"]
    share = {}
    for m in MS:
        tr = tt = 0
        for p, i in zip(ORDER, ids):
            d = pd.read_csv(ROOT / "results" / p / "tempa_lf.csv", keep_default_na=False)
            v = d[(d.Model == m) & (d.Fixed.astype(str) == "True")].Source.value_counts()
            r, t = int(v.get("rules", 0)), int(v.sum())
            share[(m, i)] = 100 * r / t; tr += r; tt += t
        share[(m, "All")] = 100 * tr / tt
    rec = json.load(open(ROOT / "results/checks/rows/rule_traits/recurring.json"))
    kinds = [("boundary", "off by one"), ("missing init, return, or step", "missing init/return"),
             ("wrong name", "misnamed variable"), ("missing call", "call without ()"), ("empty input", "empty input")]
    cols = ids + ["All"]
    x = np.arange(len(cols), dtype=float); x[-1] += 0.5
    fig, (a, b) = plt.subplots(2, 1, figsize=(2.75, 2.0), sharex=True, gridspec_kw={"height_ratios": [1.45, 1.0], "hspace": 0.12})
    w = 0.4
    for k, (m, short) in enumerate(zip(MS, ("claude", "gpt"))):
        col = F.BLUE if k == 0 else F.SKY
        v = [share[(m, c)] for c in cols]
        a.bar(x + (k - 0.5) * w, v, w, color=col, label=short)
        a.text(x[-1] - 0.5 * w if k == 0 else x[-1] + 0.04, v[-1] + 2, f"{v[-1]:.1f}", ha="center" if k == 0 else "left",
               va="bottom", fontsize=5.8)   # gpt's label right of the pair, clear of claude's bar
    a.set_ylim(0, 100); a.set_yticks([0, 50, 100]); a.tick_params(labelsize=6.2); a.set_xlim(right=x[-1] + 0.95)
    a.set_ylabel("by rules (%)", fontsize=6.4); a.grid(axis="y", alpha=0.3, lw=0.4); a.set_axisbelow(True)
    a.axvline((x[-2] + x[-1]) / 2, color="0.6", lw=0.5, ls=":")
    a.legend(loc="upper left", fontsize=6.2, handlelength=1.0, borderaxespad=0.2, ncol=2, frameon=False)
    for r, (k, lab) in enumerate(kinds):
        for jx, i in enumerate(ids):
            v = rec.get(k, {}).get(i)
            if v:
                b.plot(x[jx], r, "o", ms=2.8, color="#333333", mfc="#333333" if v == "B" else "white", mew=0.6)
    b.set_yticks(range(len(kinds)), [l for _, l in kinds], fontsize=6.2); b.set_ylim(len(kinds) - 0.5, -0.5)
    b.set_xticks(x, cols, fontsize=6.2); b.grid(alpha=0.25, lw=0.4); b.set_axisbelow(True); b.tick_params(length=0)
    for sp in b.spines.values():
        sp.set_visible(False)
    fig.align_ylabels((a, b))
    fig.savefig(ROOT / "paper/figures/fig_rules_compact.pdf", bbox_inches="tight"); plt.close(fig)
    print("  paper/figures/fig_rules_compact.pdf")


if __name__ == "__main__":
    import sys as _s
    {"rq1": rq1, "growth": growth, "ablation": ablation, "rq4": rq4, "rules_compact": rules_compact, "rq2": rq2}[_s.argv[1]]() if len(_s.argv) > 1 \
        else [f() for f in (rq1, growth, ablation, rq4, rules_compact, rq2)]
