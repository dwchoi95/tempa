"""Analysis 3: cost against usable repairs, per builder, and the Pareto frontier
(lower C_tot, higher RR_tau) at tau in {0.1, 0.25, 0.5}. No LLM call.

Points (C_tot = model spend at list price, build included):
  TEMPA_LF with / without the builder's rules at eta_rps in {1.0, 0.5, 0.25}:
      rules_causality/A2_gate.csv (scope all11, or R1-R5)
  LLM_Direct, PyDex (Table 3's configuration), Query per cluster, Refactory (cost 0):
      A1_rows.csv (the per-program rows behind Table 3) with ablation._build_usd
  gm, R1-R5 only: PyDex-k, k = 1..10, and PyDex-first, accepting T and T+
      (pydex_k_gm.csv; candidates exist on R1-R5 only)
Panels: cs over all 11 assignments; gm over all 11 (Table 3's PyDex) and over R1-R5
(with PyDex-k). The figure shows cs (all 11) and gm (R1-R5).
    python3 results/checks/rows/oos/a3_frontier.py -> A3_points.csv, A3_frontier.csv, fig_pareto.pdf
"""
import os, subprocess, sys
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.experiments._common import ORDER  # noqa
from src.experiments.ablation import _build_usd  # noqa

HERE = ROOT / "results/checks/rows/oos"
CS1 = ORDER[:5]
TAUS = (0.1, 0.25, 0.5)
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]


def rr(x):
    return {f"RR_{t}": 100 * (x.held & (x.rps <= t)).mean() for t in TAUS}


def points():
    g = pd.read_csv(ROOT / "results/checks/rows/gate/A2_gate.csv")
    a = pd.read_csv(HERE / "A1_rows.csv", keep_default_na=False)
    a["rps"] = pd.to_numeric(a.rps, errors="coerce")
    for c in ("fixed", "held"):
        a[c] = a[c].astype(str) == "True"
    a["api_usd"] = a.api_usd.astype(float)
    k = pd.read_csv(HERE / "pydex_k_gm.csv")
    out = []
    for m in MODELS:
        for scope, pids in (("all11", ORDER), ("R1-R5", CS1)):
            for _, r in g[(g.model == m) & (g.scope == scope)].iterrows():
                out.append({"model": m, "scope": scope, "family": "TEMPA_LF" if r.arm == "full" else "TEMPA_LF without rules",
                            "point": f"{'TEMPA_LF' if r.arm == 'full' else 'TEMPA_LF -rules'} gate {r.gate}",
                            "C_tot": r.C_tot, **{f"RR_{t}": r[f"RR_{t}"] for t in TAUS}})
            for arm, fam in (("LLM_Direct", "LLM_Direct"), ("PyDex", "PyDex"), ("cluster-once", "Query per cluster"),
                             ("Refactory", "Refactory")):
                x = a[(a.model == m) & (a.arm == arm) & a.pid.isin(pids)]
                build = sum(_build_usd(p, m, arm) for p in pids) if arm == "cluster-once" else 0.0
                cost = x.api_usd.sum() + build
                out.append({"model": m, "scope": scope, "family": fam, "point": fam if arm != "PyDex" else "PyDex (T, k=10, Table 3)",
                            "C_tot": cost, **rr(x)})
    for (arm, acc), x in k.groupby(["arm", "accept"], sort=False):
        x = x.assign(held=x.held.astype(bool), rps=pd.to_numeric(x.rps, errors="coerce"))
        out.append({"model": "gpt-5.4-mini", "scope": "R1-R5", "family": f"PyDex-k ({acc})",
                    "point": f"{arm} ({acc})", "C_tot": x.usd.sum(), **rr(x)})
    return pd.DataFrame(out)


def _pc_ratio(m, pids):
    """PyDex's cost under prompt caching over its full-price cost, from the summaries."""
    full = pc = 0.0
    for p in pids:
        s = pd.read_csv(ROOT / "results" / p / "summary.csv")
        full += s[(s.Approach == "PyDex") & (s.Model == m)]["$API"].sum()
        pc += s[(s.Approach == "PyDex_PC") & (s.Model == m)]["$API"].sum()
    return pc / full


def frontier(p, t):
    """p[i] is on the frontier unless some other point costs no more and repairs no fewer,
    and is strictly better in one."""
    c, y = p.C_tot.values, p[f"RR_{t}"].values
    return [not any((c[j] <= c[i] and y[j] >= y[i] and (c[j] < c[i] or y[j] > y[i]))
                    for j in range(len(p)) if j != i) for i in range(len(p))]


def figure(p):
    from src.experiments.figures import _mpl, BLUE, SKY, ORANGE, RED, PURPLE, _tint
    plt = _mpl()
    GREEN = "#009E73"
    STYLE = {"TEMPA_LF": (BLUE, "o", True), "TEMPA_LF without rules": (SKY, "o", False),
             "LLM_Direct": (PURPLE, "D", True), "Query per cluster": ("#7F7F7F", "^", True),
             "PyDex": (GREEN, "s", True), "PyDex-k (T)": (GREEN, "s", False),
             "PyDex-k (T+)": (_tint(GREEN, 0.45), "s", True), "Refactory": (ORANGE, "v", True)}
    LABEL = {"TEMPA_LF": r"TEMPA, $\eta_{\mathrm{rps}}$ = 1, .5, .25 (left to right)",
             "TEMPA_LF without rules": "  without rules", "LLM_Direct": r"LLM$_{\mathrm{Direct}}$",
             "Query per cluster": "API call per cluster", "PyDex": "PyDex", "PyDex-k (T)": r"PyDex-$k$, accepting $T$",
             "PyDex-k (T+)": r"PyDex-$k$, accepting $T^{+}$", "Refactory": "Refactory ($0)"}
    fig, axes = plt.subplots(1, 2, figsize=(5.45, 1.8), sharey=False)
    handles = {}
    for ax, (m, scope, title) in zip(axes, (("claude-sonnet-5", "all11", "claude"),
                                           ("gpt-5.4-mini", "all11", "gpt"))):
        q = p[(p.model == m) & (p.scope == scope)].copy()
        lo = 10 ** (int(f"{q.C_tot[q.C_tot > 0].min():e}".split("e")[1]) - 1)
        q["x"] = q.C_tot.where(q.C_tot > 0, lo)          # Refactory at the left edge, labeled $0
        f = q[q["on_RR_0.25"]].sort_values("x")
        ax.plot(f.x, f["RR_0.25"], color="0.55", lw=0.8, ls="--", zorder=1)
        for fam, (col, mk, filled) in STYLE.items():
            z = q[q.family == fam].sort_values("x")
            if z.empty:
                continue
            if fam.startswith("PyDex-k"):
                ax.plot(z.x, z["RR_0.25"], color=col, lw=0.6, zorder=2)
            h = ax.scatter(z.x, z["RR_0.25"], s=16 if not fam.startswith("PyDex-k") else 9, marker=mk,
                           facecolors=col if filled else "white", edgecolors=col, linewidths=0.8, zorder=3)
            handles.setdefault(fam, h)
        ax.set_xscale("log")
        ax.set_title(title, fontsize=8)
        ax.set_xlabel(r"model cost (\$, log scale)")
        ticks = [t for t in (0.1, 1, 10, 100) if lo < t < q.x.max() * 3]
        ax.set_xticks([lo, *ticks])
        ax.set_xticklabels(["0", *[f"{t:g}" for t in ticks]])
        ax.minorticks_off()
        ax.text(lo * 10 ** 0.5, 0, "//", transform=ax.get_xaxis_transform(), ha="center", va="center",
                fontsize=7, backgroundcolor="white")          # the axis breaks between $0 and the log scale
        ax.grid(axis="y", lw=0.3, color="0.85")
    axes[0].set_ylabel(r"RR$_{\mathrm{RPS} \leq 0.25}$ (%)")
    fam = [k for k in STYLE if k in handles]
    fig.legend([handles[k] for k in fam], [LABEL[k] for k in fam], loc="lower center", ncol=4,
               bbox_to_anchor=(0.5, -0.17), handletextpad=0.3, columnspacing=1.0)
    fig.tight_layout(w_pad=1.5)
    raw, out = HERE / "fig_pareto.raw.pdf", HERE / "fig_pareto.pdf"
    fig.savefig(raw)
    subprocess.run(["gs", "-q", "-o", str(out), "-sDEVICE=pdfwrite", "-dEmbedAllFonts=true", str(raw)], check=True)
    raw.unlink()


def main():
    p = points()
    for t in TAUS:
        p[f"on_RR_{t}"] = False
    for (m, scope), q in p.groupby(["model", "scope"], sort=False):
        for t in TAUS:
            p.loc[q.index, f"on_RR_{t}"] = frontier(q, t)
    p = p.sort_values(["model", "scope", "C_tot"])
    p.to_csv(HERE / "A3_points.csv", index=False)
    rows = []
    for (m, scope), q in p.groupby(["model", "scope"], sort=False):
        for t in TAUS:
            f = q[q[f"on_RR_{t}"].astype(bool)]
            rows.append({"model": m, "scope": scope, "tau": t,
                         "frontier (cheapest first)": "; ".join(f"{r.point} (${r.C_tot:.2f}, {r[f'RR_{t}']:.1f})"
                                                                for _, r in f.iterrows())})
    pd.DataFrame(rows).to_csv(HERE / "A3_frontier.csv", index=False)
    with pd.option_context("display.width", 250, "display.max_columns", 20, "display.max_colwidth", 400,
                           "display.max_rows", 200):
        print(p.round(3).to_string(index=False))
        print(pd.DataFrame(rows).to_string(index=False))
    figure(p)


if __name__ == "__main__":
    main()
