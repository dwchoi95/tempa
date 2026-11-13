"""`run.py figures` — draw the paper's figures from results/ (dev branch only).

One figure per research question, two panels each, at the text width of the
acmsmall format, in color that stays legible in grayscale (PLDI's CFP). Each
panel is its own PDF (<name>_a.pdf, <name>_b.pdf); the paper sets the panels
as subfigures and writes their sub-captions:

  fig_effect   repair rate by difficulty band; patch size on the common pairs
  fig_cost     cumulative spend against class size, per builder (N*)
  fig_source   what repaired each assignment; how deep the rule compositions go
  fig_heldout  repair rate on T and on the held-out suite (replaces a table)

Writes paper/figures/*_a.pdf and *_b.pdf.
"""
from __future__ import annotations

import argparse
import json
import logging
import subprocess

import numpy as np
import pandas as pd

from src.experiments.tables import (BANDS, CHEAP, FRONTIER, IDS, ORDER, PAPER,
                                    ROOT, _cell, _summary)

OUT = PAPER / "figures"
RES = ROOT / "results"
W = 5.45                 # acmsmall \textwidth, in inches
LIB = "/usr/local/texlive/2024/texmf-dist/fonts/opentype/public/libertine/"
MODELS = ((FRONTIER, "claude-sonnet-5"), (CHEAP, "gpt-5.4-mini"))
# arm -> (label, line color): Okabe-Ito hues, TEMPA in blues and the baselines
# in warm colors; lines also differ in style and marker, so a grayscale print
# still tells them apart
BLUE, SKY, ORANGE, RED, PURPLE = "#0072B2", "#56B4E9", "#E69F00", "#D55E00", "#CC79A7"
GREEN = "#009E73"   # PyDex: Refactory, PyDex, TEMPA run orange, green, blue
ARM = {"Refactory": ("Refactory", ORANGE),
       "PyDex": ("PyDex", GREEN),
       "LLM_Direct": (r"LLM$_{\mathrm{Direct}}$", PURPLE),
       "TEMPA_L": ("TEMPA w/o fallback", SKY),
       "TEMPA_LF": ("TEMPA", BLUE)}
# bar fills, no hatches or borders: the same hues, spread in lightness so that
# neighboring bars differ by at least 15 in CIE L* (Refactory 84.9, TEMPA_L 69.8,
# PyDex 54.2, TEMPA_LF 30.3)
FILL = {"Refactory": "#E69F00", "TEMPA_L": "#56B4E9", "PyDex": "#009E73",
        "TEMPA_LF": "#004A7C", "LLM_Direct": "#CC79A7",
        "PyDex+T+": "#7FCEB9", "TEMPA_LF (T)": "#6C8EBF"}


def _tint(c: str, f: float):
    """Color c moved the fraction f of the way to white."""
    from matplotlib.colors import to_rgb
    return tuple(x + (1 - x) * f for x in to_rgb(c))


def _mpl():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib import font_manager as fm
    logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)
    for f in ("LinLibertine_R.otf", "LinLibertine_RI.otf", "LinLibertine_RB.otf"):
        fm.fontManager.addfont(LIB + f)
    # the body font of acmart; embedded as CFF, never Type 3
    plt.rcParams.update({
        "font.family": "Linux Libertine O", "font.size": 8,
        "mathtext.fontset": "custom", "mathtext.rm": "Linux Libertine O",
        "mathtext.it": "Linux Libertine O:italic",
        "pdf.fonttype": 42, "axes.spines.top": False, "axes.spines.right": False,
        "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6,
        "legend.frameon": False, "legend.fontsize": 7,
        "savefig.bbox": "tight", "savefig.pad_inches": 0.01})
    return plt


def _save(fig, name: str, **kw):
    OUT.mkdir(parents=True, exist_ok=True)
    p = OUT / f"{name}.pdf"
    raw = p.with_suffix(".raw.pdf")
    fig.savefig(raw, **kw)
    # matplotlib embeds the OpenType font in a way PDF readers flag as a type
    # mismatch; Ghostscript rewrites it as a plain CFF font
    subprocess.run(["gs", "-q", "-o", str(p), "-sDEVICE=pdfwrite",
                    "-dEmbedAllFonts=true", str(raw)], check=True)
    raw.unlink()
    print(" ", p.relative_to(ROOT))


def _log(pid: str, stem: str) -> pd.DataFrame:
    d = pd.read_csv(RES / pid / f"{stem}.csv", keep_default_na=False)
    d["ok"] = d.Fixed.astype(str) == "True"
    return d


def _panels(fig, axes, name: str):
    """Save each panel as <name>_a.pdf, <name>_b.pdf: cropped to its axes (with
    their labels and legend), all at one height so the subfigures line up."""
    from matplotlib.transforms import Bbox
    fig.canvas.draw()
    r, inch = fig.canvas.get_renderer(), fig.dpi_scale_trans.inverted()
    boxes = [ax.get_tightbbox(r).transformed(inch) for ax in axes]
    assert all(p.x1 <= q.x0 for p, q in zip(boxes, boxes[1:])), "panels overlap"
    y0, y1 = min(b.y0 for b in boxes) - 0.01, max(b.y1 for b in boxes) + 0.01
    for s, b, ax in zip("ab", boxes, axes):
        print(f"    {name}_{s}: {b.width + 0.02:.3f} in wide ({(b.width + 0.02) / W:.3f} of the text)")
        others = [o for o in axes if o is not ax]
        for o in others:          # hidden, not just cropped: no stray text in the panel's PDF
            o.set_visible(False)
        _save(fig, f"{name}_{s}", bbox_inches=Bbox([[b.x0 - 0.01, y0], [b.x1 + 0.01, y1]]))
        for o in others:
            o.set_visible(True)


def fig_effect():
    """(a) the gap to Refactory widens with difficulty; (b) patch sizes."""
    plt = _mpl()
    fig, (a, b) = plt.subplots(1, 2, figsize=(W, 1.6),
                               gridspec_kw={"width_ratios": [1.15, 1]})
    arms = ["Refactory", "PyDex", "TEMPA_L", "TEMPA_LF"]
    x = np.arange(len(BANDS))
    w = 0.2
    for i, arm in enumerate(arms):
        rr = []
        for _name, pids in BANDS:
            n = k = 0
            for pid in pids:
                for m in (["none"] if arm == "Refactory" else [FRONTIER, CHEAP]):
                    c = _cell(_summary("", pid), arm, m)
                    nn = int(c["N"]) * (2 if arm == "Refactory" else 1)
                    n += nn; k += float(c["RR"]) * nn
            rr.append(100 * k / n)
        bars = a.bar(x + (i - 1.5) * w, rr, w, color=FILL[arm], label=ARM[arm][0])
        # "100" rather than "100.0", which is wider than its bar
        a.bar_label(bars, [f"{v:.1f}" if v < 99.95 else "100" for v in rr],
                    fontsize=5, padding=1)
    a.set_xticks(x, ["CS1", "CF 800–1000", "CF 1200–2000"])
    a.set_ylim(0, 140)  # headroom keeps the labels under the legend
    a.set_yticks([0, 25, 50, 75, 100])
    a.grid(axis="y", alpha=0.3, lw=0.4)
    a.set_axisbelow(True)
    a.set_ylabel("repair rate (%)")
    a.legend(ncol=4, loc="upper center", handlelength=1.2, columnspacing=0.8,
             handletextpad=0.4, borderaxespad=0.1)

    # RPS on the programs all three arms repaired, per builder pair
    rps = {k: [] for k in ("Refactory", "PyDex", "TEMPA_LF")}
    for pid in ORDER:
        ref = _log(pid, "refactory").set_index("Buggy")
        for m, _ in MODELS:
            px = _log(pid, "pydex"); px = px[px.Model == m].set_index("Buggy")
            lf = _log(pid, "tempa_lf"); lf = lf[lf.Model == m].set_index("Buggy")
            common = [s for s in lf.index
                      if lf.ok[s] and px.ok.get(s, False) and ref.ok.get(s, False)]
            for k, d in (("Refactory", ref), ("PyDex", px), ("TEMPA_LF", lf)):
                rps[k] += pd.to_numeric(d.loc[common, "RPS"]).tolist()
    style = {"Refactory": ("--", ORANGE, 1.2), "PyDex": (":", GREEN, 1.4),
             "TEMPA_LF": ("-", BLUE, 1.4)}
    for k, v in rps.items():
        v = np.sort(v)
        ls, col, lw = style[k]
        b.step(v, np.arange(1, len(v) + 1) / len(v), where="post", ls=ls,
               color=col, lw=lw, label=f"{ARM[k][0]} (mean {np.mean(v):.3f})")
    b.set_xlim(0, 1.5)
    b.set_ylim(0, 1.0)
    b.set_xlabel("relative patch size")
    b.set_ylabel("cumulative share")
    b.grid(alpha=0.3, lw=0.4)
    b.legend(loc="lower right", handlelength=1.8)
    print(f"    fig_effect: {len(rps['TEMPA_LF']):,} pairs repaired by all three")
    fig.tight_layout(w_pad=1.5)
    _panels(fig, (a, b), "fig_effect")
    plt.close(fig)


def fig_cost():
    """Cumulative spend for one assignment of n buggy submissions."""
    plt = _mpl()
    fig, axes = plt.subplots(1, 2, figsize=(W, 1.9), sharey=True)
    arms = [("PyDex_PC", "-", GREEN, 1.2), ("PyDex", "--", GREEN, 1.0), ("TEMPA_LF", "-", BLUE, 1.6)]
    label = {"PyDex": "PyDex, without caching", "PyDex_PC": "PyDex, with caching",
             "TEMPA_LF": ARM["TEMPA_LF"][0]}
    sizes = [int(_cell(_summary("", p), "TEMPA_L", FRONTIER)["N"]) for p in ORDER]
    x = np.logspace(0, 3, 300)
    for ax, (m, name) in zip(axes, MODELS):
        per, build = {}, 0.0
        for arm, *_ in arms:
            api = n = 0.0
            for pid in ORDER:
                c = _cell(_summary("", pid), arm, m)
                api += float(c["$API"]); n += int(c["N"])
                if arm == "TEMPA_LF":         # the tool's and its generator's
                    amp = ROOT / "benchmark" / pid / "amplified" / m / "cost.json"
                    build += (float(c["$Build"]) + (json.loads(amp.read_text())["usd"]
                              if amp.exists() else 0.0)) / len(ORDER)
            per[arm] = api / n
        for arm, ls, col, lw in arms:
            ax.plot(x, (build if arm == "TEMPA_LF" else 0) + per[arm] * x, ls=ls,
                    color=col, lw=lw, label=label[arm])
        for arm in ("PyDex_PC",):
            ns = build / (per[arm] - per["TEMPA_LF"])
            ax.plot(ns, per[arm] * ns, "o", ms=3.5, mfc="white", mec="black",
                    mew=0.8, zorder=5)
            ax.annotate(f"$N^*={ns:.0f}$", (ns, per[arm] * ns), fontsize=6.5,
                        xytext=(3, -9), textcoords="offset points", ha="left")
        ax.plot(sizes, [0.0008] * len(sizes), "|", color="black", ms=5, mew=0.7)
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_xlim(1, 1000); ax.set_ylim(0.0005, 100)
        ax.set_xlabel("buggy submissions per assignment")
        ax.grid(alpha=0.3, lw=0.4)
    axes[0].set_ylabel("model cost (\\$, log)")
    axes[0].text(1.3, 0.0011, "assignment sizes", fontsize=6, color="#404040")
    # above panel (a) only, so that each panel crops to itself
    axes[0].legend(ncol=2, loc="lower left", bbox_to_anchor=(0, 1.0),
                   handlelength=2.4, borderaxespad=0.1)
    fig.tight_layout(w_pad=1.0)
    _panels(fig, axes, "fig_cost")
    plt.close(fig)


def fig_source():
    """(a) TEMPA_LF's repairs by source; (b) depth of the rule compositions."""
    plt = _mpl()
    fig, (a, b) = plt.subplots(1, 2, figsize=(W, 1.6),
                               gridspec_kw={"width_ratios": [2.1, 1]})
    # a rule repair counts as synthesized if any rule behind it is the builder's
    keys = [("synth", "synthesized rules", BLUE),
            ("rules", "always-on rules", SKY),
            ("reference", "transplant", "#c6dbef"),
            ("llm", "fallback LLM", "#9A4F86"),  # darker than PURPLE: L* 45 against always-on rules' 70
            ("none", "unrepaired", "#404040")]
    share = {k: [] for k, *_ in keys}
    depth: dict[int, int] = {}
    for pid in ORDER:
        lf = _log(pid, "tempa_lf")
        synth = lf.Rules_L.map(lambda x: any(not n.startswith("generic_")
                                             for n in json.loads(x or "[]")))
        src = lf.Source.where(lf.ok, "none").where(
            ~((lf.Source == "rules") & synth), "synth")
        for k, *_ in keys:
            share[k].append(100 * (src == k).mean())
        l = _log(pid, "tempa_l")
        for r in l[l.ok & (l.Source == "rules")].Rules_L:
            d = len(json.loads(r))
            depth[d] = depth.get(d, 0) + 1
    x = np.arange(len(ORDER))
    bottom = np.zeros(len(ORDER))
    for k, lab, face in keys:
        a.bar(x, share[k], 0.7, bottom=bottom, color=face, label=lab)
        bottom += share[k]
    a.axvline(4.5, color="black", lw=0.6, ls=":")
    a.set_xticks(x, [IDS[p] for p in ORDER])
    a.set_ylim(0, 100)
    a.set_ylabel("share of pairs (%)")
    a.legend(ncol=5, loc="lower center", bbox_to_anchor=(0.5, 1.0),
             handlelength=1.0, columnspacing=0.7, handletextpad=0.3, fontsize=6.3)
    ds = sorted(depth)
    bars = b.bar(ds, [depth[d] for d in ds], 0.6, color=BLUE)
    b.bar_label(bars, fontsize=6, padding=1)
    b.set_xticks(ds)
    b.set_xlabel("rule applications")
    b.set_ylabel("rule repairs")
    b.set_ylim(0, max(depth.values()) * 1.18)
    fig.tight_layout(w_pad=1.5)
    _panels(fig, (a, b), "fig_source")
    plt.close(fig)


def fig_heldout():
    """(a) held-out repair rate per arm and builder, PyDex given TEMPA's oracle
    included; (b) PyDex's held-out repair rate against its number of samples k,
    accepting T or T+ (gpt-5.4-mini), the breadth effect of the overfitting
    bound. A builder pair shares the arm's fill, gpt-5.4-mini's tinted toward
    white (60% where 50% leaves the pair under 15 apart in L*; Refactory's two
    bars are one run)."""
    plt = _mpl()
    from matplotlib.patches import Patch
    h = pd.read_csv(RES / "heldout.csv")
    po = RES / "pydex_oracle"
    hyb = pd.read_csv(po / "hybrid_claude-sonnet-5.csv")
    pairs = pd.read_csv(po / "pairs_gpt-5.4-mini.csv")
    tplus = {FRONTIER: 100 * hyb[hyb.arm == "PyDex+T+"].held.mean(),
             CHEAP: 100 * pairs[(pairs.arm == "PyDex-10") & (pairs.accept == "T+")].held.mean()}
    arms = [("Refactory", "Refactory"), ("PyDex", "PyDex"),
            ("PyDex+T+", "PyDex accepting $T^{+}$"),
            ("LLM_Direct", ARM["LLM_Direct"][0]),
            ("TEMPA_LF (T)", ARM["TEMPA_LF"][0] + " accepting $T$"),
            ("TEMPA_L", ARM["TEMPA_L"][0]), ("TEMPA_LF", ARM["TEMPA_LF"][0])]
    tint = {"Refactory": 0.0, "PyDex+T+": 0.6, "TEMPA_L": 0.6}
    fig, (a, b) = plt.subplots(1, 2, figsize=(W, 1.8),
                               gridspec_kw={"width_ratios": [1.35, 1]})
    y = np.arange(len(arms))[::-1]
    for dy, (m, _name), light in ((0.19, MODELS[0], False), (-0.19, MODELS[1], True)):
        vals = []
        for arm, _ in arms:
            if arm == "PyDex+T+":
                vals.append(tplus[m]); continue
            d = h[(h.arm == arm) & (h.model == ("none" if arm == "Refactory" else m))]
            vals.append(100 * d.fixed_heldout.sum() / d.n.sum())
        cols = [_tint(FILL[arm], tint.get(arm, 0.5) if light else 0.0) for arm, _ in arms]
        bars = a.barh(y + dy, vals, 0.38, color=cols)
        a.bar_label(bars, fmt="%.1f", fontsize=5.5, padding=1.2)
    a.set_yticks(y, [lab for _, lab in arms], fontsize=6.5)
    a.set_xlim(80, 101.5)
    a.set_xlabel("held-out repair rate (%)")
    a.grid(axis="x", alpha=0.3, lw=0.4)
    a.set_axisbelow(True)
    a.spines["left"].set_visible(False)
    a.tick_params(axis="y", length=0)
    a.legend([Patch(facecolor="#888888"), Patch(facecolor=_tint("#888888", 0.5))],
             [MODELS[0][1], MODELS[1][1]], loc="lower center", ncol=2, fontsize=6,
             bbox_to_anchor=(0.45, 1.0), handlelength=1.2, borderaxespad=0.1)

    ks = [1, 2, 5, 10]
    for acc, ls, mk, lab in (("T", "--", "o", "PyDex accepting $T$"),
                             ("T+", "-", "s", "PyDex accepting $T^{+}$")):
        v = [100 * pairs[(pairs.arm == f"PyDex-{k}") & (pairs.accept == acc)].held.mean()
             for k in ks]
        b.plot(range(len(ks)), v, ls=ls, marker=mk, color=GREEN, ms=3.5, lw=1.2,
               mfc="white" if acc == "T" else GREEN, mew=0.9, label=lab)
    d = h[(h.arm == "TEMPA_LF") & (h.model == CHEAP)]
    b.axhline(100 * d.fixed_heldout.sum() / d.n.sum(), color=BLUE, lw=1.4,
              label=ARM["TEMPA_LF"][0])
    b.set_xticks(range(len(ks)), [str(k) for k in ks])
    b.set_xlabel("samples per program $k$ (gpt)")
    b.set_ylabel("held-out repair rate (%)")
    b.set_ylim(91.5, 100)
    b.grid(alpha=0.3, lw=0.4)
    b.legend(loc="lower right", fontsize=6.3, handlelength=2.0)
    fig.tight_layout(w_pad=1.5)
    _panels(fig, (a, b), "fig_heldout")
    plt.close(fig)


def main(argv: list[str]) -> int:
    argparse.ArgumentParser(prog="run.py figures").parse_args(argv)
    fig_effect()
    fig_cost()
    fig_source()
    fig_heldout()
    return 0
