"""Check and plot the Metropolis–Hastings runs of `lake exe mh`.

Usage, from the root of the repository:

    python3 scripts/mh_plot.py          # reads mh_output/, written by `lake exe mh`
    python3 scripts/mh_plot.py --run    # runs `lake exe mh` first

It checks that
* the two routes from the theory to a sampler, the program `@[computable]` wrote and the polymorphic
  program run at `RandM`, produced the same trajectory, bit for bit;
* a reference implementation in numpy, seeded alike, produces that trajectory too. It draws with
  `default_rng(seed).standard_normal` and `.binomial(1, p)`, which `NumLean` reproduces, and computes
  in doubles as the Lean program does: the proposal is `fma(sqrt(var), z, x)`, as in
  `NumLean.normal`, and `exp` and `log` are libm's, as `Float.exp` and `Float.log`.

and draws, in mh_output/:
* bimodal_traces.png: the first steps of the chain on the bimodal target, for three proposal sizes;
* bimodal_histograms.png: the states visited against the target density, for the same three;
* bimodal_diagnostics.png: autocorrelation and running mean, for the same three;
* acceptance.png: acceptance rate against proposal size, for both targets;
* stdnormal.png: the chain on the standard Gaussian.
"""

import csv
import math
import struct
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

OUT = Path("mh_output")

# The reference palette of the data-viz guidelines: surfaces, ink, and the first three categorical
# slots, which stay distinguishable pairwise under colour-vision deficiencies.
SURFACE, INK, INK_2, MUTED, GRID, AXIS = (
    "#fcfcfb", "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7")
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"

# The three bimodal runs, keyed by the colour that stands for them in every figure.
BIMODAL_RUNS = [("bimodal_small", BLUE), ("bimodal_good", ORANGE), ("bimodal_large", AQUA)]


def from_hex(h):
    return struct.unpack("<d", int(h, 16).to_bytes(8, "little"))[0]


# -- The targets, computed as the Lean programs compute them ---------------------------------------

def fexp(v):
    try:
        return math.exp(v)
    except OverflowError:
        return math.inf


def flog(v):
    return math.log(v) if v > 0 else (-math.inf if v == 0 else math.nan)


def std_normal(x):
    return -(x * x) / 2


def bimodal(x):
    return flog(0.3 * fexp(-((x + 3) * (x + 3)) / 2) + 0.7 * fexp(-((x - 3) * (x - 3)) / 2))


TARGETS = {"stdNormal": std_normal, "bimodal": bimodal}


def std_normal_density(x):
    return np.exp(-x * x / 2) / math.sqrt(2 * math.pi)


def bimodal_density(x):
    phi = lambda m: np.exp(-(x - m) ** 2 / 2) / math.sqrt(2 * math.pi)
    return 0.3 * phi(-3) + 0.7 * phi(3)


# -- The reference implementation ------------------------------------------------------------------

def fma(a, b, c):
    """`a * b + c`, rounded once, as `Float.fma`: exact in rationals, then rounded to a double."""
    return float(Fraction(a) * Fraction(b) + Fraction(c))


def mh_reference(logpi, var, steps, x0, seed):
    rng = np.random.default_rng(seed)
    sd = math.sqrt(var)
    x, xs = x0, [x0]
    for _ in range(steps):
        y = fma(sd, rng.standard_normal(), x)
        # `1 ⊓ v` on `Float` is `if 1 ≤ v then 1 else v`, which is Python's `min(1.0, v)`.
        p = min(1.0, fexp(logpi(y) - logpi(x)))
        if rng.binomial(1, p) == 1:
            x = y
        xs.append(x)
    return xs


# -- Loading and checking --------------------------------------------------------------------------

def load_runs():
    with open(OUT / "runs.csv") as f:
        runs = list(csv.DictReader(f))
    for r in runs:
        r["var"], r["x0"] = from_hex(r["var"]), from_hex(r["x0"])
        r["steps"], r["seed"] = int(r["steps"]), int(r["seed"])
        with open(OUT / f"{r['name']}.csv") as f:
            rows = list(csv.DictReader(f))
        r["computable"] = [from_hex(row["computable"]) for row in rows]
        r["polymorphic"] = [from_hex(row["polymorphic"]) for row in rows]
    return runs


def bits(xs):
    return [struct.pack("<d", x) for x in xs]


def check(runs):
    ok = True
    for r in runs:
        same_routes = bits(r["computable"]) == bits(r["polymorphic"])
        ref = mh_reference(TARGETS[r["target"]], r["var"], r["steps"], r["x0"], r["seed"])
        diverge = next((i for i, (a, b) in enumerate(zip(bits(ref), bits(r["computable"])))
                        if a != b), None)
        same_ref = diverge is None and len(ref) == len(r["computable"])
        print(f"{r['name']}: computable = polymorphic: {same_routes}; "
              + ("numpy reference: identical, all "
                 f"{len(ref)} states" if same_ref else f"numpy reference: DIVERGES at {diverge}"))
        ok = ok and same_routes and same_ref
    return ok


# -- Plotting --------------------------------------------------------------------------------------

def style():
    plt.rcParams.update({
        "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
        "font.family": "sans-serif", "font.size": 9,
        "text.color": INK, "axes.titlecolor": INK, "axes.titlesize": 10,
        "axes.titleweight": "bold", "axes.titlelocation": "left",
        "axes.labelcolor": INK_2, "xtick.color": MUTED, "ytick.color": MUTED,
        "xtick.labelcolor": INK_2, "ytick.labelcolor": INK_2,
        "axes.edgecolor": AXIS, "axes.linewidth": 0.8,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6, "grid.linestyle": "-",
        "axes.axisbelow": True, "legend.frameon": False, "legend.labelcolor": INK_2,
        "lines.linewidth": 1.5, "lines.solid_capstyle": "round",
    })


def label(r):
    return f"proposal std {math.sqrt(r['var']):g}"


def acf(xs, max_lag):
    x = np.asarray(xs) - np.mean(xs)
    n, var = len(x), np.dot(x, x) / len(x)
    return np.array([np.dot(x[: n - k], x[k:]) / n / var for k in range(max_lag + 1)])


def accept_rate(xs):
    xs = np.asarray(xs)
    return np.mean(xs[1:] != xs[:-1])


def plot_traces(runs):
    fig, axes = plt.subplots(3, 1, figsize=(9, 6.2), sharex=True, sharey=True)
    shown = 5000
    for ax, (name, color) in zip(axes, BIMODAL_RUNS):
        r = runs[name]
        ax.plot(r["computable"][: shown + 1], color=color, linewidth=0.7)
        for mode in (-3, 3):
            ax.axhline(mode, color=AXIS, linewidth=0.8, zorder=0)
        ax.set_title(f"{label(r)}  ·  acceptance {accept_rate(r['computable']):.0%}")
        ax.set_ylabel("state")
        ax.set_ylim(-8, 8)
        ax.set_yticks([-6, -3, 0, 3, 6])
    axes[-1].set_xlabel("step")
    fig.suptitle("Random-walk Metropolis–Hastings on 0.3·N(−3, 1) + 0.7·N(3, 1): "
                 f"first {shown:,} steps", x=0.01, ha="left", fontsize=11, fontweight="bold")
    fig.text(0.01, 0.935, "Grey lines mark the two modes. Too small a proposal stays in one mode; "
             "too large a one is rarely accepted.", color=INK_2, fontsize=9)
    fig.tight_layout(rect=(0, 0, 1, 0.93))
    fig.savefig(OUT / "bimodal_traces.png", dpi=150)
    plt.close(fig)


def plot_histograms(runs):
    fig, axes = plt.subplots(1, 3, figsize=(10, 3.4), sharey=True)
    grid = np.linspace(-7, 7, 600)
    edges = np.linspace(-7, 7, 71)
    for ax, (name, color) in zip(axes, BIMODAL_RUNS):
        r = runs[name]
        xs = np.asarray(r["computable"][r["steps"] // 10:])
        ax.hist(xs, bins=edges, density=True, histtype="stepfilled", color=color, alpha=0.18)
        ax.hist(xs, bins=edges, density=True, histtype="step", color=color, linewidth=1.2,
                label="states visited")
        ax.plot(grid, bimodal_density(grid), color=INK, linewidth=1.5, label="target density")
        ax.set_title(label(r))
        ax.set_xlabel("state")
        ax.set_xticks([-6, -3, 0, 3, 6])
    axes[0].set_ylabel("density")
    axes[0].legend(loc="upper left")
    fig.suptitle(f"States visited after burn-in ({runs['bimodal_good']['steps'] * 9 // 10:,} "
                 "steps) against the target", x=0.01, ha="left", fontsize=11,
                 fontweight="bold")
    fig.tight_layout()
    fig.savefig(OUT / "bimodal_histograms.png", dpi=150)
    plt.close(fig)


def plot_diagnostics(runs):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 3.6))
    max_lag = 300
    for name, color in BIMODAL_RUNS:
        r = runs[name]
        a = acf(r["computable"][r["steps"] // 10:], max_lag)
        ax1.plot(a, color=color, label=label(r))
        xs = np.asarray(r["computable"][1:])
        ax2.plot(np.arange(1, len(xs) + 1), np.cumsum(xs) / np.arange(1, len(xs) + 1),
                 color=color, label=label(r))
    ax1.set_title("Autocorrelation after burn-in")
    ax1.set_xlabel("lag")
    ax1.set_ylim(-0.05, 1.02)
    ax1.set_xlim(0, max_lag)
    ax1.legend(loc="upper right")
    ax2.axhline(1.2, color=INK, linewidth=1, label="target mean 1.2")
    ax2.legend(loc="lower right")
    ax2.set_xscale("log")
    ax2.set_title("Running mean of the states")
    ax2.set_xlabel("step")
    ax2.set_ylim(-3.5, 3.5)
    fig.tight_layout()
    fig.savefig(OUT / "bimodal_diagnostics.png", dpi=150)
    plt.close(fig)


def plot_acceptance(runs):
    with open(OUT / "acceptance.csv") as f:
        rows = list(csv.DictReader(f))
    fig, ax = plt.subplots(figsize=(7, 3.8))
    for target, color, name in (("stdNormal", BLUE, "standard Gaussian"),
                                ("bimodal", ORANGE, "bimodal mixture")):
        pts = [(float(r["std"]), float(r["computable"])) for r in rows if r["target"] == target]
        stds, rates = zip(*pts)
        ax.plot(stds, rates, color=color, label=name, marker="o", markersize=4,
                markeredgecolor=SURFACE, markeredgewidth=1)
    ax.axhline(0.44, color=AXIS, linewidth=0.8, zorder=0)
    ax.annotate("0.44, the optimal rate in one dimension", (0.05, 0.44), xytext=(0, 4),
                textcoords="offset points", color=MUTED, fontsize=8)
    ax.set_xscale("log")
    ax.set_xlim(0.04, 65)
    ax.set_ylim(0, 1.02)
    ax.set_xlabel("proposal standard deviation")
    ax.set_ylabel("acceptance rate")
    ax.set_title("Acceptance rate against proposal size (5,000 steps each)")
    ax.legend(loc="lower left")
    fig.tight_layout()
    fig.savefig(OUT / "acceptance.png", dpi=150)
    plt.close(fig)


def plot_stdnormal(runs):
    r = runs["stdnormal"]
    xs = np.asarray(r["computable"])
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 3.4), gridspec_kw={"width_ratios": [1.6, 1]})
    ax1.plot(xs[:2001], color=BLUE, linewidth=0.8)
    ax1.set_title(f"First 2,000 steps  ·  {label(r)}, acceptance {accept_rate(xs):.0%}")
    ax1.set_xlabel("step")
    ax1.set_ylabel("state")
    grid = np.linspace(-4.5, 4.5, 400)
    edges = np.linspace(-4.5, 4.5, 61)
    after = xs[r["steps"] // 10:]
    ax2.hist(after, bins=edges, density=True, histtype="stepfilled", color=BLUE, alpha=0.18)
    ax2.hist(after, bins=edges, density=True, histtype="step", color=BLUE, linewidth=1.2,
             label="states visited")
    ax2.plot(grid, std_normal_density(grid), color=INK, label="target density")
    ax2.set_title("States visited after burn-in")
    ax2.set_xlabel("state")
    ax2.legend(loc="upper left", fontsize=8)
    fig.suptitle("Random-walk Metropolis–Hastings on the standard Gaussian", x=0.01, ha="left",
                 fontsize=11, fontweight="bold")
    fig.tight_layout()
    fig.savefig(OUT / "stdnormal.png", dpi=150)
    plt.close(fig)


def main():
    if "--run" in sys.argv:
        subprocess.run(["lake", "exe", "mh"], check=True)
    runs = load_runs()
    ok = check(runs)
    style()
    by_name = {r["name"]: r for r in runs}
    plot_traces(by_name)
    plot_histograms(by_name)
    plot_diagnostics(by_name)
    plot_acceptance(by_name)
    plot_stdnormal(by_name)
    print(f"plots written to {OUT}/")
    print("all checks passed" if ok else "SOME CHECKS FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
