"""Check and plot the Gaussian bandit runs of `lake exe bandits`.

Usage, from the root of the repository:

    python3 scripts/bandit_plot.py          # reads bandit_output/, written by `lake exe bandits`
    python3 scripts/bandit_plot.py --run    # runs `lake exe bandits` first

It checks that a reference implementation in numpy, seeded alike, produces the regret of the first
seeds of each algorithm, bit for bit. It draws with `default_rng(seed)`: `standard_normal` for the
rewards, and for ε-greedy `binomial(1, ε)` for the coin and `integers(K)` for the uniform arm, in
that order, which `NumLean` reproduces. It computes in doubles as the Lean program does: the reward
is `fma(sqrt(variance), z, mean)`, as in `NumLean.normal`, the argmax is the first maximal index, as
the `Float` instance of `HasArgmax`, and `sqrt` and `log` are libm's.

It draws, in bandit_output/:
* bandit_regret.png: the regret of each algorithm against the bound proved for it, an upper bound in
  `Bandits.Theory` for explore-then-commit and UCB, a lower bound in `Bandits.EpsGreedy` for
  ε-greedy;
* bandit_compare.png: the four algorithms together, and single runs of explore-then-commit.
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

OUT = Path("bandit_output")

SURFACE, INK, INK_2, MUTED, GRID, AXIS = (
    "#fcfcfb", "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7")
COLORS = {"etc_m10": "#2a78d6", "etc_m50": "#eb6834", "ucb_c3": "#1baf7a",
          "epsgreedy_0.1": "#eda100"}
LABELS = {"etc_m10": "explore-then-commit, m = 10", "etc_m50": "explore-then-commit, m = 50",
          "ucb_c3": "UCB, c = 3", "epsgreedy_0.1": "ε-greedy, ε = 0.1"}
ORDER = ["etc_m10", "etc_m50", "ucb_c3", "epsgreedy_0.1"]


def from_hex(h):
    return struct.unpack("<d", int(h, 16).to_bytes(8, "little"))[0]


def bits(x):
    return struct.pack("<d", x)


# -- The reference implementation ------------------------------------------------------------------

def fma(a, b, c):
    """`a * b + c`, rounded once, as `Float.fma`."""
    return float(Fraction(a) * Fraction(b) + Fraction(c))


def argmax_first(xs):
    best = 0
    for a in range(len(xs)):
        if xs[best] < xs[a]:
            best = a
    return best


def greedy(N, S):
    """The first arm never pulled, and otherwise the best empirical mean: `greedyArm`."""
    for a in range(len(N)):
        if N[a] == 0:
            return a
    return argmax_first([S[a] / float(N[a]) for a in range(len(N))])


def choose(alg, param, n, N, S, last):
    K = len(N)
    if alg == "etc":
        m = param
        if n < K * m:
            return n % K
        if n == K * m:
            return argmax_first([S[a] / float(N[a]) for a in range(K)])
        return last
    c = param
    if n < K:
        return n % K
    return argmax_first([S[a] / float(N[a]) + math.sqrt(2.0 * c * math.log(float(n) + 1.0)
                                                        / float(N[a])) for a in range(K)])


def run_reference(alg, param, means, var, seed, T):
    rng = np.random.default_rng(seed)
    K = len(means)
    N, S, last = [0] * K, [0.0] * K, 0
    sd = math.sqrt(var)
    regret, curve = 0.0, []
    for n in range(T):
        if alg == "epsgreedy":
            coin = rng.binomial(1, max(0.0, min(1.0, param)))
            u = int(rng.integers(K))
            a = u if coin == 1 else greedy(N, S)
        else:
            a = choose(alg, param, n, N, S, last)
        r = fma(sd, rng.standard_normal(), means[a])
        N[a] += 1
        S[a] = S[a] + r
        last = a
        regret = regret + (1.0 - means[a])
        curve.append(regret)
    return curve


# -- The bounds of `Bandits.Theory` ----------------------------------------------------------------

def etc_bound(gaps, m, var, n):
    """`integral_regret_etc_le`, valid for `n ≥ K m`."""
    K = len(gaps)
    return sum(g * (m + (n - K * m) * math.exp(-m * g * g / (4 * var))) for g in gaps)


def epsgreedy_lower_bound(gaps, eps, n):
    """`le_integral_regret_banditRunRand`: a lower bound."""
    return n * eps / len(gaps) * sum(gaps)


def ucb_bound(gaps, c, var, n, const_sum):
    """`integral_regret_ucb_le`; the arm with no gap contributes nothing."""
    return sum(8 * c * math.log(n + 1) / g + g * (2 + 2 * const_sum) for g in gaps if g > 0)


# -- Loading and checking --------------------------------------------------------------------------

def load():
    with open(OUT / "config.csv") as f:
        config = list(csv.DictReader(f))
    runs = {}
    for c in config:
        name = c["name"]
        with open(OUT / f"{name}.csv") as f:
            rows = list(csv.DictReader(f))
        with open(OUT / f"{name}_paths.csv") as f:
            prows = list(csv.DictReader(f))
        seeds = [k for k in prows[0] if k.startswith("seed")]
        runs[name] = dict(
            alg=c["algorithm"], param=int(c["parameter"]) if c["algorithm"] == "etc"
            else float(c["parameter"]), T=int(c["rounds"]), seeds=int(c["seeds"]),
            means=[float(x) for x in c["means"].split(";")], var=float(c["variance"]),
            round=np.array([int(r["round"]) for r in rows]),
            mean=np.array([float(r["mean"]) for r in rows]),
            se=np.array([float(r["se"]) for r in rows]),
            q10=np.array([float(r["q10"]) for r in rows]),
            q90=np.array([float(r["q90"]) for r in rows]),
            paths={int(k[4:]): [from_hex(r[k]) for r in prows] for k in seeds})
    return runs


def check(runs):
    ok = True
    for name, r in runs.items():
        for seed, path in r["paths"].items():
            ref = run_reference(r["alg"], r["param"], r["means"], r["var"], seed, r["T"])
            same = [bits(x) for x in ref] == [bits(x) for x in path]
            ok = ok and same
            if not same:
                i = next(i for i, (x, y) in enumerate(zip(ref, path)) if bits(x) != bits(y))
                print(f"{name} seed {seed}: DIVERGES at round {i + 1}")
        print(f"{name}: numpy reference identical on seeds {sorted(r['paths'])}, "
              f"all {r['T']} rounds" if ok else f"{name}: MISMATCH")
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
        "lines.linewidth": 1.8, "lines.solid_capstyle": "round",
    })


def bound_curve(r):
    means, var = r["means"], r["var"]
    gaps = [max(means) - m for m in means]
    n = r["round"]
    if r["alg"] == "epsgreedy":
        return n, np.array([epsgreedy_lower_bound(gaps, r["param"], k) for k in n])
    if r["alg"] == "etc":
        m = r["param"]
        start = len(means) * m
        ns = n[n >= start]
        return ns, np.array([etc_bound(gaps, m, var, k) for k in ns])
    c = r["param"]
    const = np.cumsum([1.0 / (s + 1) ** (c / var - 1) for s in range(int(n[-1]))])
    return n, np.array([ucb_bound(gaps, c, var, k, const[k - 1]) for k in n])


def plot_regret(runs):
    fig, axes = plt.subplots(2, 2, figsize=(10, 7))
    axes = axes.ravel()
    for ax, name in zip(axes, ORDER):
        r, color = runs[name], COLORS[name]
        ns, b = bound_curve(r)
        kind = "lower" if r["alg"] == "epsgreedy" else "upper"
        ax.plot(ns, b, color=INK, linewidth=1.5, label=f"{kind} bound proved in Lean")
        ax.fill_between(r["round"], r["q10"], r["q90"], color=color, alpha=0.16, linewidth=0,
                        label="10%–90% of the runs")
        ax.plot(r["round"], r["mean"], color=color, label=f"mean over {r['seeds']} runs")
        ax.set_title(LABELS[name])
        ax.set_xlabel("round")
        ax.set_ylim(0, max(b[-1], r["q90"][-1]) * 1.08)
        below = kind == "lower"
        ax.annotate(f"{b[-1]:.0f}", (ns[-1], b[-1]), xytext=(-4, -11 if below else 4),
                    textcoords="offset points", ha="right", color=INK_2, fontsize=8)
        ax.annotate(f"{r['mean'][-1]:.0f}", (r["round"][-1], r["mean"][-1]),
                    xytext=(-4, 4), textcoords="offset points", ha="right", color=INK_2, fontsize=8)
        ax.legend(loc="upper left", fontsize=8)
    axes[0].set_ylabel("cumulative pseudo-regret")
    axes[2].set_ylabel("cumulative pseudo-regret")
    fig.suptitle("Regret of the rdo bandit programs against the bounds proved for them",
                 x=0.01, ha="left", fontsize=11, fontweight="bold")
    fig.text(0.01, 0.945, "3 Gaussian arms, means 1, 0.5 and 0, variance 1; 300 runs of 5,000 "
             "rounds each", color=INK_2, fontsize=9)
    fig.tight_layout(rect=(0, 0, 1, 0.95))
    fig.savefig(OUT / "bandit_regret.png", dpi=150)
    plt.close(fig)


def plot_compare(runs):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 3.7))
    for name in ORDER:
        r = runs[name]
        ax1.plot(r["round"], r["mean"], color=COLORS[name], label=LABELS[name])
    ax1.set_title("Mean regret")
    ax1.set_xlabel("round")
    ax1.set_ylabel("cumulative pseudo-regret")
    ax1.legend(loc="upper left", fontsize=8)
    r = runs["etc_m10"]
    for seed, path in sorted(r["paths"].items()):
        ax2.plot(r["round"], path, color=COLORS["etc_m10"], linewidth=1.1, alpha=0.9)
    ax2.axvline(len(r["means"]) * r["param"], color=AXIS, linewidth=0.8, zorder=0)
    ax2.set_title("Five runs of explore-then-commit, m = 10")
    ax2.set_xlabel("round")
    ax2.annotate("commits after 30 rounds", (len(r["means"]) * r["param"], 0), xytext=(4, 6),
                 textcoords="offset points", color=MUTED, fontsize=8)
    fig.tight_layout()
    fig.savefig(OUT / "bandit_compare.png", dpi=150)
    plt.close(fig)


def main():
    if "--run" in sys.argv:
        subprocess.run(["lake", "exe", "bandits"], check=True)
    runs = load()
    ok = check(runs)
    style()
    plot_regret(runs)
    plot_compare(runs)
    print(f"plots written to {OUT}/")
    print("all checks passed" if ok else "SOME CHECKS FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
