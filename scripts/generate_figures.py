"""Generate 3 publication-quality figures for Paper 72 (VALIANT-HIER-CERT-1.0) from live verifier data."""

from __future__ import annotations

import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.valiant_hier_verifier import verify_file  # noqa: E402

FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 8.5,
    "axes.titlesize": 9.5,
    "axes.labelsize": 8.5,
    "xtick.labelsize": 7.8,
    "ytick.labelsize": 7.8,
    "legend.fontsize": 7.4,
    "figure.dpi": 300,
})


def _tree_min_boundary_profile(h: int) -> list[int]:
    d = (1 << h) - 1
    dp0: dict[int, list[int]] = {}
    dp1: dict[int, list[int]] = {}
    INF = 10**9
    for u in range(d, 0, -1):
        sh = h - u.bit_length() + 1
        if sh == 1:
            dp0[u] = [0, INF]
            dp1[u] = [INF, 0]
        else:
            l, r = 2 * u, 2 * u + 1
            sz_l, sz_r = len(dp0[l]) - 1, len(dp0[r]) - 1
            arr0 = [INF] * (sz_l + sz_r + 2)
            arr1 = [INF] * (sz_l + sz_r + 2)
            for kl in range(sz_l + 1):
                for kr in range(sz_r + 1):
                    v0 = min(dp0[l][kl], dp1[l][kl] + 1) + min(dp0[r][kr], dp1[r][kr] + 1)
                    if v0 < arr0[kl + kr]:
                        arr0[kl + kr] = v0
                    v1 = min(dp1[l][kl], dp0[l][kl] + 1) + min(dp1[r][kr], dp0[r][kr] + 1)
                    if v1 < arr1[kl + kr + 1]:
                        arr1[kl + kr + 1] = v1
            dp0[u] = arr0
            dp1[u] = arr1
    return [min(dp0[1][k], dp1[1][k]) for k in range(1, d)]


def make_fig1() -> None:
    """Fig. 1: Mode 1 Cut Flattening Ranks & Movable Supply-Site Savings (C01-C04)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))
    fig.subplots_adjust(wspace=0.35, left=0.09, right=0.98, bottom=0.19, top=0.84)

    r01 = verify_file(ROOT / "certificates" / "C01_state_sum_proj_grid2x2_F7.json")
    r02 = verify_file(ROOT / "certificates" / "C02_state_sum_proj_char2_F2.json")
    x = np.arange(2)
    w = 0.34
    b1 = ax1.bar(x - w / 2, [r01["crossing_edges"], r02["crossing_edges"]], width=w, color="#4C78A8", edgecolor="black", lw=0.7, label=r"Cut edges $|\partial C|$")
    b2 = ax1.bar(x + w / 2, [r01["flattening_rank"], r02["flattening_rank"]], width=w, color="#54A24B", edgecolor="black", lw=0.7, label=r"Flattening rank $q^{|\partial C|}$")
    for bar in list(b1) + list(b2):
        h = bar.get_height()
        ax1.text(bar.get_x() + bar.get_width() / 2, h + 0.25, str(int(h)), ha="center", va="bottom", fontsize=7.6, fontweight="bold")
    ax1.set_xticks(x)
    ax1.set_xticklabels(["C01 ($2{\\times}2$ grid)\n$\\mathbb{F}_7, q=2$", "C02 ($K_4{-}e$)\n$\\mathbb{F}_2, q=2$"])
    ax1.set_ylabel("Exact integer count / rank")
    ax1.set_ylim(0, 10.5)
    ax1.set_title("(a) Sec. 3 Exact Cut Flattening Rank")
    ax1.legend(loc="upper left", frameon=True)
    ax1.grid(axis="y", linestyle=":", alpha=0.5)

    r03 = verify_file(ROOT / "certificates" / "C03_supply_site_saving_grid4x4.json")
    r04 = verify_file(ROOT / "certificates" / "C04_supply_site_saving_path_fig2.json")
    s03 = r03["saving"][0] / r03["saving"][1]
    t03 = r03["target_saving"][0] / r03["target_saving"][1]
    s04 = r04["saving"][0] / r04["saving"][1]
    t04 = r04["target_saving"][0] / r04["target_saving"][1]
    b3 = ax2.bar(x - w / 2, [s03, s04], width=w, color="#4C78A8", edgecolor="black", lw=0.7, label="Certified saving")
    b4 = ax2.bar(x + w / 2, [t03, t04], width=w, color="#F58518", edgecolor="black", lw=0.7, label=r"Lemma 3.2 floor $\frac{wb}{16e}$")
    for bar in list(b3) + list(b4):
        h = bar.get_height()
        ax2.text(bar.get_x() + bar.get_width() / 2, h + 0.12, f"{h:.2f}", ha="center", va="bottom", fontsize=7.4, fontweight="bold")
    ax2.set_xticks(x)
    ax2.set_xticklabels(["C03 ($4{\\times}4$ grid)\n$e=24, b=4$", "C04 (Path Fig. 2)\n$e=2, b=1$"])
    ax2.set_ylabel("Euclidean price saving")
    ax2.set_ylim(0, 4.3)
    ax2.set_title("(b) Lemma 3.2 Movable-Site Savings")
    ax2.legend(loc="upper left", frameon=True)
    ax2.grid(axis="y", linestyle=":", alpha=0.5)

    fig.savefig(FIG_DIR / "fig1_cut_rank_and_savings.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig1_cut_rank_and_savings.png", bbox_inches="tight")
    plt.close(fig)


def make_fig2() -> None:
    """Fig. 2: Mode 2 Grid Isoperimetry (C05-C06) & Mode 3 Binary-Tree Isoperimetric Profile (C09-C10)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))
    fig.subplots_adjust(wspace=0.35, left=0.09, right=0.98, bottom=0.19, top=0.84)

    r05 = verify_file(ROOT / "certificates" / "C05_grid_isoperimetry_3x3_exhaustive.json")
    r06 = verify_file(ROOT / "certificates" / "C06_grid_isoperimetry_4x4_witnesses.json")
    x = np.arange(2)
    w = 0.34
    b1 = ax1.bar(x - w / 2, [r05["min_boundary"], r06["min_boundary"]], width=w, color="#4C78A8", edgecolor="black", lw=0.7, label=r"Verified $\min |\partial U|$")
    b2 = ax1.bar(x + w / 2, [r05["ceil_r_over_3"], r06["ceil_r_over_3"]], width=w, color="#E45756", edgecolor="black", lw=0.7, label=r"Thm. 4.1 floor $\lceil r/3 \rceil$")
    for bar in list(b1) + list(b2):
        h = bar.get_height()
        ax1.text(bar.get_x() + bar.get_width() / 2, h + 0.14, str(int(h)), ha="center", va="bottom", fontsize=7.6, fontweight="bold")
    ax1.set_xticks(x)
    ax1.set_xticklabels(["C05 ($3{\\times}3$ grid)\nAll 336 cuts", "C06 ($4{\\times}4$ grid)\nWitness suite"])
    ax1.set_ylabel("Edge boundary size")
    ax1.set_ylim(0, 5.4)
    ax1.set_title("(a) Thm. 4.1 Grid Balanced-Cut Floor")
    ax1.legend(loc="upper left", frameon=True)
    ax1.grid(axis="y", linestyle=":", alpha=0.5)

    # Panel (b): Exact Bharadwaj-Chandran profile on T_5 (d=31, C10)
    prof5 = _tree_min_boundary_profile(5)
    ks = np.arange(1, len(prof5) + 1)
    cols = ["#E45756" if v == max(prof5) else "#4C78A8" for v in prof5]
    ax2.bar(ks, prof5, color=cols, edgecolor="black", lw=0.5, width=0.72)
    ax2.annotate(
        "Hardest $k^*=11$: $\\min|\\partial U|=3$",
        xy=(11, 3.05),
        xytext=(12.2, 3.38),
        fontsize=6.9,
        fontweight="bold",
        color="#B22222",
        arrowprops={"arrowstyle": "->", "color": "#B22222", "lw": 0.9},
    )
    ax2.set_xticks([1, 5, 11, 15, 20, 25, 30])
    ax2.set_xlabel("Prescribed subset size $k = |U|$ in $T_5$")
    ax2.set_ylabel(r"Exact $\min_{|U|=k} |\partial U|$")
    ax2.set_ylim(0, 4.0)
    ax2.set_title(r"(b) Thm. 5.1 Tree $T_5$ Profile (C10)")
    ax2.grid(axis="y", linestyle=":", alpha=0.5)

    fig.savefig(FIG_DIR / "fig2_grid_and_tree_isoperimetry.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig2_grid_and_tree_isoperimetry.png", bbox_inches="tight")
    plt.close(fig)


def make_fig3() -> None:
    """Fig. 3: Mode 4 Dyadic Scale Inner-Product Bound (C13-C14) & Minor Cutwidth/Pathwidth (C15-C16)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))
    fig.subplots_adjust(wspace=0.36, left=0.09, right=0.98, bottom=0.19, top=0.84)

    r13 = verify_file(ROOT / "certificates" / "C13_path_dyadic_det_d4_q2_F11.json")
    r14 = verify_file(ROOT / "certificates" / "C14_path_dyadic_det_d8_q2_F13.json")
    v13 = r13["inner_prod_lb"][0] / r13["inner_prod_lb"][1]
    v14 = r14["inner_prod_lb"][0] / r14["inner_prod_lb"][1]
    x = np.arange(2)
    w = 0.34
    b1 = ax1.bar(x - w / 2, [v13, v14], width=w, color="#4C78A8", edgecolor="black", lw=0.7, label=r"Verified $\sum \langle a_v, z_v \rangle$ LB")
    b2 = ax1.bar(x + w / 2, [1.0, 1.5], width=w, color="#54A24B", edgecolor="black", lw=0.7, label=r"Lemma 6.3 floor $\frac{1}{2}\log_2 d$")
    for bar in list(b1) + list(b2):
        h = bar.get_height()
        ax1.text(bar.get_x() + bar.get_width() / 2, h + 0.08, f"{h:.2f}", ha="center", va="bottom", fontsize=7.5, fontweight="bold")
    ax1.set_xticks(x)
    ax1.set_xticklabels(["C13 ($P_4$, $7{\\times}7$ det)\n$\\log_2 d = 2$", "C14 ($P_8$, $15{\\times}15$ det)\n$\\log_2 d = 3$"])
    ax1.set_ylabel("Multi-scale shortening bound")
    ax1.set_ylim(0, 6.5)
    ax1.set_title("(a) Lemma 6.3 Dyadic Placement & Det")
    ax1.legend(loc="upper left", frameon=True)
    ax1.grid(axis="y", linestyle=":", alpha=0.5)

    r15 = verify_file(ROOT / "certificates" / "C15_minor_centroid_C5_to_K3_F7.json")
    r16 = verify_file(ROOT / "certificates" / "C16_minor_centroid_deg4_K14_n4_F11.json")
    w3 = 0.25
    b_pw = ax2.bar(x - w3, [r15["induced_pathwidth"], r16["induced_pathwidth"]], width=w3, color="#54A24B", edgecolor="black", lw=0.7, label="Pathwidth pw")
    b_cw = ax2.bar(x, [r15["order_cutwidth"], r16["order_cutwidth"]], width=w3, color="#4C78A8", edgecolor="black", lw=0.7, label="Cutwidth cw")
    b_up = ax2.bar(x + w3, [2 * (r15["induced_pathwidth"] + 1), 3 * (r16["induced_pathwidth"] + 1)], width=w3, color="#F58518", edgecolor="black", lw=0.7, label=r"$\Delta(\mathrm{pw}+1)$")
    for bar in list(b_pw) + list(b_cw) + list(b_up):
        h = bar.get_height()
        ax2.text(bar.get_x() + bar.get_width() / 2, h + 0.18, str(int(h)), ha="center", va="bottom", fontsize=7.4, fontweight="bold")
    ax2.set_xticks(x)
    ax2.set_xticklabels(["C15 ($C_5 \\succeq K_3$)\n$q=2, n=2$", "C16 ($T_6 \\succeq K_{1,4}$)\n$q=2, b=2, n=4$"])
    ax2.set_ylabel("Graph decomposition parameter")
    ax2.set_ylim(0, 11.4)
    ax2.set_title(r"(b) Sec. 7.3 $\mathrm{pw} \leq \mathrm{cw} \leq \Delta(\mathrm{pw}+1)$")
    ax2.legend(loc="upper left", frameon=True)
    ax2.grid(axis="y", linestyle=":", alpha=0.5)

    fig.savefig(FIG_DIR / "fig3_dyadic_det_and_minors.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig3_dyadic_det_and_minors.png", bbox_inches="tight")
    plt.close(fig)


def main() -> int:
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated 3 figures in paper/figures/.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
