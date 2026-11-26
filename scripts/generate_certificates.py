"""Generate and verify all 16 canonical VALIANT-HIER-CERT-1.0 certificates (C01-C16)."""

from __future__ import annotations

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.valiant_hier_verifier import (  # noqa: E402
    SCHEMA_VERSION,
    _build_minor_host_tables,
    _eval_state_sum_fp,
    verify_file,
)

CERT_DIR = ROOT / "certificates"
CERT_DIR.mkdir(parents=True, exist_ok=True)


def build_all() -> list[tuple[str, dict[str, object]]]:
    certs: list[tuple[str, dict[str, object]]] = []

    # C01: Mode 1a - State sum projection & flattening rank on 2x2 square grid -> P_3 over F_7
    certs.append((
        "C01_state_sum_proj_grid2x2_F7.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C01",
            "paper_reference": "Eq. (1.1), Sec. 2-3 (p. 2, 5-6): 2x2 grid state sum, subgraph projection to P_3, cut rank 2^2=4 over F_7",
            "mode": "state_sum_and_euclidean_price",
            "payload": {
                "submode": "state_sum_projection_and_cut",
                "field_prime": 7,
                "num_vertices": 4,
                "edges": [[0, 1], [1, 3], [0, 2], [2, 3]],
                "alphabet_q": 2,
                "kept_vertices": [0, 1, 3],
                "kept_edge_indices": [0, 1],
                "sub_alphabet_q": 2,
                "sub_tables": [
                    [2, 3],
                    [1, 4, 2, 5],
                    [3, 1],
                ],
                "cut_C": [0, 2],
            },
        },
    ))

    # C02: Mode 1a - Characteristic-2 state sum projection & cut rank on 4-vertex K_4-e -> C_3 over F_2
    certs.append((
        "C02_state_sum_proj_char2_F2.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C02",
            "paper_reference": "Eq. (1.1), Sec. 2-3 (p. 2, 5-6): Characteristic-2 projection & cut rank 2^3=8 over F_2",
            "mode": "state_sum_and_euclidean_price",
            "payload": {
                "submode": "state_sum_projection_and_cut",
                "field_prime": 2,
                "num_vertices": 4,
                "edges": [[0, 1], [1, 2], [2, 0], [0, 3], [2, 3]],
                "alphabet_q": 2,
                "kept_vertices": [0, 1, 2],
                "kept_edge_indices": [0, 1, 2],
                "sub_alphabet_q": 2,
                "sub_tables": [
                    [1, 0, 1, 1],
                    [1, 1, 0, 1],
                    [1, 1, 1, 0],
                ],
                "cut_C": [0, 3],
            },
        },
    ))

    # C03: Mode 1b - Lemma 3.2 movable supply-site price saving on 4x4 grid (|dC|=4, sqrt(b)=2)
    edges_g4: list[list[int]] = []
    for r in range(4):
        for c in range(3):
            edges_g4.append([r * 4 + c, r * 4 + c + 1])
    for r in range(3):
        for c in range(4):
            edges_g4.append([r * 4 + c, (r + 1) * 4 + c])
    certs.append((
        "C03_supply_site_saving_grid4x4.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C03",
            "paper_reference": "Eq. (3.3)-(3.4), Lemma 3.2 (p. 7-8): Opposite-axis ||a_C||^2=4 and movable supply-site saving on 4x4 grid",
            "mode": "state_sum_and_euclidean_price",
            "payload": {
                "submode": "movable_supply_site_saving",
                "num_vertices": 16,
                "edges": edges_g4,
                "cut_C": [0, 1, 2, 3, 4, 5, 6, 7],
                "sqrt_b_int": 2,
                "log_q_w": [100, 1],
                "log_R": [80, 1],
            },
        },
    ))

    # C04: Mode 1b - Lemma 3.2 movable supply-site price saving on 3-vertex path (Fig. 2, |dC|=2 -> b=1)
    certs.append((
        "C04_supply_site_saving_path_fig2.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C04",
            "paper_reference": "Fig. 2 & Lemma 3.2 (p. 7-8): Path A-B-D with C={B}, ||a_C||^2=2, b=1 supply-site saving",
            "mode": "state_sum_and_euclidean_price",
            "payload": {
                "submode": "movable_supply_site_saving",
                "num_vertices": 3,
                "edges": [[0, 1], [1, 2]],
                "cut_C": [1],
                "sqrt_b_int": 1,
                "log_q_w": [64, 1],
                "log_R": [24, 1],
            },
        },
    ))

    # C05: Mode 2a - Exhaustive balanced-cut isoperimetry on 3x3 square grid (all 336 balanced cuts!)
    # Count balanced subsets of 9 vertices with 3 < sz <= 6 => sz in {4, 5, 6}: C(9,4)+C(9,5)+C(9,6) = 126+126+84 = 336
    # Min boundary of 4-set in 3x3 grid is 4 (e.g. 2x2 corner block); min of 6-set is 3 (two full rows)!
    certs.append((
        "C05_grid_isoperimetry_3x3_exhaustive.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C05",
            "paper_reference": "Theorem 4.1 & Lemma 4.2 (p. 8-9): Exhaustive balanced-cut isoperimetry over all 336 cuts of 3x3 grid",
            "mode": "grid_balanced_cut_and_isoperimetry",
            "payload": {
                "submode": "grid_isoperimetry_audit",
                "grid_side_r": 3,
                "exhaustive": True,
                "expected_min_boundary": 3,
                "expected_balanced_count": 336,
            },
        },
    ))

    # C06: Mode 2a - Certified balanced-cut isoperimetry on 4x4 square grid (d=16, balanced sz in 6..10, ceil(4/3)=2)
    certs.append((
        "C06_grid_isoperimetry_4x4_witnesses.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C06",
            "paper_reference": "Theorem 4.1 & Lemma 4.2 (p. 8-9): Balanced-cut isoperimetry witnesses on 4x4 grid (min boundary 4 >= 2)",
            "mode": "grid_balanced_cut_and_isoperimetry",
            "payload": {
                "submode": "grid_isoperimetry_audit",
                "grid_side_r": 4,
                "exhaustive": False,
                "balanced_cuts": [
                    [0, 1, 2, 3, 4, 5, 6, 7],        # 2 full rows: 4 vertical edges
                    [0, 1, 4, 5, 8, 9],              # 3x2 block: 5 boundary edges
                    [0, 1, 2, 4, 5, 6, 8, 9, 10],    # 3x3 block: 6 boundary edges
                    [0, 2, 5, 7, 8, 10, 13, 15],     # checkerboard-like: high boundary
                ],
                "expected_min_boundary": 4,
            },
        },
    ))

    # C07: Mode 2b - VNP Boolean-indicator sum for 2x2 grid with q=3 (2 bits/edge, 175 unused encodings zeroed!) over F_7
    certs.append((
        "C07_vnp_boolean_indicator_grid2x2_q3_F7.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C07",
            "paper_reference": "Sec. 4 (p. 10): Characteristic-free VNP Boolean-indicator encoding of Z_{G_2,3} over F_7",
            "mode": "grid_balanced_cut_and_isoperimetry",
            "payload": {
                "submode": "vnp_boolean_indicator_sum",
                "field_prime": 7,
                "grid_side_r": 2,
                "alphabet_q": 3,
                "vertex_tables": [
                    [1, 2, 3, 4, 5, 6, 1, 3, 2],
                    [2, 1, 4, 3, 2, 5, 6, 1, 4],
                    [3, 4, 1, 2, 6, 1, 5, 2, 3],
                    [4, 3, 2, 1, 5, 4, 2, 6, 1],
                ],
                "expected_state_sum": _eval_state_sum_fp(
                    4, [(0, 1), (2, 3), (0, 2), (1, 3)], 3,
                    [
                        [1, 2, 3, 4, 5, 6, 1, 3, 2],
                        [2, 1, 4, 3, 2, 5, 6, 1, 4],
                        [3, 4, 1, 2, 6, 1, 5, 2, 3],
                        [4, 3, 2, 1, 5, 4, 2, 6, 1],
                    ], 7,
                ),
            },
        },
    ))

    # C08: Mode 2b - VNP Boolean-indicator sum in characteristic 2 (q=3 over F_2!)
    tbl_f2 = [
        [1, 0, 1, 1, 1, 0, 0, 1, 1],
        [1, 1, 0, 0, 1, 1, 1, 0, 1],
        [0, 1, 1, 1, 0, 1, 1, 1, 0],
        [1, 1, 1, 0, 1, 0, 1, 1, 1],
    ]
    z_c08 = _eval_state_sum_fp(4, [(0, 1), (2, 3), (0, 2), (1, 3)], 3, tbl_f2, 2)
    if z_c08 == 0:
        tbl_f2[0][0] ^= 1
        z_c08 = _eval_state_sum_fp(4, [(0, 1), (2, 3), (0, 2), (1, 3)], 3, tbl_f2, 2)
    certs.append((
        "C08_vnp_boolean_indicator_grid2x2_q3_F2.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C08",
            "paper_reference": "Sec. 4 (p. 10): Characteristic-2 VNP Boolean-indicator encoding of Z_{G_2,3} over F_2",
            "mode": "grid_balanced_cut_and_isoperimetry",
            "payload": {
                "submode": "vnp_boolean_indicator_sum",
                "field_prime": 2,
                "grid_side_r": 2,
                "alphabet_q": 3,
                "vertex_tables": tbl_f2,
                "expected_state_sum": z_c08,
            },
        },
    ))

    # C09: Mode 3a - Complete binary tree T_3 (h=3, d=7) Eq. (5.1) telescoping & exact Bharadwaj-Chandran profile
    # For T_3 (d=7): k=1 -> 1 (leaf), k=2 -> 2, k=3 -> 1 (subtree), k=4 -> 1 (complement of subtree), k=5 -> 2, k=6 -> 1 => max_min = 2 at k=2!
    certs.append((
        "C09_tree_telescoping_T3.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C09",
            "paper_reference": "Theorem 5.1 & Eq. (5.1) (p. 11): Complete binary tree T_3 telescoping identity & max min-boundary 2 at k=2",
            "mode": "binary_tree_telescoping_and_abp",
            "payload": {
                "submode": "tree_telescoping_boundary",
                "tree_levels_h": 3,
                "witness_subsets": [
                    [2, 4, 5],       # left subtree, size 3, boundary 1
                    [4, 5],          # two leaves, size 2, boundary 2
                    [1, 2, 4, 6],    # mixed, size 4
                ],
                "expected_max_min_boundary": 2,
                "expected_hardest_k": 2,
            },
        },
    ))

    # C10: Mode 3a - Complete binary tree T_5 (h=5, d=31) Eq. (5.1) telescoping & exact Bharadwaj-Chandran profile
    # For T_5 (d=31), subtree sizes are {1, 3, 7, 15, 31}; k=11 requires 3 boundary edges (e.g. 15-3-1=11 or 7+3+1=11)!
    certs.append((
        "C10_tree_telescoping_T5.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C10",
            "paper_reference": "Theorem 5.1 & Eq. (5.1) (p. 11): Complete binary tree T_5 (d=31) telescoping identity & max min-boundary 3 at k=11",
            "mode": "binary_tree_telescoping_and_abp",
            "payload": {
                "submode": "tree_telescoping_boundary",
                "tree_levels_h": 5,
                "witness_subsets": [
                    [2, 4, 5, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23],  # left 15-subtree, bdry 1
                    [4, 8, 9, 16, 17, 18, 19, 10, 20, 21, 22],                # size 11 = 7 + 3 + 1, bdry 3
                    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],                      # top 11 nodes
                ],
                "expected_max_min_boundary": 3,
                "expected_hardest_k": 11,
            },
        },
    ))

    # C11: Mode 3b - Lemma 5.2 ABP prefix-rank decomposition over F_7 (d=3 slots, q=2, k=1, two slot orders!)
    certs.append((
        "C11_abp_prefix_rank_d3_F7.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C11",
            "paper_reference": "Lemma 5.2 (p. 10-11): Exact ABP prefix/suffix tensor decomposition A(f)=sum_{|U|=1} T_U over F_7",
            "mode": "binary_tree_telescoping_and_abp",
            "payload": {
                "submode": "abp_prefix_rank_decomposition",
                "field_prime": 7,
                "num_slots_d": 3,
                "slot_dim_q": 2,
                "prefix_size_k": 1,
                "abp_num_nodes": 7,
                "abp_edges": [
                    # Path family 1: order (slot 0 -> slot 1 -> slot 2) through nodes 0->1,2->3->6
                    {"u": 0, "v": 1, "const_term": 1, "slot": 0, "var_idx": 0, "coeff": 2},
                    {"u": 0, "v": 2, "const_term": 0, "slot": 0, "var_idx": 1, "coeff": 3},
                    {"u": 1, "v": 3, "const_term": 2, "slot": 1, "var_idx": 0, "coeff": 4},
                    {"u": 1, "v": 3, "const_term": 0, "slot": 1, "var_idx": 1, "coeff": 1},
                    {"u": 2, "v": 3, "const_term": 0, "slot": 1, "var_idx": 1, "coeff": 5},
                    {"u": 3, "v": 6, "const_term": 1, "slot": 2, "var_idx": 0, "coeff": 2},
                    {"u": 3, "v": 6, "const_term": 0, "slot": 2, "var_idx": 1, "coeff": 6},
                    # Path family 2: order (slot 2 -> slot 0 -> slot 1) through nodes 0->4->5->6
                    {"u": 0, "v": 4, "const_term": 0, "slot": 2, "var_idx": 0, "coeff": 5},
                    {"u": 0, "v": 4, "const_term": 1, "slot": 2, "var_idx": 1, "coeff": 1},
                    {"u": 4, "v": 5, "const_term": 0, "slot": 0, "var_idx": 1, "coeff": 4},
                    {"u": 5, "v": 6, "const_term": 0, "slot": 1, "var_idx": 0, "coeff": 3},
                ],
            },
        },
    ))

    # C12: Mode 3b - Lemma 5.2 ABP prefix-rank decomposition over F_5 (d=4 slots, q=2, k=2)
    certs.append((
        "C12_abp_prefix_rank_d4_F5.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C12",
            "paper_reference": "Lemma 5.2 (p. 10-11): Exact 4-slot ABP k=2 prefix/suffix tensor decomposition over F_5",
            "mode": "binary_tree_telescoping_and_abp",
            "payload": {
                "submode": "abp_prefix_rank_decomposition",
                "field_prime": 5,
                "num_slots_d": 4,
                "slot_dim_q": 2,
                "prefix_size_k": 2,
                "abp_num_nodes": 8,
                "abp_edges": [
                    # Order (0,1,2,3) via 0->1->2->3->7
                    {"u": 0, "v": 1, "const_term": 1, "slot": 0, "var_idx": 0, "coeff": 2},
                    {"u": 0, "v": 1, "const_term": 0, "slot": 0, "var_idx": 1, "coeff": 3},
                    {"u": 1, "v": 2, "const_term": 0, "slot": 1, "var_idx": 0, "coeff": 1},
                    {"u": 1, "v": 2, "const_term": 1, "slot": 1, "var_idx": 1, "coeff": 4},
                    {"u": 2, "v": 3, "const_term": 0, "slot": 2, "var_idx": 0, "coeff": 3},
                    {"u": 2, "v": 3, "const_term": 0, "slot": 2, "var_idx": 1, "coeff": 2},
                    {"u": 3, "v": 7, "const_term": 1, "slot": 3, "var_idx": 0, "coeff": 4},
                    {"u": 3, "v": 7, "const_term": 0, "slot": 3, "var_idx": 1, "coeff": 1},
                    # Order (1,3,0,2) via 0->4->5->6->7
                    {"u": 0, "v": 4, "const_term": 0, "slot": 1, "var_idx": 1, "coeff": 2},
                    {"u": 4, "v": 5, "const_term": 0, "slot": 3, "var_idx": 0, "coeff": 3},
                    {"u": 5, "v": 6, "const_term": 0, "slot": 0, "var_idx": 0, "coeff": 4},
                    {"u": 6, "v": 7, "const_term": 0, "slot": 2, "var_idx": 1, "coeff": 2},
                ],
            },
        },
    ))

    # C13: Mode 4a - Lemma 6.3 dyadic scale clustering (d=4) + Sec. 6.3 cofactor determinant embedding (q=2, F_11)
    certs.append((
        "C13_path_dyadic_det_d4_q2_F11.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C13",
            "paper_reference": "Lemma 6.3 & Sec. 6.3 (p. 13-16): d=4 dyadic scale placement & 7x7 cofactor determinant over F_11",
            "mode": "path_multiscale_det_and_minors",
            "payload": {
                "submode": "dyadic_scale_placement_and_det",
                "path_vertices_d": 4,
                "tau_leaf_order": [0, 2, 1, 3],
                "field_prime": 11,
                "alphabet_q": 2,
                "path_tables": [
                    [2, 5],
                    [1, 3, 4, 2],
                    [5, 2, 1, 6],
                    [3, 4],
                ],
            },
        },
    ))

    # C14: Mode 4a - Lemma 6.3 dyadic scale clustering (d=8, Fig. 3!) + Sec. 6.3 cofactor determinant embedding (q=2, F_13)
    certs.append((
        "C14_path_dyadic_det_d8_q2_F13.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C14",
            "paper_reference": "Fig. 3, Lemma 6.3 & Sec. 6.3 (p. 13-16): d=8 dyadic scale placement & 15x15 cofactor determinant over F_13",
            "mode": "path_multiscale_det_and_minors",
            "payload": {
                "submode": "dyadic_scale_placement_and_det",
                "path_vertices_d": 8,
                "tau_leaf_order": [0, 4, 2, 6, 1, 5, 3, 7],
                "field_prime": 13,
                "alphabet_q": 2,
                "path_tables": [
                    [1, 3],
                    [2, 1, 4, 5],
                    [3, 2, 1, 4],
                    [1, 5, 2, 3],
                    [4, 1, 3, 2],
                    [2, 3, 5, 1],
                    [1, 2, 4, 3],
                    [5, 2],
                ],
            },
        },
    ))

    # C15: Mode 4b - Lemma 7.2 weighted-centroid minor projection (K_3 minor in 5-vertex subdivided cycle) + pw/cw sandwich
    edgesG15 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    edgesH15 = [(0, 1), (1, 2), (2, 0)]
    bsets15 = [{0, 1}, {2, 3}, {4}]
    cents15 = [0, 2, 4]
    chosen15 = [1, 3, 4]  # (1,2) connects B0-B1, (3,4) connects B1-B2, (4,0) connects B2-B0
    mt15 = [[1, 2, 3, 4], [2, 1, 5, 3], [4, 3, 2, 1]]
    ht15 = _build_minor_host_tables(5, edgesG15, 2, 3, edgesH15, 2, bsets15, cents15, chosen15, mt15)
    certs.append((
        "C15_minor_centroid_C5_to_K3_F7.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C15",
            "paper_reference": "Lemma 7.2 & Sec. 7.3 (p. 18-19): Weighted-centroid minor projection C_5 -> K_3 (q=n=2) & pw<=cw sandwich",
            "mode": "path_multiscale_det_and_minors",
            "payload": {
                "submode": "minor_centroid_and_cutwidth",
                "field_prime": 7,
                "num_vertices": 5,
                "edges": [[u, v] for (u, v) in edgesG15],
                "minor_alphabet_q": 2,
                "host_alphabet_n": 2,
                "minor_num_vertices": 3,
                "minor_edges": [[u, v] for (u, v) in edgesH15],
                "branch_sets": [sorted(s) for s in bsets15],
                "branch_centroids": cents15,
                "chosen_host_edges": chosen15,
                "minor_tables": mt15,
                "host_projected_tables": ht15,
                "vertex_order": [0, 1, 4, 2, 3],
            },
        },
    ))

    # C16: Mode 4b - Lemma 7.2 degree-4 star minor K_{1,4} (Delta_H=4, b=2, q=2, n=q^2=4!) in 6-vertex tree host!
    # Host G: center 0 joined to 1 (internal branch edge), 1 joined to 2,3; 0 joined to 4,5 -> H = K_{1,4} on 5 vertices!
    # Branch sets: B0={0,1} (centroid 0, weights: w(0)=2 from edges to 4,5; w(1)=2 from edges to 2,3 -> child comp {1} has wt 2 <= 4/2 = 2!)
    # Host alphabet n = q^2 = 4 encodes the 2-label tuple on tree edge (0,1)!
    edgesG16 = [(0, 1), (1, 2), (1, 3), (0, 4), (0, 5)]
    edgesH16 = [(0, 1), (0, 2), (0, 3), (0, 4)]
    bsets16 = [{0, 1}, {2}, {3}, {4}, {5}]
    cents16 = [0, 2, 3, 4, 5]
    chosen16 = [1, 2, 3, 4]  # (1,2), (1,3), (0,4), (0,5)
    mt16 = [
        [1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 4, 2, 3, 1, 2, 5],  # vertex 0 has deg 4 => 2^4=16 entries
        [2, 3],
        [1, 4],
        [3, 2],
        [4, 1],
    ]
    ht16 = _build_minor_host_tables(6, edgesG16, 4, 5, edgesH16, 2, bsets16, cents16, chosen16, mt16)
    certs.append((
        "C16_minor_centroid_deg4_K14_n4_F11.json",
        {
            "schema_version": SCHEMA_VERSION,
            "certificate_id": "C16",
            "paper_reference": "Lemma 7.2 & Sec. 7.3 (p. 18-19): Degree-4 centroid tuple-packing minor K_{1,4} (q=2, b=2, n=4) over F_11",
            "mode": "path_multiscale_det_and_minors",
            "payload": {
                "submode": "minor_centroid_and_cutwidth",
                "field_prime": 11,
                "num_vertices": 6,
                "edges": [[u, v] for (u, v) in edgesG16],
                "minor_alphabet_q": 2,
                "host_alphabet_n": 4,
                "minor_num_vertices": 5,
                "minor_edges": [[u, v] for (u, v) in edgesH16],
                "branch_sets": [sorted(s) for s in bsets16],
                "branch_centroids": cents16,
                "chosen_host_edges": chosen16,
                "minor_tables": mt16,
                "host_projected_tables": ht16,
                "vertex_order": [2, 1, 3, 0, 4, 5],
            },
        },
    ))

    return certs


def main() -> int:
    certs = build_all()
    for fname, obj in certs:
        p = CERT_DIR / fname
        p.write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8", newline="\n")
        res = verify_file(p)
        print(f"Generated & verified {fname}: {res['mode']} ({res['submode']})")
    print(f"Total certificates generated: {len(certs)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
