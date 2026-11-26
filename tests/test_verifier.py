"""Comprehensive unit, hygiene, canonical corpus, and adversarial forgery test suite for VALIANT-HIER-CERT-1.0."""

from __future__ import annotations

import ast
import json
import pathlib
import sys

import pytest

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.valiant_hier_verifier import (  # noqa: E402
    MAX_JSON_BYTES,
    VerificationError,
    verify_certificate,
    verify_file,
)

CERT_DIR = ROOT / "certificates"
ALL_CERTS = sorted(CERT_DIR.glob("*.json"))


def _load(prefix: str) -> dict:
    matches = sorted(CERT_DIR.glob(f"{prefix}_*.json"))
    assert len(matches) == 1
    return json.loads(matches[0].read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# 1. Zero-Float / Zero-Division / Zero-Math AST Hygiene
# ---------------------------------------------------------------------------

def test_ast_zero_float_zero_division_zero_math() -> None:
    src_path = ROOT / "src" / "valiant_hier_verifier.py"
    tree = ast.parse(src_path.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            pytest.fail(f"Float literal found in verifier at line {node.lineno}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float":
            pytest.fail(f"float() call found at line {node.lineno}")
        if isinstance(node, (ast.Div,)):
            pytest.fail(f"True division operator / found at line {node.lineno}")
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name in {"math", "cmath", "numpy", "scipy"}:
                    pytest.fail(f"Forbidden floating-point module {alias.name} imported")
        if isinstance(node, ast.ImportFrom) and node.module in {"math", "cmath", "numpy", "scipy"}:
            pytest.fail(f"Forbidden floating-point module {node.module} imported")


# ---------------------------------------------------------------------------
# 2. Canonical 16-Certificate Corpus Verification
# ---------------------------------------------------------------------------

def test_canonical_corpus_count() -> None:
    assert len(ALL_CERTS) == 16


@pytest.mark.parametrize("cert_path", ALL_CERTS, ids=lambda p: p.name)
def test_canonical_certificate_verifies(cert_path: pathlib.Path) -> None:
    res = verify_file(cert_path)
    assert res["status"] == "VERIFIED"


# ---------------------------------------------------------------------------
# 3. Schema, Parsing, Size, NaN, Duplicate Keys & Recursion Hardening
# ---------------------------------------------------------------------------

def test_reject_wrong_schema_version() -> None:
    c = _load("C01")
    c["schema_version"] = "BAD-1.0"
    with pytest.raises(VerificationError):
        verify_certificate(c)


def test_reject_unknown_mode() -> None:
    c = _load("C01")
    c["mode"] = "bogus"
    with pytest.raises(VerificationError):
        verify_certificate(c)


def test_reject_duplicate_json_keys(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "dup.json"
    p.write_text('{"schema_version": "VALIANT-HIER-CERT-1.0", "schema_version": "VALIANT-HIER-CERT-1.0"}', encoding="utf-8")
    with pytest.raises(VerificationError, match="Duplicate JSON key"):
        verify_file(p)


def test_reject_nan_and_infinity(tmp_path: pathlib.Path) -> None:
    for tok in ("NaN", "Infinity", "-Infinity"):
        p = tmp_path / f"bad_{tok}.json"
        p.write_text(f'{{"schema_version": "VALIANT-HIER-CERT-1.0", "x": {tok}}}', encoding="utf-8")
        with pytest.raises(VerificationError, match="non-finite"):
            verify_file(p)


def test_reject_oversized_json(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "huge.json"
    p.write_bytes(b" " * (MAX_JSON_BYTES + 10))
    with pytest.raises(VerificationError, match="MAX_JSON_BYTES"):
        verify_file(p)


def test_reject_deeply_nested_json(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "deep.json"
    p.write_text("[" * 1500 + "0" + "]" * 1500, encoding="utf-8")
    with pytest.raises(VerificationError):
        verify_file(p)


def test_reject_unreduced_rational() -> None:
    c = _load("C03")
    c["payload"]["log_q_w"] = [200, 2]
    with pytest.raises(VerificationError, match="lowest terms"):
        verify_certificate(c)


def test_reject_bool_as_int() -> None:
    c = _load("C01")
    c["payload"]["alphabet_q"] = True
    with pytest.raises(VerificationError):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 4. Mode 1 Adversarial Forgeries
# ---------------------------------------------------------------------------

def test_mode1_reject_self_loop() -> None:
    c = _load("C01")
    c["payload"]["edges"][0] = [0, 0]
    with pytest.raises(VerificationError, match="Self-loop"):
        verify_certificate(c)


def test_mode1_reject_non_prime_field() -> None:
    c = _load("C01")
    c["payload"]["field_prime"] = 9
    with pytest.raises(VerificationError, match="not prime"):
        verify_certificate(c)


def test_mode1_reject_vacuous_all_zero_sub_tables() -> None:
    c = _load("C01")
    c["payload"]["sub_tables"] = [[0, 0], [0, 0, 0, 0], [0, 0]]
    with pytest.raises(VerificationError, match="all-zero"):
        verify_certificate(c)


def test_mode1_reject_kept_edge_leaving_kept_vertices() -> None:
    c = _load("C01")
    c["payload"]["kept_edge_indices"] = [0, 2]  # edge 2 = (0, 2), vertex 2 not kept
    with pytest.raises(VerificationError, match="leaves kept_vertices"):
        verify_certificate(c)


def test_mode1_reject_sqrt_b_exceeding_cut() -> None:
    c = _load("C03")
    c["payload"]["sqrt_b_int"] = 3  # 9 > 4
    with pytest.raises(VerificationError, match="sqrt_b_int"):
        verify_certificate(c)


def test_mode1_reject_log_R_too_large() -> None:
    c = _load("C03")
    c["payload"]["log_R"] = [100, 1]  # == (1/2) * 100 * 2, not strictly less
    with pytest.raises(VerificationError, match="Lemma 3.2 requires"):
        verify_certificate(c)


def test_mode1_reject_unknown_submode() -> None:
    c = _load("C01")
    c["payload"]["submode"] = "nope"
    with pytest.raises(VerificationError):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 5. Mode 2 Adversarial Forgeries
# ---------------------------------------------------------------------------

def test_mode2_reject_wrong_exhaustive_min_boundary() -> None:
    c = _load("C05")
    c["payload"]["expected_min_boundary"] = 4
    with pytest.raises(VerificationError, match="Mismatch"):
        verify_certificate(c)


def test_mode2_reject_unbalanced_grid_cut() -> None:
    c = _load("C06")
    c["payload"]["balanced_cuts"][0] = [0, 1]  # size 2 <= 16/3
    with pytest.raises(VerificationError, match="balanced range"):
        verify_certificate(c)


def test_mode2_reject_duplicate_vertex_in_cut() -> None:
    c = _load("C06")
    c["payload"]["balanced_cuts"][0] = [0, 0, 1, 2, 3, 4, 5, 6]
    with pytest.raises(VerificationError, match="Duplicate vertex"):
        verify_certificate(c)


def test_mode2_reject_wrong_vnp_expected_sum() -> None:
    c = _load("C07")
    c["payload"]["expected_state_sum"] = (c["payload"]["expected_state_sum"] % 6) + 1
    if c["payload"]["expected_state_sum"] == _load("C07")["payload"]["expected_state_sum"]:
        c["payload"]["expected_state_sum"] = 1
    with pytest.raises(VerificationError, match="expected_state_sum"):
        verify_certificate(c)


def test_mode2_reject_vacuous_zero_vnp_grid() -> None:
    c = _load("C07")
    c["payload"]["vertex_tables"][0] = [0] * 9
    with pytest.raises(VerificationError, match="Vacuous zero"):
        verify_certificate(c)


def test_mode2_reject_unknown_submode() -> None:
    c = _load("C05")
    c["payload"]["submode"] = "nope"
    with pytest.raises(VerificationError):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 6. Mode 3 Adversarial Forgeries
# ---------------------------------------------------------------------------

def test_mode3_reject_wrong_tree_hardest_k() -> None:
    c = _load("C09")
    c["payload"]["expected_hardest_k"] = 3  # min boundary at k=3 is 1, not 2
    with pytest.raises(VerificationError, match="Expected max_min"):
        verify_certificate(c)


def test_mode3_reject_wrong_tree_max_min_boundary() -> None:
    c = _load("C10")
    c["payload"]["expected_max_min_boundary"] = 4
    with pytest.raises(VerificationError, match="Expected max_min"):
        verify_certificate(c)


def test_mode3_reject_duplicate_vertex_in_tree_subset() -> None:
    c = _load("C09")
    c["payload"]["witness_subsets"][0] = [2, 2, 4]
    with pytest.raises(VerificationError, match="Duplicate vertex"):
        verify_certificate(c)


def test_mode3_reject_cyclic_abp_edge() -> None:
    c = _load("C11")
    c["payload"]["abp_edges"][0]["u"] = 3
    c["payload"]["abp_edges"][0]["v"] = 1
    with pytest.raises(VerificationError, match="topologically ordered DAG"):
        verify_certificate(c)


def test_mode3_reject_vacuous_zero_abp() -> None:
    c = _load("C11")
    for e in c["payload"]["abp_edges"]:
        e["coeff"] = 0
    with pytest.raises(VerificationError, match="Vacuous zero slot tensor"):
        verify_certificate(c)


def test_mode3_reject_unknown_submode() -> None:
    c = _load("C09")
    c["payload"]["submode"] = "nope"
    with pytest.raises(VerificationError):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 7. Mode 4 Adversarial Forgeries
# ---------------------------------------------------------------------------

def test_mode4_reject_invalid_leaf_order() -> None:
    c = _load("C13")
    c["payload"]["tau_leaf_order"] = [0, 0, 1, 2]
    with pytest.raises(VerificationError, match="not a permutation"):
        verify_certificate(c)


def test_mode4_reject_vacuous_zero_path_sum() -> None:
    c = _load("C13")
    c["payload"]["path_tables"][0] = [0, 0]
    with pytest.raises(VerificationError, match="Vacuous zero path"):
        verify_certificate(c)


def test_mode4_reject_minor_alphabet_too_small() -> None:
    c = _load("C16")
    c["payload"]["host_alphabet_n"] = 2  # q^b = 2^2 = 4 > 2
    with pytest.raises(VerificationError, match="Lemma 7.2 alphabet"):
        verify_certificate(c)


def test_mode4_reject_overlapping_branch_sets() -> None:
    c = _load("C15")
    c["payload"]["branch_sets"][1] = [1, 2, 3]  # overlaps vertex 1 with B0
    with pytest.raises(VerificationError, match="pairwise disjoint"):
        verify_certificate(c)


def test_mode4_reject_disconnected_branch_set() -> None:
    c = _load("C15")
    c["payload"]["branch_sets"] = [[0, 2], [1, 3], [4]]
    c["payload"]["branch_centroids"] = [0, 1, 4]
    with pytest.raises(VerificationError):
        verify_certificate(c)


def test_mode4_reject_corrupted_minor_projection_table() -> None:
    c = _load("C15")
    c["payload"]["host_projected_tables"][0][0] = (c["payload"]["host_projected_tables"][0][0] + 1) % 7
    with pytest.raises(VerificationError, match="minor projection mismatch"):
        verify_certificate(c)


def test_mode4_reject_unbalanced_centroid() -> None:
    # For C16, branch set {0, 1} has centroid 0 (wt 2, comp {1} wt 2 <= 2); move edge (0,4) to (1,4) would make wt(1)=3 > 2,
    # or test centroid outside branch set:
    c = _load("C16")
    c["payload"]["branch_centroids"][0] = 2
    with pytest.raises(VerificationError, match="not in branch_set"):
        verify_certificate(c)


def test_mode4_reject_bad_vertex_order() -> None:
    c = _load("C15")
    c["payload"]["vertex_order"] = [0, 0, 1, 2, 3]
    with pytest.raises(VerificationError, match="not a permutation"):
        verify_certificate(c)


def test_mode4_reject_unknown_submode() -> None:
    c = _load("C13")
    c["payload"]["submode"] = "nope"
    with pytest.raises(VerificationError):
        verify_certificate(c)


def test_mode1_reject_duplicate_cut_vertex() -> None:
    c = _load("C01")
    c["payload"]["cut_C"] = [0, 0]
    with pytest.raises(VerificationError, match="Duplicate vertices"):
        verify_certificate(c)


def test_mode1_reject_zero_crossing_cut() -> None:
    c = _load("C03")
    # Make a disconnected graph where cut_C has 0 crossing edges
    c["payload"]["num_vertices"] = 4
    c["payload"]["edges"] = [[0, 1], [2, 3]]
    c["payload"]["cut_C"] = [0, 1]
    with pytest.raises(VerificationError, match="zero-crossing"):
        verify_certificate(c)


def test_mode2_reject_exhaustive_r_above_3() -> None:
    c = _load("C05")
    c["payload"]["grid_side_r"] = 4
    with pytest.raises(VerificationError, match="capped at r <= 3"):
        verify_certificate(c)


def test_mode3_reject_non_prime_abp_field() -> None:
    c = _load("C11")
    c["payload"]["field_prime"] = 4
    with pytest.raises(VerificationError, match="not prime"):
        verify_certificate(c)


def test_mode4_reject_unsupported_path_length() -> None:
    c = _load("C13")
    c["payload"]["path_vertices_d"] = 6
    with pytest.raises(VerificationError, match="4 or 8"):
        verify_certificate(c)


def test_mode4_reject_duplicate_chosen_host_edges() -> None:
    c = _load("C15")
    c["payload"]["chosen_host_edges"] = [1, 1, 4]
    with pytest.raises(VerificationError, match="Duplicate chosen host edges"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 8. Round 2 Hardening Tests (B1, B2, P1)
# ---------------------------------------------------------------------------

def test_reject_json_float_literal(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "flt.json"
    p.write_text('{"schema_version": "VALIANT-HIER-CERT-1.0", "x": 1.5}', encoding="utf-8")
    with pytest.raises(VerificationError, match="floating-point"):
        verify_file(p)


def test_reject_huge_digit_int_value_error(tmp_path: pathlib.Path) -> None:
    p = tmp_path / "huge_int.json"
    p.write_text('{"schema_version": "VALIANT-HIER-CERT-1.0", "x": ' + "9" * 5000 + "}", encoding="utf-8")
    with pytest.raises(VerificationError, match="Invalid JSON"):
        verify_file(p)


def test_mode1_reject_short_sub_table_cleanly() -> None:
    c = _load("C01")
    c["payload"]["sub_tables"][1] = [1]  # expected length 4, must raise VerificationError not IndexError
    with pytest.raises(VerificationError, match="q_sub\\^deg"):
        verify_certificate(c)


def test_mode1_reject_exponential_edge_dos() -> None:
    c = _load("C01")
    c["payload"]["num_vertices"] = 12
    c["payload"]["edges"] = [[i, i + 1] for i in range(11)] * 2  # 22 edges -> 2^22 > 20000
    c["payload"]["alphabet_q"] = 4  # 4^22 huge -> must be caught BEFORE allocation!
    with pytest.raises(VerificationError, match="exceeds cap 20000"):
        verify_certificate(c)


def test_mode4_reject_forged_host_table_matching_scalar_z() -> None:
    # Forge host_projected_tables on C15 with a single nonzero entry equal to z_H (all-zero assignment)
    # so Z_G == Z_H numerically, yet host_projected_tables is NOT the Lemma 7.2 centroid projection!
    c = _load("C15")
    for vi in range(len(c["payload"]["host_projected_tables"])):
        n_ent = len(c["payload"]["host_projected_tables"][vi])
        c["payload"]["host_projected_tables"][vi] = [6 if vi == 0 else 1] + [0] * (n_ent - 1)
    with pytest.raises(VerificationError, match="deterministic centroid projection"):
        verify_certificate(c)


def test_mode4_reject_truly_unbalanced_centroid_component() -> None:
    # Build a minor H = K_{1,3} where branch set {0, 1} has centroid 0, wt(0)=1, wt(1)=2 => 2*2=4 > degH(0)=3!
    c = _load("C16")
    # Rewire edge (0,4) -> (1,4) so vertex 1 carries 3 chosen edges and vertex 0 carries 1; 2*3 = 6 > 4!
    c["payload"]["edges"][3] = [1, 4]
    with pytest.raises(VerificationError, match="Centroid balance violated"):
        verify_certificate(c)


def test_mode4_reject_duplicate_vertex_in_branch_set() -> None:
    c = _load("C15")
    c["payload"]["branch_sets"][0] = [0, 0, 1]
    with pytest.raises(VerificationError, match="Duplicate vertex inside branch_set"):
        verify_certificate(c)


def test_mode2_reject_duplicate_balanced_cut() -> None:
    c = _load("C06")
    c["payload"]["balanced_cuts"].append(list(c["payload"]["balanced_cuts"][0]))
    with pytest.raises(VerificationError, match="Duplicate balanced cut"):
        verify_certificate(c)


def test_mode3_reject_duplicate_tree_subset() -> None:
    c = _load("C09")
    c["payload"]["witness_subsets"].append(list(c["payload"]["witness_subsets"][0]))
    with pytest.raises(VerificationError, match="Duplicate tree witness subset"):
        verify_certificate(c)
