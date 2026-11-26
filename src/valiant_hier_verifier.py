"""
VALIANT-HIER-CERT-1.0: Zero-floating-point exact algebraic verifier for OpenAI's
"Paths, trees and grids separate Valiant's hierarchy" (November 24, 2026).

Strictly zero floating-point literals, zero float() calls, zero true-division (/ or /=),
and zero math/numpy imports. All arithmetic uses exact Python int, fractions.Fraction
(parsed from lowest-terms [num, den] pairs), or finite fields F_p.
"""

from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction
from typing import Any

SCHEMA_VERSION = "VALIANT-HIER-CERT-1.0"
MAX_JSON_BYTES = 1_000_000
MAX_RATIONAL_ABS = 10**18


class VerificationError(ValueError):
    """Raised whenever a certificate violates schema, bounds, or mathematical invariants."""


def _gcd(a: int, b: int) -> int:
    a = abs(a)
    b = abs(b)
    while b:
        a, b = b, a % b
    return a


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def _req_int(val: Any, name: str, lo: int | None = None, hi: int | None = None) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise VerificationError(f"Expected integer for {name}, got {type(val).__name__}")
    if lo is not None and val < lo:
        raise VerificationError(f"{name}={val} below minimum {lo}")
    if hi is not None and val > hi:
        raise VerificationError(f"{name}={val} above maximum {hi}")
    return val


def _req_str(val: Any, name: str) -> str:
    if not isinstance(val, str) or not val.strip():
        raise VerificationError(f"Expected non-empty string for {name}")
    return val


def _req_list(val: Any, name: str, min_len: int = 0, max_len: int = 10000) -> list[Any]:
    if not isinstance(val, list):
        raise VerificationError(f"Expected list for {name}")
    if len(val) < min_len or len(val) > max_len:
        raise VerificationError(f"{name} length {len(val)} out of range [{min_len}, {max_len}]")
    return val


def _req_dict(val: Any, name: str) -> dict[str, Any]:
    if not isinstance(val, dict):
        raise VerificationError(f"Expected dict for {name}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if not isinstance(val, list) or len(val) != 2:
        raise VerificationError(f"Expected [num, den] rational pair for {name}")
    num = _req_int(val[0], f"{name}[0]", -MAX_RATIONAL_ABS, MAX_RATIONAL_ABS)
    den = _req_int(val[1], f"{name}[1]", 1, MAX_RATIONAL_ABS)
    if _gcd(num, den) != 1:
        raise VerificationError(f"Rational {name}=[{num},{den}] not in lowest terms")
    return Fraction(num, den)


def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise VerificationError(f"Duplicate JSON key: {k}")
        out[k] = v
    return out


def _reject_json_constant(token: str) -> Any:
    raise VerificationError(f"Illegal non-finite JSON constant: {token}")


def _reject_json_float(token: str) -> Any:
    raise VerificationError(f"Illegal floating-point JSON literal: {token}")


def _mod_inv(a: int, p: int) -> int:
    a = a % p
    if a == 0:
        raise VerificationError(f"Non-invertible 0 mod {p}")
    return pow(a, p - 2, p)


def _mat_rank_fp(mat: list[list[int]], p: int) -> int:
    if not mat or not mat[0]:
        return 0
    rows = [[x % p for x in r] for r in mat]
    m = len(rows)
    n = len(rows[0])
    rank = 0
    for col in range(n):
        piv = -1
        for r in range(rank, m):
            if rows[r][col] != 0:
                piv = r
                break
        if piv == -1:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv_p = _mod_inv(rows[rank][col], p)
        for r in range(rank + 1, m):
            if rows[r][col] != 0:
                fac = (rows[r][col] * inv_p) % p
                for c in range(col, n):
                    rows[r][c] = (rows[r][c] - fac * rows[rank][c]) % p
        rank += 1
    return rank


def _mat_det_fp(mat: list[list[int]], p: int) -> int:
    n = len(mat)
    rows = [[x % p for x in r] for r in mat]
    det = 1
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if rows[r][col] != 0:
                piv = r
                break
        if piv == -1:
            return 0
        if piv != col:
            rows[col], rows[piv] = rows[piv], rows[col]
            det = (p - det) % p
        val = rows[col][col]
        det = (det * val) % p
        inv_v = _mod_inv(val, p)
        for r in range(col + 1, n):
            if rows[r][col] != 0:
                fac = (rows[r][col] * inv_v) % p
                for c in range(col, n):
                    rows[r][c] = (rows[r][c] - fac * rows[col][c]) % p
    return det


def _eval_state_sum_fp(
    num_vertices: int,
    edges: list[tuple[int, int]],
    q: int,
    tables: list[list[int]],
    p: int,
) -> int:
    """Evaluate Eq. (1.1) Z_{G,q}(X) over F_p by exact summation over all a in [q]^E."""
    # Precompute ordered incident edge list for each vertex
    inc: list[list[int]] = [[] for _ in range(num_vertices)]
    for ei, (u, v) in enumerate(edges):
        inc[u].append(ei)
        inc[v].append(ei)
    for v in range(num_vertices):
        expected_len = q ** len(inc[v])
        if len(tables[v]) != expected_len:
            raise VerificationError(f"Vertex {v} table len {len(tables[v])} != q^deg={expected_len}")
    e = len(edges)
    total_assigns = q ** e
    if total_assigns > 20000:
        raise VerificationError(f"State-sum enumeration q^e={total_assigns} exceeds cap 20000")
    acc = 0
    for code in range(total_assigns):
        rem = code
        assign = [0] * e
        for ei in range(e):
            assign[ei] = rem % q
            rem //= q
        prod = 1
        for v in range(num_vertices):
            idx = 0
            for ei in inc[v]:
                idx = idx * q + assign[ei]
            prod = (prod * tables[v][idx]) % p
        acc = (acc + prod) % p
    return acc


def _parse_graph(payload: dict[str, Any]) -> tuple[int, list[tuple[int, int]]]:
    d = _req_int(payload.get("num_vertices"), "num_vertices", 2, 32)
    edges_raw = _req_list(payload.get("edges"), "edges", 1, 100)
    edges: list[tuple[int, int]] = []
    for ei, e in enumerate(edges_raw):
        el = _req_list(e, f"edges[{ei}]", 2, 2)
        u = _req_int(el[0], f"edges[{ei}][0]", 0, d - 1)
        v = _req_int(el[1], f"edges[{ei}][1]", 0, d - 1)
        if u == v:
            raise VerificationError(f"Self-loop edge ({u},{v}) forbidden in loopless multigraph")
        edges.append((u, v))
    return d, edges


# ---------------------------------------------------------------------------
# Mode 1: state_sum_and_euclidean_price (Eq. 1.1, Sec. 2, Eq. 3.3-3.4, Lem. 3.2)
# ---------------------------------------------------------------------------

def _verify_mode1(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "state_sum_projection_and_cut":
        p = _req_int(payload.get("field_prime"), "field_prime", 2, 997)
        if not _is_prime(p):
            raise VerificationError(f"field_prime={p} is not prime")
        d, edges = _parse_graph(payload)
        q = _req_int(payload.get("alphabet_q"), "alphabet_q", 2, 4)
        e = len(edges)
        if q ** e > 20000:
            raise VerificationError(f"State-sum enumeration q^e={q**e} exceeds cap 20000")
        inc: list[list[int]] = [[] for _ in range(d)]
        for ei, (u, v) in enumerate(edges):
            inc[u].append(ei)
            inc[v].append(ei)
        for v in range(d):
            if q ** len(inc[v]) > 256:
                raise VerificationError(f"Vertex {v} table size q^deg={q**len(inc[v])} exceeds cap 256")

        # Verify subgraph projection H <= G with alphabet q' <= q (Sec. 2, p. 5)
        kept_v_raw = _req_list(payload.get("kept_vertices"), "kept_vertices", 2, d)
        kept_v = [_req_int(v, "kept_v", 0, d - 1) for v in kept_v_raw]
        if len(set(kept_v)) != len(kept_v):
            raise VerificationError("Duplicate kept_vertices")
        kept_e_raw = _req_list(payload.get("kept_edge_indices"), "kept_edge_indices", 1, e)
        kept_e = [_req_int(ei, "kept_e", 0, e - 1) for ei in kept_e_raw]
        if len(set(kept_e)) != len(kept_e):
            raise VerificationError("Duplicate kept_edge_indices")
        q_sub = _req_int(payload.get("sub_alphabet_q"), "sub_alphabet_q", 2, q)
        kept_v_set = set(kept_v)
        kept_e_set = set(kept_e)
        for ei in kept_e:
            u, v = edges[ei]
            if u not in kept_v_set or v not in kept_v_set:
                raise VerificationError(f"Kept edge {ei}=({u},{v}) leaves kept_vertices")

        # Parse H's vertex tables and build the Sec. 2 projection into G's tables
        v_map = {orig: idx for idx, orig in enumerate(kept_v)}
        sub_edges = [(v_map[edges[ei][0]], v_map[edges[ei][1]]) for ei in kept_e]
        sub_inc: list[list[int]] = [[] for _ in range(len(kept_v))]
        for sei, (u, v) in enumerate(sub_edges):
            sub_inc[u].append(sei)
            sub_inc[v].append(sei)
        kept_e_to_sub = {orig: idx for idx, orig in enumerate(kept_e)}

        sub_tables_raw = _req_list(payload.get("sub_tables"), "sub_tables", len(kept_v), len(kept_v))
        sub_tables: list[list[int]] = []
        nonzero_entries = 0
        for vi, tr in enumerate(sub_tables_raw):
            tl = _req_list(tr, f"sub_tables[{vi}]", 1, 256)
            expected_sub_len = q_sub ** len(sub_inc[vi])
            if len(tl) != expected_sub_len:
                raise VerificationError(
                    f"sub_tables[{vi}] length {len(tl)} != q_sub^deg={expected_sub_len}"
                )
            vals = [_req_int(x, f"sub_tables[{vi}][{j}]", 0, p - 1) for j, x in enumerate(tl)]
            nonzero_entries += sum(1 for x in vals if x != 0)
            sub_tables.append(vals)
        if nonzero_entries == 0:
            raise VerificationError("Vacuous all-zero sub_tables rejected")

        # Construct host projected tables according to Sec. 2 rule (pin unused edges to 0, retained edges in 0..q'-1)
        host_tables: list[list[int]] = []
        for v in range(d):
            deg = len(inc[v])
            tbl = [0] * (q ** deg)
            for code in range(q ** deg):
                rem = code
                loc = [0] * deg
                for pos in range(deg - 1, -1, -1):
                    loc[pos] = rem % q
                    rem //= q
                consistent = True
                sub_vals: dict[int, int] = {}
                for pos, ei in enumerate(inc[v]):
                    if ei in kept_e_set:
                        if loc[pos] >= q_sub:
                            consistent = False
                            break
                        sub_vals[kept_e_to_sub[ei]] = loc[pos]
                    else:
                        if loc[pos] != 0:
                            consistent = False
                            break
                if not consistent:
                    tbl[code] = 0
                elif v not in kept_v_set:
                    tbl[code] = 1
                else:
                    sv = v_map[v]
                    sidx = 0
                    for sei in sub_inc[sv]:
                        sidx = sidx * q_sub + sub_vals[sei]
                    tbl[code] = sub_tables[sv][sidx]
            host_tables.append(tbl)

        z_sub = _eval_state_sum_fp(len(kept_v), sub_edges, q_sub, sub_tables, p)
        z_host = _eval_state_sum_fp(d, edges, q, host_tables, p)
        if z_host != z_sub:
            raise VerificationError(f"Projection mismatch: Z_G={z_host} != Z_H={z_sub}")
        if z_sub == 0:
            raise VerificationError("Vacuous zero state-sum evaluation rejected")

        # Verify exact flattening matrix rank of A(Z_{G,q}) across cut C | V\C equals q^{|∂C|}
        cut_raw = _req_list(payload.get("cut_C"), "cut_C", 1, d - 1)
        cut_C = set(_req_int(v, "cut_C", 0, d - 1) for v in cut_raw)
        if len(cut_C) != len(cut_raw):
            raise VerificationError("Duplicate vertices in cut_C")
        cut_bar = [v for v in range(d) if v not in cut_C]
        cut_list = sorted(cut_C)
        crossing = sum(1 for (u, v) in edges if (u in cut_C) != (v in cut_C))
        if crossing == 0:
            raise VerificationError("Vacuous zero-crossing cut rejected")

        # Build explicit flattening matrix A(Z_{G,q})_{C | V\C}
        row_dim = 1
        for v in cut_list:
            row_dim *= q ** len(inc[v])
        col_dim = 1
        for v in cut_bar:
            col_dim *= q ** len(inc[v])
        if row_dim > 256 or col_dim > 256:
            raise VerificationError(f"Flattening dimensions {row_dim}x{col_dim} exceed cap 256")
        flat = [[0] * col_dim for _ in range(row_dim)]
        for code in range(q ** e):
            rem = code
            assign = [0] * e
            for ei in range(e):
                assign[ei] = rem % q
                rem //= q
            r_idx = 0
            for v in cut_list:
                loc_i = 0
                for ei in inc[v]:
                    loc_i = loc_i * q + assign[ei]
                r_idx = r_idx * (q ** len(inc[v])) + loc_i
            c_idx = 0
            for v in cut_bar:
                loc_i = 0
                for ei in inc[v]:
                    loc_i = loc_i * q + assign[ei]
                c_idx = c_idx * (q ** len(inc[v])) + loc_i
            flat[r_idx][c_idx] = (flat[r_idx][c_idx] + 1) % p

        rk = _mat_rank_fp(flat, p)
        expected_rk = q ** crossing
        if rk != expected_rk:
            raise VerificationError(f"Flattening rank {rk} != q^|dC|={expected_rk}")

        return {
            "mode": "state_sum_and_euclidean_price",
            "submode": submode,
            "field_prime": p,
            "z_value": z_sub,
            "crossing_edges": crossing,
            "flattening_rank": rk,
        }

    if submode == "movable_supply_site_saving":
        d, edges = _parse_graph(payload)
        e = len(edges)
        cut_raw = _req_list(payload.get("cut_C"), "cut_C", 1, d - 1)
        cut_C = set(_req_int(v, "cut_C", 0, d - 1) for v in cut_raw)
        if len(cut_C) != len(cut_raw):
            raise VerificationError("Duplicate vertices in cut_C")

        # Place endpoints of edge i at +e_i and -e_i in R^e
        a_v: list[list[int]] = [[0] * e for _ in range(d)]
        deg = [0] * d
        for ei, (u, v) in enumerate(edges):
            a_v[u][ei] += 1
            a_v[v][ei] -= 1
            deg[u] += 1
            deg[v] += 1
        a_C = [sum(a_v[v][ei] for v in cut_C) for ei in range(e)]
        norm_sq_aC = sum(x * x for x in a_C)
        crossing = sum(1 for (u, v) in edges if (u in cut_C) != (v in cut_C))
        if crossing == 0:
            raise VerificationError("Vacuous zero-crossing cut rejected")
        if norm_sq_aC != crossing:
            raise VerificationError(f"Eq. (3.3) failed: ||a_C||^2={norm_sq_aC} != |dC|={crossing}")

        # Verify Eq. (3.4) & Lemma 3.2 rationalized saving for a perfect-square crossing b = s^2
        s_root = _req_int(payload.get("sqrt_b_int"), "sqrt_b_int", 1, 20)
        if s_root * s_root > crossing:
            raise VerificationError(f"sqrt_b_int^2={s_root*s_root} > |dC|={crossing}")
        b = s_root * s_root
        w = _parse_rat(payload.get("log_q_w"), "log_q_w")
        log_R = _parse_rat(payload.get("log_R"), "log_R")
        if w <= 0 or log_R <= 0:
            raise VerificationError("w and log_R must be positive")
        if log_R >= w * Fraction(s_root, 2):
            raise VerificationError("Lemma 3.2 requires log R < (1/2) * w * sqrt(b)")

        # Take lam = sqrt(b) / (4*e) and verify H(T) <= 2*e*w - w*b/(16*e)
        lam = Fraction(s_root, 4 * e)
        # Use Lemma 3.2 exact bound: H_ub = 2ew - lam*(w*s_root - log_R) + e*w*lam^2
        h_ub = 2 * e * w - lam * (w * s_root - log_R) + e * w * lam * lam
        target_ub = 2 * e * w - w * Fraction(b, 16 * e)
        if h_ub > target_ub:
            raise VerificationError(f"Lemma 3.2 saving failed: {h_ub} > {target_ub}")
        saving = 2 * e * w - h_ub
        if saving <= 0:
            raise VerificationError("Non-positive price saving")

        return {
            "mode": "state_sum_and_euclidean_price",
            "submode": submode,
            "crossing_edges": crossing,
            "norm_sq_aC": norm_sq_aC,
            "saving": [saving.numerator, saving.denominator],
            "target_saving": [(w * Fraction(b, 16 * e)).numerator, (w * Fraction(b, 16 * e)).denominator],
        }

    raise VerificationError(f"Unknown Mode 1 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 2: grid_balanced_cut_and_isoperimetry (Thm. 4.1, Lemma 4.2)
# ---------------------------------------------------------------------------

def _verify_mode2(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "grid_isoperimetry_audit":
        r = _req_int(payload.get("grid_side_r"), "grid_side_r", 2, 5)
        d = r * r
        e = 2 * r * (r - 1)
        if e > 2 * d:
            raise VerificationError("Grid edge count exceeds 2d")
        # ceil(r / 3) in pure int
        ceil_r3 = (r + 2) // 3

        def grid_boundary(mask_set: set[int]) -> tuple[int, int, int]:
            horiz = 0
            vert = 0
            mixed_rows = 0
            for row in range(r):
                row_cols = [1 if (row * r + col) in mask_set else 0 for col in range(r)]
                if 0 in row_cols and 1 in row_cols:
                    mixed_rows += 1
                for col in range(r - 1):
                    if row_cols[col] != row_cols[col + 1]:
                        horiz += 1
            for row in range(r - 1):
                for col in range(r):
                    if ((row * r + col) in mask_set) != (((row + 1) * r + col) in mask_set):
                        vert += 1
            return horiz + vert, mixed_rows, vert

        exhaustive = payload.get("exhaustive", False)
        if not isinstance(exhaustive, bool):
            raise VerificationError("exhaustive must be boolean")
        if exhaustive:
            if r > 3:
                raise VerificationError("Exhaustive grid audit capped at r <= 3")
            min_bdry = e + 1
            balanced_count = 0
            for mask in range(1 << d):
                sz = bin(mask).count("1")
                if d < 3 * sz <= 2 * d:
                    balanced_count += 1
                    mset = {i for i in range(d) if (mask >> i) & 1}
                    bdry, mrows, vcross = grid_boundary(mset)
                    if bdry < ceil_r3:
                        raise VerificationError(f"Isoperimetry violated: bdry={bdry} < {ceil_r3}")
                    if mrows < ceil_r3 and vcross < r:
                        raise VerificationError("Proof of Thm. 4.1 row/column dichotomy failed")
                    if bdry < min_bdry:
                        min_bdry = bdry
            exp_min = _req_int(payload.get("expected_min_boundary"), "expected_min_boundary", 1)
            exp_cnt = _req_int(payload.get("expected_balanced_count"), "expected_balanced_count", 1)
            if min_bdry != exp_min or balanced_count != exp_cnt:
                raise VerificationError(f"Mismatch: got min={min_bdry}, cnt={balanced_count}")
            return {
                "mode": "grid_balanced_cut_and_isoperimetry",
                "submode": submode,
                "grid_side_r": r,
                "min_boundary": min_bdry,
                "ceil_r_over_3": ceil_r3,
                "checked_cuts": balanced_count,
            }

        cuts_raw = _req_list(payload.get("balanced_cuts"), "balanced_cuts", 2, 64)
        min_bdry = e + 1
        seen_cuts: set[frozenset[int]] = set()
        for ci, c_raw in enumerate(cuts_raw):
            cl = _req_list(c_raw, f"balanced_cuts[{ci}]", 1, d - 1)
            mset = set(_req_int(v, f"balanced_cuts[{ci}]", 0, d - 1) for v in cl)
            if len(mset) != len(cl):
                raise VerificationError("Duplicate vertex in balanced cut")
            fset = frozenset(mset)
            if fset in seen_cuts:
                raise VerificationError(f"Duplicate balanced cut at index {ci}")
            seen_cuts.add(fset)
            sz = len(mset)
            if not (d < 3 * sz <= 2 * d):
                raise VerificationError(f"Cut {ci} size {sz} not in balanced range (d/3, 2d/3]")
            bdry, mrows, vcross = grid_boundary(mset)
            if bdry < ceil_r3:
                raise VerificationError(f"Cut {ci} boundary {bdry} < ceil(r/3)={ceil_r3}")
            if mrows < ceil_r3 and vcross < r:
                raise VerificationError("Row/column dichotomy failed")
            if bdry < min_bdry:
                min_bdry = bdry

        exp_min = _req_int(payload.get("expected_min_boundary"), "expected_min_boundary", 1)
        if min_bdry != exp_min:
            raise VerificationError(f"expected_min_boundary={exp_min} != {min_bdry}")
        return {
            "mode": "grid_balanced_cut_and_isoperimetry",
            "submode": submode,
            "grid_side_r": r,
            "min_boundary": min_bdry,
            "ceil_r_over_3": ceil_r3,
            "checked_cuts": len(cuts_raw),
        }

    if submode == "vnp_boolean_indicator_sum":
        # Verify Sec. 4 characteristic-free VNP Boolean-indicator representation of Z_{G_r, q}(X)
        p = _req_int(payload.get("field_prime"), "field_prime", 2, 997)
        if not _is_prime(p):
            raise VerificationError(f"field_prime={p} is not prime")
        r = _req_int(payload.get("grid_side_r"), "grid_side_r", 2, 2)
        q = _req_int(payload.get("alphabet_q"), "alphabet_q", 2, 3)
        bits_per_edge = 1 if q <= 2 else 2
        # Build r x r grid edges
        d = r * r
        edges: list[tuple[int, int]] = []
        for row in range(r):
            for col in range(r - 1):
                edges.append((row * r + col, row * r + col + 1))
        for row in range(r - 1):
            for col in range(r):
                edges.append((row * r + col, (row + 1) * r + col))
        e = len(edges)
        inc: list[list[int]] = [[] for _ in range(d)]
        for ei, (u, v) in enumerate(edges):
            inc[u].append(ei)
            inc[v].append(ei)

        tables_raw = _req_list(payload.get("vertex_tables"), "vertex_tables", d, d)
        tables: list[list[int]] = []
        for vi, tr in enumerate(tables_raw):
            tl = _req_list(tr, f"vertex_tables[{vi}]", 1, 256)
            tables.append([_req_int(x, f"tbl[{vi}][{j}]", 0, p - 1) for j, x in enumerate(tl)])

        z_direct = _eval_state_sum_fp(d, edges, q, tables, p)
        if z_direct == 0:
            raise VerificationError("Vacuous zero grid state sum rejected")

        # Evaluate Sec. 4 VNP Boolean sum over {0,1}^{e * bits_per_edge}
        total_bits = e * bits_per_edge
        z_vnp = 0
        unused_encodings = 0
        for bcode in range(1 << total_bits):
            edge_vals = [0] * e
            for ei in range(e):
                val = 0
                for bi in range(bits_per_edge):
                    bit = (bcode >> (ei * bits_per_edge + bi)) & 1
                    val |= bit << bi
                edge_vals[ei] = val
            # Compute product of vertex Boolean-indicator polynomials
            prod = 1
            for v in range(d):
                v_sum = 0
                deg = len(inc[v])
                for tcode in range(q ** deg):
                    rem = tcode
                    target_labels = [0] * deg
                    for pos in range(deg - 1, -1, -1):
                        target_labels[pos] = rem % q
                        rem //= q
                    ind = 1
                    for pos, ei in enumerate(inc[v]):
                        if edge_vals[ei] != target_labels[pos]:
                            ind = 0
                            break
                    if ind:
                        v_sum = (v_sum + tables[v][tcode]) % p
                prod = (prod * v_sum) % p
            if any(ev >= q for ev in edge_vals):
                if prod != 0:
                    raise VerificationError("Unused Boolean encoding contributed nonzero term")
                unused_encodings += 1
            z_vnp = (z_vnp + prod) % p

        if z_vnp != z_direct:
            raise VerificationError(f"VNP Boolean sum {z_vnp} != Z_direct {z_direct}")
        exp_val = _req_int(payload.get("expected_state_sum"), "expected_state_sum", 1, p - 1)
        if exp_val != z_direct:
            raise VerificationError(f"expected_state_sum={exp_val} != {z_direct}")

        return {
            "mode": "grid_balanced_cut_and_isoperimetry",
            "submode": submode,
            "field_prime": p,
            "alphabet_q": q,
            "state_sum": z_direct,
            "unused_encodings_zeroed": unused_encodings,
        }

    raise VerificationError(f"Unknown Mode 2 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 3: binary_tree_telescoping_and_abp (Thm. 5.1, Lemma 5.2, Eq. 5.1)
# ---------------------------------------------------------------------------

def _verify_mode3(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "tree_telescoping_boundary":
        h = _req_int(payload.get("tree_levels_h"), "tree_levels_h", 3, 5)
        d = (1 << h) - 1
        # Heap-indexed complete binary tree: vertex 1..d, children of u are 2u, 2u+1
        # Subtree height of vertex u: level(u) = bit_length(u), subtree_h = h - level(u) + 1
        def subtree_height(u: int) -> int:
            lvl = u.bit_length()
            return h - lvl + 1

        # Exact tree DP for Bharadwaj-Chandran min_{|U|=k} |∂U| for all k in 0..d
        # dp[u][color] = list of length size(u)+1 giving min internal cut edges for each subset size
        dp0: dict[int, list[int]] = {}
        dp1: dict[int, list[int]] = {}
        INF = 10**9
        for u in range(d, 0, -1):
            sh = subtree_height(u)
            if sh == 1:
                dp0[u] = [0, INF]
                dp1[u] = [INF, 0]
            else:
                l, r = 2 * u, 2 * u + 1
                sz_l = len(dp0[l]) - 1
                sz_r = len(dp0[r]) - 1
                sz_u = 1 + sz_l + sz_r
                arr0 = [INF] * (sz_u + 1)
                arr1 = [INF] * (sz_u + 1)
                for kl in range(sz_l + 1):
                    for kr in range(sz_r + 1):
                        # Root u colored 0:
                        best_l0 = min(dp0[l][kl], dp1[l][kl] + 1)
                        best_r0 = min(dp0[r][kr], dp1[r][kr] + 1)
                        val0 = best_l0 + best_r0
                        if val0 < arr0[kl + kr]:
                            arr0[kl + kr] = val0
                        # Root u colored 1:
                        best_l1 = min(dp1[l][kl], dp0[l][kl] + 1)
                        best_r1 = min(dp1[r][kr], dp0[r][kr] + 1)
                        val1 = best_l1 + best_r1
                        if val1 < arr1[kl + kr + 1]:
                            arr1[kl + kr + 1] = val1
                dp0[u] = arr0
                dp1[u] = arr1

        min_profile = [min(dp0[1][k], dp1[1][k]) for k in range(1, d)]
        max_min_bdry = max(min_profile)
        k_star = min_profile.index(max_min_bdry) + 1

        # Verify Eq. (5.1) telescoping identity on all supplied subsets U
        subsets_raw = _req_list(payload.get("witness_subsets"), "witness_subsets", 2, 32)
        seen_subsets: set[frozenset[int]] = set()
        for si, s_raw in enumerate(subsets_raw):
            sl = _req_list(s_raw, f"witness_subsets[{si}]", 1, d - 1)
            U = set(_req_int(v, f"witness_subsets[{si}]", 1, d) for v in sl)
            if len(U) != len(sl):
                raise VerificationError("Duplicate vertex in tree subset")
            fU = frozenset(U)
            if fU in seen_subsets:
                raise VerificationError(f"Duplicate tree witness subset at index {si}")
            seen_subsets.add(fU)
            b_root = 1 if 1 in U else 0
            c_by_j = {j: 0 for j in range(1, h)}
            bdry = 0
            for u in range(1, (d // 2) + 1):
                for ch in (2 * u, 2 * u + 1):
                    j = subtree_height(ch)
                    diff = (1 if ch in U else 0) - (1 if u in U else 0)
                    c_by_j[j] += diff
                    if diff != 0:
                        bdry += 1
            reconstructed = b_root * d + sum(c_by_j[j] * ((1 << j) - 1) for j in range(1, h))
            if reconstructed != len(U):
                raise VerificationError(f"Eq. (5.1) telescoping failed on subset {si}: {reconstructed} != {len(U)}")
            if sum(abs(c_by_j[j]) for j in range(1, h)) > bdry:
                raise VerificationError("Eq. (5.1) sum |c_j| > |∂U|")
            if bdry < min_profile[len(U) - 1]:
                raise VerificationError("Subset boundary below DP optimum")

        exp_max_min = _req_int(payload.get("expected_max_min_boundary"), "expected_max_min_boundary", 1)
        exp_k_star = _req_int(payload.get("expected_hardest_k"), "expected_hardest_k", 1, d - 1)
        if max_min_bdry != exp_max_min or min_profile[exp_k_star - 1] != exp_max_min:
            raise VerificationError(
                f"Expected max_min={exp_max_min} at k={exp_k_star}, got {max_min_bdry} at k={k_star}"
            )

        return {
            "mode": "binary_tree_telescoping_and_abp",
            "submode": submode,
            "tree_levels_h": h,
            "num_vertices_d": d,
            "max_min_boundary": max_min_bdry,
            "hardest_k": exp_k_star,
        }

    if submode == "abp_prefix_rank_decomposition":
        # Verify Lemma 5.2 ABP prefix/suffix rank decomposition A(f) = sum_{|U|=k} T_U, rank(T_U) <= s
        p = _req_int(payload.get("field_prime"), "field_prime", 2, 997)
        if not _is_prime(p):
            raise VerificationError(f"field_prime={p} is not prime")
        d = _req_int(payload.get("num_slots_d"), "num_slots_d", 3, 5)
        q = _req_int(payload.get("slot_dim_q"), "slot_dim_q", 2, 3)
        k = _req_int(payload.get("prefix_size_k"), "prefix_size_k", 1, d - 1)
        num_nodes = _req_int(payload.get("abp_num_nodes"), "abp_num_nodes", 3, 20)
        source = 0
        sink = num_nodes - 1

        # Edges: list of {u, v, const_term, slot, var_idx, coeff} (each edge carries a simple affine form c0 + coeff * x_{slot, var_idx})
        abp_edges_raw = _req_list(payload.get("abp_edges"), "abp_edges", 2, 80)
        adj: list[list[tuple[int, int, int, int, int]]] = [[] for _ in range(num_nodes)]
        for ei, er in enumerate(abp_edges_raw):
            ed = _req_dict(er, f"abp_edges[{ei}]")
            u = _req_int(ed.get("u"), f"edge[{ei}].u", 0, num_nodes - 1)
            v = _req_int(ed.get("v"), f"edge[{ei}].v", 0, num_nodes - 1)
            if u >= v:
                raise VerificationError(f"ABP must be topologically ordered DAG (u={u} >= v={v})")
            c0 = _req_int(ed.get("const_term"), f"edge[{ei}].const_term", 0, p - 1)
            slot = _req_int(ed.get("slot"), f"edge[{ei}].slot", -1, d - 1)
            vidx = _req_int(ed.get("var_idx"), f"edge[{ei}].var_idx", 0, q - 1)
            coeff = _req_int(ed.get("coeff"), f"edge[{ei}].coeff", 0, p - 1)
            if slot == -1 and coeff != 0:
                raise VerificationError("slot=-1 edge must have coeff=0")
            adj[u].append((v, c0, slot, vidx, coeff))

        # Exact DP over DAG to compute full slot tensor A(f) AND Lemma 5.2 prefix/suffix tensors P_{U,v}, Q_{V\U,v}
        # State at node u: dict[(mask, tuple_of_var_indices_in_slot_order)] -> coeff mod p
        # Compute P_{U, v} (ending in a variable edge!) and direct A(f)
        # First compute direct slot tensor A(f) by forward DP
        dp_fwd: list[dict[tuple[int, tuple[int, ...]], int]] = [{} for _ in range(num_nodes)]
        dp_fwd[source][(0, ())] = 1
        # Also track P_end[v] = states arriving at v via a variable-selecting edge
        dp_end: list[dict[tuple[int, tuple[int, ...]], int]] = [{} for _ in range(num_nodes)]

        for u in range(num_nodes):
            for (mask, vals), wt in dp_fwd[u].items():
                if wt == 0:
                    continue
                for v, c0, slot, vidx, coeff in adj[u]:
                    if c0 != 0:
                        key = (mask, vals)
                        dp_fwd[v][key] = (dp_fwd[v].get(key, 0) + wt * c0) % p
                    if slot >= 0 and coeff != 0 and not ((mask >> slot) & 1):
                        new_mask = mask | (1 << slot)
                        # Insert (slot, vidx) in sorted slot order
                        slots_present = [s for s in range(d) if (mask >> s) & 1]
                        pos = sum(1 for s in slots_present if s < slot)
                        new_vals = vals[:pos] + (vidx,) + vals[pos:]
                        nkey = (new_mask, new_vals)
                        add_w = (wt * coeff) % p
                        dp_fwd[v][nkey] = (dp_fwd[v].get(nkey, 0) + add_w) % p
                        dp_end[v][nkey] = (dp_end[v].get(nkey, 0) + add_w) % p

        full_mask = (1 << d) - 1
        A_direct: dict[tuple[int, ...], int] = {}
        for (mask, vals), wt in dp_fwd[sink].items():
            if mask == full_mask and wt % p != 0:
                A_direct[vals] = wt % p
        if not A_direct:
            raise VerificationError("Vacuous zero slot tensor A(f) rejected")

        # Backward DP for Q_{W, v} (paths from v to sink selecting slots W)
        dp_bwd: list[dict[tuple[int, tuple[int, ...]], int]] = [{} for _ in range(num_nodes)]
        dp_bwd[sink][(0, ())] = 1
        for u in range(num_nodes - 1, -1, -1):
            for v, c0, slot, vidx, coeff in adj[u]:
                for (mask, vals), wt in dp_bwd[v].items():
                    if wt == 0:
                        continue
                    if c0 != 0:
                        key = (mask, vals)
                        dp_bwd[u][key] = (dp_bwd[u].get(key, 0) + wt * c0) % p
                    if slot >= 0 and coeff != 0 and not ((mask >> slot) & 1):
                        new_mask = mask | (1 << slot)
                        slots_present = [s for s in range(d) if (mask >> s) & 1]
                        pos = sum(1 for s in slots_present if s < slot)
                        new_vals = vals[:pos] + (vidx,) + vals[pos:]
                        nkey = (new_mask, new_vals)
                        dp_bwd[u][nkey] = (dp_bwd[u].get(nkey, 0) + wt * coeff) % p

        # Reconstruct A(f) = sum_{|U|=k} T_U where T_U = sum_v P_{U,v} (x) Q_{V\U,v} and verify rank(T_U) <= num_nodes
        A_recon: dict[tuple[int, ...], int] = {}
        max_cut_rank = 0
        nonempty_cuts = 0
        for u_mask in range(1 << d):
            if bin(u_mask).count("1") != k:
                continue
            comp_mask = full_mask ^ u_mask
            u_slots = [s for s in range(d) if (u_mask >> s) & 1]
            c_slots = [s for s in range(d) if (comp_mask >> s) & 1]
            rdim = q ** k
            cdim = q ** (d - k)
            T_U = [[0] * cdim for _ in range(rdim)]
            has_nz = False
            for node in range(num_nodes):
                p_vec = [0] * rdim
                q_vec = [0] * cdim
                p_nz = False
                q_nz = False
                for (m1, v1), w1 in dp_end[node].items():
                    if m1 == u_mask and w1 % p != 0:
                        idx = 0
                        for x in v1:
                            idx = idx * q + x
                        p_vec[idx] = w1 % p
                        p_nz = True
                if not p_nz:
                    continue
                for (m2, v2), w2 in dp_bwd[node].items():
                    if m2 == comp_mask and w2 % p != 0:
                        idx = 0
                        for x in v2:
                            idx = idx * q + x
                        q_vec[idx] = w2 % p
                        q_nz = True
                if not q_nz:
                    continue
                has_nz = True
                for ri in range(rdim):
                    if p_vec[ri] == 0:
                        continue
                    for ci in range(cdim):
                        if q_vec[ci] != 0:
                            T_U[ri][ci] = (T_U[ri][ci] + p_vec[ri] * q_vec[ci]) % p
            if has_nz:
                nonempty_cuts += 1
                rk = _mat_rank_fp(T_U, p)
                if rk > num_nodes:
                    raise VerificationError(f"Lemma 5.2 rank bound violated: {rk} > {num_nodes}")
                if rk > max_cut_rank:
                    max_cut_rank = rk
                for ri in range(rdim):
                    for ci in range(cdim):
                        val = T_U[ri][ci]
                        if val != 0:
                            # Merge indices back into full slot order
                            full_t = [0] * d
                            rem = ri
                            for pos in range(k - 1, -1, -1):
                                full_t[u_slots[pos]] = rem % q
                                rem //= q
                            rem = ci
                            for pos in range(d - k - 1, -1, -1):
                                full_t[c_slots[pos]] = rem % q
                                rem //= q
                            ft = tuple(full_t)
                            A_recon[ft] = (A_recon.get(ft, 0) + val) % p

        A_recon_nz = {k_: v_ for k_, v_ in A_recon.items() if v_ % p != 0}
        if A_recon_nz != A_direct:
            raise VerificationError("Lemma 5.2 prefix/suffix sum != direct ABP slot tensor A(f)")

        return {
            "mode": "binary_tree_telescoping_and_abp",
            "submode": submode,
            "field_prime": p,
            "nonzero_monomials": len(A_direct),
            "nonempty_cuts": nonempty_cuts,
            "max_cut_rank": max_cut_rank,
        }

    raise VerificationError(f"Unknown Mode 3 submode: {submode}")


def _build_minor_host_tables(
    dG: int,
    edgesG: list[tuple[int, int]],
    n_host: int,
    dH: int,
    edgesH: list[tuple[int, int]],
    q: int,
    branch_sets: list[set[int]],
    centroids: list[int],
    chosen_host_edges: list[int],
    minor_tables: list[list[int]],
) -> list[list[int]]:
    """Deterministically build Lemma 7.2 host projected tables (0, 1, or minor table entries)."""
    incG: list[list[int]] = [[] for _ in range(dG)]
    for ei, (u, v) in enumerate(edgesG):
        incG[u].append(ei)
        incG[v].append(ei)

    incH: list[list[int]] = [[] for _ in range(dH)]
    for mei, (hu, hv) in enumerate(edgesH):
        incH[hu].append(mei)
        incH[hv].append(mei)

    for v in range(dH):
        if len(minor_tables[v]) != q ** len(incH[v]):
            raise VerificationError(f"Minor vertex {v} table len {len(minor_tables[v])} != q^deg={q**len(incH[v])}")
    for u in range(dG):
        if n_host ** len(incG[u]) > 256:
            raise VerificationError(f"Host vertex {u} table size {n_host**len(incG[u])} exceeds cap 256")

    chosen_to_mei = {gei: mei for mei, gei in enumerate(chosen_host_edges)}
    chosen_set = set(chosen_host_edges)
    v_to_hv: dict[int, int] = {}
    for hv, bs in enumerate(branch_sets):
        for u in bs:
            v_to_hv[u] = hv

    tree_edge_payload: dict[int, tuple[int, int, list[int]]] = {}
    tree_edges_set: set[int] = set()
    node_parent_edge: dict[int, int] = {}
    node_child_edges: dict[int, list[int]] = {u: [] for u in range(dG)}

    for hv, bs in enumerate(branch_sets):
        root = centroids[hv]
        adj: dict[int, list[tuple[int, int]]] = {u: [] for u in bs}
        for gei, (gu, gv) in enumerate(edgesG):
            if gei not in chosen_set and gu in bs and gv in bs:
                adj[gu].append((gv, gei))
                adj[gv].append((gu, gei))
        parent: dict[int, int | None] = {root: None}
        order = [root]
        idx = 0
        while idx < len(order):
            cur = order[idx]
            idx += 1
            for nxt, gei in adj[cur]:
                if nxt not in parent:
                    parent[nxt] = cur
                    node_parent_edge[nxt] = gei
                    node_child_edges[cur].append(gei)
                    tree_edges_set.add(gei)
                    order.append(nxt)
        sub_meis: dict[int, list[int]] = {u: [] for u in bs}
        for u in reversed(order):
            meis_here = [chosen_to_mei[gei] for gei in incG[u] if gei in chosen_to_mei]
            for c_gei in node_child_edges[u]:
                gu, gv = edgesG[c_gei]
                ch = gv if gu == u else gu
                meis_here.extend(sub_meis[ch])
            sub_meis[u] = sorted(meis_here)
            if parent[u] is not None:
                p_gei = node_parent_edge[u]
                tree_edge_payload[p_gei] = (u, int(parent[u]), sub_meis[u])

    host_tables: list[list[int]] = []
    for u in range(dG):
        deg = len(incG[u])
        tbl = [0] * (n_host ** deg)
        for code in range(n_host ** deg):
            rem = code
            loc = [0] * deg
            for pos in range(deg - 1, -1, -1):
                loc[pos] = rem % n_host
                rem //= n_host
            consistent = True
            known_mei_vals: dict[int, int] = {}
            for pos, gei in enumerate(incG[u]):
                val = loc[pos]
                if gei in chosen_to_mei:
                    if val >= q:
                        consistent = False
                        break
                    known_mei_vals[chosen_to_mei[gei]] = val
                elif gei in tree_edges_set:
                    _, par, m_list = tree_edge_payload[gei]
                    if val >= (q ** len(m_list)):
                        consistent = False
                        break
                    if u == par:
                        r2 = val
                        dec = [0] * len(m_list)
                        for p2 in range(len(m_list) - 1, -1, -1):
                            dec[p2] = r2 % q
                            r2 //= q
                        for mei, mv in zip(m_list, dec):
                            known_mei_vals[mei] = mv
                else:
                    if val != 0:
                        consistent = False
                        break
            if not consistent:
                tbl[code] = 0
                continue
            if u not in v_to_hv:
                tbl[code] = 1
                continue
            hv = v_to_hv[u]
            if u == centroids[hv]:
                midx = 0
                for mei in incH[hv]:
                    midx = midx * q + known_mei_vals[mei]
                tbl[code] = minor_tables[hv][midx]
            else:
                p_gei = node_parent_edge[u]
                _, _, m_list = tree_edge_payload[p_gei]
                enc = 0
                for mei in m_list:
                    enc = enc * q + known_mei_vals[mei]
                p_pos = incG[u].index(p_gei)
                tbl[code] = 1 if loc[p_pos] == enc else 0
        host_tables.append(tbl)
    return host_tables


# ---------------------------------------------------------------------------
# Mode 4: path_multiscale_det_and_minors (Thm. 6.1, Lem. 6.3, Thm. 7.1, Lem. 7.2)
# ---------------------------------------------------------------------------

def _verify_mode4(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "dyadic_scale_placement_and_det":
        # Part A: Lemma 6.3 exact dyadic scale clustering on path P_d (d power of 2 in {4, 8})
        d = _req_int(payload.get("path_vertices_d"), "path_vertices_d", 4, 8)
        if d not in (4, 8):
            raise VerificationError("path_vertices_d must be 4 or 8")
        # Leaf order of ordered full binary tree tau (permutation of 0..d-1)
        leaf_order_raw = _req_list(payload.get("tau_leaf_order"), "tau_leaf_order", d, d)
        leaf_order = [_req_int(v, "leaf_order", 0, d - 1) for v in leaf_order_raw]
        if sorted(leaf_order) != list(range(d)):
            raise VerificationError("tau_leaf_order is not a permutation of 0..d-1")

        # Opposite-axis terminal vectors for path P_d (e = d - 1 edges)
        e = d - 1
        a_v = [[0] * e for _ in range(d)]
        for ei in range(e):
            a_v[ei][ei] += 1
            a_v[ei + 1][ei] -= 1

        # At each dyadic scale k in {1, 2, ..., d/2}, balanced binary tree maximal subtrees of size <= k
        # partition leaf_order into blocks of exact size k, forming d/k clusters of size k each!
        log2_d = 2 if d == 4 else 3
        total_lower_bound = Fraction(0, 1)
        k = 1
        scales_checked = 0
        while k <= d // 2:
            num_clusters = d // k
            if num_clusters * 2 * k < d:
                raise VerificationError("Too few clusters at scale k")
            scale_norm_lb = 0
            for ci in range(num_clusters):
                cl = set(leaf_order[ci * k : (ci + 1) * k])
                aC = [sum(a_v[v][ei] for v in cl) for ei in range(e)]
                nsq = sum(x * x for x in aC)
                if nsq < 1:
                    raise VerificationError(f"Disconnected cluster norm^2={nsq} < 1")
                # Integer floor of sqrt(nsq) >= 1 gives exact rational lower bound on ||a_C||
                s_floor = 1
                while (s_floor + 1) * (s_floor + 1) <= nsq:
                    s_floor += 1
                scale_norm_lb += s_floor
            total_lower_bound += Fraction(k * scale_norm_lb, d)
            scales_checked += 1
            k *= 2

        if total_lower_bound < Fraction(log2_d, 2):
            raise VerificationError(f"Lemma 6.3 inner product bound {total_lower_bound} < (1/2) log2 d")

        # Part B: Sec. 6.3 exact cofactor determinant embedding of Z_{P_d, q} over F_p
        p = _req_int(payload.get("field_prime"), "field_prime", 2, 997)
        if not _is_prime(p):
            raise VerificationError(f"field_prime={p} is not prime")
        q = _req_int(payload.get("alphabet_q"), "alphabet_q", 2, 3)
        # Path edges (0,1), (1,2), ..., (d-2, d-1)
        path_edges = [(i, i + 1) for i in range(e)]
        tables_raw = _req_list(payload.get("path_tables"), "path_tables", d, d)
        tables: list[list[int]] = []
        for vi, tr in enumerate(tables_raw):
            tl = _req_list(tr, f"path_tables[{vi}]", 1, 27)
            tables.append([_req_int(x, f"path_tables[{vi}][{j}]", 0, p - 1) for j, x in enumerate(tl)])

        z_path = _eval_state_sum_fp(d, path_edges, q, tables, p)
        if z_path == 0:
            raise VerificationError("Vacuous zero path state sum rejected")

        # Build layered ABP adjacency matrix A of order N_abp = (d - 1)*q + 2:
        # Node 0 = source, layers 1..(d-1) each have q nodes, node N_abp - 1 = sink
        # Note: in Sec. 6.3, contracting source/sink gives minor of order (d-1)*q + 1!
        N_abp = (d - 1) * q + 2
        A = [[0] * N_abp for _ in range(N_abp)]
        # Source -> layer 1 (vertex 0 table: length q)
        for j in range(q):
            A[0][1 + j] = tables[0][j] % p
        # Layer t -> Layer t+1 (vertex t table: length q^2, indexed i*q + j)
        for t in range(1, d - 1):
            base_in = 1 + (t - 1) * q
            base_out = 1 + t * q
            for i in range(q):
                for j in range(q):
                    A[base_in + i][base_out + j] = tables[t][i * q + j] % p
        # Layer d-1 -> sink (vertex d-1 table: length q)
        base_last = 1 + (d - 2) * q
        for i in range(q):
            A[base_last + i][N_abp - 1] = tables[d - 1][i] % p

        # Form M = I - A (strictly upper-triangular A => det(M) = 1)
        M = [[((1 if i == j else 0) - A[i][j]) % p for j in range(N_abp)] for i in range(N_abp)]
        if _mat_det_fp(M, p) != 1:
            raise VerificationError("det(I - A) != 1")
        # (source, sink) entry of (I - A)^{-1} = (-1)^(0 + N_abp - 1) * det(M deleting row N_abp-1 and col 0)
        minor_mat = [[M[r][c] for c in range(1, N_abp)] for r in range(0, N_abp - 1)]
        sign = 1 if ((N_abp - 1) % 2 == 0) else (p - 1)
        cofactor_val = (sign * _mat_det_fp(minor_mat, p)) % p
        if cofactor_val != z_path:
            raise VerificationError(f"Sec. 6.3 cofactor {cofactor_val} != Z_path {z_path}")

        return {
            "mode": "path_multiscale_det_and_minors",
            "submode": submode,
            "path_vertices_d": d,
            "scales_checked": scales_checked,
            "inner_prod_lb": [total_lower_bound.numerator, total_lower_bound.denominator],
            "minor_order": N_abp - 1,
            "cofactor_value": cofactor_val,
        }

    if submode == "minor_centroid_and_cutwidth":
        # Part A: Lemma 7.2 weighted-centroid minor projection Z_{H,q} from Z_{G,n} (q^b <= n)
        p = _req_int(payload.get("field_prime"), "field_prime", 2, 997)
        if not _is_prime(p):
            raise VerificationError(f"field_prime={p} is not prime")
        dG, edgesG = _parse_graph(payload)
        q = _req_int(payload.get("minor_alphabet_q"), "minor_alphabet_q", 2, 2)
        n_host = _req_int(payload.get("host_alphabet_n"), "host_alphabet_n", 2, 4)

        dH = _req_int(payload.get("minor_num_vertices"), "minor_num_vertices", 2, dG - 1)
        edgesH_raw = _req_list(payload.get("minor_edges"), "minor_edges", 1, len(edgesG))
        edgesH = [
            (_req_int(el[0], "m_u", 0, dH - 1), _req_int(el[1], "m_v", 0, dH - 1))
            for el in (_req_list(e, "minor_edge", 2, 2) for e in edgesH_raw)
        ]
        degH = [0] * dH
        for u, v in edgesH:
            if u == v:
                raise VerificationError("Self-loop in minor H")
            degH[u] += 1
            degH[v] += 1
        delta_H = max(degH)
        b_exp = max(1, delta_H // 2)
        if q ** b_exp > n_host:
            raise VerificationError(f"Lemma 7.2 alphabet condition violated: q^b={q**b_exp} > n={n_host}")

        # Branch sets & weighted centroids for each vertex of H
        branch_raw = _req_list(payload.get("branch_sets"), "branch_sets", dH, dH)
        centroids_raw = _req_list(payload.get("branch_centroids"), "branch_centroids", dH, dH)
        chosen_host_edges_raw = _req_list(payload.get("chosen_host_edges"), "chosen_host_edges", len(edgesH), len(edgesH))
        chosen_host_edges = [_req_int(ei, "chosen_host_edge", 0, len(edgesG) - 1) for ei in chosen_host_edges_raw]
        if len(set(chosen_host_edges)) != len(chosen_host_edges):
            raise VerificationError("Duplicate chosen host edges for minor H")

        branch_sets: list[set[int]] = []
        used_host_v: set[int] = set()
        for hv, br in enumerate(branch_raw):
            br_list = _req_list(br, f"branch[{hv}]", 1, dG)
            bs = set(_req_int(v, f"branch[{hv}]", 0, dG - 1) for v in br_list)
            if len(bs) != len(br_list):
                raise VerificationError(f"Duplicate vertex inside branch_set {hv}")
            if used_host_v & bs:
                raise VerificationError("Branch sets are not pairwise disjoint")
            used_host_v |= bs
            branch_sets.append(bs)

        centroids = [_req_int(c, f"centroid[{hv}]", 0, dG - 1) for hv, c in enumerate(centroids_raw)]
        for hv in range(dH):
            if centroids[hv] not in branch_sets[hv]:
                raise VerificationError(f"Centroid {centroids[hv]} not in branch_set {hv}")

        # Verify each chosen host edge joins the corresponding two branch sets
        for mei, (hu, hv) in enumerate(edgesH):
            gei = chosen_host_edges[mei]
            gu, gv = edgesG[gei]
            ok1 = (gu in branch_sets[hu] and gv in branch_sets[hv])
            ok2 = (gu in branch_sets[hv] and gv in branch_sets[hu])
            if not (ok1 or ok2):
                raise VerificationError(f"Host edge {gei}=({gu},{gv}) does not connect branch sets {hu},{hv}")

        # For each branch set, check connectivity and weighted centroid balance (every component below centroid has weight <= degH[hv]/2)
        chosen_set = set(chosen_host_edges)
        for hv in range(dH):
            bs = branch_sets[hv]
            root = centroids[hv]
            # Weight of host vertex u in branch set hv = count of chosen edges incident to u
            wt = {u: 0 for u in bs}
            for gei in chosen_host_edges:
                gu, gv = edgesG[gei]
                if gu in bs:
                    wt[gu] += 1
                if gv in bs:
                    wt[gv] += 1
            if sum(wt.values()) != degH[hv]:
                raise VerificationError(f"Branch set {hv} total weight != degH")
            # Build adjacency inside bs (excluding chosen edges)
            adj_bs: dict[int, list[int]] = {u: [] for u in bs}
            for gei, (gu, gv) in enumerate(edgesG):
                if gei not in chosen_set and gu in bs and gv in bs:
                    adj_bs[gu].append(gv)
                    adj_bs[gv].append(gu)
            # Check connectivity via BFS from root
            visited = {root}
            queue = [root]
            while queue:
                cur = queue.pop(0)
                for nxt in adj_bs[cur]:
                    if nxt not in visited:
                        visited.add(nxt)
                        queue.append(nxt)
            if visited != bs:
                raise VerificationError(f"Branch set {hv} is disconnected")
            # Check each connected component of bs \ {root} has weight <= degH[hv] // 2
            rem_nodes = bs - {root}
            seen_rem: set[int] = set()
            for start in rem_nodes:
                if start in seen_rem:
                    continue
                comp_w = 0
                q_c = [start]
                seen_rem.add(start)
                while q_c:
                    cur = q_c.pop(0)
                    comp_w += wt[cur]
                    for nxt in adj_bs[cur]:
                        if nxt in rem_nodes and nxt not in seen_rem:
                            seen_rem.add(nxt)
                            q_c.append(nxt)
                if 2 * comp_w > degH[hv]:
                    raise VerificationError(f"Centroid balance violated in branch {hv}: 2*{comp_w} > {degH[hv]}")

        # Verify actual projection identity Z_{G,n}(projected_tables) == Z_{H,q}(minor_tables)
        minor_tables_raw = _req_list(payload.get("minor_tables"), "minor_tables", dH, dH)
        minor_tables = [
            [_req_int(x, f"mt[{vi}][{j}]", 0, p - 1) for j, x in enumerate(_req_list(tr, f"mt[{vi}]", 1, 64))]
            for vi, tr in enumerate(minor_tables_raw)
        ]
        host_proj_raw = _req_list(payload.get("host_projected_tables"), "host_projected_tables", dG, dG)
        host_proj = [
            [_req_int(x, f"ht[{vi}][{j}]", 0, p - 1) for j, x in enumerate(_req_list(tr, f"ht[{vi}]", 1, 256))]
            for vi, tr in enumerate(host_proj_raw)
        ]
        expected_host_proj = _build_minor_host_tables(
            dG, edgesG, n_host, dH, edgesH, q, branch_sets, centroids, chosen_host_edges, minor_tables
        )
        if host_proj != expected_host_proj:
            raise VerificationError("Lemma 7.2 minor projection mismatch: host_projected_tables differs from deterministic centroid projection")
        z_H = _eval_state_sum_fp(dH, edgesH, q, minor_tables, p)
        z_G = _eval_state_sum_fp(dG, edgesG, n_host, host_proj, p)
        if z_H == 0:
            raise VerificationError("Vacuous zero minor state sum rejected")
        if z_G != z_H:
            raise VerificationError(f"Lemma 7.2 minor projection mismatch: Z_G={z_G} != Z_H={z_H}")

        # Part B: Sec. 7.1 & 7.3 exact vertex-order cutwidth & pathwidth sandwich on G
        v_order_raw = _req_list(payload.get("vertex_order"), "vertex_order", dG, dG)
        v_order = [_req_int(v, "v_order", 0, dG - 1) for v in v_order_raw]
        if sorted(v_order) != list(range(dG)):
            raise VerificationError("vertex_order is not a permutation of 0..dG-1")
        pos_of = {v: i for i, v in enumerate(v_order)}
        # Compute cutwidth of this linear order and induced path decomposition width (Sec. 7.3)
        degG = [0] * dG
        for u, v in edgesG:
            degG[u] += 1
            degG[v] += 1
        delta_G = max(degG)
        max_cut = 0
        max_bag_minus_1 = 0
        for step in range(dG):
            prefix = set(v_order[: step + 1])
            # Cut after prefix (for step < dG - 1)
            cut_e = sum(1 for (u, v) in edgesG if (u in prefix) != (v in prefix))
            if cut_e > max_cut:
                max_cut = cut_e
            # Sec. 7.3 bag: current vertex plus earlier vertices having an edge to a strictly later vertex
            earlier = set(v_order[:step])
            later = set(v_order[step:])
            bag = {v_order[step]}
            for u, v in edgesG:
                if u in earlier and v in later:
                    bag.add(u)
                elif v in earlier and u in later:
                    bag.add(v)
            if len(bag) - 1 > max_bag_minus_1:
                max_bag_minus_1 = len(bag) - 1

        if delta_G > 2 * max_cut:
            raise VerificationError("Delta(G) > 2*cw(G)")
        if not (max_bag_minus_1 <= max_cut <= delta_G * (max_bag_minus_1 + 1)):
            raise VerificationError("Sec. 7.3 pw <= cw <= Delta*(pw+1) sandwich violated")

        return {
            "mode": "path_multiscale_det_and_minors",
            "submode": submode,
            "minor_state_sum": z_H,
            "delta_H": delta_H,
            "order_cutwidth": max_cut,
            "induced_pathwidth": max_bag_minus_1,
        }

    raise VerificationError(f"Unknown Mode 4 submode: {submode}")


# ---------------------------------------------------------------------------
# Entry Points
# ---------------------------------------------------------------------------

def verify_certificate(cert: Any) -> dict[str, Any]:
    d = _req_dict(cert, "certificate")
    if d.get("schema_version") != SCHEMA_VERSION:
        raise VerificationError(f"Expected schema_version={SCHEMA_VERSION}, got {d.get('schema_version')}")
    _req_str(d.get("certificate_id"), "certificate_id")
    _req_str(d.get("paper_reference"), "paper_reference")
    mode = _req_str(d.get("mode"), "mode")
    payload = _req_dict(d.get("payload"), "payload")

    if mode == "state_sum_and_euclidean_price":
        res = _verify_mode1(payload)
    elif mode == "grid_balanced_cut_and_isoperimetry":
        res = _verify_mode2(payload)
    elif mode == "binary_tree_telescoping_and_abp":
        res = _verify_mode3(payload)
    elif mode == "path_multiscale_det_and_minors":
        res = _verify_mode4(payload)
    else:
        raise VerificationError(f"Unknown mode: {mode}")

    res["certificate_id"] = d["certificate_id"]
    res["status"] = "VERIFIED"
    return res


def verify_file(path: pathlib.Path | str) -> dict[str, Any]:
    p = pathlib.Path(path)
    raw = p.read_bytes()
    if len(raw) > MAX_JSON_BYTES:
        raise VerificationError(f"Certificate {p.name} exceeds MAX_JSON_BYTES={MAX_JSON_BYTES}")
    try:
        data = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_no_dup_pairs,
            parse_constant=_reject_json_constant,
            parse_float=_reject_json_float,
        )
    except VerificationError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise VerificationError(f"Invalid JSON in {p.name}: {exc}") from exc
    return verify_certificate(data)


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if not args:
        print("Usage: python -m src.valiant_hier_verifier <file-or-dir> [...]", file=sys.stderr)
        return 2
    files: list[pathlib.Path] = []
    for a in args:
        p = pathlib.Path(a)
        if p.is_dir():
            files.extend(sorted(p.glob("*.json")))
        else:
            files.append(p)
    if not files:
        print("No certificate files found.", file=sys.stderr)
        return 2
    verified = 0
    for f in files:
        res = verify_file(f)
        print(f"[VERIFIED] {f.name}: {res['mode']} ({res['submode']})")
        verified += 1
    print(f"Verified {verified}/{len(files)} certificates under {SCHEMA_VERSION}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
