#!/usr/bin/env python3
"""4-rail functional bench: reproduce trilinear uniqueness and 4-rail smearing.

K-type model of sl2 acting on lowest-weight (holomorphic, k=12) and
highest-weight (antiholomorphic) discrete series:
  hol:  H v_j = (k+2j) v_j,   E v_j = v_{j+1},        F v_j = j(k+j-1) v_{j-1}
  anti: H w_j = -(k+2j) w_j,  F w_j = w_{j+1},        E w_j = j(k+j-1) w_{j-1}
Invariant multilinear functionals = nullspace of (Delta E)^T, (Delta F)^T on
the weight-zero slice, truncated at j <= L per slot.

Gates (classical facts the bench must reproduce):
  3 rails (hol, hol, anti): dim -> 1 as L grows   [trilinear uniqueness]
  4 rails (hol, hol, anti, anti): dim grows ~ L   [the spectral continuum]
"""
import numpy as np
import itertools, sys

K = 12

def slice_states(rails, L):
    """States: tuples (j_1..j_n), total weight zero. rails: list of (sign, k)."""
    states = []
    for js in itertools.product(range(L + 1), repeat=len(rails)):
        w = sum((k + 2 * j) * (1 if sg == '+' else -1) for j, (sg, k) in zip(js, rails))
        if w == 0:
            states.append(js)
    return {s: i for i, s in enumerate(states)}, states

def op_rows(rails, L, idx, states, which):
    """Rows of (Delta X)^T restricted: for each source state s in the +2 (E) or
    -2 (F) weight slice reached FROM the zero slice, one linear condition.
    Implementation: conditions indexed by target states t in weight ±2 slice:
      sum over rails of amplitude(s -> t) * lambda(s) = 0."""
    # build target slice (weight +2 for E, -2 for F)
    tgt = {}
    conds = {}
    for s in states:
        for i, (r, kk) in enumerate(rails):
            j = s[i]
            if which == 'E':
                if r == '+':
                    t = s[:i] + (j + 1,) + s[i + 1:]
                    amp = 1.0
                    if t[i] > L:
                        continue
                else:
                    if j == 0:
                        continue
                    t = s[:i] + (j - 1,) + s[i + 1:]
                    amp = j * (kk + j - 1)
            else:
                if r == '+':
                    if j == 0:
                        continue
                    t = s[:i] + (j - 1,) + s[i + 1:]
                    amp = j * (kk + j - 1)
                else:
                    t = s[:i] + (j + 1,) + s[i + 1:]
                    amp = 1.0
                    if t[i] > L:
                        continue
            conds.setdefault(t, []).append((idx[s], amp))
    rows = []
    for t, entries in conds.items():
        row = np.zeros(len(states))
        for col, amp in entries:
            row[col] += amp
        rows.append(row)
    return rows

def invariant_dim(rails, L):
    idx, states = slice_states(rails, L)
    if not states:
        return 0, 0
    rows = op_rows(rails, L, idx, states, 'E') + op_rows(rails, L, idx, states, 'F')
    A = np.array(rows)
    # column scaling for conditioning (amplitudes grow like j^2)
    scal = np.maximum(np.abs(A).max(axis=0), 1e-30)
    A = A / scal
    s = np.linalg.svd(A, compute_uv=False)
    smax = s.max() if len(s) else 1.0
    nullity = int((s / smax < 1e-9).sum()) + (len(states) - len(s) if A.shape[0] < len(states) else 0)
    return nullity, len(states)

if __name__ == '__main__':
    Ls = [int(t) for t in (sys.argv[1].split(',') if len(sys.argv) > 1 else ['8', '12', '16', '20'])]
    cases = [
        ("(12,12,-24) [gate: dim=1, balanced trilinear m=0]", [('+',12),('+',12),('-',24)]),
        ("(12,12,-28) [gate: dim=1, balanced m=2]", [('+',12),('+',12),('-',28)]),
        ("(12,12,-12) [gate: dim=0, selection rule]", [('+',12),('+',12),('-',12)]),
        ("(12,12,-12,-12) [gate: dim ~ L, continuum]", [('+',12),('+',12),('-',12),('-',12)]),
    ]
    for label, rails in cases:
        print(f"# rails={label}")
        for L in Ls:
            d, n = invariant_dim(rails, L)
            print(f"#   L={L}: dim={d}  (slice {n})")
