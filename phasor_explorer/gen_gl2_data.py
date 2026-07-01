"""gen_gl2_data.py — emit gl2_data.json for explorer_v2.html's GL(2) families.

Coefficients come from the canonical builders in focal_closure.py (repo root):
  delta : lambda(n) = tau(n)/n^{11/2}, tau via eta(q)^24 exact limb-split squarings
          (the builder itself asserts the tau table, Hecke multiplicativity and
          the Deligne bound — running it IS the verification);
  e11   : lambda(n) = a_n/sqrt(n) for elliptic curve 11.a via eta(q)^2 eta(q^11)^2
          (builder asserts the a_n table).

Zero ordinates are focal_closure.REFERENCE_ORDINATES (LMFDB, LOADED — never
recomputed here), rounded to 10 decimals to match the explorer's Dirichlet table.

HONESTY / coverage policy.  A zero is shipped only if its eigenheight e^gamma
fits in the lambda table with headroom (>=10%, target ~20%); anything that does
not fit the size budget is EXCLUDED and recorded in the JSON's "excluded" list
so the explorer can say so out loud.  Budgets:
  delta : N_CAP = 1,300,000 — focal_closure's validated max_N for the exact
          limb-split eta^24 build; gamma_2 (e^g ~ 1.10e6) therefore gets 18.6%
          headroom instead of 20%.
  e11   : size budget only — gamma_5 (e^g ~ 7.8e5) would add ~0.9M entries
          (~10 MB) and push the file past the ~25 MB cap, so it is excluded;
          gamma_1..gamma_4 ship with full 20% headroom.
lambda values are rounded to 9 significant digits (plenty for the explorer's
float64 sums; keeps the JSON ~20 MB).

Run:  python3 gen_gl2_data.py        (from phasor_explorer/; ~1-3 min for delta)
"""

from __future__ import annotations

import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import focal_closure as fc  # noqa: E402

HEADROOM = 1.2      # target headroom above the largest shipped eigenheight
HEADROOM_MIN = 1.1  # a zero ships only if the cap gives it at least this much
CAPS = {
    "delta": 1_300_000,   # validated exactness cap (focal_closure max_N)
    "e11": 120_000,       # size budget: gamma_5 alone would add ~10 MB
}
LABELS = {
    "delta": "Δ — Ramanujan (GL2, wt 12)",
    "e11": "E11 — curve 11.a (GL2, wt 2)",
}
LEVEL_WEIGHT = {"delta": (1, 12), "e11": (11, 2)}


def sig9(x: float) -> float:
    return float(f"{x:.9g}")


def build(name: str) -> dict:
    cap = CAPS[name]
    ref = fc.REFERENCE_ORDINATES[name]
    zeros, excluded = [], []
    for g in ref:
        (zeros if math.exp(g) * HEADROOM_MIN <= cap else excluded).append(g)
    assert zeros, name
    nmax = min(cap, int(math.ceil(HEADROOM * math.exp(max(zeros)))))
    print(f"{name}: nmax={nmax:,}  zeros={len(zeros)}/{len(ref)}  "
          f"headroom on last={nmax / math.exp(max(zeros)):.3f}x")
    coeffs, keys = fc.FAMILIES[name].coeff(nmax)   # builders assert tau/Hecke/Deligne/a_n
    lam = coeffs.real
    assert lam.shape[0] == nmax + 1 and lam[0] == 0.0
    assert abs(lam[2] * lam[3] - lam[6]) <= 1e-12 * max(1.0, abs(lam[6]))  # Hecke, coprime
    out = [sig9(float(v)) for v in lam]
    # 9-sig-digit rounding must preserve Hecke to ~1e-8 relative (the JS check)
    assert abs(out[2] * out[3] - out[6]) <= 1e-8 * max(1.0, abs(out[6]))
    q, k = LEVEL_WEIGHT[name]
    return {
        "label": LABELS[name],
        "q": q, "k": k, "nmax": nmax,
        "zeros": [round(g, 10) for g in zeros],
        "excluded": [round(g, 10) for g in excluded],
        "excluded_note": ("" if not excluded else
                          f"reference ordinates above are omitted: eigenheight e^gamma "
                          f"exceeds the shipped lambda table (n <= {nmax:,}; data-size budget)"),
        "source": "ordinates: LMFDB (via focal_closure.REFERENCE_ORDINATES); "
                  "lambda: focal_closure exact eta-product builders",
        "lam": out,
    }


def main() -> None:
    data = {name: build(name) for name in ("delta", "e11")}
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gl2_data.json")
    with open(path, "w") as f:
        json.dump(data, f, separators=(",", ":"))
    mb = os.path.getsize(path) / 1e6
    print(f"wrote {path}  ({mb:.1f} MB)")
    assert mb < 25.0, "size budget exceeded"
    for name, d in data.items():
        for g in d["zeros"]:
            assert math.exp(g) * HEADROOM_MIN <= d["nmax"] + 1, (name, g)
        print(f"  {name}: zeros={d['zeros']}  excluded={d['excluded']}")


if __name__ == "__main__":
    main()
