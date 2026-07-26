# hunt-spec 2026-07-26, session 18a3f704 — Campaign 1, round-1 driver
# Siegel-corridor audit over real primitive characters chi_d, d fundamental.
#   Arm A (Siegel box): sign changes of L(sigma, chi_d) on the real segment
#     [max(1/2, 1 - 3/log q), 0.999]  — any sign change = EVENT (real zero
#     near s=1, the classical exceptional-zero corridor).
#   Arm B (strip audit): count zeros on the line in (0, T] via lcalc vs the
#     main-term census; |count - main| > 2 = FLAG (possible off-line pair /
#     missed zeros / multiplicity) -> manual ladder.
# Telemetry: L(1, chi) (near-exceptional statistic), min |L| on the box grid.
# Round 2 (separate driver): 3D-locator cross-validation of every flag.
import json, sys
from sage.libs.lcalc.lcalc_Lfunction import Lfunction_from_character

DMAX_FULL = int(sys.argv[1]) if len(sys.argv) > 1 else 200
T_STRIP = 30.0
OUT = f"/Users/samuellavery/work/helix_frobenius/tmp/siegel_round1_D{DMAX_FULL}.jsonl"

def fundamental_discs(limit):
    for n in range(2, limit + 1):
        for d in (n, -n):
            if d % 4 in (0, 1) and d != 1 and Integer(d).is_fundamental_discriminant():
                yield d

def main_term(q, T):
    # (T/pi)(log(qT/(2*pi)) - 1) + 1/4-ish; used only as a +-2 audit anchor
    return float((T / (2 * pi)) * (log(q * T / (2 * pi)) - 1))

events, flags, done = 0, 0, 0
with open(OUT, "w") as fh:
    for d in fundamental_discs(DMAX_FULL):
        q = abs(d)
        try:
            chi = kronecker_character(d)
            L = Lfunction_from_character(chi.primitive_character())
            # --- Arm A: Siegel box grid
            lo = max(0.5, 1.0 - 3.0 / float(log(q))) if q > 20 else 0.5
            grid = [lo + (0.999 - lo) * k / 39 for k in range(40)]
            vals = [float(L.value(s).real()) for s in grid]
            L1 = float(L.value(1.0000001).real())
            signch = sum(1 for a, b in zip(vals, vals[1:]) if a * b < 0)
            minabs = min(abs(v) for v in vals)
            # --- Arm B: strip census
            zs = L.find_zeros(0.01, T_STRIP, 0.06)
            nz = len([z for z in zs if 0 < float(z) <= T_STRIP])
            mt = main_term(q, T_STRIP)
            dev = nz - mt
            rec = {"d": int(d), "q": int(q), "signch": int(signch),
                   "minabsL_box": minabs, "L1": L1, "n_zeros": int(nz),
                   "main_term": mt, "dev": float(dev)}
            if signch > 0:
                rec["EVENT"] = "siegel-box-sign-change"; events += 1
            if abs(dev) > 2.0:
                rec["FLAG"] = "strip-count-deviation"; flags += 1
            fh.write(json.dumps(rec) + "\n")
        except Exception as e:
            fh.write(json.dumps({"d": int(d), "error": str(e)[:120]}) + "\n")
        done += 1
        if done % 200 == 0:
            print(f"[{done}] d={d} events={events} flags={flags}", flush=True)
print(f"DONE chars={done} events={events} flags={flags} -> {OUT}", flush=True)
