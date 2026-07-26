# hunt-spec 2026-07-26, session 18a3f704 — Campaign 1 ROUND 2
# Arm A (Siegel box) for ALL fundamental |d| in (DMIN, DMAX];
# Arm B (strip audit, T=30) for |d| <= STRIP_MAX, SELF-HEALING:
#   |dev|>2 -> inline rerun at step 0.01; records resolution + min gap
#   (close-pair harvest). Unresolved after heal -> ESCALATE flag.
# Resume-capable: skips d already in OUT.
import json, os, sys
from sage.libs.lcalc.lcalc_Lfunction import Lfunction_from_character

DMIN = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
STRIP_MAX = 30000
T = 30.0
OUT = f"/Users/samuellavery/work/helix_frobenius/tmp/siegel_round2_D{DMAX}.jsonl"

done = set()
if os.path.exists(OUT):
    for line in open(OUT):
        try: done.add(json.loads(line)["d"])
        except Exception: pass

def main_term(q, TT):
    return float((TT / (2 * pi)) * (log(q * TT / (2 * pi)) - 1))

events = flags = healed = cnt = 0
fh = open(OUT, "a", buffering=1)
for n in range(max(2, DMIN + 1), DMAX + 1):
    for d in (n, -n):
        if d in done or d % 4 not in (0, 1) or d == 1:
            continue
        if not Integer(d).is_fundamental_discriminant():
            continue
        q = abs(d)
        try:
            chi = kronecker_character(d)
            L = Lfunction_from_character(chi.primitive_character())
            lo = 1.0 - 3.0 / float(log(q))
            grid = [lo + (0.999 - lo) * k / 39 for k in range(40)]
            vals = [float(L.value(s).real()) for s in grid]
            L1 = float(L.value(1.0000001).real())
            signch = sum(1 for a, b in zip(vals, vals[1:]) if a * b < 0)
            rec = {"d": int(d), "q": int(q), "signch": int(signch),
                   "minabsL_box": min(abs(v) for v in vals), "L1": L1}
            if signch > 0:
                rec["EVENT"] = "siegel-box-sign-change"; events += 1
                print(f"*** EVENT d={d} ***", flush=True)
            if q <= STRIP_MAX:
                zs = L.find_zeros(0.01, T, 0.06)
                nz = len([z for z in zs if 0 < float(z) <= T])
                dev = nz - main_term(q, T)
                rec["n_zeros"], rec["dev"] = int(nz), float(dev)
                if abs(dev) > 2.0:
                    zs2 = sorted(float(z) for z in L.find_zeros(0.01, T, 0.01)
                                 if 0 < float(z) <= T)
                    dev2 = len(zs2) - main_term(q, T)
                    gaps = [zs2[i+1] - zs2[i] for i in range(len(zs2)-1)]
                    rec["n_zeros_fine"], rec["dev_fine"] = len(zs2), float(dev2)
                    rec["min_gap"] = round(min(gaps), 5) if gaps else None
                    if abs(dev2) > 2.0:
                        rec["FLAG"] = "unresolved-after-heal"; flags += 1
                        print(f"*** UNRESOLVED FLAG d={d} dev_fine={dev2:+.2f} ***",
                              flush=True)
                    else:
                        rec["healed"] = True; healed += 1
            fh.write(json.dumps(rec) + "\n")
        except Exception as e:
            fh.write(json.dumps({"d": int(d), "error": str(e)[:120]}) + "\n")
        cnt += 1
        if cnt % 500 == 0:
            print(f"[{cnt}] d={d} events={events} healed={healed} flags={flags}",
                  flush=True)
print(f"DONE chars={cnt} events={events} healed={healed} unresolved={flags}",
      flush=True)
