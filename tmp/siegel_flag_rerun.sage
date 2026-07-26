# hunt-spec 2026-07-26 — flag ladder: re-run the 15 flagged characters with
# 6x finer zero-search step; a missed close pair reveals itself as a count
# INCREASE at finer step; stable count = anchor artifact (S(t) tail).
import json
from sage.libs.lcalc.lcalc_Lfunction import Lfunction_from_character
flags = []
for line in open("siegel_round1_D10000.jsonl"):
    r = json.loads(line)
    if r.get("FLAG"): flags.append(r)
print(f"re-running {len(flags)} flags at step 0.01 (was 0.06)")
for r in flags:
    d = r["d"]
    chi = kronecker_character(d)
    L = Lfunction_from_character(chi.primitive_character())
    zs = L.find_zeros(0.01, 30.0, 0.01)
    nz2 = len([z for z in zs if 0 < float(z) <= 30.0])
    delta = nz2 - r["n_zeros"]
    verdict = "STABLE (anchor artifact)" if delta == 0 else f"COUNT CHANGED +{delta} -> ESCALATE"
    print(f"d={d:>7} nz_coarse={r['n_zeros']} nz_fine={nz2} dev_was={r['dev']:+.2f}  {verdict}")
