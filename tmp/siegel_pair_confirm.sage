import json
from sage.libs.lcalc.lcalc_Lfunction import Lfunction_from_character
targets = [-2551, -2999, 3061, -3288, 3289, 3505, 4737, 4920, -5108, 7673, -7691, -7988, -8103, 8113, -9204]
pairs = []
for d in targets:
    chi = kronecker_character(d)
    L = Lfunction_from_character(chi.primitive_character())
    zs = sorted(float(z) for z in L.find_zeros(0.01, 30.0, 0.01) if 0 < float(z) <= 30)
    gaps = [(zs[i+1]-zs[i], zs[i]) for i in range(len(zs)-1)]
    g, t = min(gaps)
    pairs.append((d, round(g,4), round(t,3)))
    # stability spot-check on the two worst originals
    if d in (-2999, 8113):
        zs3 = [z for z in L.find_zeros(0.01, 30.0, 0.002) if 0 < float(z) <= 30]
        print(f"  d={d}: fine={len(zs)} ultrafine={len(zs3)} {'STABLE' if len(zs3)==len(zs) else 'STILL MOVING'}")
print("close-pair sites (d, min gap, at t):")
for p in sorted(pairs, key=lambda x: x[1]): print(f"  {p}")
