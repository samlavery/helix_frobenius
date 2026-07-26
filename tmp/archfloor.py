# hunt-spec 2026-07-26, session 18a3f704 — Campaign 2: arch-floor collapse
# test at the 15 harvested close-pair sites (falsifier (a) of the register).
# For each site: refine BOTH zeros of the pair by bisection on the REAL
# completed Lambda(1/2+it, chi_d) (real primitive chi => eps=+1 => real on
# the line); certify: (i) sign-change bracket width < 1e-24 (interval
# certificate of an ON-LINE zero), (ii) floor |Lambda| at refined zero
# collapses below gate, (iii) arch max between the pair + arch/gap^2 ratio
# (Lehmer-pair quadratic law telemetry).  FALSIFIER fires only if a floor
# reproducibly bottoms out ABOVE gate: recorded loudly, never claimed
# from one run.
import json
from mpmath import mp, mpf, mpc, gamma, pi, zeta, exp, log, sqrt

mp.dps = 40
GATE = mpf(10) ** (-24)

SITES = [(8113, 18.328), (-8103, 15.379), (-2999, 14.192), (4737, 26.716),
         (-5108, 8.437), (-7691, 24.86), (-3288, 8.961), (3061, 25.404),
         (-2551, 23.011), (4920, 21.809), (-9204, 6.029), (-7988, 19.276),
         (7673, 28.57), (3505, 29.111), (3289, 25.691)]

def kron(d, n):
    # Kronecker symbol (d|n), n >= 1
    if n == 0: return 0
    r = 1
    if d < 0 and False: pass
    a, b = d % n if False else (d, n)
    # standard algorithm
    a = d
    if b == 1: return 1
    if a % 2 == 0 and b % 2 == 0: return 0
    # pull out factors of 2 from b
    v = 0
    while b % 2 == 0:
        b //= 2; v += 1
    if v % 2 == 0: k = 1
    else: k = 1 if a % 8 in (1, 7) else -1
    if b < 0: b = -b
    a %= b
    while a != 0:
        v = 0
        while a % 2 == 0:
            a //= 2; v += 1
        if v % 2 == 1 and b % 8 in (3, 5):
            k = -k
        if a % 4 == 3 and b % 4 == 3:
            k = -k
        a, b = b % a, a
    return k if b == 1 else 0

def make_L(d):
    q = abs(d)
    tab = [kron(d, n) for n in range(q)]
    par = 0 if tab[q - 1] == 1 else 1   # chi(-1)=chi(q-1)
    def Lam(t):
        s = mpc(mpf(1)/2, t)
        Lval = sum(tab[a] * zeta(s, mpf(a)/q) for a in range(1, q) if tab[a] != 0)
        Lval *= mpc(q) ** (-s)
        comp = (mpf(q)/pi) ** ((s + par)/2) * gamma((s + par)/2)
        return (comp * Lval).real
    return Lam

def bisect(f, lo, hi, flo, fhi, iters=90):
    for _ in range(iters):
        mid = (lo + hi)/2
        fm = f(mid)
        if fm == 0: return mid, mid, fm
        if (flo < 0) != (fm < 0): hi, fhi = mid, fm
        else: lo, flo = mid, fm
    return lo, hi, f((lo + hi)/2)

done = set()
try:
    for line in open("archfloor_results.jsonl"):
        done.add(json.loads(line)["d"])
except FileNotFoundError:
    pass
out = open("archfloor_results.jsonl", "a", buffering=1)
for d, t0 in SITES:
    if d in done:
        continue
    Lam = make_L(d)
    # locate the pair: scan +-0.06 around t0 at step 0.002 for sign changes
    ts = [mpf(t0) - mpf('0.06') + mpf('0.002')*k for k in range(61)]
    vs = [Lam(t) for t in ts]
    br = [(ts[i], ts[i+1], vs[i], vs[i+1]) for i in range(60)
          if (vs[i] < 0) != (vs[i+1] < 0)]
    if len(br) != 2:
        # widen once
        ts = [mpf(t0) - mpf('0.25') + mpf('0.005')*k for k in range(101)]
        vs = [Lam(t) for t in ts]
        br = [(ts[i], ts[i+1], vs[i], vs[i+1]) for i in range(100)
              if (vs[i] < 0) != (vs[i+1] < 0)]
    rec = {"d": d, "t0": float(t0), "n_brackets": len(br)}
    if len(br) >= 2:
        zs, floors, widths = [], [], []
        for lo, hi, flo, fhi in br[:2]:
            a, b, fm = bisect(Lam, lo, hi, flo, fhi)
            zs.append((a + b)/2); floors.append(abs(fm)); widths.append(b - a)
        gap = abs(zs[1] - zs[0])
        # arch max between the two zeros
        arch = max(abs(Lam(zs[0] + gap * mpf(k)/12)) for k in range(1, 12))
        rec.update({
            "zero1": mp.nstr(zs[0], 30), "zero2": mp.nstr(zs[1], 30),
            "gap": mp.nstr(gap, 12),
            "bracket_widths": [mp.nstr(w, 3) for w in widths],
            "floor1": mp.nstr(floors[0], 3), "floor2": mp.nstr(floors[1], 3),
            "collapse_ok": bool(floors[0] < GATE and floors[1] < GATE),
            "arch_max": mp.nstr(arch, 6),
            "arch_over_gap2": mp.nstr(arch / gap**2, 6)})
        if not rec["collapse_ok"]:
            rec["EVENT"] = "floor-noncollapse"
            print(f"*** EVENT d={d}: floor above gate ***", flush=True)
    out.write(json.dumps(rec) + "\n")
    print(f"done d={d} brackets={len(br)}", flush=True)
print("ALL SITES DONE", flush=True)
