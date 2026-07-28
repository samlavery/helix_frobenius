# sixfold step-0 (2026-07-27): construct the non-split Weil sixfold candidate
#   B = Prym(C~ / C0),  C0: w^3 + 2w + (u+v) = 0 over E0: v^2 = u^3 + 1
#   (certified primary base, b=1 A=2 B=(1,1,0)); eta = (0,1) in E0[3];
#   C~ = C0 x_{E0,psi} E1 with psi = dual of the 3-isogeny E0 -> E1 = E0/<eta>.
# Gates per prime:
#   G1 connectivity: one prime with genus-12-consistent counts proves f*eta != 0
#      (disconnected cover => s(B) = 2 s(C0) => deg-12 FE completion fails Weil);
#   G2 Prym L-factor: deg-12 Newton+FE completion, integral coefficients,
#      all roots |alpha| = sqrt(p);
#   G3 split primes: P_B = Norm_{Q(zeta3)/Q}(deg-6) factorization (zeta3 action);
#   G4 squeeze first reading: H^1 commutant (End^0(B) bound) and Lambda^6
#      cluster profile / Tate mult / commutant  -- the sixfold phantom-count
#      instrument's first light.
# Counting route: enumerate E1(F_{p^k}) affine points, push through psi's
# rational maps (denominator zero = kernel bucket -> pairs with C0's infinity
# pattern), count roots of w^3 + 2w + (u0+v0) by gcd(w^q - w, cubic).
import sys
sys.path.insert(0, '.')
from sage.all import (EllipticCurve, QQ, GF, PolynomialRing, ComplexField,
                      CDF, CyclotomicField, power_mod, gcd)
import json, math
from itertools import combinations

AW = 2
BW = (1, 1, 0)
KMAX = 6
OUT = "sixfold_step0.jsonl"

E0Q = EllipticCurve(QQ, [0, 1])
phiQ = E0Q.isogeny(E0Q(0, 1))
E1Q = phiQ.codomain()
psiQ = phiQ.dual()
XQ, YQ = psiQ.rational_maps()

PATTERNS6 = {"split": [3]*6, "partial": [1, 3, 1, 3, 1, 3],
             "inert": [0, 0, 3, 0, 0, 3]}

def root_count(F, Rw, w, c):
    f = w**3 + F(AW)*w + c
    wq = power_mod(w, F.order(), f)
    return gcd(wq - w, f).degree()

def counts_at(p, k):
    """returns (N_C0_affine, N_Ctilde_affine_nonker, ker_bucket, N_E0)"""
    F = GF(p**k, 'a')
    Rw = PolynomialRing(F, 'w'); w = Rw.gen()
    # compiled psi maps over F (x,y) -> (X, Y)
    Rxy = PolynomialRing(F, ['x', 'y'])
    Xn = Rxy(XQ.numerator());  Xd = Rxy(XQ.denominator())
    Yn = Rxy(YQ.numerator());  Yd = Rxy(YQ.denominator())
    a1, a2, a3, a4, a6 = [F(c) for c in E1Q.a_invariants()]
    nC0 = 0; nE0 = 0
    for u in F:
        rhs = u**3 + F(1)
        vs = []
        if rhs == 0:
            vs = [F(0)]
        elif rhs.is_square():
            s = rhs.sqrt(); vs = [s, -s]
        for v in vs:
            nE0 += 1
            nC0 += root_count(F, Rw, w, F(BW[0])*u + F(BW[1])*v + F(BW[2]))
    nCt = 0; ker = 1   # O_{E1} in the kernel bucket
    for x in F:
        # E1 affine points: y^2 + a1 x y + a3 y = x^3 + a2 x^2 + a4 x + a6
        # complete the square (p != 2)
        bb = a1*x + a3
        cc = x**3 + a2*x**2 + a4*x + a6
        disc = bb**2 + 4*cc
        ys = []
        if disc == 0:
            ys = [-bb/2]
        elif disc.is_square():
            r = disc.sqrt(); ys = [(-bb + r)/2, (-bb - r)/2]
        for y in ys:
            d = Xd(x, y)
            if d == 0:
                ker += 1
                continue
            u0 = Xn(x, y)/d
            v0 = Yn(x, y)/Yd(x, y)
            nCt += root_count(F, Rw, w, F(BW[0])*u0 + F(BW[1])*v0 + F(BW[2]))
    return nC0, nCt, ker, nE0

def newton_fe(svals, deg_half, p):
    """monic deg = 2*deg_half Weil poly from s_1..s_{deg_half} via Newton +
    FE completion c_{2h-i} = p^{h-i} c_i; returns coefficient list or None."""
    c = [QQ(1)]
    for k in range(1, deg_half + 1):
        acc = svals[k]
        for i in range(1, k):
            acc += c[i]*svals[k-i]
        ck = -acc/k
        c.append(ck)
    if any(x.denominator() != 1 for x in c[1:]):
        return None
    full = list(c) + [QQ(0)]*deg_half
    for i in range(0, deg_half):
        full[2*deg_half - i] = QQ(p)**(deg_half - i)*c[i]
    return full

def weil_roots(full, p, deg):
    C100 = ComplexField(100)
    R = PolynomialRing(QQ, 'T'); T = R.gen()
    P = sum(full[j]*T**(deg - j) for j in range(deg + 1))
    rts = []
    for r, m in P.change_ring(C100).roots():
        rts += [CDF(r)]*m
    if len(rts) != deg:
        return None, P
    if max(abs(abs(r) - math.sqrt(p)) for r in rts) > 1e-6:
        return None, P
    return rts, P

def cluster(vals, digits=7):
    cl = {}
    for v in vals:
        key = (round(v.real(), digits), round(v.imag(), digits))
        cl[key] = cl.get(key, 0) + 1
    prof = sorted(cl.values(), reverse=True)
    tate = 0
    for kk, m in cl.items():
        if abs(CDF(kk[0], kk[1]) - 1) < 1e-6:
            tate = m
    return prof, sum(m*m for m in prof), tate

def run_prime(p, fh):
    print(f"---- p = {p} ({'SPLIT' if p % 3 == 1 else 'INERT'}) ----", flush=True)
    aff0, afft, kers, e0s = [None], [None], [None], [None]
    for k in range(1, KMAX + 1):
        nC0, nCt, ker, nE0 = counts_at(p, k)
        aff0.append(nC0); afft.append(nCt); kers.append(ker); e0s.append(nE0)
        print(f"  k={k}: C0_aff={nC0} Ct_aff={nCt} ker={ker} E0={nE0 + 1}",
              flush=True)
    # fit the infinity pattern on C0 (deg-8 gate) then build the Prym factor
    for name, pat in PATTERNS6.items():
        s0 = [None] + [QQ(p**k + 1 - (aff0[k] + pat[k-1]))
                       for k in range(1, KMAX + 1)]
        full0 = newton_fe(s0, 4, p)
        if full0 is None:
            continue
        r0, P0 = weil_roots(full0, p, 8)
        if r0 is None:
            continue
        # C~ totals with the same pattern through the kernel bucket
        sT = [None] + [QQ(p**k + 1 - (afft[k] + kers[k]*pat[k-1]))
                       for k in range(1, KMAX + 1)]
        sB = [None] + [sT[k] - s0[k] for k in range(1, KMAX + 1)]
        fullB = newton_fe(sB, 6, p)
        gate_int = fullB is not None
        rB = PB = None
        if gate_int:
            rB, PB = weil_roots(fullB, p, 12)
        rec = {"p": int(p), "pattern": name,
               "kind": "SPLIT" if p % 3 == 1 else "INERT",
               "sB": [int(x) for x in sB[1:]],
               "gate_integral": bool(gate_int),
               "gate_weil": bool(rB is not None)}
        if rB is None:
            print(f"  pattern={name}: Prym gates integral={gate_int} weil=FAIL",
                  flush=True)
            fh.write(json.dumps(rec, default=int) + "\n"); fh.flush()
            continue
        # G3: zeta3 norm structure at split primes
        if p % 3 == 1:
            K3 = CyclotomicField(3)
            fac = PB.change_ring(K3).factor()
            degs = sorted(f.degree() for f, m in fac for _ in range(m))
            rec["zeta3_factor_degrees"] = degs
        # G4: squeeze first reading
        prof1, comm1, _ = cluster([r/CDF(math.sqrt(p)) for r in rB])
        vals6 = []
        q3 = CDF(p)**3
        for idx in combinations(range(12), 6):
            v = CDF(1)
            for i in idx:
                v *= rB[i]
            vals6.append(v/q3)
        prof6, comm6, tate6 = cluster(vals6)
        rec.update({"H1_profile": prof1, "H1_commutant": int(comm1),
                    "L6_profile_head": prof6[:8], "L6_D": len(prof6),
                    "L6_commutant": int(comm6), "L6_tate": int(tate6),
                    "PB": str(PB)})
        print(f"  pattern={name}: PRYM GATES PASS  sB={rec['sB']}", flush=True)
        print(f"    P_B = {PB}", flush=True)
        if "zeta3_factor_degrees" in rec:
            print(f"    zeta3 factor degrees: {rec['zeta3_factor_degrees']}",
                  flush=True)
        print(f"    H^1 profile {prof1} commutant {comm1}; "
              f"L^6: D={len(prof6)} head={prof6[:8]} commutant={comm6} "
              f"Tate={tate6}", flush=True)
        fh.write(json.dumps(rec, default=int) + "\n"); fh.flush()

import os
PRIMES = [int(a) for a in sys.argv[1:]] if len(sys.argv) > 1 else [5, 7, 11, 13]
fh = open(OUT, "a")
for p in PRIMES:
    try:
        run_prime(p, fh)
    except Exception as ex:
        import traceback; traceback.print_exc()
        print(f"p={p} ERROR {ex}", flush=True)
fh.close()
print("STEP0 DONE", flush=True)
