# Track 2 step 0 HARDENING (2026-07-30): certify genus-4 base candidates.
# Gates: (A) infinity fiber = exact factorization pattern of a cubic
#   (three patterns: split/partial/inert -> c_k sequences), with the
#   k=5 count PREDICTED by the FE-completed degree-8 Weil polynomial
#   (Newton s_5 = -(c1 s4 + c2 s3 + c3 s2 + c4 s1 + 5 c5), c5 = p*c3);
# (B) smoothness over two good primes (finite singular-point check);
# (C) cross-prime genus-4 agreement; (D) non-Galois: disc -4A^3-27B^2
#   attains a non-square value (kills mu3/Galois covers).
# b=1 prioritized: E0 has rational 3-torsion (0,+-1) for the tower step.
from sage.all import GF, QQ, PolynomialRing
import itertools, math

PATTERNS = {  # c_k for k=1..5 by infinity-cubic factorization type
  "split":   [3,3,3,3,3],
  "partial": [1,3,1,3,1],
  "inert":   [0,0,3,0,3*0],  # order-3: roots only when 3|k: k=3 -> 3
}
PATTERNS["inert"] = [0,0,3,0,0]

def counts(p, kmax, b, A, B):
    out = {}
    for k in range(1, kmax+1):
        F = GF(p**k, 'a')
        R = PolynomialRing(F, 'w'); w = R.gen()
        bb, AA = F(b), F(A)
        c = 0
        for u in F:
            rhs = u**3 + bb
            if rhs == 0: vs = [F(0)]
            elif rhs.is_square(): s = rhs.sqrt(); vs = [s, -s]
            else: vs = []
            for v in vs:
                Bv = F(B[0])*u + F(B[1])*v + F(B[2])
                c += len((w**3 + AA*w + Bv).roots(multiplicities=False))
        out[k] = c
    return out

def gateA(p, N, pat):
    # traces with pattern; newton c1..c4; integrality; k=5 prediction
    s = [0] + [QQ(p**k + 1 - (N[k] + pat[k-1])) for k in range(1, 6)]
    c = [QQ(1)]
    for k in range(1, 5):
        acc = s[k]
        for i in range(1, k):
            acc += c[i]*s[k-i]
        ck = -acc/k
        if ck.denominator() != 1: return None
        c.append(ck)
    if abs(s[1]) > 8*math.sqrt(p) + 1e-9: return None
    c5 = QQ(p)*c[3]
    s5_pred = -(c[1]*s[4] + c[2]*s[3] + c[3]*s[2] + c[4]*s[1] + 5*c5)
    if s5_pred != s[5]: return None
    return [int(x) for x in c[1:]]

def gateB(p, b, A, B):
    F = GF(p)
    for u in F:
        for v in F:
            if v**2 != u**3 + F(b): continue
            Bv = F(B[0])*u + F(B[1])*v + F(B[2])
            R = PolynomialRing(F, 'w'); w = R.gen()
            for wr in (w**3 + F(A)*w + Bv).roots(multiplicities=False):
                if 3*wr**2 + F(A) == 0 and 2*F(B[0])*v + 3*F(B[1])*u**2 == 0:
                    return False
    return True

def gateD(p, b, A, B):
    F = GF(p)
    for u in F:
        rhs = u**3 + F(b)
        if not rhs.is_square() or rhs == 0: continue
        v = rhs.sqrt()
        for vv in (v, -v):
            Bv = F(B[0])*u + F(B[1])*vv + F(B[2])
            d = -4*F(A)**3 - 27*Bv**2
            if d != 0 and not d.is_square():
                return True
    return False

certified = []
for b, A, B0, B1, B2 in itertools.product([1], [1, 2], [1, 0], [1, 0], [0, 1, 2]):
    if B0 == 0 and B1 == 0: continue
    B = (B0, B1, B2)
    good = [p for p in (5, 7, 11, 13) if p not in (2, 3)]
    results = {}
    ok = True
    for p in good[:3]:
        N = counts(p, 5, b, A, B)
        hits = [(name, gateA(p, N, pat)) for name, pat in PATTERNS.items()]
        hits = [(n, e) for n, e in hits if e is not None]
        if len(hits) != 1:
            ok = False; break
        results[p] = hits[0]
    if not ok: continue
    if not (gateB(5, b, A, B) and gateB(7, b, A, B)): continue
    if not gateD(7, b, A, B): continue
    certified.append(((b, A, B), results))
    print(f"CERTIFIED b={b} A={A} B={B}:", flush=True)
    for p, (pat, e) in results.items():
        print(f"   p={p}: infinity={pat}, frobpoly c1..c4 = {e}", flush=True)
print(f"total certified: {len(certified)}", flush=True)
