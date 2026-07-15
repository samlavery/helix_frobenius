"""
Collective hidden-class hunt on the mu_21 cover y^21=x(1-x): products over sector-structured
rail subsets S, freeze = prod_{j in S} J_j / p^{|S|/2}, root of unity <=> collective class.
Order 1's sixfold Weil class = the mu_3 omega-eigenspace product (6 rails j==1 mod3, j!=0 mod7).
Hunt: does any OTHER structured subset freeze -- especially sector-CROSSING (mu_3 x mu_7) ones =
a hidden combined class the sub-readings miss?  MULTI-RAIL / HARMONIC(mu_21) / ETA(prod/p^{|S|/2}).
"""
import cmath, math

def primes_1mod21(lo, hi):
    return [p for p in range(lo, hi) if p % 21 == 1 and all(p % q for q in range(2, int(p**0.5)+1))]

def prim_root(p):
    m, fac, d = p-1, [], 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g

def jacobi_all(p):
    g = prim_root(p); e = (p-1)//21; ge = pow(g, e, p)
    idx = {}; cur = 1
    for t in range(21):
        idx[cur] = t; cur = (cur*ge) % p
    ci = lambda a: idx[pow(a, e, p)] if a % p else None
    z = [cmath.exp(2j*math.pi*t/21) for t in range(21)]
    J = [0j]*21
    for x in range(2, p):
        tx = ci(x); t1x = ci((1-x) % p)
        if tx is None or t1x is None: continue
        for j in range(1, 21):
            J[j] += z[(j*tx) % 21] * z[(j*t1x) % 21]
    return J

def order_of(z, tol=3e-2):
    for o in (1,2,3,6,7,9,14,18,21,42,63):
        if abs(z**o - 1) < tol: return o
    return None

# structured subsets by (mod3, mod7) pattern
def subset(cond):
    return [j for j in range(1, 21) if cond(j)]
CANDS = {
    "mu3-omega (SIXFOLD Weil)":  subset(lambda j: j%3==1 and j%7!=0),
    "mu3-omega2 (conj)":         subset(lambda j: j%3==2 and j%7!=0),
    "mu7-c1":                    subset(lambda j: j%7==1 and j%3!=0),
    "mu7-c2":                    subset(lambda j: j%7==2 and j%3!=0),
    "mu7-c3":                    subset(lambda j: j%7==3 and j%3!=0),
    "mixed j==1 mod21 coset*1":  subset(lambda j: j%3==1 and j%7==1),
    "mixed j==1mod3 & 1mod7 etc":subset(lambda j: (j%3,j%7) in {(1,1),(2,2),(1,2),(2,1)}),
    "all j==1 mod3 (incl mu3)":  subset(lambda j: j%3==1),
    "all j==1 mod7 (incl mu7)":  subset(lambda j: j%7==1),
    "sqrt21 pattern (QR3*QR7)":  subset(lambda j: (pow(j,1,3) in (1,) ) == (pow(j%7 or 7,3,7)==1)),
}
P = primes_1mod21(43, 400)
print("== collective hidden-class hunt, mu_21 cover y^21=x(1-x) ==")
print("primes:", P)
print(" subset                          size  freeze prod/p^(|S|/2)      order(stable?)")
Js = {p: jacobi_all(p) for p in P}
for name, S in CANDS.items():
    if not S:
        print("  %-30s  (empty)" % name); continue
    orders = []
    val0 = None
    for p in P:
        J = Js[p]
        pr = 1+0j
        for j in S: pr *= J[j]
        r = pr / (p ** (len(S)/2))
        if p == P[0]: val0 = r
        orders.append(order_of(r))
    stable = len(set(o for o in orders if o is not None)) == 1 and all(o is not None for o in orders)
    oshow = orders[0] if stable else orders
    print("  %-30s  %3d   %+.3f%+.3fi      %s%s"
          % (name, len(S), val0.real, val0.imag, ("order %s STABLE" % orders[0]) if stable else "not stable %s" % orders,
             "  <== FREEZE" if stable else ""))
