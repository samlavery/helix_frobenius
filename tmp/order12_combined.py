"""
Order 1 (sixfold, mu_3) + Order 2 (non-self-dual, mu_7) COMBINED on the mu_21 = lcm(3,7) clock.
Curve y^21 = x(1-x): H^1 eigenspaces V_j (j=1..20) under mu_21, eigenvalue = Jacobi sum
J_j = sum_x chi_21^j(x) chi_21^j(1-x), |J_j| = sqrt(p).  Sectors:
  mu_3  rail (the sixfold Weil sector): j = 7, 14           (chi_21^7 has order 3)
  mu_7  rail (the non-self-dual sector): j = 3,6,9,12,15,18  (order 7)
  mixed rail (gcd(j,21)=1):              j = 1,2,4,5,8,...   (order 21)

HIDDEN-CLASS HUNT: Tate classes in H^1 x H^1 are eigenvalue products = p.  OBVIOUS: J_i J_{-i}
= |J_i|^2 = p (polarization, self-dual, scalar-visible).  HIDDEN: J_i J_j = p*(root of unity)
with i+j != 0 mod 21 -- an extra correspondence connecting rails, invisible to the scalar sum
and to either sub-reading.  Flag hidden ones and their sector-crossing (mu_3 <-> mu_7 = the
combined class).  MULTI-RAIL (all 20 rails), ETA (J/sqrt p ; product/p for the Tate class),
HARMONIC (mu_21 unifying mu_3, mu_7), ROOTS (branch 0,1,inf).
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

def chi21_index(p):
    """a -> t in 0..20 with chi_21(a) = zeta_21^t (a != 0)."""
    g = prim_root(p); e = (p-1)//21; ge = pow(g, e, p)
    idx = {}; cur = 1
    for t in range(21):
        idx[cur] = t; cur = (cur*ge) % p
    return lambda a: idx[pow(a, e, p)] if a % p else None

def jacobi_all(p):
    """J_j for j=1..20 : sum_x chi^j(x) chi^j(1-x)."""
    ci = chi21_index(p); z = [cmath.exp(2j*math.pi*t/21) for t in range(21)]
    J = [0j]*21
    for x in range(2, p):                      # x != 0,1 ; also skip 1-x=0 => x=1
        tx = ci(x); t1x = ci((1-x) % p)
        if tx is None or t1x is None: continue
        for j in range(1, 21):
            J[j] += z[(j*tx) % 21] * z[(j*t1x) % 21]
    return J

def order_of(z, tol=2e-2):
    for o in (1,2,3,6,7,14,21,42):
        if abs(z**o - 1) < tol: return o
    return None

def sector(j):
    if j % 7 == 0: return "mu3"       # order 3
    if j % 3 == 0: return "mu7"       # order 7
    return "mix"

P = primes_1mod21(43, 400)
print("== mu_21 combined 6fold(mu_3) + non-self-dual(mu_7): hidden-class hunt ==")
print("primes p=1 mod21:", P)
# collect hidden Tate pairs consistently across primes
hidden_counts = {}
for p in P:
    J = jacobi_all(p)
    for i in range(1, 21):
        for j in range(i, 21):
            if (i + j) % 21 == 0:      # trivial polarization pair
                continue
            r = (J[i]*J[j]) / p
            if abs(abs(r) - 1) < 1e-6:
                o = order_of(r)
                if o is not None:
                    hidden_counts.setdefault((i, j), []).append((p, o))
print("\nHIDDEN Tate relations J_i J_j = p*(root of unity), i+j != 0 mod 21:")
found = False
for (i, j), hits in sorted(hidden_counts.items()):
    if len(hits) >= max(2, len(P)//2):        # stable across >= half the primes
        found = True
        secs = "%s+%s" % (sector(i), sector(j))
        crossing = " <== SECTOR-CROSSING (combined class!)" if sector(i) != sector(j) else ""
        orders = sorted(set(o for _, o in hits))
        print("  (i=%2d, j=%2d)  sectors %s  orders %s  stable %d/%d%s"
              % (i, j, secs, orders, len(hits), len(P), crossing))
if not found:
    print("  none stable across primes -> only the polarization pairs (obvious) freeze; no hidden class.")
# also: which single rails are non-self-dual (J_j != conj J_{-j} would break; check magnitudes)
print("\nsanity: |J_1|/sqrt p over primes:", [round(abs(jacobi_all(p)[1])/math.sqrt(p),3) for p in P[:4]])
