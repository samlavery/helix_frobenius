"""
ggk_multirail_ladder.py -- push the multi-rail freeze mass to 4, 5, 6 rails.

freeze mass M1 = avg_p |W_p|^2 / p,  W_p = sum_{x in F_p} chi3(h(x))  (chi3-eigenspace trace).
Must read it where the fiber's automorphisms are RATIONAL: p == 1 mod lcm(3, m) for a mu_m curve.

Two ladders:
 (A) single fibers with larger cyclic symmetry mu_m:  y^3 = (x^m+1)(x^m+s)^2, aut x->zeta_m x.
     (m=4 already gave 3 rails.)  the chi3-part splits under mu_m into more rails as m grows.
 (B) CONTROLLED n-rail fibers: direct sum of n DISTINCT simple family-B curves.  each simple
     curve is one rail (mass 1); distinct (non-isogenous) => cross terms vanish =>
     freeze mass = Sum 1^2 = n exactly.  a clean n-rail cross-check.
"""
import cmath, math
W3 = cmath.exp(2j * cmath.pi / 3)

def is_prime(n):
    if n < 2: return False
    return all(n % q for q in range(2, int(n**0.5) + 1))

def primes_1mod(mod, hi, count):
    out = []
    p = mod + 1
    while len(out) < count and p < hi:
        if is_prime(p): out.append(p)
        p += mod
    return out

def prim_root(p):
    fac, m, d = [], p - 1, 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac): return g
    return 2

def chi3_table(p):
    g = prim_root(p); r = pow(g, (p - 1) // 3, p); e = (p - 1) // 3
    tab = [0j] * p
    for a in range(1, p):
        v = pow(a, e, p)
        tab[a] = 1 + 0j if v == 1 else (W3 if v == r else W3 * W3)
    return tab

def ev(co, x, p):
    v = 0
    for c in co: v = (v * x + c) % p
    return v

def W_single(fco, gco, p, tab):
    # chi3( f * g^2 )
    s = 0j
    for x in range(p):
        f = ev(fco, x, p); g = ev(gco, x, p)
        s += tab[(f * g % p) * g % p]
    return s

def mass_single(fco, gfam, svals, primes):
    tot = wsum = 0.0
    for p in primes:
        tab = chi3_table(p)
        for s in svals:
            W = W_single(fco, gfam(s), p, tab)
            tot += abs(W) ** 2 / p; wsum += 1.0
    return tot / wsum

def mass_sum(curves, primes):
    # curves: list of (fco, gco); fiber = direct sum; W = sum of the individual W's
    tot = wsum = 0.0
    for p in primes:
        tab = chi3_table(p)
        W = sum(W_single(fco, gco, p, tab) for (fco, gco) in curves)
        tot += abs(W) ** 2 / p; wsum += 1.0
    return tot / wsum

lines = ["== multi-rail freeze mass ladder: aiming for 4, 5, 6 rails =="]

# ---- (A) single fibers with cyclic symmetry mu_m ------------------------------
lines.append("-- (A) single mu_m curves  y^3=(x^m+1)(x^m+s)^2  (p==1 mod lcm(3,m)) --")
for m in (4, 6, 8, 12):
    lcm = m if m % 3 == 0 else 3 * m
    P = primes_1mod(lcm, 4000, 40)
    F = [1] + [0] * (m - 1) + [1]                 # x^m + 1
    gfam = lambda s, m=m: [1] + [0] * (m - 1) + [s]   # x^m + s
    mass = mass_single(F, gfam, [2, 3], P)
    lines.append("  mu_%-2d : freeze mass = %.3f   (n=%d primes, lcm=%d)" % (m, mass, len(P), lcm))

# ---- (B) controlled n-rail: sum of n distinct simple family-B curves ----------
lines.append("-- (B) sum of n DISTINCT simple curves  y^3=(x^4+1)(x^4+s_i x+2)^2  => n rails --")
F4 = [1, 0, 0, 0, 1]
simpleB = lambda s: (F4, [1, 0, 0, s, 2])          # (f, g) with g = x^4 + s x + 2
P12 = primes_1mod(12, 6000, 120)
for n in (2, 3, 4, 5, 6):
    curves = [simpleB(s) for s in range(2, 2 + n)]   # s = 2..n+1, distinct
    mass = mass_sum(curves, P12)
    lines.append("  n=%d : freeze mass = %.3f   (expect %d)" % (n, mass, n))

out = "\n".join(lines)
print(out)
open("/Users/samuellavery/work/helix_frobenius/tmp/ggk_multirail_ladder_results.txt", "w").write(out + "\n")
