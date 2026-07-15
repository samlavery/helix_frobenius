"""
GGK freeze-mass meter on a genuine SIXFOLD (order-1 new ground; the pre-registered open reading).
Extends the v2 fourfold-validated meter to genus 6, signature (3,3), K=Q(sqrt-3) mu_3 rails.

Family (count-probe's genus-6 base, made a degenerating family):
  f = x(x-1)(x-2)(x-3)          [deg 4, fixed]
  g_s = (x-4)(x-5)(x-s)          [deg 3, moving third root]
  h = f * g^2                    [deg 10 -> cyclic trigonal cover, genus 6, (3,3)]
Degenerations (named algebraic loci):
  s in {0,1,2,3} : g shares a root with f  (branch collision -> algebraicity materializes)
  s in {4,5}     : g has a repeated root   (curve degenerates)
Generic s (8,9,10,11,6): simple sixfold, Weil class present transcendentally.

Meter (validated on fourfolds): M_k(s) = weighted avg |W_p^(k)|^2 / p^k over K-split primes,
excess = M_k - 1 (Katz-Sarnak Haar baseline); C_k = phase coherence (frozen => C->1).
PRE-REGISTERED no-orphan reading: every M-explosion sits on a NAMED algebraic locus (a
collision), generic members carry a bounded frozen excess (the Weil class), no orphan jump.
"""
import cmath, math

W3 = cmath.exp(2j * math.pi / 3)

def primes(lo, hi):
    out = []
    for p in range(lo, hi):
        if p % 3 == 1 and all(p % q for q in range(2, int(p**0.5) + 1)):
            out.append(p)
    return out

def prim_root(p):
    m, fac, d = p - 1, [], 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g

def chi3_table(p):
    g = prim_root(p); r = pow(g, (p - 1) // 3, p); e = (p - 1) // 3
    tab = [0j] * p
    for a in range(1, p):
        v = pow(a, e, p)
        tab[a] = 1 + 0j if v == 1 else (W3 if v == r else W3 * W3)
    return tab

def find_irr(p, k):
    for c in range(p):
        for d in range(1, p):
            co = [1, c, d] if k == 2 else [1, 0, c, d]
            has_root = False
            for x in range(p):
                v = 0
                for cc in co: v = (v * x + cc) % p
                if v == 0: has_root = True; break
            if not has_root:
                return co
    return None

def field_ops(p, k, irr):
    def mul(a, b):
        prod = [0] * (2 * k - 1)
        for i in range(k):
            if a[i]:
                for j in range(k):
                    prod[i + j] = (prod[i + j] + a[i] * b[j]) % p
        for deg in range(2 * k - 2, k - 1, -1):
            c = prod[deg]
            if c:
                prod[deg] = 0
                for j in range(1, k + 1):
                    prod[deg - j] = (prod[deg - j] - c * irr[j]) % p
        return tuple(prod[:k])
    def norm(a):
        basis = [tuple(1 if i == j else 0 for i in range(k)) for j in range(k)]
        cols = [mul(a, e) for e in basis]
        if k == 2:
            (m00, m10), (m01, m11) = cols
            return (m00 * m11 - m01 * m10) % p
        (a0, a1, a2), (b0, b1, b2), (c0, c1, c2) = cols
        return (a0*(b1*c2-b2*c1) - b0*(a1*c2-a2*c1) + c0*(a1*b2-a2*b1)) % p
    return mul, norm

def weil_sum(p, k, tab, hco):
    if k == 1:
        s = 0j
        for x in range(p):
            v = 0
            for c in hco: v = (v * x + c) % p
            s += tab[v]
        return s
    irr = find_irr(p, k); mul, norm = field_ops(p, k, irr); hmod = [c % p for c in hco]
    s = 0j
    def elems(idx, cur):
        if idx == k:
            yield tuple(cur); return
        for v in range(p):
            cur.append(v); yield from elems(idx + 1, cur); cur.pop()
    for x in elems(0, []):
        acc = tuple([hmod[0]] + [0]*(k-1))
        for c in hmod[1:]:
            acc = mul(acc, x)
            acc = tuple((acc[i] + (c if i == 0 else 0)) % p for i in range(k))
        s += tab[norm(acc)]
    return s

def poly_from_roots(roots):
    co = [1]                                  # high-to-low coeffs
    for r in roots:
        new = [0] * (len(co) + 1)
        for i in range(len(co)):
            new[i] += co[i]                   # x * co
            new[i + 1] += -r * co[i]          # -r * co
        co = new
    return co

def hpoly(fco, gco):
    def pm(a, b):
        r = [0]*(len(a)+len(b)-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b): r[i+j] += x*y
        return r
    return pm(fco, pm(gco, gco))

fco = poly_from_roots([0, 1, 2, 3])            # x(x-1)(x-2)(x-3)
P1, P2, P3 = primes(13, 260), primes(13, 95), [13, 19, 31, 37, 43]
KP = {1: P1, 2: P2, 3: P3}
print("== GGK freeze-mass on the SIXFOLD  y^3 = f * g_s^2  (genus 6, (3,3), K=Q(sqrt-3)) ==")
print("primes: k1 n=%d(<=%d)  k2 n=%d(<=%d)  k3 %s" % (len(P1), P1[-1], len(P2), P2[-1], P3))
print("f = x(x-1)(x-2)(x-3);  g_s = (x-4)(x-5)(x-s)")
print(" s     locus            M1     C1  |   M2       C2  |   M3       C3")
svals = [(0,"collide f@0"),(1,"collide f@1"),(2,"collide f@2"),(3,"collide f@3"),
         (4,"g double@4"),(5,"g double@5"),(6,"generic"),(8,"generic"),(9,"generic"),(10,"generic"),(11,"generic")]
for s, tag in svals:
    gco = poly_from_roots([4, 5, s])
    h = hpoly(fco, gco)
    res = {}
    for k, plist in KP.items():
        tot, wsum, coh = 0.0, 0.0, 0j
        L0, L1 = math.log(plist[0]), math.log(plist[-1]) + 1e-9
        for p in plist:
            tab = chi3_table(p); W = weil_sum(p, k, tab, h); q = float(p)**k
            w = math.cos(0.5*math.pi*(math.log(p)-L0)/(L1-L0))**2
            tot += w*abs(W)**2/q; wsum += w
            if abs(W) > 1e-9: coh += w*W/abs(W)
        res[k] = (tot/wsum, abs(coh)/wsum)
    print(" %2d   %-14s  %7.3f %.3f | %8.3f %.3f | %8.3f %.3f"
          % (s, tag, res[1][0], res[1][1], res[2][0], res[2][1], res[3][0], res[3][1]))
