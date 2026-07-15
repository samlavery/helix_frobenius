"""
Combined 6fold + non-self-dual, done right: mu_21 cover of ORDER-1's sixfold.
Curve y^21 = f*g^2, f=x(x-1)(x-2)(x-3) [deg4, exp 1], g=(x-4)(x-5)(x-6) [deg3, exp 2].
Exponents a=[1,1,1,1,2,2,2,11(inf)] (Sum=21).  mu_3 part (j=7,14) = the order-1 sixfold Weil
sector; mu_7 part (j%3==0) = non-self-dual; MIXED (gcd(j,21)=1) = the genuine combination.

CHECKLIST:
 ROOTS/dim: Chevalley-Weil  dim H^{1,0}_j = -1 + sum_i <j a_i/21>;  dim V_j = H^{1,0}_j + H^{1,0}_{-j}.
   Balanced (1,1) dim-2 eigenspaces = Hodge-class candidates (det type (1,1)).
 HARMONIC: det(Frob|V_j)= ^{dim}V_j (top), NOT 2nd moment.  For dim2: det=(t1^2-t2)/2.
 ETA: freeze r_j = det/p^{dim/2}; root of unity <=> class.  ALL RAILS j=1..20 by sector.
 HUNT: a frozen dim-2 (1,1) eigenspace in the MIXED or mu_7 sector = the hidden combined class.
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
    g = prim_root(p); e = (p-1)//21; ge = pow(g, e, p)
    idx = {}; cur = 1
    for t in range(21):
        idx[cur] = t; cur = (cur*ge) % p
    return lambda a: idx[pow(a, e, p)] if a % p else None

def poly_from_roots(rts):
    co = [1]
    for r in rts:
        nw = [0]*(len(co)+1)
        for i, a in enumerate(co): nw[i] += a; nw[i+1] += -r*a
        co = nw
    return co

def hpoly(fco, gco):
    def pm(a, b):
        r = [0]*(len(a)+len(b)-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b): r[i+j] += x*y
        return r
    return pm(fco, pm(gco, gco))

fco = poly_from_roots([0,1,2,3]); gco = poly_from_roots([4,5,6]); hc = hpoly(fco, gco)
a_exp = [1,1,1,1,2,2,2, (-10) % 21]     # exponents incl infinity

def frac(x): return x - math.floor(x)
def dimH10(j):
    return round(-1 + sum(frac(j*ai/21) for ai in a_exp))
def dimV(j):
    return dimH10(j % 21) + dimH10((-j) % 21)
def sig(j):
    return (dimH10(j % 21), dimH10((-j) % 21))

def W1(p, ci, z):
    acc = [0j]*21
    for x in range(p):
        v = 0
        for c in hc: v = (v*x + c) % p
        t = ci(v)
        if t is not None:
            for j in range(1,21): acc[j] += z[(j*t) % 21]
    return acc

def W2(p, ci, z):
    c = next(cc for cc in range(2,p) if pow(cc,(p-1)//2,p)==p-1)   # nonresidue
    acc = [0j]*21
    for aa in range(p):
        for bb in range(p):
            r0, r1 = 0, 0
            for co in hc:
                r0, r1 = (r0*aa + r1*bb*c) % p, (r0*bb + r1*aa) % p
                r0 = (r0 + co) % p
            nm = (r0*r0 - c*r1*r1) % p
            t = ci(nm)
            if t is not None:
                for j in range(1,21): acc[j] += z[(j*t) % 21]
    return acc

def order_of(zz, tol=3e-2):
    for o in (1,2,3,6,7,14,21,42):
        if abs(zz**o - 1) < tol: return o
    return None
def sector(j):
    if j % 7 == 0: return "mu3"
    if j % 3 == 0: return "mu7"
    return "mix"

print("== combined mu_21 cover y^21=f g^2 (order-1 sixfold + non-self-dual), test done right ==")
print(" j  sector dimV  sig     ", end="")
balanced2 = [j for j in range(1,21) if dimV(j)==2 and sig(j)==(1,1)]
print("\n balanced (1,1) dim-2 eigenspaces (Hodge-class candidates):", balanced2)
alldims = {j:(dimV(j), sig(j), sector(j)) for j in range(1,21)}
print(" all dims:", {j:alldims[j] for j in range(1,21)})

P = primes_1mod21(43, 200)
z = [cmath.exp(2j*math.pi*t/21) for t in range(21)]
print("\n freeze det(V_j)/p for the dim-2 rails, all primes:")
print("  j  sector sig    p=%s" % P)
for j in balanced2 + [jj for jj in range(1,21) if dimV(jj)==2 and jj not in balanced2]:
    rr = []
    for p in P:
        ci = chi21_index(p)
        t1 = W1(p, ci, z); t2 = W2(p, ci, z)
        det = (t1[j]**2 - t2[j]) / 2
        r = det / p
        rr.append(order_of(r))
    frozen = all(o is not None for o in rr) and len(set(rr))==1
    print("  %2d  %s  %s   %s%s" % (j, sector(j), sig(j), rr, "  <== FROZEN CLASS" if frozen else ""))
