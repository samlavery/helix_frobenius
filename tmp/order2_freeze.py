"""
Order 2 (B) decisive: a non-self-dual Hodge/Tate FREEZE, scalar-blind.  Standard-rules enforced.

Curve y^7 = f(x), f CUBIC -> genus 6, each C_7-eigenspace V_j (j=1..6) is DIM 2 (even).
HARMONIC: the g-th (top) exterior ^2 V_j = det(Frob|V_j) (weight 2), NOT the 2nd moment.
ETA: freeze r_j = det(Frob|V_j)/p  (|det|=p, so |r_j|=1); root of unity <=> Hodge/Tate class.
ROOTS: genus 6, dim-2 eigenspaces; distinct roots mod p; p = 1 mod 7; bad primes skipped.
EXTRA RAILS: all six V_j; V_{-j} = dual = conjugate of V_j (checked).
det(Frob|V_j) = (t1^2 - t2)/2,  t1 = W^(j)(1) = sum_{F_p} chi_7^j(f),
                                 t2 = W^(j)(2) = sum_{F_p^2} chi_7^j(Norm f).
Generic-vs-special contrast catches a trivial-determinant freeze (false positive):
if EVERY curve freezes at r_j, it's the determinant character (not a class); a class shows as a
freeze that SPECIAL curves have and generic ones don't.
"""
import cmath, math

def primes_1mod7(lo, hi):
    return [p for p in range(lo, hi) if p % 7 == 1 and all(p % q for q in range(2, int(p**0.5)+1))]

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

def chi7_of(p):
    """return function a(int in F_p) -> index t in 0..6 with chi_7(a)=zeta_7^t (a!=0)."""
    g = prim_root(p); e = (p-1)//7; ge = pow(g, e, p)
    idx = {}; cur = 1
    for t in range(7):
        idx[cur] = t; cur = (cur*ge) % p
    return lambda a: idx[pow(a, e, p)] if a % p else None    # None for a=0

def nonresidue(p):
    for c in range(2, p):
        if pow(c, (p-1)//2, p) == p-1: return c

def W1(p, fco, chi_t, z7):
    acc = [0j]*7
    for x in range(p):
        v = 0
        for c in fco: v = (v*x + c) % p
        t = chi_t(v)
        if t is not None:
            for j in range(1, 7): acc[j] += z7[(j*t) % 7]
    return acc

def W2(p, fco, chi_t, z7):
    """sum over F_{p^2}=F_p[u]/(u^2-c) of chi_7^j(Norm(f(x))), Norm(a+bu)=a^2-c b^2."""
    c = nonresidue(p)
    acc = [0j]*7
    for a in range(p):
        for b in range(p):
            # f(a+bu) in F_{p^2}: Horner with u^2=c
            r0, r1 = 0, 0                       # r0 + r1 u
            for co in fco:
                # multiply (r0+r1 u) by (a+b u): = (r0 a + r1 b c) + (r0 b + r1 a) u
                r0, r1 = (r0*a + r1*b*c) % p, (r0*b + r1*a) % p
                r0 = (r0 + co) % p              # add constant co
            nm = (r0*r0 - c*r1*r1) % p          # Norm to F_p
            t = chi_t(nm)
            if t is not None:
                for j in range(1, 7): acc[j] += z7[(j*t) % 7]
    return acc

def poly_from_roots(rts):
    co = [1]
    for r in rts:
        nw = [0]*(len(co)+1)
        for i, a in enumerate(co): nw[i] += a; nw[i+1] += -r*a
        co = nw
    return co

def order_of(z):
    for o in (1, 2, 3, 6, 7, 14, 21):
        if abs(z**o - 1) < 3e-2: return o
    return None

z7 = [cmath.exp(2j*math.pi*k/7) for k in range(7)]
FAMS = [
    ("generic  f=x^3+x+1", [1,0,1,1]),
    ("generic  f=x(x-1)(x-3)", poly_from_roots([0,1,3])),
    ("special  f=x^3-1  (mu_3 sym)", [1,0,0,-1]),
    ("special  f=x^3    (Fermat/CM)", [1,0,0,0]),
]
P = primes_1mod7(29, 130)
print("== Order 2(B): non-self-dual freeze  r_j = det(Frob|V_j)/p  on y^7=f (dim-2 eigenspaces) ==")
print("primes p=1 mod7:", P)
for name, fco in FAMS:
    print("\n-- %s --" % name)
    print("  p    r_1=det V1/p        ord  | dual|r_1-conj r_6|  | all-j orders")
    froze = []
    for p in P:
        chi_t = chi7_of(p); z = z7
        t1 = W1(p, fco, chi_t, z); t2 = W2(p, fco, chi_t, z)
        det = [((t1[j]**2 - t2[j]) / 2) for j in range(7)]     # det(Frob|V_j), j=1..6
        r = [det[j] / p if j >= 1 else 0 for j in range(7)]
        orders = [order_of(r[j]) for j in range(1, 7)]
        dualdev = abs(r[1] - r[6].conjugate())                 # V_6 = V_{-1} dual = conj
        print("  %3d   %+.4f%+.4fi   %-4s |   %8.1e         | %s"
              % (p, r[1].real, r[1].imag, str(orders[0]), dualdev, orders))
        froze.append(all(o is not None for o in orders))
    print("  freeze on ALL 6 rails, ALL primes: %s   (%d/%d primes)"
          % (all(froze), sum(froze), len(froze)))
