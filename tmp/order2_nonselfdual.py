"""
Order 2 (B), first slice: a NON-CM, NON-SELF-DUAL geometric piece the scalar 1D can't carry.

Curve  y^7 = f(x)  (superelliptic, C_7 acts by y -> zeta_7 y).  H^1 splits into 6 eigenspaces
V_1..V_6 under C_7; V_j dual = V_{-j} (NON-self-dual as Galois reps), tr(Frob|V_j) = -W^{(j)}
where W^{(j)}(p) = sum_x chi_7^j(f(x))  (complex).  The curve's SCALAR trace
a_p = -sum_j W^{(j)} is a real INTEGER -- provably blind to Im(W^{(j)}).  The multi-rail
zeta_7 clock reads each complex W^{(j)}.

Tests (this slice):
 (1) NON-SELF-DUAL: Im(W^{(j)}) != 0 and W^{(-j)} = conj(W^{(j)}) (dual = conjugate eigenspace).
 (2) SCALAR-BLIND: a_p = -sum_j W^{(j)} is real; two eigenspace configs with the same a_p differ
     in Im -- the scalar cannot separate them (the F21 collapse, now geometric).
 (3) NON-CM: the per-eigenspace trace spreads across primes and is NOT a fixed Jacobi/CM pattern
     (contrast a genuinely CM/Fermat f, y^7 = x, whose W^{(j)} ARE Jacobi sums).
"""
import cmath, math

def primes_1mod7(lo, hi):
    return [p for p in range(lo, hi) if p % 7 == 1 and all(p % q for q in range(2, int(p**0.5)+1))]

def prim_root(p):
    m, fac, d = p - 1, [], 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g

def chi7_tables(p):
    """chi_7^j table for j=0..6 (j=0 trivial). chi_7(prim_root)=zeta_7."""
    g = prim_root(p); e = (p-1)//7
    z7 = [cmath.exp(2j*math.pi*k/7) for k in range(7)]
    # discrete log base g, then chi_7^j(a) = z7[(j*dlog(a)) mod 7 ... ] -- but only need order-7 part
    # a^{(p-1)/7} = g^{e*dlog} = (g^e)^{dlog}; g^e has order 7. index = which power of g^e.
    ge = pow(g, e, p)
    powge = {}
    cur = 1
    for t in range(7):
        powge[cur] = t
        cur = (cur*ge) % p
    tabs = [[0j]*p for _ in range(7)]
    for a in range(1, p):
        t = powge[pow(a, e, p)]                 # a^{(p-1)/7} = (g^e)^t
        for j in range(7):
            tabs[j][a] = z7[(j*t) % 7]
    return tabs

def Wj(p, fco, tabs):
    """W^{(j)}(p) = sum_x chi_7^j(f(x)) for j=1..6 (f(x)=0 contributes 0)."""
    acc = [0j]*7
    for x in range(p):
        v = 0
        for c in fco: v = (v*x + c) % p
        for j in range(1, 7):
            acc[j] += tabs[j][v]
    return acc

def poly(roots_or_coeffs, from_roots=True):
    if not from_roots: return roots_or_coeffs
    co = [1]
    for r in roots_or_coeffs:
        nw = [0]*(len(co)+1)
        for i, a in enumerate(co):
            nw[i] += a; nw[i+1] += -r*a
        co = nw
    return co

FAMILIES = [
    ("NON-CM  f=x^4+x+1", [1, 0, 0, 1, 1]),                 # irreducible quartic, generic
    ("NON-CM  f=x(x-1)(x-3)(x-7)", poly([0,1,3,7])),         # non-symmetric roots
    ("CM ctrl f=x  (Fermat, Jacobi sums)", [1, 0]),          # y^7=x : eigenspace traces ARE Jacobi sums
]
P = primes_1mod7(29, 260)
print("== Order 2 (B) first slice: y^7 = f(x), C_7-eigenspace traces W^(j) ==")
print("primes p=1 mod 7:", P)
for name, fco in FAMILIES:
    print("\n-- %s --" % name)
    print("  p    a_p(scalar,real)   |Im W^(1)|  dual-check |W^(-j)-conj W^(j)|   |W^(1)|/sqrt(p)")
    spread = []
    for p in P[:8]:
        tabs = chi7_tables(p)
        W = Wj(p, fco, tabs)
        ap = -sum(W[j] for j in range(1, 7))          # curve H^1 trace = real integer
        dualdev = max(abs(W[7-j] - W[j].conjugate()) for j in range(1, 7))
        print("  %3d   %+8.3f%+8.3fi   %8.3f    %10.2e            %.3f"
              % (p, ap.real, ap.imag, abs(W[1].imag), dualdev, abs(W[1])/math.sqrt(p)))
        spread.append(round(W[1].real, 2))
    print("  distinct Re W^(1) across primes: %d/8  (CM => locked few values; non-CM => spread)"
          % len(set(spread)))
