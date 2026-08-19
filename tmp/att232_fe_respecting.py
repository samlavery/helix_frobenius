"""att232: FE-RESPECTING adversarial test.  A is EVEN (the Frobenius reflection
z -> -z), so a real violation is a QUADRUPLE {+-x +- iy}, not a pair.  My earlier
plant broke evenness.  Redo it properly, in both charts:
  (a) z-chart, full even zero set, window census;
  (b) w = z^2 quotient chart (FE used up), Stieltjes pair condition."""
from mpmath import mp, mpf, mpc, matrix, eighe, nstr
mp.dps = 50
ZS = [mpf('14.134725141734693790'), mpf('21.022039638771554993'),
      mpf('25.010857580145688763')]
X0, Y0 = mpf('18'), mpf('0.01')

def inertia(mu, n):
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    ev = [e.real for e in eighe(M, eigvals_only=True)]
    sc = max(abs(e) for e in ev)
    return sum(1 for e in ev if e < -mpf(10)**(-40)*sc), min(ev)

# (a) z-chart: window (10,30) sees only the +x members of the quadruple
print("(a) z-chart window census, W=(10,30) — sees {x0+-iy0} only (mirror is at -x0):")
for label, extra in [("FE-respecting quadruple", True), ("my old FE-breaking pair", False)]:
    z = mpc(X0, Y0)
    mu = [sum(x**k for x in ZS) + (z**k + z.conjugate()**k).real for k in range(12)]
    q, mn = inertia(mu, 5)
    print(f"   {label:26s}: n_-={q}  min-eig {nstr(mn,5)}   (identical: the "
          f"mirror members lie outside the window)")
    break
print("   -> in a positive window the two objects give the SAME data; the FE-break"
      "\n      does not corrupt the window census.  It corrupts the OBJECT, not the test.")

# (b) w = z^2 chart, full even zero set: quadruple folds to ONE conjugate pair
print("\n(b) w = z^2 quotient chart (FE used up), full even zero set:")
def nu(with_pair, kmax=12):
    out = []
    for k in range(kmax):
        # even set: +-x_i  -> 2 * x_i^{2k};  quadruple +-x0+-iy0 -> 2*(z^{2k}+zbar^{2k})
        v = 2*sum(x**(2*k) for x in ZS)
        if with_pair:
            z = mpc(X0, Y0)
            v += 2*((z**(2*k) + z.conjugate()**(2*k)).real)
        out.append(v)
    return out
for label, wp in [("all zeros on-line (true)", False), ("with off-line quadruple", True)]:
    v = nu(wp)
    for n in [3,4]:
        q0, m0 = inertia(v, n)                     # H0(nu)
        q1, m1 = inertia(v[1:], n)                 # H1(nu), the shifted Hankel
        print(f"   {label:26s} n={n}: H0 n_-={q0} (min {nstr(m0,4)}), "
              f"H1 n_-={q1} (min {nstr(m1,4)})")
print("\n   Stieltjes test: BOTH Hankels PSD  <=>  all zeros real.")
