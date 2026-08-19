"""att233: w=z^2 chart AT/ABOVE threshold (m = 3 real + 1 pair = 5), and the
amplification: w = (x0+iy0)^2 has Im w = 2*x0*y0 — the FE quotient multiplies
the off-line depth by the HEIGHT."""
from mpmath import mp, mpf, mpc, matrix, eighe, nstr
mp.dps = 60
ZS = [mpf('14.134725141734693790'), mpf('21.022039638771554993'),
      mpf('25.010857580145688763')]

def inertia(mu, n):
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    ev = [e.real for e in eighe(M, eigvals_only=True)]
    sc = max(abs(e) for e in ev)
    return sum(1 for e in ev if e < -mpf(10)**(-45)*sc), min(ev)

def nu(x0, y0, with_pair, kmax=16):
    out = []
    for k in range(kmax):
        v = 2*sum(x**(2*k) for x in ZS)
        if with_pair:
            z = mpc(mpf(x0), mpf(y0))
            v += 2*((z**(2*k) + z.conjugate()**(2*k)).real)
        out.append(v)
    return out

print("w = z^2 chart, at/above threshold m = 5:")
for label, wp in [("TRUE (all on-line)", False), ("off-line quadruple 18+-0.01i", True)]:
    v = nu('18','0.01',wp)
    for n in [5,6]:
        q0,m0 = inertia(v,n); q1,m1 = inertia(v[1:],n)
        print(f"  {label:30s} n={n}: H0 n_-={q0} min {nstr(m0,4):>12} | "
              f"H1 n_-={q1} min {nstr(m1,4):>12}")

print("\nAMPLIFICATION: Im w = 2*x0*y0 — depth multiplied by the height")
for x0 in ['18','100','1000']:
    z = mpc(mpf(x0), mpf('0.01'))
    w = z**2
    print(f"  x0={x0:>5}, y0=0.01 -> w = {nstr(w.real,8)} + {nstr(w.imag,5)}i   "
          f"(depth x{nstr(w.imag/mpf('0.01'),4)})")

print("\nsignal in the w-chart vs the z-chart at the same physical violation:")
for x0 in ['18','30']:
    vz = [sum(x**k for x in ZS) + (mpc(mpf(x0),mpf('0.01'))**k
          + mpc(mpf(x0),mpf('0.01')).conjugate()**k).real for k in range(12)]
    qz, mz = inertia(vz,5)
    vw = nu(x0,'0.01',True)
    qw, mw = inertia(vw,5)
    scz = max(abs(e) for e in [mz]); 
    print(f"  x0={x0}: z-chart min-eig {nstr(mz,5):>13} (n_-={qz})   "
          f"w-chart min-eig {nstr(mw,5):>13} (n_-={qw})")
