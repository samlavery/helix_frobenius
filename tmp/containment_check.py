#!/usr/bin/env python3
"""First direct test of the zero-containment target at rung 5.

Containment: Z(Lambda(Sym3 Delta)) <= Z(Lambda(Delta x Sym4 Delta)).
Method: completed functions via the reflection-split incomplete Mellin,
  Lambda(s) = sum_n lam(n) [ F(s,n) + eps * F(1-s,n) ],
  F(s,n) = n^{-s} * Phi(s, n),  Phi(s,a) = int_a^inf K(u) u^{s-1} du,
with the phase-1 floor-verified kernels and measured signs
(eps3 = -1 so Lambda3 is purely imaginary on the line; pair eps = +1 so
Lambda_pair is real there).  Locate sign changes of Im Lambda3(1/2+it),
bisect, then evaluate Lambda_pair at each zero: containment predicts
vanishing relative to the local scale.  Vectorized: kernels tabulated once,
Phi(s, n) for all n by suffix sums on a dense grid.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import mpmath as mp
from adapter_sym_probe import tau_coeffs, sym_coeffs, gammaR_params, kernel_factory

mp.mp.dps = 25

def tab(lams, umin, umax, pts):
    K = kernel_factory(lams)
    us = np.exp(np.linspace(np.log(umin), np.log(umax), pts))
    vals = np.array([float(v) if (v := K(mp.mpf(float(u)))) != 0 else 0.0 for u in us])
    return us, vals

class Completed:
    """Lambda(s) = sum lam(n) [ n^-s Phi(s,n) + eps (1-s)-term ]."""
    def __init__(self, lams, lam, N, eps, pts=2600):
        self.lam = np.array(lam[1:N+1])
        self.n = np.arange(1, N + 1)
        self.eps = eps
        umax_needed = 4.0 * ((mp.mp.dps + 12) * mp.log(10) / (len(lams) * mp.pi)) ** (len(lams) / 2.0)
        self.us, self.Kv = tab(lams, 0.5, float(umax_needed) * 1.5, pts)
        self.du = np.diff(self.us)
        self.mid = 0.5 * (self.us[1:] + self.us[:-1])
        self.Kmid = 0.5 * (self.Kv[1:] + self.Kv[:-1])
    def Phi_all(self, s):
        # Phi(s, a) for a = each n: suffix sums of K(u) u^{s-1} du from n up
        w = self.Kmid * self.mid ** (s - 1) * self.du
        suf = np.concatenate([np.cumsum(w[::-1])[::-1], [0.0]])
        # index of first grid point >= n
        idx = np.searchsorted(self.us, self.n)
        idx = np.clip(idx, 0, len(suf) - 1)
        return suf[idx]
    def value(self, s):
        t1 = np.sum(self.lam * self.n ** (-s) * self.Phi_all(s))
        t2 = np.sum(self.lam * self.n ** (-(1 - s)) * self.Phi_all(1 - s))
        return t1 + self.eps * t2

def dirichlet_conv(a, b, N):
    c = [0.0] * (N + 1)
    for i in range(1, N + 1):
        if a[i] == 0:
            continue
        for j in range(1, N // i + 1):
            c[i * j] += float(a[i]) * float(b[j])
    return c

def main(T0=12.0, dt=0.1, nzeros=4):
    N3, Np = 80, 220
    tau = tau_coeffs(max(N3, Np))
    lam3 = [float(x) for x in sym_coeffs(3, Np, tau)]
    lam5 = [float(x) for x in sym_coeffs(5, Np, tau)]
    cpair = dirichlet_conv(lam5, lam3, Np)
    L3 = Completed(gammaR_params(3), lam3, N3, -1.0)
    Lp = Completed(gammaR_params(5) + gammaR_params(3), cpair, Np, +1.0)
    # normalization checks on the line
    s0 = 0.5 + 1.3j
    v3, vp = L3.value(s0), Lp.value(s0)
    print(f"# checks at t=1.3: |Re L3|/|L3| = {abs(v3.real)/abs(v3):.2e} (want ~0), "
          f"|Im Lp|/|Lp| = {abs(vp.imag)/abs(vp):.2e} (want ~0)")
    f3 = lambda t: L3.value(0.5 + 1j * t).imag
    ts = np.arange(0.4, T0, dt)
    vals = np.array([f3(t) for t in ts])
    roots = []
    for i in range(len(ts) - 1):
        if vals[i] * vals[i + 1] < 0:
            a, b = ts[i], ts[i + 1]
            for _ in range(50):
                m = 0.5 * (a + b)
                if f3(a) * f3(m) <= 0:
                    b = m
                else:
                    a = m
            roots.append(0.5 * (a + b))
            if len(roots) >= nzeros:
                break
    print(f"# first zeros of Lambda(Sym3): {[f'{r:.6f}' for r in roots]}")
    # containment test: |Lambda_pair| at each zero vs local scale
    for r in roots:
        vz = Lp.value(0.5 + 1j * r)
        loc = max(abs(Lp.value(0.5 + 1j * (r + d))) for d in (-0.5, -0.25, 0.25, 0.5))
        print(f"# t={r:.6f}: |L_pair(rho)| = {abs(vz):.3e}   local scale = {loc:.3e}   "
              f"ratio = {abs(vz)/loc:.3e}")
    # control: pair at a non-zero point of Sym3
    tc = 0.5 * (roots[0] + roots[1]) if len(roots) > 1 else roots[0] + 0.7
    vc = Lp.value(0.5 + 1j * tc)
    print(f"# control t={tc:.4f} (not a Sym3 zero): |L_pair| = {abs(vc):.3e}")

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'diag':
        pass
    else:
        main()

def diagnose():
    N3, N5, Np = 80, 220, 220
    tau = tau_coeffs(Np)
    lam3 = [float(x) for x in sym_coeffs(3, Np, tau)]
    lam5 = [float(x) for x in sym_coeffs(5, Np, tau)]
    cpair = dirichlet_conv(lam5, lam3, Np)
    L3 = Completed(gammaR_params(3), lam3, N3, -1.0)
    L5 = Completed(gammaR_params(5), lam5, N5, -1.0)
    Lp = Completed(gammaR_params(5) + gammaR_params(3), cpair, Np, +1.0)
    print("# product-identity residual |Lp - L5*L3|/max(|Lp|,|L5*L3|):")
    for t in (1.3, 2.5, 4.0, 4.155858, 5.549114, 8.112023):
        s = 0.5 + 1j * t
        a, b = Lp.value(s), L5.value(s) * L3.value(s)
        den = max(abs(a), abs(b), 1e-30)
        print(f"#   t={t:.6f}: |Lp|={abs(a):.3e} |L5*L3|={abs(b):.3e} rel-resid={abs(a-b)/den:.3e}")
    # N-sensitivity of Lp at the first zero
    for Ntest in (120, 170, 220):
        Lpt = Completed(gammaR_params(5) + gammaR_params(3), cpair, Ntest, +1.0)
        print(f"#   N={Ntest}: |Lp(rho1)| = {abs(Lpt.value(0.5 + 4.155858j)):.4e}")

if len(sys.argv) > 1 and sys.argv[1] == 'diag':
    diagnose()
