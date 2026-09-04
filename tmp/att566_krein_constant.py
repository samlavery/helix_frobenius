#!/usr/bin/env python3
"""
att566 — THE KREIN CONSTANT OF THE FRONT (ledger 567).

Ledger 532 measured the finite-front marriage measure D'_Q on the line as SIGNED, with "bounded negative
mass ≈ 0.4–0.55 per window, Krein at every stage, Hilbert only in the limit" — unexplained.  The compiled
truncated formula (563–565) gives it a closed form.  On the line s₀ = ½ + it, an on-line zero enters the
comb through Re K(i u), u = γ − t, and the pole's real part vanishes there, so the density is
      D_T(t) = ϑ′(t)/π + END_T(t) − (1/π) Σ_n w_T(n) Λ(n) n^{−½} cos(t log n)  =  (1/π) Σ_γ Re K_T(i(γ − t))   [+ tiny]
with a kernel k_T(v) := Re K_T(i v/L)·(L/π) in the scaled variable v = L u, which is INDEPENDENT of the front:
  sharp cutoff  K = x^w / w                  : k(v) = sin v /(π v)                        Dirichlet   — negative mass ~ (2/π²) log V  (divergent)
  Selberg       K = (x^{2w} − x^w)/(w² L)    : k(v) = (2/π)(sin² v − sin²(v/2))/v²        difference of two Fejér kernels — negative mass 0.2179
  cubic         K = (x^{4w} − 3x^{3w} + 3x^{2w} − x^w)/(w⁴ L³) : k(v) = sin(5v/2) sinc³(v/2)/(π v) — negative mass 0.1850
Each has total mass 1.  The negative mass per zero is a pure number of the taper SHAPE, not of the front x
and not of arithmetic.  (Bochner: any taper equal to 1 up to a front x > 1 has a signed kernel, since a
characteristic function equal to 1 on an interval is identically 1.)

PRE-REGISTERED (windows = midpoints between consecutive zeros, the 13 zeros in (10, 60), as in 532):
  P1  Selberg: mean negative mass per window in [0.19, 0.25] at EVERY front x ∈ {10^2.5, 10^3, 10^3.5}, spread ≤ 0.05.
  P2  cubic:   in [0.16, 0.21] at x ∈ {10^1.75, 10^2} (primes to x⁴).
  P3  sharp:   per-window negative mass tracks (2/π²)·log(L·h) + c, h = window half-width — grows with x.
  P4  mean |count − 1| for Selberg ≤ that of the sharp cutoff at the same x (1/v² side lobes vs 1/v).
DECISION: P1 spread > 0.05 kills "front-independent"; P1 outside [0.19, 0.25] kills the closed form.
"""
import math, time, numpy as np, mpmath as mp
mp.mp.dps = 20

ZEROS = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513,
         32.935061587739190, 37.586178158825671, 40.918719012147495, 43.327073280914999,
         48.005150881167160, 49.773832477672302, 52.970321477714461, 56.446247697063395,
         59.347044002602353, 60.831778524609809]

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def prime_powers(N):
    """(n, Λ(n)) for prime powers n ≤ N."""
    ps = primes_upto(N); ns, lams = [], []
    for p in ps:
        lp = math.log(p); pk = p
        while pk <= N:
            ns.append(pk); lams.append(lp); pk *= p
    o = np.argsort(ns); return np.array(ns, float)[o], np.array(lams)[o]

def theta_prime_over_pi(z):
    lp = float(mp.log(mp.pi)); out = np.empty_like(z)
    for i, t in enumerate(z):
        out[i] = (0.5*float(mp.digamma(mp.mpc(0.25, t/2)).real) - 0.5*lp)/math.pi
    return out

def bank(z, ns, lams, w):
    """(1/π) Σ_n w(n) Λ(n) n^{−½} cos(z log n), chunked."""
    acc = np.zeros_like(z); coef = w*lams/np.sqrt(ns); ln = np.log(ns)
    for a in range(0, len(ns), 4000):
        acc += np.cos(np.outer(z, ln[a:a+4000])) @ coef[a:a+4000]
    return acc/math.pi

def weights(kind, L, ln):
    v = ln
    if kind == "sharp":   return (v <= L).astype(float)
    if kind == "selberg": return np.clip((2*L - v)/L, 0.0, 1.0)*(v <= 2*L) + 0.0*(v <= L)  # =1 for v<=L, (2L−v)/L on [L,2L]
    if kind == "cubic":
        r = lambda c: np.maximum(c - v, 0.0)**3
        return (r(4*L) - 3*r(3*L) + 3*r(2*L) - r(L))/(6*L**3)

def end_term(kind, L, z):
    w = 0.5 - 1j*z; x = math.exp(L)
    if kind == "sharp":   K = x**w / w
    if kind == "selberg": K = (x**(2*w) - x**w)/(w**2*L)
    if kind == "cubic":   K = (x**(4*w) - 3*x**(3*w) + 3*x**(2*w) - x**w)/(w**4*L**3)
    return np.real(K)/math.pi

def kernel_negmass(kind, V):
    v = np.linspace(-V, V, 400001); v[v == 0] = 1e-9
    if kind == "sharp":   k = np.sin(v)/(np.pi*v)
    if kind == "selberg": k = (2/np.pi)*(np.sin(v)**2 - np.sin(v/2)**2)/v**2
    if kind == "cubic":   k = np.sin(2.5*v)*(np.sin(v/2)/(v/2))**3/(np.pi*v)
    dv = v[1] - v[0]; return -np.sum(k[k < 0])*dv, np.sum(k)*dv

def windows():
    mids = [(ZEROS[i] + ZEROS[i+1])/2 for i in range(len(ZEROS) - 1)]
    W = [(10.0, mids[0], ZEROS[0])] + [(mids[k-1], mids[k], ZEROS[k]) for k in range(1, 13)]
    return W

def run(kind, L, z, thp, dz):
    x = math.exp(L); N = {"sharp": x, "selberg": x**2, "cubic": x**4}[kind]
    ns, lams = prime_powers(int(N) + 1)
    w = weights(kind, L, np.log(ns))
    D = thp + end_term(kind, L, z) - bank(z, ns, lams, w)
    rows = []
    for a, b, g in windows():
        sel = (z >= a) & (z < b)
        cnt = np.sum(D[sel])*dz; neg = np.sum(np.maximum(-D[sel], 0))*dz
        peak = z[sel][np.argmax(D[sel])]; h = (b - a)/2
        pred, _ = kernel_negmass(kind, L*h)      # predicted per-window negative mass from the kernel alone
        rows.append((a, b, g, cnt, peak - g, neg, pred))
    return rows

def main():
    dz = 0.01; z = np.arange(5.0, 65.0 + dz/2, dz)
    t0 = time.time(); thp = theta_prime_over_pi(z); print("theta'/pi on %d points: %.0fs" % (len(z), time.time() - t0))
    print("kernel negative masses on |v| ≤ 400: " + ", ".join("%s %.4f (total %.4f)" % (k, *kernel_negmass(k, 400)) for k in ("selberg", "cubic")))
    print("sharp (Dirichlet) on |v| ≤ V: " + ", ".join("V=%d: %.3f" % (V, kernel_negmass("sharp", V)[0]) for V in (5, 10, 20, 40)))
    plan = [("sharp", math.log(10**2.5)), ("sharp", math.log(1e3)), ("sharp", math.log(10**3.5)),
            ("selberg", math.log(10**2.5)), ("selberg", math.log(1e3)), ("selberg", math.log(10**3.5)),
            ("cubic", math.log(10**1.75)), ("cubic", math.log(1e2))]
    summary = []
    for kind, L in plan:
        t0 = time.time(); rows = run(kind, L, z, thp, dz)
        negs = [r[5] for r in rows]; preds = [r[6] for r in rows]; errs = [abs(r[3] - 1) for r in rows]; disp = [abs(r[4]) for r in rows]
        print("=" * 96)
        print("%-8s x = e^L = %.1f (L = %.3f), resolution 2π/L = %.2f   [%.0fs]" % (kind, math.exp(L), L, 2*math.pi/L, time.time() - t0))
        print("   window            zero      count    peak−zero   neg.mass   kernel-predicted neg.mass (window-truncated)")
        for a, b, g, cnt, d, neg, pred in rows:
            print("   [%6.2f,%6.2f]  %8.4f  %+8.4f  %+9.4f  %8.4f   %8.4f" % (a, b, g, cnt, d, neg, pred))
        print("   mean|count−1| = %.4f  max = %.4f ;  mean|peak−zero| = %.4f ;  MEAN NEGATIVE MASS = %.4f  (kernel prediction %.4f)"
              % (np.mean(errs), np.max(errs), np.mean(disp), np.mean(negs), np.mean(preds)))
        summary.append((kind, math.exp(L), np.mean(negs), np.mean(preds), np.mean(errs)))
    print("=" * 96); print("SUMMARY   taper      x        mean neg.mass   kernel pred   mean|count−1|")
    for kind, x, nm, pr, er in summary:
        print("          %-8s %8.1f   %8.4f       %8.4f     %8.4f" % (kind, x, nm, pr, er))

if __name__ == "__main__":
    main()
