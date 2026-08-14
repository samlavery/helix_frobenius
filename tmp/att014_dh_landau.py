"""ATTEMPT 014, secondary #2 -- the SAME dichotomy, tested on the standing off-line control.

Attempt 011 measured DH's tape lines against Lambda_f(n) (the Dirichlet coefficients of -f'/f)
and found them ABSENT at composite n (obs/pred 0.043, 0.001, 0.004, 0.072).  Attempt 011 used
only DH's ON-LINE zeros (sign changes of Z_DH) and the UNWEIGHTED sum.  Attempt 014's zeta'
measurement says the law needs the x^{beta} weight and a COMPLETE 2D census.  So:

  A_w(x) = sum_{rho: T<gamma<T+W} x^{rho - 1/2}      [weighted, complete 2D census]
  A_u(x) = sum_{rho}            x^{i gamma}          [unweighted -- what 011 measured]
  Landau/residue prediction (degree-independent, the W/2pi is the contour length):
      A_w(x) = -(W/2pi) Lambda_f(x) / sqrt(x)

HYPOTHESIS: A_w matches, A_u does not.  That would give attempt 011's negative a cause.
NULL: A_w fails too (then the residue transport is not what is going on and 014's zeta'
      result does not generalize), or A_u matches equally well (then the weight is irrelevant).
"""
import numpy as np, math, sys, time
from att014_dh_winding import dh, winding, XI

def P(*a): print(*a); sys.stdout.flush()
TWOPI = 2*math.pi

def lambda_f(N=64):
    c = np.zeros(N+1); base = [1.0, XI, -XI, -1.0, 0.0]
    for n in range(1, N+1): c[n] = base[(n-1) % 5]
    L = np.zeros(N+1)
    for n in range(2, N+1):
        s = c[n]*math.log(n)
        for d in range(1, n):
            if n % d == 0: s -= L[d]*c[n//d]
        L[n] = s
    return L

def newton_f(seeds, tlo, thi, iters=60, cap=0.5):
    s = np.array(seeds, complex); alive = np.ones(s.shape, bool)
    for _ in range(iters):
        idx = np.nonzero(alive)[0]
        if idx.size == 0: break
        v, vp = dh(s[idx])
        st = np.where(np.abs(vp) > 0, v/np.where(vp == 0, 1, vp), 0.0)
        a = np.abs(st); st = np.where(a > cap, st*(cap/np.maximum(a, 1e-300)), st)
        ns = s[idx] - st
        bad = (ns.real < -2.0) | (ns.real > 3.0) | (ns.imag < tlo-20) | (ns.imag > thi+20)
        s[idx] = np.where(bad, s[idx], ns); alive[idx[bad]] = False
    v, vp = dh(s)
    ok = alive & (np.abs(v)/np.maximum(np.abs(vp), 1e-30) < 1e-9)
    return s[ok]

def dedupe(s, tol=1e-6):
    o = np.argsort(s.imag); s = s[o]; keep = []
    for z in s:
        if keep and any(abs(z-w) < tol for w in keep[-12:]): continue
        keep.append(z)
    return np.array(keep)

if __name__ == "__main__":
    P(__doc__)
    T0, T1 = 200.0, 500.0; W = T1-T0
    SL, SH = -1.2, 2.2
    w, mx, mn = winding(dh, 0, SL, SH, T0, T1, dt=0.02, dsig=0.002)
    w2, _, _ = winding(dh, 0, SL, SH, T0, T1, dt=0.01, dsig=0.001)
    P(f"CENSUS certificate: winding of f on sigma({SL},{SH}) x t({T0},{T1}) = {w:.3f} "
      f"(dt halved: {w2:.3f})  max step {mx:.2f} rad  min|f| {mn:.2e}")
    sg = np.arange(SL+0.02, SH, 0.07); tg = np.arange(T0, T1, 0.30)
    S, TT = np.meshgrid(sg, tg)
    seeds = np.concatenate([(S+1j*TT).ravel(), 0.5+1j*np.arange(T0, T1, 0.15)])
    t_ = time.time()
    r = dedupe(newton_f(seeds, T0, T1)); r = r[(r.imag >= T0) & (r.imag <= T1)]
    P(f"Newton: {len(seeds)} seeds -> {len(r)} distinct DH zeros in the window ({time.time()-t_:.0f}s)")
    b = r.real - 0.5
    off = np.abs(b) > 1e-6
    P(f"  on-line |beta-1/2|<1e-6: {int((~off).sum())}    off-line: {int(off.sum())}   "
      f"max |beta-1/2| = {np.abs(b).max():.4f}")
    P(f"  off-line beta values: " + " ".join(f"{v:.4f}" for v in np.sort(r.real[off])[:20]))
    LF = lambda_f(64)
    P("")
    P(f"  {'x':>4}{'Lambda_f':>11}{'|pred|':>10} | {'|A_w|':>10}{'w o/p':>8} | {'|A_u|':>10}{'u o/p':>8}")
    rw, ru = [], []
    for x in (2,3,4,5,7,6,8,9,11,13,14,16,21,26,27,29,31):
        if abs(LF[x]) < 1e-9: continue
        lx = math.log(x)
        Aw = np.abs(np.sum(np.exp((r-0.5)*lx)))
        Au = np.abs(np.sum(np.exp(1j*r.imag*lx)))
        pred = W/TWOPI*abs(LF[x])/math.sqrt(x)
        rw.append(Aw/pred); ru.append(Au/pred)
        kind = "PP" if all(x % p or x == p**int(round(math.log(x)/math.log(p))) for p in (2,3,5,7,11,13)) else ""
        P(f"  {x:>4}{LF[x]:>11.4f}{pred:>10.3f} | {Aw:>10.3f}{Aw/pred:>8.3f} | {Au:>10.3f}{Au/pred:>8.3f}")
    rw = np.array(rw); ru = np.array(ru)
    P(f"  -> WEIGHTED   median obs/pred = {np.median(rw):.3f}   IQR {np.percentile(rw,25):.3f}-{np.percentile(rw,75):.3f}")
    P(f"  -> UNWEIGHTED median obs/pred = {np.median(ru):.3f}   IQR {np.percentile(ru,25):.3f}-{np.percentile(ru,75):.3f}")
    rng = np.random.default_rng(3)
    ctrl = [np.abs(np.sum(np.exp((r-0.5)*l))) / (W/TWOPI/math.sqrt(math.exp(l)))
            for l in rng.uniform(0.7, 3.5, 60)]
    P(f"  control: 60 off-lattice log x -- |A_w| / [(W/2pi)/sqrt(x)] median {np.median(ctrl):.3f}, "
      f"90pct {np.percentile(ctrl,90):.3f}  (Lambda_f = 0 there, so this is the floor)")
