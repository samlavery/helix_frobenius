# att649 — does the RIGID co-monotone bank Z_N(t) = 2 Σ_{n≤N} n^{-1/2} cos(ϑ(t) − t log n), fixed N, have non-real zeros?
# ϑ continued analytically: ϑ(t) = (logΓ(1/4+it/2) − logΓ(1/4−it/2))/(2i) − (t/2) log π.
# PRE-REGISTERED: my 648 claim says non-real zeros exist for N ≥ 3 in a generic range; if a systematic
# Newton search from seeds (real zero ± i·{0.15,0.4,0.8}) over t ∈ [20, 80] finds NONE for N = 3..12 while
# finding them for a scrambled-phase control, the claim is refuted and the rigid bank's real-rootedness is live.
from mpmath import mp, mpf, mpc, loggamma, log, pi, cos, findroot, fabs, siegeltheta, sqrt
import numpy as np
mp.dps = 25
def theta(t): return (loggamma(mpf(1)/4 + 1j*t/2) - loggamma(mpf(1)/4 - 1j*t/2))/(2j) - t*log(pi)/2
print("theta continuation check at t=30: analytic %s  siegeltheta %s" % (theta(mpf(30)), siegeltheta(30)))
def ZN(t, N, phases=None):
    th = theta(t)
    return 2*sum(mpf(n)**(-mpf(1)/2) * cos(th - t*log(n) + (phases[n-1] if phases is not None else 0)) for n in range(1, N+1))
def real_zeros(N, a, b, phases=None, step=0.05):
    zs = []; ts = np.arange(a, b, step); prev = ZN(mpf(ts[0]), N, phases).real
    for t in ts[1:]:
        cur = ZN(mpf(t), N, phases).real
        if prev*cur < 0:
            try: zs.append(findroot(lambda x: ZN(x, N, phases), mpf(t - step/2)).real)
            except Exception: pass
        prev = cur
    return zs
def complex_zero_search(N, a, b, phases=None):
    found = []
    rz = real_zeros(N, a, b, phases)
    seeds = []
    for z in rz:
        for y in (0.15, 0.4, 0.8): seeds.append(mpc(z, y))
    for gap in zip(rz[:-1], rz[1:]):            # also mid-gap seeds
        m = (gap[0]+gap[1])/2
        for y in (0.15, 0.4, 0.8): seeds.append(mpc(m, y))
    for s in seeds:
        try:
            r = findroot(lambda x: ZN(x, N, phases), s, tol=1e-18, maxsteps=60)
            if fabs(ZN(r, N, phases)) < 1e-12 and fabs(r.imag) > 1e-6 and a - 2 < r.real < b + 2:
                if not any(fabs(r - f) < 1e-6 for f in found): found.append(r)
        except Exception: pass
    return rz, found
print("rigid bank Z_N on t ∈ [20, 80]:")
for N in (3, 4, 6, 8, 12):
    rz, cz = complex_zero_search(N, 20, 80)
    print("   N=%2d: real zeros found %3d ; non-real zeros found %d %s" % (N, len(rz), len(cz), [("%.3f%+.3fi" % (float(c.real), float(c.imag))) for c in cz[:4]]))
print("scrambled-phase control (same amplitudes, random phase offsets added to each clock):")
rng = np.random.default_rng(20260907)
for N in (4, 8):
    ph = [mpf(x) for x in rng.uniform(0, 2*np.pi, N)]
    rz, cz = complex_zero_search(N, 20, 80, phases=ph)
    print("   N=%2d: real zeros found %3d ; non-real zeros found %d %s" % (N, len(rz), len(cz), [("%.3f%+.3fi" % (float(c.real), float(c.imag))) for c in cz[:4]]))
print("UNDER-COMPLETE regime (N ≤ N_t = sqrt(t/2π) throughout the range): all clocks turn forward")
for N, a, b in ((3, 60, 300), (5, 160, 400), (8, 410, 800), (12, 910, 1300)):
    rz, cz = complex_zero_search(N, a, b)
    print("   N=%2d on [%d,%d] (N_t from %.2f to %.2f): real zeros %3d ; non-real zeros %d %s" % (N, a, b, sqrt(mpf(a)/(2*pi)), sqrt(mpf(b)/(2*pi)), len(rz), len(cz), [("%.3f%+.3fi" % (float(c.real), float(c.imag))) for c in cz[:4]]))
print("OVER-COMPLETE control at the same N (N > N_t): N=5 on [20,150], N=8 on [100,380]")
for N, a, b in ((5, 20, 150), (8, 100, 380)):
    rz, cz = complex_zero_search(N, a, b)
    print("   N=%2d on [%d,%d] (N_t from %.2f to %.2f): real zeros %3d ; non-real zeros %d %s" % (N, a, b, sqrt(mpf(a)/(2*pi)), sqrt(mpf(b)/(2*pi)), len(rz), len(cz), [("%.3f%+.3fi" % (float(c.real), float(c.imag))) for c in cz[:6]]))
