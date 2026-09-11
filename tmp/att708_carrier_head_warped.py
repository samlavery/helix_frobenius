#!/usr/bin/env python3
"""att708 — CARRIER SCALING AND FIBER WARP AT THE SAME TIME (Sam).  Carrier scale enters the growth register through
   the compiled head law W(y) ≈ 9 e^{2y} (ledger 556, r = 3 gauge, pitch 1): at height t the carrier has absorbed
   x(t) = 9 t² sites, so the front is SLAVED to the height.  Fiber warp = Π_x (END carried, att707).  The two-ended
   multiplicative fiber at its own head is then ONE function of t:  G(t) := E^w_{x(t)}(½+it) + χ E^w_{x(t)}(½−it),
   real after rotation: u(t) = 2 Re(e^{iϑ} E^w_{x(t)}(½+it)), and its first-order domination is D_{R,x(t)}(t) ≥ 0.
   PRE-REGISTERED.  P1: D_{R,9t²}(t) > 0 for every t ∈ [10, 100] (RH holds there; 568 gives ≥ 0 at every x).
   P2: u(t) has exactly N(100) − N(10) = 29 sign changes on [10, 100], and their RMS displacement from the true
   zeros is < 0.1 mean spacing (the registry's stations with END at the carrier's own head; 566/601).
   Decision: any D ≤ 0 refutes P1; count ≠ 29 or RMS ≥ 0.1 spacing refutes P2."""
import numpy as np, mpmath as mp
mp.mp.dps = 20
out = open("tmp/att708_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def vonmangoldt_upto(x):
    N = int(x) + 1; lam = np.zeros(N); sieve = np.ones(N, dtype=bool); sieve[:2] = False
    for p in range(2, N):
        if sieve[p]:
            sieve[p*p::p] = False; q = p
            while q < N: lam[q] = np.log(p); q *= p
    return lam
T0, T1 = 10.0, 100.0
Xmax = int(9*T1**2) + 1
lam = vonmangoldt_upto(Xmax); n = np.arange(2, len(lam)); ln = np.log(n); lam = lam[2:]
keep = lam > 0; n, ln, lam = n[keep], ln[keep], lam[keep]
zeros = [float(mp.zetazero(k).imag) for k in range(1, 40)]
zeros = np.array([z for z in zeros if T0 < z < T1])
say(f"prime powers up to {Xmax}: {len(n)};  true zeros in ({T0},{T1}): {len(zeros)}")
ts = np.arange(T0, T1, 0.005)
thp = np.array([float(mp.diff(mp.siegeltheta, t)) for t in ts[::20]]); thp = np.interp(ts, ts[::20], thp)
th = np.array([float(mp.siegeltheta(t)) for t in ts[::20]]); th = np.interp(ts, ts[::20], th)
D = np.empty_like(ts); u = np.empty_like(ts); kap = np.empty_like(ts)
CH = 300
for i0 in range(0, len(ts), CH):
    t = ts[i0:i0+CH]; x = 9*t**2; L = np.log(x)
    w = np.clip(1 - np.outer(ln, 1/L), 0, None)                     # (n, t) Riesz weights at the carrier head
    phase = np.outer(ln, t)                                          # log n · t
    amp = (lam/np.sqrt(n))[:, None]
    clock = np.sum(w*amp*np.cos(phase), axis=0)                      # Σ w Λ n^{−½} cos(t log n)
    # log-face on the axis: L_x(½+it) = Σ w Λ/log n · n^{−½} e^{−it log n}
    Lx = np.sum(w*(lam/(ln*np.sqrt(n)))[:, None]*np.exp(-1j*phase), axis=0)
    # warp Π_x(s) at s = ½+it:  −Ei(L(1−s)) + (x^{1−s} − 1)/(L(1−s)),  1−s = ½ − it ; and END = Re K_R(½−it)/π
    Pi = np.empty(len(t), dtype=complex); KR = np.empty(len(t), dtype=complex)
    for j in range(len(t)):
        uu = mp.mpc(0.5, -t[j]); LL = mp.mpf(L[j])
        Pi[j] = complex(-mp.ei(LL*uu) + (mp.e**(LL*uu) - 1)/(LL*uu))
        KR[j] = complex((mp.e**(LL*uu) - 1)/(LL*uu**2))
    D[i0:i0+CH] = thp[i0:i0+CH]/np.pi + np.real(KR)/np.pi - clock/np.pi
    kap[i0:i0+CH] = -2*np.pi*D[i0:i0+CH]
    u[i0:i0+CH] = 2*np.real(np.exp(1j*th[i0:i0+CH])*np.exp(Lx + Pi))
say(f"P1: min D_{{R,9t²}}(t) on [{T0},{T1}] = {D.min():+.5f} at t={ts[np.argmin(D)]:.2f};  frac D≤0 = {np.mean(D<=0):.4f};  "
    f"pole shadow amplitude 3/(πt log 9t²) at t=10: {3/(np.pi*10*np.log(900)):.4f}, at t=100: {3/(np.pi*100*np.log(90000)):.5f}")
sc = np.where(np.sign(u[:-1])*np.sign(u[1:]) < 0)[0]
stations = ts[sc] - u[sc]*(ts[sc+1]-ts[sc])/(u[sc+1]-u[sc])
say(f"P2: sign changes of the warped two-ended fiber at its own head on [{T0},{T1}]: {len(stations)}  (true zeros: {len(zeros)})")
if len(stations) == len(zeros):
    d = stations - zeros; sp = np.mean(np.diff(zeros))
    say(f"    displacement station − zero: RMS {np.sqrt(np.mean(d**2)):.4f} (= {np.sqrt(np.mean(d**2))/sp:.4f} mean spacings), "
        f"max {np.max(np.abs(d)):.4f}; mean spacing {sp:.3f}")
    say("    first ten: " + ", ".join(f"{z:.3f}→{s:.3f}" for z, s in zip(zeros[:10], stations[:10])))
else:
    say("    stations: " + ", ".join(f"{s:.3f}" for s in stations[:40]))
    say("    zeros:    " + ", ".join(f"{z:.3f}" for z in zeros[:40]))
