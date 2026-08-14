"""ATTEMPT 014, stage 1 -- locate the zeros of zeta'(s) in the cached zeta-zero windows.

2D complex Newton on zeta' (analytic zeta'' supplied), seeded from
  (a) midpoints of consecutive zeta zeros, three offsets to the right of the line, and
  (b) a coarse 2D grid covering 0.55 <= sigma <= 2.8 (zeta' does have zeros with sigma > 1),
then deduplicated.

CENSUS (pre-registered, this is the null for stage 1):
  Berndt 1970 / Levinson-Montgomery: N_1(T) = (T/2pi) log(T/4pi) - T/2pi + O(log T),
  so the count in [T, T+W] must be (W/2pi) log(T_c/4pi), NOT (W/2pi) log(T_c/2pi).
  Equivalently  #zeta'-zeros / #zeta-zeros -> rho = log(T/4pi)/log(T/2pi) = 1 - log2/L.
  NULL (density is the same as zeta's): ratio = 1.000.
  Independent certificate: argument-principle winding of zeta' round a sub-box.
"""
import numpy as np, math, sys, os, time
from att014_afe import zeta_afe, theta

def P(*a): print(*a); sys.stdout.flush()
TWOPI = 2*math.pi

def newton_zprime(seeds, tlo, thi, iters=60, cap=0.6):
    s = np.array(seeds, dtype=complex)
    alive = np.ones(s.shape, bool)
    for it in range(iters):
        idx = np.nonzero(alive)[0]
        if idx.size == 0: break
        _, z1, z2 = zeta_afe(s[idx])
        step = np.where(np.abs(z2) > 0, z1/np.where(z2 == 0, 1, z2), 0.0)
        a = np.abs(step)
        step = np.where(a > cap, step*(cap/np.maximum(a, 1e-300)), step)
        ns = s[idx] - step
        # keep inside the search region
        bad = (ns.real < 0.15) | (ns.real > 4.5) | (ns.imag < tlo-30) | (ns.imag > thi+30)
        s[idx] = np.where(bad, s[idx], ns)
        alive[idx[bad]] = False
    _, z1, z2 = zeta_afe(s)
    resid = np.abs(z1)/np.maximum(np.abs(z2), 1e-30)      # Newton step length = distance to root
    ok = alive & (resid < 1e-8) & (s.real > 0.2) & (s.real < 4.0)
    return s[ok]

def dedupe(s, tol=1e-5):
    o = np.argsort(s.imag); s = s[o]
    keep = []
    for z in s:
        if keep and abs(z - keep[-1]) < tol:  continue
        if keep and any(abs(z-w) < tol for w in keep[-8:]): continue
        keep.append(z)
    return np.array(keep)

def winding_zprime(sig_lo, sig_hi, t_lo, t_hi, dt, dsig):
    """(1/2pi) * total change of arg zeta' round the box.  Returns (count, max step in rad)."""
    def edge(pts):
        _, z1, _ = zeta_afe(pts)
        d = np.angle(z1[1:]/z1[:-1])
        return d.sum(), np.abs(d).max()
    tot = 0.0; mx = 0.0
    # bottom: sigma lo->hi at t_lo ; right: t_lo->t_hi ; top: hi->lo ; left: t_hi->t_lo
    ns = max(200, int((sig_hi-sig_lo)/dsig))
    sg = np.linspace(sig_lo, sig_hi, ns)
    nt = max(200, int((t_hi-t_lo)/dt))
    tt = np.linspace(t_lo, t_hi, nt)
    for pts in (sg + 1j*t_lo, sig_hi + 1j*tt, sg[::-1] + 1j*t_hi, sig_lo + 1j*tt[::-1]):
        a, b = edge(pts); tot += a; mx = max(mx, b)
    return tot/TWOPI, mx

def find_all(T, cache, seed_grid=(0.60,0.72,0.85,1.00,1.15,1.32,1.55,1.85,2.25,2.70), grid_dt=1.5):
    g = np.load(cache)
    t0, t1 = float(g[0]), float(g[-1])
    Lc = math.log(((t0+t1)/2)/TWOPI)
    mid = (g[:-1]+g[1:])/2
    seeds = []
    for off in (0.6/Lc, 2.0/Lc, 5.0/Lc):
        seeds.append(0.5+off + 1j*mid)
    tg = np.arange(t0, t1, grid_dt)
    for sg in seed_grid:
        seeds.append(sg + 1j*tg)
    seeds = np.concatenate(seeds)
    t_ = time.time()
    r = newton_zprime(seeds, t0, t1)
    r = dedupe(r)
    r = r[(r.imag >= t0) & (r.imag <= t1)]
    P(f"  T={T:.0e}: {len(seeds)} seeds -> {len(r)} distinct zeta' zeros in [{t0:.1f},{t1:.1f}]  ({time.time()-t_:.1f}s)")
    return g, r, t0, t1, Lc

if __name__ == "__main__":
    P("STAGE 1 -- zeta' zeros, census against Berndt's log(T/4pi) density.\n")
    P("  NULL: ratio #zeta'/#zeta = 1.000 (same density).  Prediction: rho = 1 - log2/L.\n")
    for T, cache in ((1e5, "att010_zeros_1e+05.npy"), (1e6, "att010_zeros_1e+06.npy")):
        g, r, t0, t1, Lc = find_all(T, cache)
        W = t1 - t0
        pred1 = W/TWOPI*math.log(((t0+t1)/2)/(4*math.pi))
        pred0 = W/TWOPI*math.log(((t0+t1)/2)/TWOPI)
        rho = math.log(((t0+t1)/2)/(4*math.pi))/Lc
        P(f"    zeta zeros {len(g)}  (asymptotic {pred0:.1f})")
        P(f"    zeta' zeros {len(r)}  (Berndt asymptotic {pred1:.1f};  if density were log(T/2pi): {pred0:.1f})")
        P(f"    ratio obs {len(r)/len(g):.5f}   predicted rho = log(T/4pi)/log(T/2pi) = {rho:.5f}   NULL 1.0")
        b = r.real - 0.5
        P(f"    beta'-1/2 : min {b.min():.6f}  median {np.median(b):.5f}  mean {b.mean():.5f}  "
          f"max {b.max():.4f}   #(beta'>1) = {(r.real>1).sum()}   #(beta'<0.5) = {(r.real<0.5).sum()}")
        P(f"    median (beta'-1/2)*L = {np.median(b)*Lc:.4f}")
        np.save(f"att014_zprime_{T:.0e}.npy", r)
        # winding certificate on a sub-box
        for dt, dsig in ((0.02, 0.002), (0.01, 0.001)):
            tA, tB = t0+50.0, t0+250.0
            w, mx = winding_zprime(0.30, 3.60, tA, tB, dt, dsig)
            nsub = ((r.imag > tA) & (r.imag < tB)).sum()
            P(f"    winding box sigma(0.30,3.60) t({tA:.0f},{tB:.0f})  dt={dt}: "
              f"winding {w:.3f}  Newton count {nsub}  max arg step {mx:.3f} rad")
        P("")
