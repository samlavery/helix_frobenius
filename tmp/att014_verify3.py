"""ADVERSARIAL VERIFICATION of attempt 014, stage 3.

FULLY INDEPENDENT instrument: pure mpmath (Riemann-Siegel / Euler-Maclaurin as mpmath
chooses), NOT their hand-rolled Stirling AFE.  Fresh window, fresh zeta zeros (siegelz sign
changes + bisection), fresh zeta' zeros (Newton on zeta'/zeta''), fresh winding certificate.

Window: t in (1e6, 1e6+600) -- INSIDE their 1e6 window but with an independent root set.
Tape validity R = W^2 lam /(2 pi T L) = 0.003 (theirs was 0.040 at 1e6).
"""
import numpy as np, math, sys, os, time
from multiprocessing import Pool
import mpmath as mp
from fractions import Fraction

mp.mp.dps = 20
TWOPI = 2*math.pi
T0, T1 = 1000000.0, 1000600.0
SIG_LO, SIG_HI = 0.30, 3.60

def P(*a): print(*a); sys.stdout.flush()

# ---------------------------------------------------------------- workers
def _z(t):
    return float(mp.siegelz(mp.mpf(t)))

def _zp(s):
    return complex(mp.zeta(mp.mpc(s.real, s.imag), derivative=1))

def _newton(seed):
    s = mp.mpc(seed.real, seed.imag)
    for _ in range(40):
        f = mp.zeta(s, derivative=1)
        g = mp.zeta(s, derivative=2)
        if g == 0: return None
        d = f/g
        if abs(d) > 3: d = d*3/abs(d)
        s = s - d
        if s.real < 0.05 or s.real > 5.0 or s.imag < T0-10 or s.imag > T1+10: return None
        if abs(d) < 1e-13:
            break
    else:
        return None
    if abs(mp.zeta(s, derivative=1)) > 1e-8*max(1.0, abs(mp.zeta(s, derivative=2))):
        return None
    return complex(s)

def _bisect(ab):
    a, b = ab
    fa = float(mp.siegelz(mp.mpf(a)))
    for _ in range(60):
        m = (a+b)/2
        fm = float(mp.siegelz(mp.mpf(m)))
        if fm == 0: return m
        if (fa < 0) != (fm < 0): b = m
        else: a, fa = m, fm
        if b-a < 1e-10: break
    return (a+b)/2

# ---------------------------------------------------------------- main
if __name__ == "__main__":
    from att014_verify import coeffs_recursive, zeta_lambda, theta_f
    pool = Pool(10)
    tc = (T0+T1)/2; W = T1-T0; L = math.log(tc/TWOPI)
    P(f"window ({T0:.0f},{T1:.0f})  W={W}  L={L:.5f}  "
      f"Berndt N1={W/TWOPI*math.log(tc/(4*math.pi)):.1f}  N={W/TWOPI*L:.1f}")

    # ---------- 1. zeta zeros by siegelz sign changes  (independent of att010) ----------
    f_g = "att014_ver_zeta.npy"
    if os.path.exists(f_g):
        gz = np.load(f_g)
    else:
        t_ = time.time()
        grid = np.arange(T0-0.6, T1+0.6, 0.04)
        vals = np.array(pool.map(_z, grid.tolist(), chunksize=200))
        idx = np.nonzero(np.sign(vals[:-1]) != np.sign(vals[1:]))[0]
        brackets = [(grid[i], grid[i+1]) for i in idx]
        gz = np.array(pool.map(_bisect, brackets, chunksize=20))
        gz = gz[(gz >= T0) & (gz <= T1)]
        np.save(f_g, gz)
        P(f"  zeta zeros: {len(gz)} found in {time.time()-t_:.0f}s "
          f"(grid 0.04, {len(grid)} siegelz evals)")
    Ntheo = (theta_f(np.array([T1]))[0]-theta_f(np.array([T0]))[0])/math.pi
    P(f"  ZETA CENSUS: found {len(gz)}   theta/pi increment {Ntheo:.2f}   "
      f"min gap {np.diff(gz).min():.4f}  [S(t) fluctuation makes these differ by O(1)]")

    # ---------- 2. winding certificate for zeta' on a sub-box ----------
    def winding(sa, sb, ta, tb, dt_left, dt_right, nsig):
        pts = []
        sig = np.linspace(sa, sb, nsig)
        pts += [complex(x, ta) for x in sig]                       # bottom L->R
        tt = np.arange(ta, tb, dt_right)
        pts += [complex(sb, y) for y in tt] + [complex(sb, tb)]    # right up
        pts += [complex(x, tb) for x in sig[::-1]]                 # top R->L
        tt2 = np.arange(tb, ta, -dt_left)
        pts += [complex(sa, y) for y in tt2] + [complex(sa, ta)]   # left down
        vals = pool.map(_zp, pts, chunksize=50)
        arg = np.unwrap(np.angle(np.array(vals)))
        d = np.abs(np.diff(np.angle(np.array(vals))))
        d = np.minimum(d, 2*np.pi-d)
        return (arg[-1]-arg[0])/TWOPI, d.max(), len(pts)

    for (ta, tb) in ((T0+50, T0+250),):
        for (dl, dr) in ((0.05, 0.5), (0.025, 0.25)):
            t_ = time.time()
            w, mx, npts = winding(SIG_LO, SIG_HI, ta, tb, dl, dr, 60)
            P(f"  WINDING zeta' sigma({SIG_LO},{SIG_HI}) t({ta:.0f},{tb:.0f}) dt_left={dl}: "
              f"{w:.4f}  max arg step {mx:.2f} rad  ({npts} pts, {time.time()-t_:.0f}s)  "
              f"Berndt {(tb-ta)/TWOPI*math.log(tc/(4*math.pi)):.1f}")

    # ---------- 3. zeta' zeros by mpmath Newton ----------
    f_r = "att014_ver_zprime.npy"
    if os.path.exists(f_r):
        zp = np.load(f_r)
    else:
        t_ = time.time()
        mids = (gz[:-1]+gz[1:])/2
        seeds = []
        for off in (0.5/L, 1.5/L, 4.0/L, 9.0/L):
            seeds += [complex(0.5+off, m) for m in mids]
        for off in (2.0/L, 6.0/L):
            seeds += [complex(0.5+off, g) for g in gz]
        sg = np.arange(0.55, 3.2, 0.25)
        tg = np.arange(T0, T1, 0.5)
        seeds += [complex(a, b) for b in tg for a in sg]
        P(f"  zeta' Newton from {len(seeds)} seeds ...")
        res = pool.map(_newton, seeds, chunksize=20)
        res = np.array([r for r in res if r is not None])
        res = res[(res.imag >= T0) & (res.imag <= T1)]
        # dedupe
        o = np.argsort(res.imag); res = res[o]
        keep = []
        for z in res:
            if not keep or min(abs(z-k) for k in keep[-12:]) > 1e-6:
                keep.append(z)
        zp = np.array(keep)
        np.save(f_r, zp)
        P(f"  zeta' zeros: {len(zp)} in {time.time()-t_:.0f}s")
    P(f"  ZETA' CENSUS: found {len(zp)}   Berndt {W/TWOPI*math.log(tc/(4*math.pi)):.1f}   "
      f"ratio #zp/#z = {len(zp)/len(gz):.5f}   rho=log(T/4pi)/log(T/2pi) = "
      f"{math.log(tc/(4*math.pi))/L:.5f}")
    b = zp.real - 0.5
    P(f"  beta'-1/2: median {np.median(b):.4f} mean {b.mean():.4f} max {b.max():.4f} "
      f"min {b.min():.4f} #(<0)={int((b<0).sum())}   E[2^b]={np.mean(2.0**b):.4f}")

    # ---------- 3b. cross-check against THEIR AFE root set in the same window ----------
    th = np.load("att014_zpz_1e+06.npy")
    th = th[(th.imag >= T0) & (th.imag <= T1)]
    P(f"  their AFE root set in the same window: {len(th)}   mine: {len(zp)}")
    dg, ds = [], []
    for z in th:
        j = np.argmin(np.abs(zp - z))
        ds.append(abs(zp[j]-z)); dg.append(abs(zp[j].imag-z.imag))
    ds = np.array(ds); dg = np.array(dg)
    P(f"    match: max|Delta s| {ds.max():.3e}  median {np.median(ds):.3e} | "
      f"max|Delta t| {dg.max():.3e}   #unmatched(>0.05) {int((ds>0.05).sum())}")
    bias = np.array([zp[np.argmin(np.abs(zp-z))].real - z.real for z in th])
    P(f"    beta' bias (mine - theirs): median {np.median(bias):+.5f}  mean {bias.mean():+.5f}  "
      f"max|.| {np.abs(bias).max():.4f}")

    # ---------- 4. the tape ----------
    H = coeffs_recursive(2.4); Z = zeta_lambda(2.4)
    LAM = [(math.log(float(r)), str(r), H[r]**2*math.exp(-math.log(float(r))))
           for r in sorted(H, key=float) if 0.2 < math.log(float(r)) <= 1.65]
    ZL = {round(math.log(n), 12): (n, Lm*Lm/n) for n, Lm in Z.items()}
    uz = theta_f(gz)/np.pi; uz -= uz[0]; Uz = uz[-1]
    o = np.argsort(zp.imag); gp = zp.imag[o]; bp = zp.real[o]-0.5
    up = theta_f(gp)/np.pi; up -= up[0]; Up = up[-1]
    rng = np.random.default_rng(2026)
    lam_rand = rng.uniform(0.25, 1.65, 500)
    Kfl_p = np.array([abs(np.exp(2j*np.pi*(l/L)*up).sum())**2/len(up) for l in lam_rand])
    Kfl_z = np.array([abs(np.exp(2j*np.pi*(l/L)*uz).sum())**2/len(uz) for l in lam_rand])
    P("")
    P(f"  EMPIRICAL FLOOR (500 random lam): zeta' median {np.median(Kfl_p):.4f} "
      f"90pct {np.percentile(Kfl_p,90):.3f} 99pct {np.percentile(Kfl_p,99):.3f} | "
      f"zeta median {np.median(Kfl_z):.4f} 90pct {np.percentile(Kfl_z,90):.3f} "
      f"99pct {np.percentile(Kfl_z,99):.3f}   [their pre-registered null: Exp(1), median 0.693]")
    P(f"  {'lam':>8}{'r':>7}{'R':>7} | {'K_H1':>8}{'K_H2':>8}{'pred':>8}{'H1o/p':>7}{'H2o/p':>7} | "
      f"{'K_zeta':>8}{'predz':>7}{'o/p':>6} | {'H1 vs zeta-law':>15}")
    r1, r2 = [], []
    for lam, rs, A in LAM:
        tau = lam/L
        E = np.exp(2j*np.pi*tau*up)
        kp = abs(E.sum())**2/len(up)
        kw = abs((E*np.exp(lam*bp)).sum())**2/len(up)
        kz = abs(np.exp(2j*np.pi*tau*uz).sum())**2/len(uz)
        pred = Up*Up*A/(L*L*len(up))
        zz = ZL.get(round(lam, 12))
        predz = Uz*Uz*zz[1]/(L*L*len(uz)) if zz else float('nan')
        # NULL-A: zeta' ordinates carry the ZETA amplitude Lambda(n)^2/n
        predA = Up*Up*zz[1]/(L*L*len(up)) if zz else float('nan')
        R = Up*lam*math.log(1+W/tc)/(L*L)
        r1.append(kp/pred); r2.append(kw/pred)
        fl = "" if np.isnan(predA) else f"{kp/predA:>15.3f}"
        if not fl: fl = f"{'(zeta-only: n/a)':>15}"
        zs = f"{kz:>8.2f}{predz:>7.2f}{kz/predz:>6.2f}" if zz else f"{kz:>8.2f}{'--':>7}{'--':>6}"
        P(f"  {lam:>8.5f}{rs:>7}{R:>7.4f} | {kp:>8.2f}{kw:>8.2f}{pred:>8.2f}{kp/pred:>7.3f}"
          f"{kw/pred:>7.3f} | {zs} | {fl}")
    r1 = np.array(r1); r2 = np.array(r2)
    P(f"  -> H1 median {np.median(r1):.3f}  IQR {np.percentile(r1,25):.3f}-{np.percentile(r1,75):.3f}")
    P(f"  -> H2 median {np.median(r2):.3f}  IQR {np.percentile(r2,25):.3f}-{np.percentile(r2,75):.3f}")
    # C1 control: zeta zeros at zeta'-only frequencies
    only = [(lam, rs) for lam, rs, _ in LAM if round(lam, 12) not in ZL]
    kk = [abs(np.exp(2j*np.pi*(l/L)*uz).sum())**2/len(uz) for l, _ in only]
    kp2 = [abs(np.exp(2j*np.pi*(l/L)*up).sum())**2/len(up) for l, _ in only]
    P("  C1 (zeta zeros at zeta'-ONLY freqs): " + " ".join(f"{rs}:{v:.2f}" for (l, rs), v in zip(only, kk)))
    P("  H1 (zeta' ordinates, SAME freqs):    " + " ".join(f"{rs}:{v:.2f}" for (l, rs), v in zip(only, kp2)))
    P(f"  fraction of zeta'-only H1 values above the zeta' floor 90pct "
      f"({np.percentile(Kfl_p,90):.3f}): {sum(1 for v in kp2 if v > np.percentile(Kfl_p,90))}/{len(kp2)}")
    pool.close()
