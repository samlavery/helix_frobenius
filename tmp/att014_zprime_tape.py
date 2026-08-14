"""ATTEMPT 014 -- put zeta-prime's zeros on the theta-tape.

HOUSE   : the theta-tape spectral instrument (attempt 010) + the Speiser winding detector (008).
CLASSICAL: Speiser's theorem, Levinson-Montgomery/Berndt density, Landau's formula for
           sum_{0<gamma<T} x^{i gamma} transported to -zeta''/zeta'.

DERIVATION (att014_afe.py has the algebra; a_lambda are EXACT, no fit):
  -zeta''/zeta'(s) = sum_lambda a_lambda e^{-s lambda}, lambda = log(n_1..n_k/2^k), n_i >= 3.
  DC term a_0 = log 2 exactly  ==>  density of zeta' zeros = (1/2pi) log(t/4pi).   [checked by winding]
  Two INEQUIVALENT transports of Landau's formula to the tape, which this script separates:
   (H1) count-fluctuation route: N_1 = theta/pi - (t/2pi)log2 + c + S_1,
        S_1 = (1/pi) arg(1+X)(1/2+it), giving the UNWEIGHTED sum
             |sum_k e^{2 pi i tau_lambda u_k}|      = (U/L)|a_lambda| e^{-lambda/2}
   (H2) residue route: sum_{rho'} x^{rho'} = -(W/2pi) a(x), giving the beta'-WEIGHTED sum
             |sum_k x^{beta'_k-1/2} e^{2 pi i tau_lambda u_k}| = (U/L)|a_lambda| e^{-lambda/2}.
  Same amplitude, different sums -- so measuring both DISCRIMINATES them.  Under H1 the zeta'
  zeros have zero mean weight-dependence; under H2 they do not.  Pre-registered.

NULLS, written down before running:
  NULL-A  ("no new observable"): zeta'-zeros show the SAME amplitudes as zeta's, i.e.
          K(tau_lambda)*L^2*n/U^2 = Lambda(n)^2/n at lambda = log n, and the Exp(1) FLOOR
          (K ~ 1, median ln2 = 0.693) at lambda = log(3/2), log(9/4), log(5/2), ... which are
          absent from zeta's spectrum.
  NULL-B  ("instrument does not transfer"): K ~ 1 (Exp(1) floor) at EVERY lambda for zeta'.
  Both are pre-registered; the hypothesis is the a_lambda law above.

CONTROLS (must fail by MISSING STRUCTURE, never by more cancellation):
  C1  zeta's own zeros evaluated at the zeta'-only frequencies log(3/2), log(9/4), log(5/2):
      zeta has no such frequency, so this must sit at the floor.
  C2  off-lattice lambda (not in either spectrum): floor.
  C3  a synthetic point set with the same count and window but Poisson positions: floor.
  C4  the empirical floor: 200 random lambda in (0.3,2.2) -- median must be ~ln2 = 0.693.
"""
import numpy as np, math, sys, os, time
from fractions import Fraction
from att014_afe import zeta_afe, theta, zprime_coeffs, zeta_coeffs
from att014_zprime_roots import newton_zprime, dedupe, winding_zprime

def P(*a): print(*a); sys.stdout.flush()
TWOPI = 2*math.pi
RUNS = ((1e5, "att010_zeros_1e+05.npy"), (1e6, "att010_zeros_1e+06.npy"), (1e7, "att010_zeros_1e+07.npy"))

# ---------------------------------------------------------------- zeta' zero location
def zprime_zeros(T, cache, dsig=0.08, dt=0.4, sig_hi=3.0):
    out = f"att014_zpz_{T:.0e}.npy"
    g = np.load(cache); t0, t1 = float(g[0]), float(g[-1])
    if os.path.exists(out):
        return g, np.load(out), t0, t1
    Lc = math.log(((t0+t1)/2)/TWOPI)
    mids = (g[:-1]+g[1:])/2
    seeds = [0.5+off + 1j*mids for off in (0.4/Lc, 1.2/Lc, 3.0/Lc, 7.0/Lc)]
    sg = np.arange(0.52, sig_hi, dsig); tg = np.arange(t0, t1, dt)
    S, TT = np.meshgrid(sg, tg); seeds.append((S + 1j*TT).ravel())
    seeds = np.concatenate(seeds)
    t_ = time.time()
    r = dedupe(newton_zprime(seeds, t0, t1))
    r = r[(r.imag >= t0) & (r.imag <= t1)]
    P(f"    located {len(r)} zeta' zeros from {len(seeds)} seeds in {time.time()-t_:.0f}s")
    np.save(out, r)
    return g, r, t0, t1

# ---------------------------------------------------------------- spectra
def K_of(u, taus, w=None):
    """form factor |sum w_k exp(2 pi i tau u_k)|^2 / n  (n = number of points)."""
    E = np.exp(2j*np.pi*np.outer(np.asarray(taus, float), u))
    F = (E*w).sum(1) if w is not None else E.sum(1)
    return np.abs(F)**2/len(u)

if __name__ == "__main__":
    C = zprime_coeffs(2.3); Z = zeta_coeffs(2.3)
    # frequency menu: everything with lambda <= 1.65 and a decent predicted amplitude
    LAM = []
    for r, a in sorted(C.items(), key=lambda kv: float(kv[0])):
        lam = math.log(float(r))
        if 0.2 < lam <= 1.65: LAM.append((lam, str(r), a*a*math.exp(-lam)))
    ZL = {round(math.log(n), 12): (n, L*L/n) for n, L in Z.items()}
    OFF = [0.5493061443, 0.7621400520, 1.0203, 1.4500, 0.6100]      # off-lattice controls

    P(__doc__)
    P("="*104)
    P("PREDICTED tape amplitudes  A = a_lambda^2 e^{-lambda}  (zeta': exact) vs  Lambda^2/n (zeta)")
    P(f"  {'lambda':>9}{'r':>8}{'A_zprime':>11}{'A_zeta':>11}   ratio")
    for lam, rs, A in LAM:
        zz = ZL.get(round(lam, 12))
        P(f"  {lam:>9.5f}{rs:>8}{A:>11.5f}" + (f"{zz[1]:>11.5f}   {A/zz[1]:>6.3f}" if zz else f"{0.0:>11.5f}   {'--':>6}"))
    P("="*104 + "\n")

    for T, cache in RUNS:
        P(f"### T = {T:.0e}")
        g, r, t0, t1 = zprime_zeros(T, cache)
        W = t1 - t0; tc = (t0+t1)/2
        L = math.log(tc/TWOPI); rho_pred = math.log(tc/(4*math.pi))/L
        # ---- census, certified by winding on a sub-box
        P(f"  window [{t0:.1f},{t1:.1f}]  W={W:.1f}  L(centre)={L:.5f}")
        P(f"  CENSUS  zeta zeros {len(g)}   zeta' zeros {len(r)}   ratio {len(r)/len(g):.5f}")
        P(f"          predicted rho = log(T/4pi)/log(T/2pi) = {rho_pred:.5f}   [NULL: 1.00000]")
        P(f"          Berndt count (W/2pi)log(Tc/4pi) = {W/TWOPI*math.log(tc/(4*math.pi)):.1f}"
          f"   vs log(Tc/2pi) count {W/TWOPI*math.log(tc/TWOPI):.1f}")
        for (tA, tB) in ((t0+50, t0+250), (tc-100, tc+100), (t1-250, t1-50)):
            w, mx = winding_zprime(0.30, 3.60, tA, tB, 0.01, 0.001)
            nsub = ((r.imag > tA) & (r.imag < tB)).sum()
            P(f"          winding certificate t({tA:.0f},{tB:.0f}): {w:.3f}   Newton {nsub}   "
              f"Berndt {(tB-tA)/TWOPI*math.log(tc/(4*math.pi)):.1f}   max arg step {mx:.2f} rad")
        b = r.real - 0.5
        P(f"  beta'-1/2: median {np.median(b):.5f}  mean {b.mean():.5f}  max {b.max():.4f}  "
          f"#(beta'>1)={int((r.real>1).sum())}  (median*L = {np.median(b)*L:.3f})")

        # ---- tape
        uz = theta(g)/np.pi;  uz -= uz[0];  Uz = uz[-1]
        gp = np.sort(r.imag); order = np.argsort(r.imag); bp = r.real[order] - 0.5
        up = theta(gp)/np.pi; u0 = up[0]; up = up - u0; Up = up[-1]
        taus = [lam/L for lam, _, _ in LAM]
        Kz = K_of(uz, taus); Kp = K_of(up, taus)
        Kw = np.array([K_of(up, [lam/L], w=np.exp(lam*bp))[0] for lam, _, _ in LAM])
        P(f"  tape: U_zeta={Uz:.1f} n={len(uz)}   U_zprime={Up:.1f} n={len(up)}  "
          f"(n/U = {len(up)/Up:.5f}, predicted rho {rho_pred:.5f})")
        P(f"  {'lambda':>9}{'r':>7}{'tau':>8}{'R':>7} | {'K_zp':>9}{'pred':>9}{'o/p':>7} | "
          f"{'Kw_zp':>9}{'o/p':>7} | {'K_zeta':>9}{'predz':>9}{'o/p':>7}")
        rat1, rat2 = [], []
        for (lam, rs, A), tau, kp, kw, kz in zip(LAM, taus, Kp, Kw, Kz):
            R = Up*lam*math.log(1+W/tc)/(L*L)
            predp = Up*Up*A/(L*L*len(up))
            zz = ZL.get(round(lam, 12))
            predz = Uz*Uz*zz[1]/(L*L*len(uz)) if zz else float('nan')
            rat1.append(kp/predp); rat2.append(kw/predp)
            zs = f"{kz:>9.2f}{predz:>9.2f}{kz/predz:>7.2f}" if zz else f"{kz:>9.2f}{'--':>9}{'--':>7}"
            P(f"  {lam:>9.5f}{rs:>7}{tau:>8.4f}{R:>7.3f} | {kp:>9.2f}{predp:>9.2f}{kp/predp:>7.2f} | "
              f"{kw:>9.2f}{kw/predp:>7.2f} | {zs}")
        r1 = np.array(rat1); r2 = np.array(rat2)
        P(f"  -> H1 (unweighted) median obs/pred = {np.median(r1):.3f}   IQR "
          f"{np.percentile(r1,25):.3f}-{np.percentile(r1,75):.3f}")
        P(f"  -> H2 (beta'-weighted) median obs/pred = {np.median(r2):.3f}   IQR "
          f"{np.percentile(r2,25):.3f}-{np.percentile(r2,75):.3f}")

        # ---- controls
        rng = np.random.default_rng(11)
        lam_rand = rng.uniform(0.3, 2.2, 200)
        floor_p = K_of(up, lam_rand/L); floor_z = K_of(uz, lam_rand/L)
        pois = np.sort(rng.uniform(0, Up, len(up)))
        floor_c3 = K_of(pois, taus)
        P(f"  C4 empirical floor (200 random lambda): zeta' median {np.median(floor_p):.3f} "
          f"99pct {np.percentile(floor_p,99):.2f} | zeta median {np.median(floor_z):.3f} "
          f"99pct {np.percentile(floor_z,99):.2f}   [Exp(1) => ln2 = 0.693]")
        P(f"  C3 Poisson set, same n and U, at the same taus: median K {np.median(floor_c3):.3f} "
          f"max {floor_c3.max():.2f}")
        koff_p = K_of(up, [l/L for l in OFF]); koff_z = K_of(uz, [l/L for l in OFF])
        P(f"  C2 off-lattice lambda {OFF}:  zeta' K = " + " ".join(f"{v:.2f}" for v in koff_p)
          + " | zeta K = " + " ".join(f"{v:.2f}" for v in koff_z))
        only = [(lam, rs) for lam, rs, _ in LAM if round(lam, 12) not in ZL]
        kk = K_of(uz, [l/L for l, _ in only])
        P("  C1 zeta zeros at zeta'-ONLY frequencies: " +
          "  ".join(f"{rs}:{v:.2f}" for (l, rs), v in zip(only, kk)))
        # half-window stability
        half = len(up)//2
        for nm, sl in (("first half", slice(0, half)), ("second half", slice(half, None))):
            uu = up[sl] - up[sl][0]; UU = uu[-1]
            kk = K_of(uu, taus)
            rr = np.array([k/(UU*UU*A/(L*L*len(uu))) for k, (_, _, A) in zip(kk, LAM)])
            P(f"  noise audit, {nm} of the zeta' tape (n={len(uu)}): H1 median obs/pred {np.median(rr):.3f}")
        P("")
