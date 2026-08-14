"""ATTEMPT 023 -- the transition band just above tau = 1.

WHY HERE.  Attempt 016 measured K(tau) on (1,3) and returned a clean flat negative, but its
adversarial verifier refused the record's own explanation: "the residual is not uniform over
(1.05,3.00) and it is not noise-shaped", and decomposing gives (1.30,3.00) pooled 1.00004,
z = +0.06 -- dead flat.  So whatever is there is confined to (1.00, 1.30).  That is exactly
the band the Zeta23 certificate cannot read: their cap is a band-limit at lambda <= 1, and
higher trace moments need the Rudnick-Sarnak range k*lambda < 2.

PAIRING.  house: the calibrated tape form factor K(tau), plus the exact integer-frequency
identity K(m) = n |<e^{-2 pi i m S}>|^2 established in attempt 022, which pins the tau = 1
point mass independently.  classical: Bogomolny-Keating off-diagonal pair correlation and
Montgomery's F(alpha) beyond the diagonal.  MECHANISM: the point mass at tau = 1 is now a
MEASURED quantity, not a fitted one, so its finite-window leakage into (1, 1.3) can be
PREDICTED and subtracted rather than invoked -- which is precisely the step 016 skipped.

THE THREE CANDIDATE EXPLANATIONS, separated by construction:
  (a) leakage from the tau=1 point mass through the finite-window kernel.  For a pure lattice
      the kernel is (sin(pi delta n)/sin(pi delta))^2/n, envelope 1/(n sin^2(pi delta)) --
      at delta = 0.05, n = 4204 this is 0.0097, i.e. NEGLIGIBLE beyond a few/U.  Computed, not
      assumed.
  (b) unresolved prime lines: below tau = 1 the lines are at log n / L; above tau = 1 they are
      absent, but at low T the spacing is comparable to the bin width and a bin mean is then a
      sum of a few heavy draws rather than many light ones.  Handled by the scatter audit.
  (c) genuine off-diagonal structure -- the only interesting outcome.

STATED NULL, pre-registered.  K(tau) on (1.00,1.35) is flat at 1.000 within audited error
bars and indistinguishable from CUE at matched n; the (1.05,1.30) excess is entirely (a)+(b).
Numerically: pooled <K> on (1.05,1.30) within 3 audited sigma of both 1.000 and the CUE value,
and the leakage prediction accounting for the residual.
"""
import numpy as np, math, sys, os
from math import pi, log

def P(*a): print(*a); sys.stdout.flush()
rng = np.random.default_rng(20260812)

def theta_rs(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)

SETS = [('1e3','att010_zeros_1e+03.npy'), ('1e4','att010_zeros_1e+04.npy'),
        ('1e5','att010_zeros_1e+05.npy'), ('1e6','att010_zeros_1e+06.npy'),
        ('1e7','att010_zeros_1e+07.npy'), ('long','att019_zeros_to20k.npy')]

def K_of(u, taus):
    out = np.empty(len(taus))
    B = 4000
    for i in range(0, len(taus), B):
        ch = np.asarray(taus[i:i+B], float)
        out[i:i+B] = np.abs(np.exp(2j*pi*np.outer(ch, u)).sum(axis=1))**2/len(u)
    return out

def cue_u(N):
    z = (rng.standard_normal((N, N)) + 1j*rng.standard_normal((N, N)))/math.sqrt(2)
    q, r = np.linalg.qr(z); q = q*(np.diag(r)/np.abs(np.diag(r)))
    ph = np.sort(np.angle(np.linalg.eigvals(q)))
    return ph*N/(2*pi)

def band_stats(u, lo, hi, ntau=None):
    U = u[-1] - u[0]
    n = len(u)
    ntau = ntau or max(400, int((hi-lo)*U*2))
    taus = lo + (hi-lo)*np.arange(ntau)/ntau
    K = K_of(u - u[0], taus)
    # audited error bar: use the EMPIRICAL scatter, not the nominal Exp(1)/sqrt(dof)
    return K.mean(), K.std(ddof=1)/math.sqrt(len(K)), K, taus

P("Pooled <K> by band, with empirically audited error bars.\n")
P(f"  {'set':>6}{'n':>7}   " + "".join(f"{b:>22}" for b in
                                       ('(1.00,1.05)','(1.05,1.30)','(1.30,3.00)')))
rows = []
for name, f in SETS:
    if not os.path.exists(f): continue
    g = np.load(f); u = theta_rs(g)/pi; u = u - u[0]
    line = f"  {name:>6}{len(g):>7}   "
    vals = []
    for lo, hi in ((1.00, 1.05), (1.05, 1.30), (1.30, 3.00)):
        m, e, K, tt = band_stats(u, lo, hi)
        vals.append((m, e))
        line += f"{m:>13.4f} +-{e:>6.4f}"
    P(line)
    rows.append((name, len(g), u, vals))

P("\nCUE CONTROL at matched n (3 draws each), same bands:")
for N in (4000,):
    for tr in range(3):
        cu = cue_u(N); cu = cu - cu[0]
        line = f"  CUE#{tr+1}{N:>6}   "
        for lo, hi in ((1.00,1.05), (1.05,1.30), (1.30,3.00)):
            m, e, _, _ = band_stats(cu, lo, hi)
            line += f"{m:>13.4f} +-{e:>6.4f}"
        P(line)

P("\n(a) LEAKAGE from the tau=1 point mass, PREDICTED not assumed.")
P("    pure-lattice kernel (sin(pi d n)/sin(pi d))^2/n, envelope 1/(n sin^2(pi d)),")
P("    scaled by the measured mass m = K(1)/n.")
P(f"  {'set':>6}{'K(1)':>10}{'mass m':>10}{'envelope at d=0.05':>21}{'-> leak into (1.05,1.3)':>25}")
for name, n, u, vals in rows:
    K1 = float(K_of(u, [1.0])[0]); m = K1/n
    env = 1.0/(n*math.sin(pi*0.05)**2)
    P(f"  {name:>6}{K1:>10.3f}{m:>10.5f}{env:>21.5f}{m*env*n:>25.6f}")

P("\n(b) SCATTER AUDIT: is the (1.05,1.30) bin mean a sum of many light draws or a few heavy?")
P(f"  {'set':>6}{'measured sd':>14}{'Exp(1) nominal':>16}{'inflation':>11}{'eff. dof':>10}")
for name, n, u, vals in rows:
    m, e, K, tt = band_stats(u, 1.05, 1.30)
    P(f"  {name:>6}{K.std(ddof=1):>14.4f}{1.0:>16.4f}{K.std(ddof=1):>11.2f}"
      f"{len(K)/max(K.std(ddof=1),1e-9)**2:>10.1f}")

P("\nVERDICT LINE: z of (1.05,1.30) against 1.000 using the audited (inflated) error bar,")
P("and against the CUE mean at matched n.")
cu = cue_u(4000); cu = cu - cu[0]
cm, ce, cK, _ = band_stats(cu, 1.05, 1.30)
P(f"  CUE(4000) reference on (1.05,1.30): {cm:.4f} +- {ce:.4f}")
P(f"  {'set':>6}{'<K>':>10}{'audited se':>12}{'z vs 1':>9}{'z vs CUE':>10}")
for name, n, u, vals in rows:
    m, e, K, tt = band_stats(u, 1.05, 1.30)
    se = K.std(ddof=1)/math.sqrt(len(K))
    P(f"  {name:>6}{m:>10.4f}{se:>12.4f}{(m-1)/se:>9.2f}{(m-cm)/math.sqrt(se*se+ce*ce):>10.2f}")

P("\nPOSITIVE CONTROL: inject a density ripple at tau0=1.15 on the REAL tape and recover it.")
name, n, u, vals = rows[-2]
for A in (0.15, 0.5):
    uu = u + (A/(2*pi*1.15))*np.sin(2*pi*1.15*u)
    m, e, K, tt = band_stats(uu, 1.05, 1.30)
    k0 = float(K_of(uu, [1.15])[0])
    P(f"    A={A:.2f}:  K(1.15) = {k0:8.2f}   (n J_1(A)^2 = {n*(0.5*A-A**3/16)**2:8.2f})"
      f"   band <K> = {m:.4f}")
