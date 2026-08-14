"""ATTEMPT 028 -- STAGE 6.  Verification and noise audit of the stage-5 positive.

CHECKS (each with the criterion stated before running):
  C1  every located off-line zero must have winding number exactly 1 on a small box around it
      (criterion: |N - 1| < 0.01 for all 24), so they are genuine simple zeros, not Newton
      artefacts or near-misses.
  C2  every located off-line zero must survive re-evaluation by a SECOND, independent engine
      built with a different rotation angle and a different quadrature step
      (delta 0.012 -> 0.030, h 1e-4 -> 5e-5): criterion |F(rho)| < 1e-7.
  C3  noise audit: which n produce the large beta-weighted noise, and by how much does the
      n^{beta-1/2} weighting inflate the floor?  Line/floor ratio reported per cell.
  C4  a SHUFFLE control that must fail by MISSING structure: keep the 24 off-line betas but
      attach them to randomly chosen on-line gammas.  If the n=6 line survives that, the
      beta-weighting is not carrying arithmetic and stage 5 is an artefact.
"""
import numpy as np, math, sys, time
from math import pi, log, sqrt
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_offline import GEngine
from att028_engine import coefficients, vonmangoldt_like

def P(*a): print(*a); sys.stdout.flush()

T0, T1 = 10.0, 200.0
W = T1 - T0
a1, aC, dK, bf = coefficients(6000)
LAMF = vonmangoldt_like(a1, 64)
off = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_offline_F.npy')
onF = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_F.npy')
onF = onF[(onF > T0) & (onF < T1)]

engA = GEngine(a1, 0.5, delta=0.012, h=1e-4)
engB = GEngine(a1, 0.5, delta=0.030, h=5e-5, guard=46.0)

# ---------------------------------------------------------------- C1
def winding_box(eng, sc, tc, rad, npts=400):
    th = 2*pi*np.arange(npts)/npts
    vals = np.array([eng.lam_gen(sc + rad*math.cos(a), tc + rad*math.sin(a)) for a in th])
    vals = np.append(vals, vals[0])
    d = np.diff(np.angle(vals))
    d = np.where(d > pi, d-2*pi, np.where(d < -pi, d+2*pi, d))
    return d.sum()/(2*pi)

P("C1  winding number on a box of radius 0.02 around each located off-line zero:")
ws = [winding_box(engA, b, g, 0.02) for b, g in off]
P(f"    all 24: min {min(ws):.4f}  max {max(ws):.4f}  "
  f"[{'PASS' if all(abs(w-1) < 0.01 for w in ws) else 'FAIL'}]")

# ---------------------------------------------------------------- C2
P("C2  |F(rho)| under the second engine (delta 0.030, h 5e-5, guard 46):")
resid = [abs(engB.Fval(b, g)) for b, g in off]
residA = [abs(engA.Fval(b, g)) for b, g in off]
P(f"    engine A (the one that found them): max |F| = {max(residA):.2e}")
P(f"    engine B (independent):             max |F| = {max(resid):.2e}   "
  f"[{'PASS' if max(resid) < 1e-7 else 'FAIL'}]")
sh = []
for b, g in off:
    s = complex(b, g)
    for _ in range(40):
        e = 1e-5
        f0 = engB.Fval(s.real, s.imag)
        d = -1j*(engB.Fval(s.real, s.imag+e) - engB.Fval(s.real, s.imag-e))/(2*e)
        s = s - f0/d
        if abs(f0/d) < 1e-13: break
    sh.append(abs(s - complex(b, g)))
P(f"    beta agreement engine A vs B, re-Newtoned: max |rho_A - rho_B| = {max(sh):.2e}")

# ---------------------------------------------------------------- C3
NS = [4, 6, 8, 9, 12, 16, 18, 23, 25, 27, 49]
NOISE = [10, 14, 15, 20, 21, 22, 26, 28, 30, 33, 34, 35, 38, 39, 40, 42, 44, 45, 50]
def bw(g_on, offs, n):
    ln = log(n)
    tot = np.exp(1j*g_on*ln).sum()
    for b, gm in offs:
        tot += (n**(b-0.5) + n**(0.5-b))*np.exp(1j*gm*ln)
    return complex(tot/(W/(2*pi)))

P("\nC3  noise audit.  beta-weighted |a| at n where ALL specimens are silent:")
nf = [(n, abs(bw(onF, off, n))) for n in NOISE]
for n, v in sorted(nf, key=lambda z: -z[1])[:6]:
    P(f"      n={n:>3}  |a| = {v:.4f}   (max n^{{beta-1/2}} inflation = "
      f"{n**(off[:,0].max()-0.5):.2f}x)")
med = np.median([v for _, v in nf])
P(f"    median floor {med:.4f}, max {max(v for _, v in nf):.4f}")
P("    line / floor:")
for n in (6, 12, 18, 4, 8, 27):
    P(f"      n={n:>3}  |a| = {abs(bw(onF, off, n)):.4f}  = {abs(bw(onF,off,n))/med:.1f}x the "
      f"median floor;  predicted {abs(LAMF[n])/sqrt(n):.4f}")

# ---------------------------------------------------------------- C4
P("\nC4  SHUFFLE control (must FAIL by missing structure): same 24 betas, random gammas.")
rng = np.random.default_rng(20260812)
for n in (6, 12, 18):
    pred = -LAMF[n]/sqrt(n)
    vals = []
    for _ in range(400):
        gg = rng.choice(onF, size=len(off), replace=False)
        shuf = np.column_stack([off[:, 0], gg])
        vals.append(bw(onF, shuf, n).real/pred)
    vals = np.array(vals)
    true = bw(onF, off, n).real/pred
    P(f"    n={n:>3}: true beta-weighted obs/pred {true:+.4f};  shuffled "
      f"{vals.mean():+.4f} +- {vals.std():.4f}  -> z = {(true-vals.mean())/vals.std():+.1f} sigma")
