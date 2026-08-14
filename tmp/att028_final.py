"""ATTEMPT 028 -- STAGE 8 (final).  Corrected line/noise partition, window [10,600], W = 590.

CORRECTION TO STAGE 5/7 (caught by the stage-6 noise audit, rule 3).  My hand-written "silent"
list contained n = 26 and n = 39, which are NOT silent: Lambda_1(26) = 2 log 26 and
Lambda_1(39) = 2 log 39.  They were the two large "noise" entries.  The partition is now
computed, not asserted:  LINE  <=>  Lambda_1(n) != 0 ;  SILENT <=> Lambda_1 = 0 for all three
specimens.  n = 48 is kept as a separate, sharper test: Lambda_1(48) = -2 log 48 is NEGATIVE, so
the predicted line there is a POSITIVE real -- a sign flip at a non-prime-power that no Euler
product can produce.
"""
import numpy as np, math, sys
from math import pi, log, sqrt
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_engine import coefficients, vonmangoldt_like

def P(*a): print(*a); sys.stdout.flush()

T0, T1 = 10.0, 600.0
W = T1 - T0
a1, aC, dK, bf = coefficients(2000)
LF = vonmangoldt_like(a1, 64); LK = vonmangoldt_like(dK, 64); Lf = vonmangoldt_like(bf, 64)
off = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_offline_F600.npy')
on = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_F.npy')
on = on[(on > T0) & (on < T1)]

def isppow(n):
    for p in range(2, n+1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return m == 1
    return False

LINES = [n for n in range(2, 65) if abs(LF[n]) > 1e-9]
SILENT = [n for n in range(2, 65)
          if abs(LF[n]) < 1e-9 and abs(LK[n]) < 1e-9 and abs(Lf[n]) < 1e-9]
NPP = [n for n in LINES if not isppow(n)]
P(f"computed partition:  {len(LINES)} lines, of which {len(NPP)} are NON-PRIME-POWERS {NPP}")
P(f"                     {len(SILENT)} all-silent n (the noise set) {SILENT}")

def bw(n, w=True):
    ln = log(n)
    tot = np.exp(1j*on*ln).sum()
    if w:
        tot += np.sum((n**(off[:, 0]-0.5) + n**(0.5-off[:, 0]))*np.exp(1j*off[:, 1]*ln))
    return complex(tot/(W/(2*pi)))

P(f"\nF = Epstein principal class, D = -23, h = 3.  on-line {len(on)} + off-line {len(off)*2}"
  f" = {len(on)+2*len(off)} zeros (argument principle: 976).  W = {W:.0f}, no fitted parameter.")
P(f"  {'n':>4} {'ppow':>5}{'Lam_1(n)':>11}{'a_pred':>10}{'ordinate':>10}{'o/p':>8}"
  f"{'BETA-WTD':>10}{'o/p':>8}{'arg/pi':>8}")
r1, r2, rn = [], [], []
for n in LINES:
    ao, ab = bw(n, False), bw(n, True)
    pred = -LF[n]/sqrt(n)
    q1, q2 = ao.real/pred, ab.real/pred
    r1.append(q1); r2.append(q2); rn.append(n)
    P(f"  {n:>4} {'y' if isppow(n) else 'NO':>5}{LF[n]:>11.5f}{pred:>10.5f}{ao.real:>10.5f}"
      f"{q1:>8.3f}{ab.real:>10.5f}{q2:>8.4f}"
      f"{math.atan2(ab.imag, ab.real)/pi:>8.4f}")
r1, r2 = np.array(r1), np.array(r2)
m = np.array([not isppow(n) for n in rn])
P(f"  -> ALL {len(r2)} lines : ordinate-only median {np.median(r1):.4f} | "
  f"BETA-WEIGHTED median {np.median(r2):.4f}  IQR {np.percentile(r2,25):.4f}-{np.percentile(r2,75):.4f}")
P(f"  -> the {m.sum()} NON-PRIME-POWER lines only : ordinate-only median {np.median(r1[m]):.4f} | "
  f"BETA-WEIGHTED median {np.median(r2[m]):.4f}  range {r2[m].min():.4f}-{r2[m].max():.4f}")
nf = [abs(bw(n)) for n in SILENT]
nf0 = [abs(bw(n, False)) for n in SILENT]
P(f"  -> NOISE FLOOR over {len(SILENT)} computed-silent n: beta-weighted median {np.median(nf):.4f}"
  f" max {max(nf):.4f} | ordinate-only median {np.median(nf0):.4f} max {max(nf0):.4f}")
P(f"  -> smallest non-prime-power line |a| = {min(abs(bw(n)) for n in NPP):.4f} = "
  f"{min(abs(bw(n)) for n in NPP)/np.median(nf):.1f}x the beta-weighted floor")

P("\nSIGN TEST at n = 48, where Lambda_1(48) = -2 log 48 < 0 so the line must be a POSITIVE real:")
a48 = bw(48)
P(f"   a_pred(48) = {-LF[48]/sqrt(48):+.5f};  measured {a48.real:+.5f} {a48.imag:+.5f}i;  "
  f"arg/pi = {math.atan2(a48.imag,a48.real)/pi:+.4f};  obs/pred = {a48.real/(-LF[48]/sqrt(48)):.4f}")

P("\nSHUFFLE control on every non-prime-power line (same 103 betas, random on-line gammas):")
rng = np.random.default_rng(20260812)
for n in NPP:
    pred = -LF[n]/sqrt(n)
    v = []
    for _ in range(600):
        gg = rng.choice(on, size=len(off), replace=False)
        ln = log(n)
        tot = np.exp(1j*on*ln).sum() + np.sum(
            (n**(off[:, 0]-0.5) + n**(0.5-off[:, 0]))*np.exp(1j*gg*ln))
        v.append(complex(tot/(W/(2*pi))).real/pred)
    v = np.array(v); true = bw(n).real/pred
    P(f"   n={n:>3}: true {true:+.4f};  shuffled {v.mean():+.4f} +- {v.std():.4f}"
      f"  -> z = {(true-v.mean())/v.std():+.1f} sigma")
