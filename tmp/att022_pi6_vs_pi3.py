"""ATTEMPT 022 -- harmonizing S(t) at pi/6 instead of pi/3 (Sam's request).

WHAT IS ALREADY FORECLOSED, stated before measuring.
 (1) THEOREM.  universal.tex thm:harmonic-family-S / Lean Sgap_pi_div = 0, Sgap_pi6_one:
     EVERY harmonic scale pi/m realizes the event mark at m cells, once per closed 2m-cell
     monodromy loop, so S_{pi/m,1}(t) = S_ev(t) for every m >= 1.  The REGISTRATION GAP at
     pi/6 is identically the pi/3 one.  Not re-tested here; it is compiled.
 (2) MEASURED 2026-08-12.  Zero cell-phases are uniform on harmonic cells: pi/3 +0.53 sigma,
     pi/6 +0.46 sigma, with the pi/3 excess flipping sign across a decade of height.

WHAT IS NOT FORECLOSED, and is what this attempt does.  The tape SPECTRUM at the cell
frequency has never been evaluated: attempt 010 ran to tau <= 1.6 and attempt 016 to tau <= 3,
so tau = 6 (the pi/6 cell) has never been looked at, and tau = 3 only inside a broad band mean.

THE COLLAPSE THAT MAKES THIS EXACT.  On the tape u_k = k - 3/2 - S(gamma_k), so for INTEGER m
    e^{2 pi i m u_k} = e^{-2 pi i m S(gamma_k)}   (m*k and 3m/2 contribute a constant phase),
hence
    K(m) = n | < e^{-2 pi i m S(gamma)} > |^2 .
So "is there a pi/m cell" IS "are the fractional parts of m*S equidistributed".  With S
asymptotically Gaussian of variance V (Selberg), < e^{-2 pi i m S} > ~ e^{-2 pi^2 m^2 V}, so
    K(m) ~ n * exp(-4 pi^2 m^2 V) ,
falling off in m^2 -- brutally.  pi/3 is m=3, pi/6 is m=6, so the pi/6 signal is the pi/3 one
raised to the power 4.

PAIRING.  house: the theta-tape + the compiled harmonic-family registration law
(Sgap_pi_div = 0) x classical: Weyl equidistribution / Selberg's CLT read as a form factor at
integer frequency.  MECHANISM: the theorem says the registration ledger cannot distinguish
pi/6 from pi/3; the form factor at tau = m is the one observable the theorem does not cover,
and the CLT predicts its exact size.

STATED NULL (pre-registered).  K(3) and K(6) both sit at the noise floor and are
indistinguishable from the CUE control -- i.e. pi/6 yields nothing pi/3 does not.  The
ALTERNATIVE, with its own number: K(m) = n exp(-4 pi^2 m^2 V) with V the measured Var S, in
which case m=1 is visible and everything above it is dead, and the pi/6 "cell" is dead by a
factor exp(-4 pi^2 (36-9) V) ~ 10^{-46} relative to pi/3.
"""
import numpy as np, math, sys, os
from math import pi, log

def P(*a): print(*a); sys.stdout.flush()
rng = np.random.default_rng(2026)

def theta_rs(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)

SETS = [('T=1e3','att010_zeros_1e+03.npy'), ('T=1e4','att010_zeros_1e+04.npy'),
        ('T=1e5','att010_zeros_1e+05.npy'), ('T=1e6','att010_zeros_1e+06.npy'),
        ('T=1e7','att010_zeros_1e+07.npy'), ('long [14,2e4]','att019_zeros_to20k.npy')]

def K_at(u, taus):
    return np.abs(np.exp(2j*pi*np.outer(np.asarray(taus,float), u)).sum(axis=1))**2/len(u)

# CUE control: eigenphases of a Haar-random unitary, unfolded to density 1
def cue_u(N):
    z = (rng.standard_normal((N,N)) + 1j*rng.standard_normal((N,N)))/math.sqrt(2)
    q, r = np.linalg.qr(z)
    q = q*(np.diag(r)/np.abs(np.diag(r)))
    ph = np.sort(np.angle(np.linalg.eigvals(q)))
    return ph*N/(2*pi)

MS = [1,2,3,4,5,6,7,8,12]
P("K(m) = n |<exp(-2 pi i m S)>|^2   -- the pi/m cell frequency.  pi/3 is m=3, pi/6 is m=6.\n")
P(f"  {'set':>14}{'n':>7}{'VarS':>8}   " + "".join(f"{'m='+str(m):>10}" for m in MS))
rows = []
for name, f in SETS:
    if not os.path.exists(f): continue
    g = np.load(f)
    th = theta_rs(g); u = th/pi
    k = np.arange(1, len(g)+1)
    S = (k - 1.5) - (u - u[0]) - (u[0] - np.floor(u[0]))*0   # S up to an additive integer
    S = S - S.mean()
    V = float(S.var())
    uu = u - u[0]
    Kv = K_at(uu, MS)
    rows.append((name, len(g), V, Kv))
    P(f"  {name:>14}{len(g):>7}{V:>8.4f}   " + "".join(f"{x:>10.3f}" for x in Kv))

P("\n  IDENTITY GATE.  K(m) computed from the tape vs n|<exp(-2 pi i m S)>|^2 from S directly:")
for name, f in SETS[:3]:
    if not os.path.exists(f): continue
    g = np.load(f); u = theta_rs(g)/pi; uu = u - u[0]
    k = np.arange(1, len(g)+1); S = (k - 1.5) - uu
    a = K_at(uu, [1,3,6])
    b = [len(g)*abs(np.exp(-2j*pi*m*S).mean())**2 for m in (1,3,6)]
    P(f"    {name:>10}  tape {a[0]:.4f} {a[1]:.5f} {a[2]:.5f}   from S {b[0]:.4f} {b[1]:.5f} {b[2]:.5f}")

P("\n  CUE CONTROL (no arithmetic, same n).  K(m) must be at the Exp(1) floor for ALL m:")
for N in (4000,):
    for trial in range(3):
        cu = cue_u(N)
        Kc = K_at(cu - cu[0], MS)
        P(f"    CUE({N}) #{trial+1}   " + "".join(f"{x:>10.3f}" for x in Kc))

P("\n  ALTERNATIVE, pre-registered:  K(m) = n exp(-4 pi^2 m^2 VarS).")
P(f"  {'set':>14}" + "".join(f"{'m='+str(m):>12}" for m in (1,2,3,6)))
for name, n, V, Kv in rows:
    pred = [n*math.exp(-4*pi*pi*m*m*V) for m in (1,2,3,6)]
    P(f"  {name:>14}" + "".join(f"{p:>12.3e}" for p in pred))
P(f"  {'measured':>14}" + "".join("" for _ in (1,)))
for name, n, V, Kv in rows:
    P(f"  {name:>14}" + "".join(f"{Kv[MS.index(m)]:>12.3e}" for m in (1,2,3,6)))

P("\n  FINE SCAN around tau = 3 and tau = 6 (is a peak sitting slightly off the integer?)")
for name, f in (SETS[4], SETS[5]):
    if not os.path.exists(f): continue
    g = np.load(f); u = theta_rs(g)/pi; uu = u - u[0]; U = uu[-1]
    for centre in (3.0, 6.0):
        tt = centre + np.arange(-40, 41)/U
        kk = K_at(uu, tt)
        i = int(np.argmax(kk))
        P(f"    {name:>14}  near tau={centre:.0f}: max K = {kk[i]:.3f} at tau = {tt[i]:.5f}"
          f"   (offset {(tt[i]-centre)*U:+.1f}/U);  K at exact integer = {kk[40]:.3f}")

P("\n  READING.  pi/3 is m=3 and pi/6 is m=6; the predicted ratio of their cell signals is")
P("  exp(-4 pi^2 (36-9) VarS), i.e. the pi/6 cell is the pi/3 cell to the fourth power.")
