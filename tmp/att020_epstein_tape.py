"""ATTEMPT 020 -- Epstein zeta of a class-number-3 form x the theta-tape line amplitude.

THE RULE-4 GAP.  The tape instrument (attempt 010) was calibrated on zeta only.  Epstein-h>1
is this repo's other standing positive control and the one with genuinely off-line zeros
(Davenport-Heilbronn 1936).  It has never faced the instrument.

SPECIMEN.  D = -23, h = 3.  Principal form Q0 = x^2 + xy + 6y^2.  Its Epstein zeta is
Z_Q0(s) = sum' Q0(x,y)^{-s} = w * zeta_{K,1}(s), the PARTIAL Dedekind zeta of the principal
class of K = Q(sqrt(-23)), w = 2.  Since zeta_{K,1} = (1/3)(zeta_K + 2 L(f)) with f the
weight-one level-23 dihedral newform, it is a SUM of Euler products and therefore NOT an
Euler product.  Conjugation maps the class C to C^{-1} preserving norms, so the coefficients
are real and Lambda_Q(s) = Lambda_Q(1-s) with Lambda_Q(s) = (sqrt(23)/2pi)^s Gamma(s) Z_Q(s).

THE PREDICTION, and it is multi-point and quantitative.  Let a(n) = #{ideals of norm n in the
principal class} = r_{Q0}(n)/2, and define Lambda_1 by the standard recursion

        a(n) log n = sum_{d | n} Lambda_1(d) a(n/d),        a(1) = 1.

Then the tape line amplitude must be   K(tau_n) = U * Lambda_1(n)^2 / (L^2 n)   at
tau_n = log n / L, L = 2 dtheta_Q/dt at the window centre -- with Lambda_1 NOT supported on
prime powers.  Computed by hand from the recursion:
   Lambda_1(2) = 0        (2 splits, but its primes are non-principal)   -- zeta has log 2
   Lambda_1(3) = 0        (same)                                        -- zeta has log 3
   Lambda_1(4) = log 4    (the ideal (2))                               -- zeta has log 2
   Lambda_1(6) = 2 log 6  A NON-PRIME-POWER LINE, a(6)=2                -- zeta has 0
So the two functions must disagree at n = 2, 3, 4 and 6, in specified directions.

STATED NULL (pre-registered).  The Epstein tape shows the SAME line structure as zeta --
i.e. lines at n = 2, 3 with zeta's amplitudes and nothing at n = 6.  Then the tape instrument
cannot see the Euler product and attempt 011's whole premise is wrong.  Equally fatal: the
measured amplitudes fail to match U Lambda_1(n)^2/(L^2 n) at the n where Lambda_1 != 0.
"""
import numpy as np, mpmath as mp, sys, math, os
from math import log, pi

def P(*a): print(*a); sys.stdout.flush()
mp.mp.dps = 20

D = 23
c = 2*mp.pi/mp.sqrt(D)          # the self-dual scale:  h(y) = (c/y) h(c^2/y)
cf = float(c)

# ---------------------------------------------------------------- r_{Q0}(n) and a(n)
NMAX = 4000
r = np.zeros(NMAX+1, dtype=np.int64)
B = int(math.isqrt(4*NMAX//3)) + 3
for x in range(-3*B, 3*B+1):
    for y in range(-B, B+1):
        v = x*x + x*y + 6*y*y
        if 1 <= v <= NMAX: r[v] += 1
assert r[1] == 2 and r[2] == 0 and r[3] == 0 and r[4] == 2 and r[6] == 4, \
    (r[1], r[2], r[3], r[4], r[6])
a = r/2.0                                       # ideals of norm n in the principal class
P(f"specimen: Q0 = x^2+xy+6y^2, D=-23, h=3.   a(1..12) = {[int(a[i]) for i in range(1,13)]}")

# ---------------------------------------------------------------- Lambda_1 by recursion
NL = 64
Lam1 = np.zeros(NL+1)
for n in range(2, NL+1):
    s = a[n]*math.log(n)
    for d in range(2, n):
        if n % d == 0: s -= Lam1[d]*a[n//d]
    Lam1[n] = s/a[1]
P("Lambda_1 from the recursion (compare zeta's von Mangoldt):")
P(f"  {'n':>4}{'a(n)':>7}{'Lambda_1(n)':>14}{'zeta Lambda(n)':>16}")
def vonm(n):
    m = n
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m % p == 0:
            while m % p == 0: m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0
for n in (2,3,4,5,6,7,8,9,10,11,12,13,16,18,23,24,27,32,36,49):
    P(f"  {n:>4}{int(a[n]):>7}{Lam1[n]:>14.6f}{vonm(n):>16.6f}")

# ---------------------------------------------------------------- Lambda_Q on the line
NZ = [n for n in range(1, 60) if r[n] > 0]
def LamQ(t):
    """Lambda_Q(1/2+it) = sum_n r(n) * 2Re[(nc)^{-s} Gamma(s,nc)] - 1/(1/4+t^2), real."""
    s = mp.mpf(0.5) + 1j*mp.mpf(t)
    tot = mp.mpf(0)
    for n in NZ:
        x = n*c
        tot += r[n]*2*mp.re(x**(-s)*mp.gammainc(s, x))
    return tot - 1/(mp.mpf(0.25) + mp.mpf(t)**2)

def LamQ_gen(s):
    """general s, for the FE gate"""
    s = mp.mpc(s); tot = mp.mpf(0)*1j
    for n in NZ:
        x = n*c
        tot += r[n]*(x**(-s)*mp.gammainc(s, x) + x**(s-1)*mp.gammainc(1-s, x))
    return tot + 1/(s-1) - 1/s

P("\nGATES.")
for s in (mp.mpc('0.3','1.7'), mp.mpc('2.0','0.4'), mp.mpc('-0.7','3.1')):
    d = abs(LamQ_gen(s) - LamQ_gen(1-s))
    P(f"  FE |Lambda(s)-Lambda(1-s)| at s={s} : {mp.nstr(d,3)}")
ser = sum(mp.mpf(int(r[n]))*mp.mpf(n)**(-2) for n in range(1, NMAX+1) if r[n])
lhs = (mp.sqrt(D)/(2*mp.pi))**2*mp.gamma(2)*ser
P(f"  Dirichlet series check at s=2: incomplete-gamma {mp.nstr(LamQ_gen(2),12)}"
  f"  vs series {mp.nstr(lhs,12)}   |diff| {mp.nstr(abs(LamQ_gen(2)-lhs),3)}")
P(f"  Lambda_Q(1/2+i*37) imaginary part: {mp.nstr(mp.im(LamQ_gen(mp.mpf(0.5)+37j)),3)}  (must be 0)")

# ---------------------------------------------------------------- zeros
def theta_Q(t):
    t = np.asarray(t, float)
    return t*math.log(math.sqrt(D)/(2*pi)) + np.array(
        [float(mp.im(mp.loggamma(mp.mpf(0.5)+1j*mp.mpf(x)))) for x in np.atleast_1d(t)])

CACHE = 'att020_epstein_zeros.npy'
T0, T1, STEP = 10.0, 600.0, 0.08
if os.path.exists(CACHE):
    Z = np.load(CACHE); P(f"\nloaded {len(Z)} Epstein zeros from cache")
else:
    P(f"\nscanning Lambda_Q on [{T0},{T1}] at step {STEP} ...")
    ts = np.arange(T0, T1, STEP)
    vals = np.array([float(LamQ(t)) for t in ts])
    idx = np.nonzero(np.signbit(vals[:-1]) != np.signbit(vals[1:]))[0]
    P(f"  {len(idx)} sign changes; refining ...")
    lo, hi = ts[idx].copy(), ts[idx+1].copy()
    flo = vals[idx].copy()
    for _ in range(28):
        mid = (lo+hi)/2
        fm = np.array([float(LamQ(x)) for x in mid])
        left = np.signbit(flo) != np.signbit(fm)
        hi = np.where(left, mid, hi)
        lo = np.where(left, lo, mid)
        flo = np.where(left, flo, fm)
    Z = (lo+hi)/2
    np.save(CACHE, Z)
    P(f"  {len(Z)} zeros located")

th = theta_Q(Z)
exp_n = (theta_Q(np.array([T1]))[0] - theta_Q(np.array([T0]))[0])/pi
P(f"zeros {len(Z)}   theta_Q-count over the window {exp_n:.2f}   S-jump {exp_n-len(Z):+.2f}")

u = th/pi; u = u - u[0]; U = u[-1]; nz = len(u)
tc = float((Z[0]+Z[-1])/2)
Lq = 2*(math.log(math.sqrt(D)/(2*pi)) + float(mp.re(mp.digamma(mp.mpf(0.5)+1j*mp.mpf(tc)))))
P(f"tape: U={U:.1f}, zeros={nz}, L_Q (window centre, t={tc:.1f}) = {Lq:.4f}")
W = float(Z[-1]-Z[0])
P(f"window criterion R(n=6) = U log6 log(1+W/T)/L^2 = "
  f"{U*math.log(6)*math.log(1+W/T0)/Lq**2:.2f}   (must be << 1)")

def K_at(uu, taus):
    n = len(uu)
    return np.abs(np.exp(2j*pi*np.outer(np.asarray(taus,float), uu)).sum(axis=1))**2/n

P("\nTHE TEST.  measured K at tau_n = log n / L, against U Lambda_1(n)^2/(L^2 n).")
P(f"  {'n':>4}{'Lambda_1':>11}{'pred K':>10}{'obs K':>10}{'obs/pred':>10}   "
  f"{'zeta Lam':>10}{'zeta pred K':>13}")
ns = [2,3,4,5,6,7,8,9,10,11,12,13]
Kobs = K_at(u, [math.log(n)/Lq for n in ns])
for n, ko in zip(ns, Kobs):
    pr = U*Lam1[n]**2/(Lq*Lq*n)
    zp = U*vonm(n)**2/(Lq*Lq*n)
    ratio = f"{ko/pr:.3f}" if pr > 0.05 else "  --"
    P(f"  {n:>4}{Lam1[n]:>11.5f}{pr:>10.3f}{ko:>10.3f}{ratio:>10}   {vonm(n):>10.5f}{zp:>13.3f}")

c0 = K_at(u, np.arange(1, int(1.6*U))/U)
c0 = c0[(np.arange(1, int(1.6*U))/U > 1.2)]
P(f"\n  noise floor (control band tau in (1.2,1.6)): median {np.median(c0):.3f}"
  f"  99pct {np.percentile(c0,99):.3f}   [Exp(1) predicts 0.693 / 4.61]")
P("\n  READING.  n=6 is the decisive cell: Lambda_1(6)=log6 but zeta's Lambda(6)=0, so a line")
P("  there is impossible for an Euler product.  n=2,3 are the mirror test: zeta rings, the")
P("  Epstein class must be silent.  n=4 tests the AMPLITUDE (log4 vs log2, a factor 4 in K).")
