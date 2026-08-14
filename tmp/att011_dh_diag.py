"""ATTEMPT 011, stage 2 -- WHY prediction (b) failed, and what the DH tape actually shows.

Stage 1 result: for DH the tape lines predicted from Lambda_f(n) (the Dirichlet coefficients
of -f'/f) are ABSENT at composite n -- obs/pred = 0.043 (n=6), 0.001 (14), 0.004 (21),
0.072 (26) at T=1e6 -- but DH's tape is NOT featureless: it has strong lines at
n = 2,3,4,7,9,11,16,19,29,31.  So the pre-registered null for (b) HOLDS and the
Lambda_f-based prediction was wrong.  This stage identifies the blocker.

=========================== PRE-REGISTERED, STAGE 2 ===========================
D1  IDENTITY.  Claim: a_n = 2 Re(A chi(n)) with chi the QUARTIC character mod 5 (chi(2)=i)
    and A = (1 - i*XI)/2; hence f = A L(s,chi) + conj(A) L(s,chibar), and on the critical
    line Z_DH = const * (Z_chi + Z_chibar).
    NULL: the identity fails at the 1e-12 level -> the decomposition story is wrong.

D2  GROWTH OF Lambda_f.  Prediction (b) used Landau's contour argument, which needs
    sum Lambda_f(n) n^{-s} to converge for some Re s slightly > 1.
    NULL (what is true if prediction (b) was well-founded): max_{n<=N} |Lambda_f(n)| grows
    like log N, as it does for zeta and chi_-3.
    PREDICT: POLYNOMIAL growth |Lambda_f(n)| ~ n^delta, delta > 0, because DH has zeros in
    sigma > 1 (Davenport-Heilbronn 1936), so -f'/f has poles there and the Dirichlet series
    of log f has abscissa of convergence > 1.  Then prediction (b) was never licensed.

D3  EXPLICIT sigma > 1 ZERO of DH, by argument-principle count + Newton.
    NULL: no zero with sigma > 1 in the searched box.

D4  H_avg, tested OUT OF SAMPLE.  From the T=1e5 data the DH line strengths look like
    Lambda_eff(n) = Lambda(n) * Re chi(n), i.e. present at n = +-1 mod 5, absent at +-2 mod 5.
    Tested here at T=1e6 on prime powers up to n = 60 (n = 33..60 never inspected before).
    NULL: no split by residue class mod 5 -- ratios at n = +-1 and n = +-2 look the same.

D5  FOURTH SPECIMEN: L(s,chi), chi quartic mod 5.  An Euler function with COMPLEX
    coefficients, |Lambda(n)chi(n)| = Lambda(n) for all (n,5)=1.
    PREDICT: FULL lines U Lambda(n)^2/(L^2 n) at EVERY n coprime to 5, including n = +-2 mod 5.
    NULL: lines only at n = +-1 mod 5 -- then the residue split of D4 is not caused by the
    linear combination and H_avg is wrong.

D6  OFF-LINE CENSUS.  Argument-principle winding of DH around sigma in [-1,2], t in a window,
    vs the sign-change count of Z_DH and vs delta theta/pi.
    NULL: winding == sign changes, i.e. the 11% tape deficit is an artifact of the zero finder.
===============================================================================
"""
import numpy as np, mpmath as mp, math, os, sys, time
mp.mp.dps = 30
def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'

A_DH = (4/np.sqrt(5))*np.sin(2*np.pi/5); B_DH = (4/np.sqrt(5))*np.sin(4*np.pi/5)
XI   = (np.sqrt(A_DH**2+B_DH**2)-A_DH)/B_DH
CHI4 = np.array([0, 1, 1j, -1j, -1])          # quartic chi mod 5, chi(2)=i  (index = n mod 5)
Acst = (1 - 1j*XI)/2

# ---------- D1 : the identity ----------------------------------------------
P("\nD1  IDENTITY  a_n = 2 Re(A chi(n)),  A = (1 - i XI)/2,  chi quartic mod 5.")
aDH = np.array([0.0, 1.0, XI, -XI, -1.0])
err = max(abs(aDH[r] - 2*np.real(Acst*CHI4[r])) for r in range(5))
P(f"    max_r |a_r - 2 Re(A chi(r))| = {err:.3e}    NULL would be O(1)")
tau_chi = sum(CHI4[r]*np.exp(2j*np.pi*r/5) for r in range(1,5))
eps_chi = tau_chi/(1j*np.sqrt(5))
PSI = np.angle(eps_chi)/2
P(f"    tau(chi) = {tau_chi:.6f}   eps = tau/(i sqrt5) = {eps_chi:.6f}  |eps| = {abs(eps_chi):.12f}")
P(f"    psi = arg(eps)/2 = {PSI:.9f} rad;   arg(A) = {np.angle(Acst):.9f} rad;  "
  f"arg(A) + psi = {np.angle(Acst)+PSI:.3e}   (must be 0 mod pi for Z_DH = c(Z_chi + Z_chibar))")

# ---------- fast vectorised Hurwitz zeta (Euler-Maclaurin) ------------------
_BER = [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730, 7/6]
def hurwitz(s, a, M=4000, J=7):
    """zeta(s,a) by Euler-Maclaurin; s complex array.  Gated below against mpmath."""
    s = np.asarray(s, complex); k = np.arange(M)
    base = (k + a)[None, :]
    tot = np.exp(-s[:, None]*np.log(base)).sum(axis=1)
    Ma = M + a
    tot += Ma**(1-s)/(s-1) + 0.5*Ma**(-s)
    poch = s.copy(); fac = 1.0
    for j in range(1, J+1):
        # term B_2j/(2j)! * (s)_{2j-1} * (M+a)^{-s-2j+1}
        fac = math.factorial(2*j)
        p = np.ones_like(s)
        for i in range(2*j-1): p = p*(s+i)
        tot += _BER[j-1]/fac * p * Ma**(-s-2*j+1)
    return tot

def f_DH(s):
    s = np.atleast_1d(np.asarray(s, complex))
    tot = np.zeros_like(s)
    for r, c in ((1, 1.0), (2, XI), (3, -XI), (4, -1.0)):
        tot += c*hurwitz(s, r/5.0)
    return 5.0**(-s)*tot

P("\n    gate on the vectorised Hurwitz/DH evaluator vs mpmath:")
tst = np.array([0.8+85.6993485j, 1.2+300.0j, -0.5+1000.0j, 2.0+1050.0j])
ref = []
for s in tst:
    ss = mp.mpc(complex(s))
    ref.append(complex(mp.power(5, -ss)*(mp.zeta(ss, mp.mpf(1)/5) + mp.mpf(str(XI))*mp.zeta(ss, mp.mpf(2)/5)
                                        - mp.mpf(str(XI))*mp.zeta(ss, mp.mpf(3)/5) - mp.zeta(ss, mp.mpf(4)/5))))
got = f_DH(tst)
for s, a, b in zip(tst, got, ref):
    P(f"      s={s}   |num - mpmath| = {abs(a-b):.3e}   |f| = {abs(b):.3e}")

# ---------- D2 : growth of Lambda_f ----------------------------------------
P("\nD2  GROWTH OF Lambda_f(n).  NULL (prediction (b) licensed): max|Lambda_f| ~ log N.")
def lamf_upto(N, coef, q):
    n = np.arange(N+1); a = np.zeros(N+1); a[1:] = np.array(coef)[n[1:] % q]
    S = a*np.log(np.maximum(n, 1)); L = np.zeros(N+1)
    for d in range(2, N+1):
        L[d] = S[d]
        if L[d] != 0.0:
            m = np.arange(2, N//d + 1)
            S[d*m] -= L[d]*a[m]
    return L
NMAX = 20000
for nm, coef, q in (('zeta', [1.0], 1), ('chi-3', [0.0,1.0,-1.0], 3),
                    ('DH', [0.0,1.0,XI,-XI,-1.0], 5)):
    t0 = time.time(); L = lamf_upto(NMAX, coef, q)
    run = np.maximum.accumulate(np.abs(L))
    pts = [10, 30, 100, 300, 1000, 3000, 10000, 20000]
    P(f"    {nm:>6}  max_{{n<=N}}|Lambda_f(n)| :  " +
      "  ".join(f"N={N}:{run[N]:.3g}" for N in pts) + f"   ({time.time()-t0:.0f}s)")
    x = np.log(np.arange(200, NMAX+1)); y = np.log(np.maximum(run[200:], 1e-300))
    sl = np.polyfit(x, y, 1)[0]
    P(f"            slope of log(max|Lambda_f|) vs log n on [200,{NMAX}]  =  {sl:.4f}"
      f"   (0 = log-like/Euler,  >0 = polynomial)")
    np.save(TMP+f'att011_lamfull_{nm}.npy', L)

# ---------- D3 : a DH zero with sigma > 1 -----------------------------------
P("\nD3  ZERO OF DH WITH sigma > 1.  NULL: none in the box.")
sg = np.linspace(1.0, 1.35, 36); tt = np.linspace(2.0, 260.0, 2600)
Sg, Tt = np.meshgrid(sg, tt, indexing='ij')
V = f_DH((Sg + 1j*Tt).ravel()).reshape(Sg.shape)
i0, j0 = np.unravel_index(np.abs(V).argmin(), V.shape)
P(f"    grid minimum |f| = {abs(V[i0,j0]):.4f} at s = {sg[i0]:.4f} + {tt[j0]:.4f}i")
z = complex(sg[i0], tt[j0])
for _ in range(60):
    h = 1e-6
    d = (f_DH(np.array([z+h]))[0] - f_DH(np.array([z-h]))[0])/(2*h)
    zn = z - f_DH(np.array([z]))[0]/d
    if not np.isfinite(zn): break
    z = zn
P(f"    Newton -> s = {z.real:.9f} + {z.imag:.9f}i   |f(s)| = {abs(f_DH(np.array([z]))[0]):.3e}")
P(f"    (Davenport-Heilbronn 1936: f has zeros in sigma > 1.  This is a numerical exhibit.)")

# ---------- D6 : argument-principle census ---------------------------------
P("\nD6  ARGUMENT-PRINCIPLE CENSUS of DH zeros in sigma in [-1,2], t in [1000,1100].")
def winding(f, s0, s1, npts=6000):
    a, b = s0.real, s1.real; c, d = s0.imag, s1.imag
    xs = np.linspace(a, b, npts); ys = np.linspace(c, d, npts)
    path = np.concatenate([xs + 1j*c, b + 1j*ys[1:], xs[::-1][1:] + 1j*d, a + 1j*ys[::-1][1:]])
    v = f(path); ang = np.angle(v)
    return np.sum(np.diff(np.unwrap(ang)))/(2*np.pi), np.abs(v).min()
t0 = time.time()
w, mn = winding(f_DH, -1+1000j, 2+1100j, 4000)
P(f"    winding number (= # zeros in the box) = {w:.4f}   min|f| on the contour = {mn:.3e}  "
  f"({time.time()-t0:.0f}s)")
# zeta control
def f_zeta(s):
    s = np.atleast_1d(np.asarray(s, complex)); return hurwitz(s, 1.0)
wz, mnz = winding(f_zeta, -1+1000j, 2+1100j, 4000)
P(f"    zeta control: winding = {wz:.4f}  min|zeta| = {mnz:.3e}")
P("    (zeta's box also contains the pole at s=1, which contributes -1 to the winding.)")
