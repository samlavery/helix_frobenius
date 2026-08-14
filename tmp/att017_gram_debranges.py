"""ATTEMPT 017 -- de Branges phase / Gram's law x the exact tape arithmetic.

THE STRUCTURAL POINT (this is the pairing, not an analogy).  In de Branges theory a structure
function E(x) = |E(x)| exp(-i phi(x)) has a phase phi; Hermite-Biehler needs phi' > 0, and the
A-zeros sit at phi = 0 mod pi.  For zeta, zeta(1/2+it) = Z(t) exp(-i theta(t)), so the TAPE
COORDINATE u = theta/pi IS the de Branges phase, normalised; its A-zeros are the GRAM POINTS,
and monotonicity of the FULL phase is exactly GRAM'S LAW, whose failures are Rosser's rule
violations.  Attempt 010 gives the arithmetic perturbation in closed form, so the FAILURE RATE
is the observable to predict.

LITERATURE, read at source before designing (rule 6):
  * Hanga & Hughes, "Probabilistic models for Gram's Law", arXiv:1911.03190.  Models Gram's law
    from the Montgomery-Dyson/CUE conjecture and NOTHING ELSE -- they state they use no
    explicit-formula functions, no L-functions, no arithmetic sums.  Their N->infinity limits:
        E(0,J) = 0.17022   (empty Gram interval)
        E(1,J) = 0.66143   (Gram's law holds)
        E(2,J) = 0.16649   (two zeros)
    Their finite-N SU(N) refinement gives 0.721401 at N = 18.
  * Brent, van de Lune et al., counted data: 72.61% of the first 1.5e9 Gram intervals
    (up to t = 545,439,823.215) obey Gram's law.  N ~ log(T/2pi) = 18.28 there, matching N=18.
  * Trudgian, "Gram's Law Fails a Positive Proportion of the Time", arXiv:0811.0883
    (Acta Arith. 148 (2011) 225-256): a positive proportion of Gram intervals violate it.

SO THE OPEN QUESTION OUR INSTRUMENT IS BUILT FOR: the published model is arithmetic-blind by
construction, and at accessible heights the truth sits well above its asymptotic (0.7261 vs
0.66143).  Does the EXACT finite-height arithmetic content predict the observed rate and its
drift with height?

STATED NULL, pre-registered.  The measured Gram-law success rate is flat in T across
1e3..1e7, or it does not lie between the CUE asymptotic 0.66143 and the counted 0.7261, or the
exact-variance Gaussian model predicts it no better than the CUE asymptotic does.  Any of those
and the arithmetic adds nothing here.

NOTE ON SCOPE: this is a MEASUREMENT plus a literature comparison.  It is not a proof and it
does not improve a published constant.
"""
import numpy as np, math, sys
from math import log, pi, sqrt, erf

def P(*a): print(*a); sys.stdout.flush()

def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)
def dtheta(t):
    return 0.5*np.log(t/(2*pi)) - 1/(48*t**2) - 21/(5760*t**4)

def gram_point(M):
    """solve theta(g) = M pi by Newton; M integer >= 0."""
    t = np.full_like(np.asarray(M, float), 0.0)
    x = 2*pi*np.exp(1 + np.maximum(np.asarray(M, float), 1.0))  # crude start
    t = np.maximum(np.asarray(M, float), 1.0)
    t = 2*pi*np.exp(1 + t/1.0)
    # better start: invert theta ~ (t/2)log(t/2pi e)
    t = np.asarray(M, float)*0 + 20.0
    g = np.maximum(2*pi*np.exp(1.0), np.asarray(M, float))
    g = np.full(np.shape(M), 20.0)
    g = np.where(np.asarray(M) > 0, 2*pi*(np.asarray(M, float)+1)/np.log(np.asarray(M, float)+3), 20.0)
    for _ in range(200):
        g = g - (theta(g) - np.asarray(M, float)*pi)/dtheta(g)
        g = np.maximum(g, 7.0)
    return g

P("ATTEMPT 017 -- Gram's law rate from the cached zeros, vs the arithmetic-free CUE model.\n")

# --- exact finite-height variance of S from the prime sum (DC first, no asymptotic) ---
def sieve_lambda(X):
    X = int(X); is_c = np.zeros(X+1, bool); lam = np.zeros(X+1)
    for p in range(2, X+1):
        if not is_c[p]:
            q = p
            while q <= X:
                lam[q] = math.log(p)
                for m in range(2*q, X+1, q): is_c[m] = True
                q *= p
            for m in range(p*p, X+1, p): is_c[m] = True
    return lam

def var_S_exact(L, X=10**7, lam=None):
    """Var S = (1/(2 pi^2)) sum_{n<=X} Lambda(n)^2 / (n log^2 n), cut at log n = L."""
    if lam is None: lam = sieve_lambda(X)
    n = np.arange(2, len(lam))
    l = lam[2:]
    m = (l > 0) & (np.log(n) <= L)
    return float((l[m]**2/(n[m]*np.log(n[m])**2)).sum()/(2*pi*pi))

P("  building Lambda sieve to 1e7 ...")
LAM = sieve_lambda(10**7)

RUNS = [(1e3, 'att010_zeros_1e+03.npy'), (1e4, 'att010_zeros_1e+04.npy'),
        (1e5, 'att010_zeros_1e+05.npy'), (1e6, 'att010_zeros_1e+06.npy'),
        (1e7, 'att010_zeros_1e+07.npy')]

P(f"\n  {'T':>8}{'L':>8}{'Gram ivals':>12}{'k=0':>9}{'k=1':>9}{'k=2':>9}{'k>=3':>9}"
  f"{'sigma_exact':>13}{'Gauss P(S=0)':>14}")
rows = []
for T, f in RUNS:
    g = np.load(f)
    L = log((g[0] + g[-1])/2/(2*pi))
    M0 = int(math.ceil(theta(g[0])/pi)) + 1
    M1 = int(math.floor(theta(g[-1])/pi)) - 1
    Ms = np.arange(M0, M1)
    gp = gram_point(Ms)
    # verify the Gram points really solve theta(g)=M pi
    resid = np.max(np.abs(theta(gp) - Ms*pi))
    counts = np.diff(np.searchsorted(g, gp))
    tot = len(counts)
    k0 = float((counts == 0).mean()); k1 = float((counts == 1).mean())
    k2 = float((counts == 2).mean()); k3 = float((counts >= 3).mean())
    sig = sqrt(var_S_exact(L, lam=LAM))
    pg = erf(1/(2*sig*sqrt(2)))          # P(|N(0,sig^2)| < 1/2)
    P(f"  {T:>8.0e}{L:>8.3f}{tot:>12}{k0:>9.4f}{k1:>9.4f}{k2:>9.4f}{k3:>9.4f}"
      f"{sig:>13.4f}{pg:>14.4f}   [theta resid {resid:.1e}]")
    rows.append((T, L, tot, k0, k1, k2, k3, sig, pg))

P("\n  ANCHORS from the literature (fetched at source, not from memory):")
P("    Hanga-Hughes arXiv:1911.03190, CUE N->inf :  k=0 0.17022   k=1 0.66143   k=2 0.16649")
P("    Hanga-Hughes finite-N SU(N), N=18         :  k=1 0.721401")
P("    Brent / van de Lune et al. counted        :  k=1 0.7261  (1.5e9 intervals, t<5.45e8)")
P("    Trudgian arXiv:0811.0883                  :  a POSITIVE PROPORTION violate Gram's law")

P("\n  TREND TEST.  Does the measured rate fall with height toward the CUE asymptotic,")
P("  and does the exact-variance Gaussian track it better than the flat asymptotic does?")
P(f"  {'T':>8}{'L':>8}{'measured k=1':>14}{'CUE asympt':>12}{'|err|':>9}"
  f"{'Gauss(exact)':>14}{'|err|':>9}")
eC = []; eG = []
for T, L, tot, k0, k1, k2, k3, sig, pg in rows:
    P(f"  {T:>8.0e}{L:>8.3f}{k1:>14.4f}{0.66143:>12.4f}{abs(k1-0.66143):>9.4f}"
      f"{pg:>14.4f}{abs(k1-pg):>9.4f}")
    eC.append(abs(k1-0.66143)); eG.append(abs(k1-pg))
P(f"  mean |err|:  CUE asymptotic {np.mean(eC):.4f}    exact-variance Gaussian {np.mean(eG):.4f}")
P("\n  (The Gaussian model ignores the correlation between adjacent Gram points and is crude")
P("   BY CONSTRUCTION; it is here as a cheap arithmetic-aware baseline, not as a rival to the")
P("   SU(N) computation.  Read the comparison as: does knowing sigma exactly buy anything?)")
