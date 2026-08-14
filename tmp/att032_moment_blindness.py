"""ATTEMPT 032 -- is the Zeta23 two-moment ceiling a BLINDNESS OF THE INPUTS?

PAIRING
  HOUSE     : the theta-tape / Fejer form-factor double sum over zeros -- the same object
              measured exhaustively in attempts 010/016 -- used here as a DIRECT reader of
              the certificate's two INPUT moments, without ever building the Gram matrix.
  CLASSICAL : Zeta23's Gram compression (Prop 5.3, Thm 5.8, Remark 5.10) = Montgomery's
              first and second moments (Mon73; BGSTB24 Thm 1; GS26 Lemma 2).
  MECHANISM : Remark 5.10 says the zero-side reading of tr G~^2 is exactly the Fejer-kernel
              pair sum at COMPLEX differences gamma_rho - gamma_rho' = -i(rho - rho').  So the
              tape evaluates the certificate's inputs on any zero set, real or complex, and can
              compare specimens directly.

VERBATIM DEFINITIONS TAKEN FROM refs/zeta23_paper.txt (no reconstruction from values):
  (5.11) tr G~ = a L N(T,2T) + O(L sqrt X) = L N (1 + O(E_T))
  (5.12) tr G~^2 = 2 pi b L int_T^2T mu^2  +  (T/pi) sum_{n<=X} (Lambda(n)^2/n) g(log n)
                   + O(L l log l (l^2+X))
               = (T L / 2 pi) ( l1^2 + L^2/3 ) (1 + O(E_T))
  units (4.4): tr G^ = tr G~/(aL),   ||G^||_F^2 = tr G~^2/(aL)^2
  (5.9)  int Phi(x)^2 e^{ixy} dx = 2 pi g(y);  untapered a=b=1, Phi(x)^2=(sin(Lx/2)/(x/2))^2,
         g(y) = (L-|y|)_+.
  Rmk 5.10: tr G~^2 = sum_{rho,rho'} m m' Phi(gamma-gamma')^2, gamma-gamma' = -i(rho-rho');
         "for phi=1, lambda=1 and under RH, (5.12) reads
          sum_{gamma,gamma' in I} (sin((gamma-gamma')l/2)/((gamma-gamma')/2))^2 ~ (4/3) N l^2"
  Thm 5.8: E_T = w/L + (l^2+X) log l/(T l) + T^{lambda/2-1}.
  Rmk 7.2(ii) VERBATIM: "For Davenport-Heilbronn-type functions without Euler product,
         sum_{n<=x}|c(n)|^2 for the coefficients of -F'/F grows like x^{1+delta}
         (zeros in sigma > 1), Proposition 5.6 fails, and the certificate is empty."
  App C.4 VERBATIM: "the Davenport-Heilbronn and Epstein controls under-certified rather
         than over-certified, because their Dirichlet coefficients grow too fast for the
         mean-value step."

===================== PRE-REGISTERED NULLS (written before running) =====================

STATED NULL (the assignment's):  mu_1 and mu_2 DO differ between zeta and DH by more than the
  certificate's error budget E_T at some accessible lambda.  If the null HOLDS the inputs are
  not blind on DH and the ceiling is algebraic for that specimen.

G1 GATE / positive control (instrument).  The zero-side double Fejer sum on zeta's cached
   zeros must reproduce the INDEPENDENTLY computed prime-side value
        mu_2 = l_c/L + 2 S_2 /(L^2 l_c),   S_2 = sum_{n<=X} Lambda(n)^2 (L - log n)/n
   to within 10 percent at T >= 1e5 (Remark 5.9 warns convergence is only 1 - O(1/L):
   the paper itself quotes the finite-L taper factor 0.89 at L=4.4, 0.975 at L=16).
   NULL for G1: the two sides disagree by more than 10 percent -> instrument BROKEN, every
   number downstream is void.  This gate is computed FIRST.

G2 DH coefficient growth.  NULL: max_{n<=x}|Lambda_DH(n)| and sum_{n<=x}|Lambda_DH(n)|^2/n
   grow log-like (as for zeta), i.e. delta = 0 and Prop 5.6 does NOT fail for DH.
   The paper asserts delta > 0 but never gives delta.  We MEASURE delta.

G3 The separation.  Report mu_1, mu_2 for zeta and DH at matched (T, lambda, X), and the
   difference in units of E_T.  Decision rule fixed here: |mu_2^DH - mu_2^zeta|/mu_2^zeta
   <= E_T  =>  BLIND (hypothesis);  > E_T  =>  NOT BLIND (stated null holds).

G4 The depth law (this is the quantity the paper leaves unquantified).  DERIVED BEFORE
   RUNNING from Remark 5.10: an off-line pair {rho, 1-rhobar} at depth y = beta - 1/2 has
   gamma_rho - gamma_rho* = -2iy, so its two cross terms contribute
        Phi(-2iy)^2 / L^2 = sinh^2(L y)/(L y)^2      each,
   against 1 each for two on-line zeros at the same ordinate.  Excess per pair
        Delta(y) = 2 [ sinh^2(Ly)/(Ly)^2 - 1 ],   Delta(y) ~ (2/3)(Ly)^2 as y->0,
        Delta(y) ~ X^{2y}/(2 (Ly)^2) as Ly -> infinity   (matches the paper's "X^{|2beta-1|}").
   Blindness of mu_2 to a proportion p/N of off-line pairs at depth y:
        (p/N) Delta(y) <= E_T   <=>   y <= y*(T) := (1/L) sqrt( 3 E_T / (2 p/N) ).
   PRE-REGISTERED PREDICTION, to be checked by injection, not assumed:
   the measured shift in the zero-side mu_2 caused by replacing 2p on-line zeros by p
   off-line pairs of depth y equals (p/N) Delta(y) to within 2 percent, and the measured
   blinding depth agrees with y* to within 5 percent.
   NULL for G4: the injected shift does not follow Delta(y) -- then the depth law is wrong.
   NOISE-AUDIT SHAPE (rule 3): the control must fail by MISSING STRUCTURE.  At small y the
   injected specimen is a genuine off-line configuration and mu_2 must FAIL TO SEE IT
   (shift -> 0); at large y mu_2 must see it explosively.  A control that merely cancels
   better is rejected.

RESTATEMENT CHECK (rule 2).  mu_2 unfolds to Montgomery's second moment:
   mu_2 = (1/(L^2 N)) sum_{gamma,gamma'} (sin(L(gamma-gamma')/2)/((gamma-gamma')/2))^2
        = int_{-lambda}^{lambda} (lambda - |alpha|) F(alpha) dalpha / lambda ... (Rmk 5.10),
   i.e. the Fejer-weighted pair correlation.  NOT a new object.  Stated as such.
========================================================================================
"""
import numpy as np, math, sys, os, time
import mpmath as mp

def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'

# ------------------------------------------------------------------ DH definition
# a_n = 2 Re(A chi(n)), chi quartic mod 5 with chi(2)=i, A=(1-i XI)/2   (attempt 011, 3.4e-14)
A_DH = (4/np.sqrt(5))*np.sin(2*np.pi/5); B_DH = (4/np.sqrt(5))*np.sin(4*np.pi/5)
XI   = (np.sqrt(A_DH**2+B_DH**2)-A_DH)/B_DH
CHI4 = np.array([0, 1, 1j, -1j, -1])
Acst = (1 - 1j*XI)/2
A_COEF = np.array([2*np.real(Acst*CHI4[r]) for r in range(5)])   # a_n depends on n mod 5

# ------------------------------------------------------------------ Lambda_f by recursion
def lambda_f(N, coef_mod, q):
    """Lambda_f(n) from  a_n log n = sum_{k|n} Lambda_f(k) a_{n/k},  a_1 = 1."""
    a = np.array([coef_mod[n % q] for n in range(N+1)], float); a[0] = 0.0
    acc = np.zeros(N+1); acc[1:] = a[1:]*np.log(np.arange(1, N+1))
    Lam = np.zeros(N+1)
    for k in range(2, N+1):
        v = acc[k]
        Lam[k] = v
        if v != 0.0:
            m = np.arange(2, N//k + 1)
            acc[k*m] -= v*a[m]
    return Lam

def lambda_vm(N):
    """von Mangoldt Lambda(n), n<=N."""
    Lam = np.zeros(N+1)
    sieve = np.ones(N+1, bool); sieve[:2] = False
    for p in range(2, int(N**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    for p in np.nonzero(sieve)[0]:
        q = int(p); lp = math.log(p)
        while q <= N:
            Lam[q] = lp; q *= p
    return Lam

# ------------------------------------------------------------------ moments
def prime_side_mu2(Lam, X, L, l_c):
    """mu_2 = l_c/L + 2 S_2/(L^2 l_c),  S_2 = sum_{n<=X} Lam(n)^2 (L-log n)/n."""
    n = np.arange(1, min(int(X), len(Lam)-1)+1)
    ln = np.log(n)
    S2 = np.sum(Lam[n]**2 * np.maximum(L-ln, 0.0)/n)
    return l_c/L + 2*S2/(L*L*l_c), S2

def zero_side_mu2(g_in, g_all, L, chunk=400):
    """(1/(L^2 N_in)) sum_{g in inner} sum_{g' in all} (sin(L(g-g')/2)/((g-g')/2))^2 ,
       real ordinates only (the on-line case)."""
    tot = 0.0
    for i in range(0, len(g_in), chunk):
        d = g_in[i:i+chunk][:, None] - g_all[None, :]
        s = np.sin(L*d/2.0)
        with np.errstate(divide='ignore', invalid='ignore'):
            v = np.where(np.abs(d) < 1e-13, L*L, (s/(d/2.0))**2)
        tot += v.sum()
    return tot/(L*L*len(g_in))

# =====================================================================================
# STAGE G1 -- GATE: zero-side vs prime-side mu_2 on zeta.  Run FIRST.
# =====================================================================================
def stage_G1():
    P("="*86); P("G1  GATE / positive control: zero-side Fejer sum vs prime-side moment, zeta")
    P("    NULL: they disagree by >10% at T>=1e5  ->  instrument BROKEN, all downstream void.")
    P("="*86)
    sets = [('1e+03', TMP+'att010_zeros_1e+03.npy'), ('1e+04', TMP+'att010_zeros_1e+04.npy'),
            ('1e+05', TMP+'att010_zeros_1e+05.npy'), ('1e+06', TMP+'att010_zeros_1e+06.npy'),
            ('1e+07', TMP+'att010_zeros_1e+07.npy')]
    Xmax = 2_600_000
    Lam = lambda_vm(Xmax)
    P(f"    von Mangoldt sieved to n <= {Xmax}")
    P(f"    {'set':>7} {'Tc':>11} {'Nin':>6} {'l_c':>7} {'L':>7} {'lam':>5} "
      f"{'mu2 zero':>9} {'mu2 prime':>9} {'1/l+l/3':>9} {'rel diff':>9}")
    rows = []
    for nm, path in sets:
        z = np.load(path); z = np.sort(z)
        T0, T1 = z[0], z[-1]
        marg = 60.0
        g_in = z[(z > T0+marg) & (z < T1-marg)]
        if len(g_in) < 200: continue
        Tc = 0.5*(g_in[0]+g_in[-1])
        l_c = math.log(Tc/(2*math.pi))
        for lam in (1.0, 0.7):
            L = lam*l_c; X = math.exp(L)
            if X > Xmax: X = Xmax
            m2z = zero_side_mu2(g_in, z, L)
            m2p, S2 = prime_side_mu2(Lam, X, L, l_c)
            asym = 1.0/lam + lam/3.0
            rel = (m2z-m2p)/m2p
            rows.append((nm, Tc, len(g_in), l_c, L, lam, m2z, m2p, asym, rel))
            P(f"    {nm:>7} {Tc:11.4g} {len(g_in):6d} {l_c:7.3f} {L:7.3f} {lam:5.2f} "
              f"{m2z:9.4f} {m2p:9.4f} {asym:9.4f} {rel:+9.4f}")
    ok = [r for r in rows if r[1] >= 1e5]
    worst = max(abs(r[-1]) for r in ok)
    P(f"    worst |rel diff| at T>=1e5 : {worst:.4f}   gate = 0.10   "
      f"{'PASS' if worst <= 0.10 else 'FAIL'}")
    return worst <= 0.10, Lam

if __name__ == '__main__':
    t0 = time.time()
    ok, Lam = stage_G1()
    np.save(TMP+'att032_lam_vm.npy', Lam)
    P(f"[{time.time()-t0:.1f}s]")
