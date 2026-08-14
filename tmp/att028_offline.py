"""ATTEMPT 028 -- STAGE 4.  Is F's 20.9% census deficit really OFF-LINE zeros, and does the
BETA-WEIGHTED Landau sum restore the non-prime-power lines that the ordinate-only sum lost?

The campaign's closed finding says the adaptive variable is ordinate-only and therefore reads
sum_rho x^{beta} x^{i gamma} only when beta == 1/2 collapses the two; measured on zeta-prime's
2D zero set, ordinate-only failed by 20-30x while beta-weighted held at 2%.  Stage 3 measured
exactly that failure on F.  This stage supplies the beta's.

PRE-REGISTERED (before running):
  A. argument principle over the rectangle sigma in [-1,2], t in [T0,T1] must give a zero count
     equal to the theta_Q count to within ~1 (that is the Riemann-von Mangoldt statement).  If it
     instead equals the ON-LINE sign-change count, then the deficit was missed on-line zeros and
     the engine, not the specimen, is at fault.
  B. NULL for the beta-weighted test: including the off-line zeros with their true beta does NOT
     restore the lines -- i.e. after adding them, |obs/pred - 1| stays > 0.5 at n = 6, 12, 18.
     Then the residual is not the off-line zeros and something else is wrong.
  C. positive control: the SAME beta-weighted machinery run on L(f), whose zeros are all on the
     line, must return the same answer as the ordinate-only run (nothing to add).
"""
import numpy as np, math, sys, time
from math import pi, log, sqrt
from scipy.special import loggamma
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_engine import D, C, coefficients, Engine, theta_Q, vonmangoldt_like

def P(*a): print(*a); sys.stdout.flush()

T0, T1 = 10.0, 200.0
DELTA = 0.012
a1, aC, dK, bf = coefficients(6000)


class GEngine(Engine):
    """adds Lambda(sigma+it) off the critical line, from the same precomputed phi grid."""
    def __init__(self, coef, pc, **kw):
        super().__init__(coef, pc, **kw)
        self.phi = (self.G.reshape(-1))*np.exp(-self.v/2)   # undo the e^{v/2}; keeps trap weight
        self._cache = {}

    def _sig(self, sigma):
        if sigma not in self._cache:
            w = self.phi*np.exp(self.v*sigma)
            self._cache[sigma] = w.reshape(self.K1, self.K2)
            if len(self._cache) > 60: self._cache.pop(next(iter(self._cache)))
        return self._cache[sigma]

    def _dft(self, Gm, t):
        A = np.exp(1j*t*self.h*self.K2*np.arange(self.K1))
        B = np.exp(1j*t*self.h*np.arange(self.K2))
        return A @ (Gm @ B)

    def _Pk_gen(self, s, k, conj=False):
        dp = np.conj(self.Dphi) if conj else self.Dphi
        return sum(math.comb(k, j)*s**(k-j)*dp[j] for j in range(k+1))

    def lam_gen(self, sigma, t):
        """Lambda(sigma+it) * e^{pi t/2}."""
        h = self.h
        s = sigma + 1j*t
        IA = h*self._dft(self._sig(sigma), t)
        IA += (h**2/12)*self._Pk_gen(s, 1) - (h**4/720)*self._Pk_gen(s, 3) \
              + (h**6/30240)*self._Pk_gen(s, 5)
        s2 = 1 - s
        IB = h*np.conj(self._dft(self._sig(1-sigma), t))     # conj(phi) e^{v(1-s)} sum
        IB += (h**2/12)*self._Pk_gen(s2, 1, True) - (h**4/720)*self._Pk_gen(s2, 3, True) \
              + (h**6/30240)*self._Pk_gen(s2, 5, True)
        # fold e^{pi t/2} in analytically: |e^{i a s}| = |e^{-i a (1-s)}| = e^{-a t}, so both
        # prefactors times e^{pi t/2} are e^{delta t} in modulus.  (Computing e^{pi t/2}
        # separately overflows double for t > 450.)
        a = self.alpha
        pa = np.exp(1j*a*sigma)
        pb = np.exp(-1j*a*(1-sigma))
        return (pa*IA + pb*IB + self.pc*(pb/(s-1) - pa/s))*math.exp(self.delta*t)

    def Fval(self, sigma, t):
        """Lambda(s)/[(sqrt23/2pi)^s Gamma(s)] = the Dirichlet series itself; zeros are clean."""
        s = sigma + 1j*t
        lg = loggamma(s)
        return self.lam_gen(sigma, t)*np.exp(-lg - s*log(sqrt(D)/(2*pi)) - pi*t/2)


engF = GEngine(a1, 0.5, delta=DELTA)
engf = GEngine(bf, 0.0, delta=DELTA)

# ---------------------------------------------------------------- gate the off-line evaluator
P("gate: lam_gen(0.5,t) must reproduce lam_scaled(t) (the on-line engine), and")
P("      Lambda(sigma+it) = Lambda(1-sigma-it)* must hold (functional equation + reality):")
for sg, t in ((0.5, 37.4), (0.5, 151.9), (1.3, 61.2), (-0.4, 88.8), (1.9, 133.1)):
    g = engF.lam_gen(sg, t)
    if sg == 0.5:
        P(f"   sigma={sg} t={t}: lam_gen {g.real:.12g} (im {g.imag:.2e})  "
          f"lam_scaled {engF.lam_scaled(t):.12g}")
    fe = engF.lam_gen(1-sg, -t) if False else np.conj(engF.lam_gen(1-sg, t))
    # Lambda(s)=Lambda(1-s) and Lambda(s-bar)=conj Lambda(s)  =>  Lambda(sigma+it) = conj Lambda(1-sigma+it)
    P(f"   sigma={sg:>5} t={t:>7}: |Lambda(s) - conj Lambda(1-sigma+it)| / |Lambda| = "
      f"{abs(g-fe)/abs(g):.2e}")

# ---------------------------------------------------------------- A. argument principle
def winding(eng, S0, S1, Ta, Tb, nv, nh):
    pts = []
    pts += [(S0 + (S1-S0)*k/nh, Ta) for k in range(nh)]
    pts += [(S1, Ta + (Tb-Ta)*k/nv) for k in range(nv)]
    pts += [(S1 - (S1-S0)*k/nh, Tb) for k in range(nh)]
    pts += [(S0, Tb - (Tb-Ta)*k/nv) for k in range(nv)]
    vals = np.array([eng.lam_gen(sg, t) for sg, t in pts])
    vals = np.append(vals, vals[0])
    ph = np.angle(vals)
    d = np.diff(ph)
    jump = np.max(np.abs(np.where(np.abs(d) > pi, np.abs(d) - 2*pi, d)))
    d = np.where(d > pi, d - 2*pi, np.where(d < -pi, d + 2*pi, d))
    return d.sum()/(2*pi), jump

exp_n = (theta_Q(np.array([T1]))[0] - theta_Q(np.array([T0]))[0])/pi
zF = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_F.npy')
zf = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_Lf.npy')
onF = zF[(zF > T0) & (zF < T1)]
onf = zf[(zf > T0) & (zf < T1)]
P(f"\nA. argument principle on sigma in [-1,2], t in [{T0},{T1}]")
P(f"   theta_Q count = {exp_n:.2f};  on-line sign changes: F {len(onF)}, L(f) {len(onf)}")
for nm, eng in (('F', engF), ('L(f)', engf)):
    t0 = time.time()
    for nv, nh in ((4000, 200), (8000, 400)):
        N, jump = winding(eng, -1.0, 2.0, T0, T1, nv, nh)
        P(f"   {nm:>5}: nv={nv} -> N = {N:.4f}   (max phase step {jump:.3f} rad, must be < pi)"
          f"   [{time.time()-t0:.0f}s]")
