"""(A) CLIP <-> CONDUCTOR.  What the finite conductor N clips off the helix, and the law.

Model (AntihelixWindow.lean, bsd_weld.py):  the completed L of a curve of conductor N is the
double-ended incomplete-Gamma kernel

    Lambda(s) = sum_n a_n [ r_n^s Gamma(s, x_n)  +  eps r_n^{2-s} Gamma(2-s, x_n) ],
    x_n = 2 pi n / sqrt(N),   r_n = sqrt(N) / (2 pi n),   r_n x_n = 1.

The upper-incomplete-Gamma factor Gamma(s, x_n) is a GROWTH WINDOW (AntihelixWindow.upperGamma_*):
full weight Gamma(s) at x_n = 0, monotone dying, -> 0.  So phasor n is 'open' while x_n = O(1)
and 'clipped off' once x_n >> 1.  At the weld (central point) the surviving profile is
Gamma(1,x) = e^{-x} (upperGamma_one), so the weld amplitude of phasor n is

    A_n = |a_n| * 2 * r_n * e^{-x_n} = |a_n| * (sqrt(N)/(pi n)) * e^{-2 pi n / sqrt(N)}.

CLIP = the finite extent of the fiber (phasor count / arclength) set by this window.
QUESTION: does the clip scale like log N, sqrt(N), or N?

We measure two clip observables that depend ONLY on N (the geometric clip, a_n set to 1):
  * n_eff(thr): number of phasors with window e^{-x_n} >= thr  (x_n <= -ln thr).
  * arclen:  sum_n A_n with |a_n|=1  = sum_n (sqrt(N)/(pi n)) e^{-2 pi n/sqrt(N)}.
and fit the exponent p in observable ~ N^p over a wide conductor sweep.
Then overlay three real conductors (37a rk1, 389a rk2, 49a CM rk0).
"""
import math
import numpy as np

TWO_PI = 2 * math.pi


def n_eff(N, thr=0.01):
    """# phasors whose weld window e^{-x_n} >= thr, x_n = 2 pi n / sqrt(N)."""
    xcut = -math.log(thr)                 # e^{-x} >= thr  <=>  x <= -ln thr
    return xcut * math.sqrt(N) / TWO_PI   # n_max = xcut sqrt(N)/(2 pi)  (real-valued count)


def weld_arclength(N):
    """Pure-carrier arclength at the weld: sum_n (sqrt(N)/(pi n)) e^{-2 pi n/sqrt(N)}."""
    sq = math.sqrt(N)
    nmax = int(60 * sq / TWO_PI) + 5      # window dead past x~60
    n = np.arange(1, nmax + 1, dtype=np.float64)
    return float(np.sum((sq / (math.pi * n)) * np.exp(-TWO_PI * n / sq)))


def fit_exponent(Ns, vals):
    """least-squares slope of log val vs log N."""
    x = np.log(np.array(Ns, float)); y = np.log(np.array(vals, float))
    A = np.vstack([x, np.ones_like(x)]).T
    p, c = np.linalg.lstsq(A, y, rcond=None)[0]
    return p, math.exp(c)


print("=" * 78)
print("(A) CLIP <-> CONDUCTOR : geometric clip observables vs N")
print("=" * 78)

# wide conductor sweep (geometric clip depends only on N)
Ns = [10, 30, 100, 300, 1000, 3000, 1e4, 3e4, 1e5, 1e6, 1e7, 1e8]
neff = [n_eff(N, 0.01) for N in Ns]
arcs = [weld_arclength(N) for N in Ns]

p_neff, c_neff = fit_exponent(Ns, neff)
p_arc, c_arc = fit_exponent(Ns, arcs)

print(f"{'N':>10} {'sqrt(N)':>10} {'n_eff(1%)':>10} {'n_eff/sqrtN':>12} "
      f"{'arclen':>10} {'arclen/sqrtN':>13}")
for N, ne, ar in zip(Ns, neff, arcs):
    sq = math.sqrt(N)
    print(f"{N:>10.0f} {sq:>10.2f} {ne:>10.3f} {ne/sq:>12.5f} {ar:>10.3f} {ar/sq:>13.5f}")

print()
print(f"FIT  n_eff(1%)  ~  {c_neff:.4f} * N^{p_neff:.4f}      (pure sqrt(N): exponent 0.5)")
print(f"FIT  arclength  ~  {c_arc:.4f} * N^{p_arc:.4f}     (sqrt(N)*log correction: >0.5)")
print()
print("n_eff/sqrt(N) is CONSTANT  =>  live-phasor count clip is EXACTLY sqrt(N)-scaled.")
print("arclength carries a slow log factor: arclen ~ (sqrt(N)/pi)*ln(sqrt(N)/2pi) = ")
print("  (sqrt(N)/2pi)*ln N + O(sqrt N).  Leading power still 1/2, log-modulated.")
print()

# closed-form check of the log structure: sum_n e^{-2pi n/sqrt N}/n = -ln(1-e^{-2pi/sqrtN})
print("closed-form arclength check (geometric-series identity):")
for N in [1e4, 1e6, 1e8]:
    sq = math.sqrt(N)
    closed = (sq / math.pi) * (-math.log(1 - math.exp(-TWO_PI / sq)))
    print(f"  N={N:>10.0f}: measured {weld_arclength(N):>10.4f}  closed {closed:>10.4f}  "
          f"asymp (sqrt(N)/2pi)lnN = {(sq/TWO_PI)*math.log(N):>10.4f}")
print()

# ---- overlay real conductors (the clip is set by N; ranks vary) ----
print("=" * 78)
print("real conductors on the same clip law (n_eff at 1% window, x_cut = 4.605):")
print("=" * 78)
REAL = [("37a  rank1", 37), ("389a rank2", 389), ("49a  CM rk0", 49),
        ("5077a rk3", 5077), ("11a  rank0", 11)]
print(f"{'curve':>12} {'N':>6} {'sqrt(N)':>9} {'n_eff(1%)':>10} {'x_n=45 cut n_max':>17} "
      f"{'n_eff/sqrtN':>12}")
for tag, N in REAL:
    sq = math.sqrt(N)
    ne = n_eff(N, 0.01)
    nmax45 = 45 * sq / TWO_PI          # the literal kernel cutoff used in bsd_weld (x>45 break)
    print(f"{tag:>12} {N:>6} {sq:>9.3f} {ne:>10.3f} {nmax45:>17.2f} {ne/sq:>12.5f}")

print()
print("VERDICT: the conductor clips the fiber to a finite phasor bank whose live count is")
print("   n_eff = (x_cut/2pi) * sqrt(N),  linear in sqrt(N)  (NOT log N, NOT N).")
print("The two legs (helix strand n^s-side, antihelix n^{2-s}-side) each end at the SAME")
print("phasor index n_max ~ (x_cut/2pi) sqrt(N) where the incomplete-Gamma window closes;")
print("they meet at the weld (x_n->0 <=> the center).  clip-length = f(N) = c*sqrt(N).")
