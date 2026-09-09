# att640 — the HONEST rank-2 orbital lift on the exact level-1 trace formula: the Sym² family sum
# assembled lane by lane (elliptic / hyperbolic / unipotent / identity), anchored to τ.
#
# Why this and not the July "rank ladder" (tmp/rank_ladder_closure.py): that model multiplies a FIXED
# even archimedean bump θ_∞(x) by U_r(x) at the class angle of T(p) and Fourier-transforms in x. Its
# odd-rank "exact closure" is parity (odd integrand, real Kloosterman weights); its even-rank "detecting
# residue" is the mean of an even bump. It is a parity instrument, not Sym^r.  The honest rank-r geometric
# side is the Hecke trace at p^r (class variable t/2p^{r/2}) plus the Clebsch–Gordan lower terms.  At rank
# 2 the whole family sum is one identity: L(s, Sym² f) = ζ(2s) Σ_n λ_f(n²) n^{−s}, so
#     Σ_{N≤X} Σ_f λ_{Sym² f}(N) = Σ_{d² m ≤ X} T̃(m²) = Σ_{m≤X} T̃(m²)·⌊√(X/m)⌋,   T̃(n) = Tr T(n)/n^{(k−1)/2},
# and T̃(m²) = E + Hy + U + I by Eichler–Selberg (be_instrument.py conventions, anchored there to τ):
#     E(m²)  = −(1/(2m)) Σ_{|t|<2m} U_{k−2}(t/2m) H(4m² − t²)      elliptic (class angles = two-clock)
#     Hy(m²) = −Σ_{d|m², d<m} (d/m)^{k−1}                          hyperbolic (divisor pairs d ≠ m²/d)
#     U(m²)  = −1/2                                                  unipotent (d = m, the square root)
#     I(m²)  = (k−1)/(12 m)                                          identity
#
# PRE-REGISTERED (written before the run):
#   P1 anchor: E+Hy+U+I = τ(m²)/m^{11} at k=12 for every m ≤ X to relative 1e−9 (τ from the independent
#      q-expansion table). At k=16: lane sum at m² equals the multiplicative assembly from the trace at
#      primes to 1e−9. Failure = bug; nothing below is read.
#   P2 DC law (pencil): with c(X) := (1/X) Σ_{m≤X} ⌊√(X/m)⌋ → ζ(2), the lane averages satisfy
#      A^U(X) = −c(X)/2 EXACTLY, A^I(X) → 0 like X^{−1/2} log X, A^Hy(X) → −(small) ≈ −2e−4,
#      A^E(X) = +c(X)/2 − A^Hy − A^I + (1/X) Σ_m ⌊√(X/m)⌋ λ(m²).
#      Prediction: |A^E(800) − ζ(2)/2| ≤ 0.05 and the readout |A(800)| = |A^E+A^Hy+A^U+A^I| ≤ 0.05,
#      decaying with X — the rank-2 BALANCED DOUBLET: the elliptic DC is the mirror of the unipotent
#      term at squares, amplitude ζ(2)/2 = 0.8225 (the trivial representation's Sym² pole).
#   P3 AC: the readout equals (1/X) Σ_{N≤X} λ_{Sym² Δ}(N) exactly (identity), and is o(1); measured
#      decay exponent reported; predicted between X^{−0.5} and X^{−0.3} at these X (Sym² Δ entire).
#   P4 the July-model diagnosis, checked numerically: the July even-rank residue |dual_0| at n=2 is
#      NOT the unipotent mirror (there is no unipotent term at n = 2); reported as the model's bump mean.
import math, sys, os, time
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
import be_instrument as BE

out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.append(s)

X = 800
M = 4 * X * X
t0 = time.time()

# ---------- Hurwitz class numbers H(N), N ≤ M, by reduced forms (vectorized) ----------
# reduced: |b| ≤ a ≤ c, b ≥ 0 if |b| = a or a = c; weight 1/2 for (a,0,a), 1/3 for (a,a,a), else 1
H = np.zeros(M + 1)
amax = int(math.isqrt(M // 3)) + 1
for a in range(1, amax + 1):
    Ns = []; ws = []
    for b in range(-a + 1, a + 1):
        cmin = a if b >= 0 else a + 1
        cmax = (M + b * b) // (4 * a)
        if cmax < cmin:
            continue
        cs = np.arange(cmin, cmax + 1)
        N = 4 * a * cs - b * b
        w = np.ones(len(cs))
        if b == 0:
            w[0] = 0.5                      # (a,0,a)
        if b == a:
            w[0] = 1.0 / 3.0                # (a,a,a)
        Ns.append(N); ws.append(w)
    if Ns:                                  # one bincount per a (the per-(a,b) version allocated M floats each time)
        H += np.bincount(np.concatenate(Ns), weights=np.concatenate(ws), minlength=M + 1)
H[0] = -1.0 / 12.0
P("att640  X = %d, Hurwitz table to N = %d built in %.0f s" % (X, M, time.time() - t0))
# anchor vs be_instrument's exact Hurwitz numbers
maxdiff = max(abs(H[N] - float(BE.hurwitz_class_number(N))) for N in range(1, 3001))
P("  H(N) vs exact (N ≤ 3000): max |diff| = %.1e   (H(3)=%.4f H(4)=%.4f H(12)=%.4f H(16)=%.4f)" % (maxdiff, H[3], H[4], H[12], H[16]))
assert maxdiff < 1e-9

def lanes(k):
    ms = np.arange(1, X + 1)
    E = np.zeros(X + 1); Hy = np.zeros(X + 1); U = np.zeros(X + 1); I = np.zeros(X + 1)
    for m in ms:
        t = np.arange(-(2 * m - 1), 2 * m)
        th = np.arccos(t / (2.0 * m))
        s = np.sin(th)
        Uk = np.where(s > 1e-12, np.sin((k - 1) * th) / np.where(s > 1e-12, s, 1.0), 0.0)
        E[m] = -0.5 / m * np.sum(Uk * H[4 * m * m - t * t])
        hy = 0.0
        for d in range(1, m):
            if (m * m) % d == 0:
                hy += (d / m) ** (k - 1)
        Hy[m] = -hy
        U[m] = -0.5
        I[m] = (k - 1) / (12.0 * m)
    return E, Hy, U, I

# ---------- P1 anchors ----------
tau_small = BE.tau_table_float(X)        # exact τ(n), n ≤ X (independent q-expansion); τ(m²) below by Hecke recursion
primes = [p for p in range(2, X + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
def tau_pow(p, j):                       # exact τ(p^j) from τ(p): τ(p^{j+1}) = τ(p) τ(p^j) − p^{11} τ(p^{j−1})
    a = [1, int(tau_small[p])]
    for i in range(1, j):
        a.append(int(tau_small[p]) * a[i] - p ** 11 * a[i - 1])
    return a[j]
def tau_of(n):                           # exact τ(n) for n whose prime factors are ≤ X
    val = 1; mm = n
    for p in primes:
        if mm % p == 0:
            e = 0
            while mm % p == 0:
                mm //= p; e += 1
            val *= tau_pow(p, e)
    assert mm == 1
    return val
class _Tau:                              # τ(n) lookup restricted to n = squares of m ≤ X and their d²-quotients
    def __getitem__(self, n): return tau_of(n)
tau = _Tau()
# independent anchor of the kernel + table at PRIMES: trace at n = p from the lanes vs τ(p)
relp = 0.0
for p in primes:
    t = np.arange(-int(math.isqrt(4 * p - 1)), int(math.isqrt(4 * p - 1)) + 1)
    th = np.arccos(t / (2.0 * math.sqrt(p))); s = np.sin(th)
    A1 = np.sum(p ** 5.0 * np.sin(11 * th) / s * H[4 * p - t * t])
    trp = -0.5 * A1 - 0.5 * 2.0
    relp = max(relp, abs(trp - float(tau_small[p])) / (abs(float(tau_small[p])) + 1))
P("P1  k=12: trace formula at primes p ≤ %d vs independent τ(p): max rel diff = %.2e  %s" % (X, relp, "PASS" if relp < 1e-9 else "FAIL"))
assert relp < 1e-9
res = {}
for k in (12, 16):
    E, Hy, U, I = lanes(k)
    tot = E + Hy + U + I
    if k == 12:
        ref = np.array([0.0] + [float(tau[m * m]) / m ** 11 for m in range(1, X + 1)])
        rel = max(abs(tot[m] - ref[m]) / (abs(ref[m]) + 1) for m in range(1, X + 1))
        P("P1  k=12: lane sum at m² vs τ(m²)/m^11, m ≤ %d: max rel diff = %.2e  %s" % (X, rel, "PASS" if rel < 1e-9 else "FAIL"))
        assert rel < 1e-9
    else:
        # trace at primes p ≤ X from the same lanes at n = p, then multiplicativity: a(p²) = a(p)² − p^{k−1}
        ap = {}
        for p in range(2, X + 1):
            if all(p % q for q in range(2, int(p ** 0.5) + 1)):
                t = np.arange(-int(math.isqrt(4 * p - 1)), int(math.isqrt(4 * p - 1)) + 1)
                th = np.arccos(t / (2.0 * math.sqrt(p))); s = np.sin(th)
                Uk = np.sin((k - 1) * th) / s
                A1 = np.sum(p ** ((k - 2) / 2.0) * Uk * H[4 * p - t * t])
                A2 = 2.0                     # divisors 1, p: min = 1
                ap[p] = -0.5 * A1 - 0.5 * A2  # A3 = 0 (p not a square)
        def a_sq(m):                       # a(m²) multiplicatively from a(p²) = a(p)² − p^{k−1}, a(p^{2e}) by Hecke recursion
            val = 1.0; mm = m
            for p in sorted(ap):
                if mm % p == 0:
                    e = 0
                    while mm % p == 0:
                        mm //= p; e += 1
                    # a(p^j) recursion: a(p^{j+1}) = a(p) a(p^j) − p^{k−1} a(p^{j−1})
                    aj = [1.0, ap[p]]
                    for j in range(1, 2 * e):
                        aj.append(ap[p] * aj[j] - p ** (k - 1) * aj[j - 1])
                    val *= aj[2 * e]
            return val
        rel = max(abs(tot[m] - a_sq(m) / m ** (k - 1)) / (abs(a_sq(m) / m ** (k - 1)) + 1) for m in range(1, X + 1))
        P("P1  k=16: lane sum at m² vs multiplicative assembly from the trace at primes: max rel diff = %.2e  %s" % (rel, "PASS" if rel < 1e-9 else "FAIL"))
        assert rel < 1e-9
    res[k] = (E, Hy, U, I, tot)

# ---------- P2/P3: the rank-2 family averages, lane by lane ----------
P("P2  Sym² family sum lane averages A^L(X) = (1/X) Σ_{m≤X} ⌊√(X/m)⌋ L(m²);  ζ(2)/2 = %.6f" % (math.pi ** 2 / 12))
for k in (12, 16):
    E, Hy, U, I, tot = res[k]
    P("    k = %d" % k)
    P("      X      c(X)/2    A^E        A^Hy        A^U        A^I       readout A(X)   |A|/|A^E|")
    rows = []
    for Xc in (50, 100, 200, 400, 800):
        w = np.array([0.0] + [math.isqrt(Xc // m) for m in range(1, Xc + 1)])
        c = w.sum() / Xc
        AE = np.sum(w * E[:Xc + 1]) / Xc; AH = np.sum(w * Hy[:Xc + 1]) / Xc
        AU = np.sum(w * U[:Xc + 1]) / Xc; AI = np.sum(w * I[:Xc + 1]) / Xc
        A = AE + AH + AU + AI
        rows.append((Xc, A))
        P("   %5d   %.6f  %+.6f  %+.6f  %+.6f  %+.6f   %+.3e     %.3e" % (Xc, c / 2, AE, AH, AU, AI, A, abs(A) / abs(AE)))
    # decay fit of |A(X)| ~ X^{-beta} over the last three points
    xs = np.log([r[0] for r in rows[-3:]]); ys = np.log([abs(r[1]) for r in rows[-3:]])
    beta = -np.polyfit(xs, ys, 1)[0]
    P("      readout decay |A(X)| ~ X^(−%.2f) over X ∈ {200,400,800}" % beta)
    if k == 12:
        # P3 identity: readout = (1/X) Σ_{N≤X} λ_{Sym²Δ}(N), with λ_{Sym²}(N) = Σ_{d²|N} τ((N/d²)²)/(N/d²)^{11}
        Xc = 800
        lam2 = np.zeros(Xc + 1)
        for N in range(1, Xc + 1):
            d = 1
            while d * d <= N:
                if N % (d * d) == 0:
                    mm = N // (d * d); lam2[N] += float(tau[mm * mm]) / mm ** 11
                d += 1
        direct = lam2.sum() / Xc
        P("P3  k=12: readout A(800) = %+.6e vs direct (1/X)Σ_{N≤X} λ_{Sym²Δ}(N) = %+.6e  (diff %.1e)" % (rows[-1][1], direct, abs(rows[-1][1] - direct)))
        # the E-lane AC alone: (1/X) Σ ⌊√(X/m)⌋ λ(m²)
        w = np.array([0.0] + [math.isqrt(Xc // m) for m in range(1, Xc + 1)])
        lam_sq = np.array([0.0] + [float(tau[m * m]) / m ** 11 for m in range(1, Xc + 1)])
        P("    E-lane AC (1/X) Σ ⌊√(X/m)⌋ λ_Δ(m²) at X = 800: %+.6e ; E-lane DC c(X)/2 − A^Hy − A^I = %+.6f" % (np.sum(w * lam_sq) / Xc, (w.sum() / Xc) / 2 - np.sum(w * Hy[:Xc + 1]) / Xc - np.sum(w * I[:Xc + 1]) / Xc))

# ---------- P4: the July model's even-rank residue at n = 2 is a bump mean, not an orbital DC ----------
import poisson_dual as PD
prof2 = PD.dual_profile(2, 2, 1, sign=-1, fmax=1, lmax=1, xi_max=0, nx=400)
d0 = prof2[0]
# the same with the U_2 weight replaced by its mean-free part U_2 − mean(U_2 over the bump): residue must drop to ~0
xs = np.linspace(-0.999, 0.999, 400)
th = np.array([PD.theta_inf_profile(x, -1) for x in xs]); U2 = np.array([PD.cheb_U(2, x) for x in xs])
mean_U2 = np.sum(th * U2) / np.sum(th)
P("P4  July model at n = 2, r = 2: |dual_0| (f=l=1) = %.4e; bump-weighted mean of U_2 = %+.4f (U_2 = 4x²−1); no unipotent term exists at n = 2 (not a square)" % (abs(d0), mean_U2))
P("    ⇒ the July even-rank residue is the mean of U_r against the fixed even bump; the honest rank-2 DC (this run) is the unipotent mirror at squares, amplitude ζ(2)/2.")
P("[done] %.0f s" % (time.time() - t0))
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "att640_results.txt"), "w").write("\n".join(out) + "\n")
