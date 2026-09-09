# att641 — the HONEST rank-r ladder (the next step named in ledger 640).
#
# 1. Clebsch–Gordan assembly: λ_{Sym^r f}(p^a) = h_a(α^r, α^{r−2}, …, α^{−r}) = Σ_j c_r(a,j) λ_f(p^j) exactly
#    (U_j(cos θ) = λ_f(p^j)), hence for the level-1 family  Σ_f λ_{Sym^r f}(N) = Σ_{(j_p)} ∏_p c_r(a_p, j_p) T̃(∏ p^{j_p}),
#    T̃(n) = Tr T(n)/n^{(k−1)/2}: the rank-r geometric side is a FINITE combination of Hecke traces.
# 2. Lanes at every n' (Eichler–Selberg, be_instrument conventions): E (elliptic cells, two-clock angle),
#    Hy (two ends at different heights), U (coincident ends, n' a square), I (identity). Rank-r family
#    averages A^L_r(X) = (1/X) Σ_{N≤X} Σ_{n'} c_r(N,n') L(n').
# 3. The honest rank-r Poisson dual on the July machinery: poisson_dual.dual_profile(r=0, p, k=r) — the U_r
#    modulation OFF, the prime-power exponent = r, so the class variable is t/2p^{r/2}: the elliptic lane
#    of T(p^r) dualized. (The July ladder varied the modulation and held k = 1: a parity instrument, 640.)
#
# PRE-REGISTERED:
#   Q1 (identity, k = 12): Σ_{n'} c_r(N,n') τ(n')/n'^{11/2} = λ_{Sym^r Δ}(N) (from the Satake angles) for
#      r = 2,3,4, N ≤ 100, to 1e−9. Failure = bug in the assembly; nothing below is read.
#   Q1b (lanes): E+Hy+U+I = τ(n')/n'^{11/2} at every n' used, to 1e−9.
#   Q2 (lane DC law): rank 3 at X = 100 and rank 4 at X = 32 — the unipotent lane average is nonzero at
#      BOTH ranks (squares enter at odd rank through a ≥ 2), the elliptic DC mirrors it, and the readout
#      |A_r(X)| ≤ 0.1·max_L |A^L_r(X)| (the Sym^r AC, o(1) by Kim–Shahidi). Rank 2 at X = 1000 as control.
#   Q3 (honest rank-r dual, uniformity probe): for r ∈ {1,2,3} and p ∈ {2,3,5}: (i) anchor gap
#      g = |dual_0 + S − E(p^r)|/|E(p^r)| reported (the July truncation f ≤ 2, l ≤ 3 is expected to leave a
#      gap; PREDICTION: g > 0.05 at every (r,p) — the July absolute normalization is not anchored);
#      (ii) tail ratio ρ = M/|dual_0| (M = Σ_{ξ≠0}|dual_ξ|): PREDICTION: at r = 1 and r = 2, ρ stays ≤ 3
#      across p; at r = 3 ρ grows with p (the productivity boundary on honest terms). Refutation of
#      either half is a finding.
import math, sys, os, time
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import be_instrument as BE
import poisson_dual as PD

out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.append(s)
t0 = time.time()
K = 12

# ---------- Clebsch–Gordan: λ_{Sym^r}(p^a) in the U basis, exact ----------
def laurent_mul(A, B):
    C = {}
    for e1, c1 in A.items():
        for e2, c2 in B.items():
            C[e1 + e2] = C.get(e1 + e2, 0) + c1 * c2
    return {e: c for e, c in C.items() if c != 0}
def cg_coeffs(r, amax):
    """c_r(a, j): λ_{Sym^r}(p^a) = Σ_j c_r(a,j) U_j.  h_a of the multiset {α^{r−2i}} via ∏ 1/(1 − α^{e}T)."""
    exps = [r - 2 * i for i in range(r + 1)]
    # series in T with Laurent-poly coefficients: start with 1
    series = [dict({0: 1})] + [dict() for _ in range(amax)]
    for e in exps:
        # multiply by 1/(1 − α^e T) = Σ_n α^{en} T^n
        new = [dict() for _ in range(amax + 1)]
        for n1 in range(amax + 1):
            for n2 in range(amax + 1 - n1):
                term = laurent_mul(series[n1], {e * n2: 1})
                for ee, cc in term.items():
                    new[n1 + n2][ee] = new[n1 + n2].get(ee, 0) + cc
        series = [{e: c for e, c in d.items() if c != 0} for d in new]
    out_c = {}
    for a in range(amax + 1):
        poly = dict(series[a]); coeffs = {}
        while poly:
            top = max(poly); c = poly[top]
            coeffs[top] = c
            for i in range(top + 1):          # subtract c·U_top = c Σ_i α^{top−2i}
                ee = top - 2 * i
                poly[ee] = poly.get(ee, 0) - c
                if poly[ee] == 0: del poly[ee]
        out_c[a] = coeffs
    return out_c
CG = {r: cg_coeffs(r, 10) for r in (1, 2, 3, 4)}   # exponents a ≤ 10 (2^10 > 1000)
P("att641  Clebsch–Gordan c_r(a,j) (λ_{Sym^r}(p^a) = Σ_j c U_j):")
for r in (2, 3, 4):
    P("   r=%d: a=1 → %s ; a=2 → %s ; a=3 → %s" % (r, CG[r][1], CG[r][2], CG[r][3]))

# ---------- τ, Satake angles, λ_{Sym^r Δ} ----------
NMAX = 1000
tau_small = BE.tau_table_float(NMAX)
primes = [p for p in range(2, NMAX + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
def tau_pow(p, j):
    a = [1, int(tau_small[p])]
    for i in range(1, j): a.append(int(tau_small[p]) * a[i] - p ** 11 * a[i - 1])
    return a[j]
def factor(n):
    f = {}; m = n
    for p in primes:
        if p * p > m: break
        while m % p == 0: m //= p; f[p] = f.get(p, 0) + 1
    if m > 1: f[m] = f.get(m, 0) + 1
    return f
def tau_of(n):
    return math.prod(tau_pow(p, e) for p, e in factor(n).items()) if n > 1 else 1
def Ttilde(n):                      # normalized trace = λ_Δ(n) exactly (k = 12, dim 1)
    return tau_of(n) / n ** 5.5
theta = {p: math.acos(max(-1.0, min(1.0, int(tau_small[p]) / (2.0 * p ** 5.5)))) for p in primes}
def lam_symr_pa(r, p, a):           # from the Satake angle directly
    al = np.exp(1j * theta[p]); ev = [al ** (r - 2 * i) for i in range(r + 1)]
    # h_a via power-sum recursion (Newton): h_a = (1/a) Σ_{i=1}^a p_i h_{a−i}
    h = [1.0 + 0j]
    for m in range(1, a + 1):
        h.append(sum(sum(e ** i for e in ev) * h[m - i] for i in range(1, m + 1)) / m)
    return h[a].real
def lam_symr(r, N):
    return math.prod(lam_symr_pa(r, p, a) for p, a in factor(N).items()) if N > 1 else 1.0
def family_terms(r, N):             # list of (coefficient, n') with Σ_f λ_{Sym^r f}(N) = Σ coeff·T̃(n')
    terms = [(1, 1)]
    for p, a in factor(N).items():
        new = []
        for c0, n0 in terms:
            for j, c in CG[r][a].items():
                new.append((c0 * c, n0 * p ** j))
        terms = new
    return terms
# Q1
worst = 0.0
for r in (2, 3, 4):
    for N in range(1, 101):
        lhs = sum(c * Ttilde(n1) for c, n1 in family_terms(r, N))
        rhs = lam_symr(r, N)
        worst = max(worst, abs(lhs - rhs) / (abs(rhs) + 1))
P("Q1  Σ c_r(N,n') τ(n')/n'^{11/2} vs λ_{Sym^r Δ}(N) (r = 2,3,4; N ≤ 100): max rel diff = %.2e  %s" % (worst, "PASS" if worst < 1e-9 else "FAIL"))
assert worst < 1e-9

# ---------- Hurwitz table and lanes ----------
XR = {2: 1000, 3: 100, 4: 32}
need = set()
for r, X in XR.items():
    for N in range(1, X + 1):
        for c, n1 in family_terms(r, N): need.add(n1)
NPMAX = max(need); M = 4 * NPMAX
P("    distinct n' needed: %d, max n' = %d, Hurwitz table to N = %d" % (len(need), NPMAX, M))
t1 = time.time()
H = np.zeros(M + 1)
amax = int(math.isqrt(M // 3)) + 1
for a in range(1, amax + 1):
    Ns = []; ws = []
    for b in range(-a + 1, a + 1):
        cmin = a if b >= 0 else a + 1
        cmax = (M + b * b) // (4 * a)
        if cmax < cmin: continue
        cs = np.arange(cmin, cmax + 1)
        Ns.append(4 * a * cs - b * b)
        w = np.ones(len(cs))
        if b == 0: w[0] = 0.5
        if b == a: w[0] = 1.0 / 3.0
        ws.append(w)
    if Ns: H += np.bincount(np.concatenate(Ns), weights=np.concatenate(ws), minlength=M + 1)
H[0] = -1.0 / 12.0
P("    sieve %.0f s; check vs exact H(N), N ≤ 3000: %.1e" % (time.time() - t1, max(abs(H[N] - float(BE.hurwitz_class_number(N))) for N in range(1, 3001))))

def lanes_at(n, k=K):
    s = math.isqrt(n); sq = (s * s == n)
    tmax = math.isqrt(4 * n - 1)
    t = np.arange(-tmax, tmax + 1)
    th = np.arccos(np.clip(t / (2.0 * math.sqrt(n)), -1, 1)); si = np.sin(th)
    Uk = np.where(si > 1e-12, np.sin((k - 1) * th) / np.where(si > 1e-12, si, 1.0), (k - 1.0) * np.sign(t) ** (k - 2))
    E = -0.5 / math.sqrt(n) * np.sum(Uk * H[4 * n - t * t])
    hy = 0.0
    for d in range(1, s + 1):
        if n % d == 0 and d * d != n:
            hy += 2.0 * (d / math.sqrt(n)) ** (k - 1)
    Hy = -0.5 * hy
    U = -0.5 if sq else 0.0
    I = (k - 1) / (12.0 * s) if sq else 0.0
    return E, Hy, U, I
LANE = {n1: lanes_at(n1) for n1 in sorted(need)}
worst = max(abs(sum(LANE[n1]) - Ttilde(n1)) / (abs(Ttilde(n1)) + 1) for n1 in need)
P("Q1b lanes E+Hy+U+I vs τ(n')/n'^{11/2} at all %d n': max rel diff = %.2e  %s" % (len(need), worst, "PASS" if worst < 1e-9 else "FAIL"))
assert worst < 1e-9

# ---------- Q2: the lane DC law at ranks 2, 3, 4 ----------
P("Q2  rank-r family lane averages A^L_r(X) = (1/X) Σ_{N≤X} Σ_{n'} c_r(N,n') L(n')")
P("      r     X       A^E        A^Hy       A^U        A^I      readout A     |A|/max|A^L|   check Σλ_{Sym^r Δ}(N)/X")
for r, X in XR.items():
    for Xc in sorted(set([X // 4, X // 2, X])):
        acc = np.zeros(4)
        for N in range(1, Xc + 1):
            for c, n1 in family_terms(r, N):
                acc += c * np.array(LANE[n1])
        acc /= Xc
        A = acc.sum()
        direct = sum(lam_symr(r, N) for N in range(1, Xc + 1)) / Xc
        P("     %d  %5d   %+.5f   %+.5f   %+.5f   %+.5f   %+.3e     %.3e      %+.3e" % (r, Xc, acc[0], acc[1], acc[2], acc[3], A, abs(A) / np.abs(acc).max(), direct))

# ---------- Q3: the honest rank-r Poisson dual (modulation off, exponent = r) ----------
P("Q3  honest rank-r elliptic Poisson dual: dual_profile(r=0, p, k=r), f ≤ 2, l ≤ 3, ξ ≤ 16")
P("      r   p    n=p^r   |dual_0|     M=Σ|dual_ξ≠0|   |S|=|Σ dual_ξ≠0|   ρ=M/|dual_0|   E(p^r) exact   gap |d0+S−E|/|E|")
for r in (1, 2, 3):
    for p in (2, 3, 5):
        n1 = p ** r
        prof = PD.dual_profile(0, p, r, sign=-1, fmax=2, lmax=3, xi_max=16, nx=400)
        d0 = prof[0]; S = sum(v for xi, v in prof.items() if xi != 0); Mt = sum(abs(v) for xi, v in prof.items() if xi != 0)
        Eex = lanes_at(n1)[0] if n1 in LANE else lanes_at(n1)[0]
        # dual_profile's elliptic object is the UNNORMALIZED weight-12 elliptic sum? compare both normalizations
        gap = abs(d0 + S - Eex) / (abs(Eex) + 1e-300)
        P("     %d  %2d   %5d   %.4e    %.4e      %.4e        %.3f        %+.4e     %.2e" % (r, p, n1, abs(d0), Mt, abs(S), Mt / abs(d0) if abs(d0) > 0 else float("nan"), Eex, gap))
P("[done] %.0f s" % (time.time() - t0))
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "att641_results.txt"), "w").write("\n".join(out) + "\n")
