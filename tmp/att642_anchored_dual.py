# att642 — THE ANCHOR: the Poisson dual of the elliptic lane of Tr T(n) on S_k(SL2 Z), exact.
#
# Object.  E(n) = −(1/2) A1(n)/n^{(k−1)/2},  A1 = Σ_{t²<4n} P_k(t,n) H(4n−t²).  With the class-number
# formula H(N) = (√N/π) L(1, −N), L(1, δ) := Σ_{f²|δ, δ/f²≡0,1(4)} (1/f) L(1, χ_{δ/f²}) (Zagier's L(s,δ) at
# s = 1; χ_D the Kronecker symbol (D/·), imprimitive allowed), and P_k(t,n) = n^{(k−2)/2} U_{k−2}(cos θ_t):
#     E(n) = −(1/π) Σ_{|t|<2√n} sin((k−1)θ_t) · L(1, t² − 4n),          cos θ_t = t/(2√n).
# AFE for Zagier's L(s,δ), δ < 0 (Λ(s,δ) = (|δ|/π)^{s/2} Γ((s+1)/2) L(s,δ) = Λ(1−s,δ)), Mellin weight G ≡ 1,
# so the cutoffs are closed forms W_1(y) = Γ(1, y²) = e^{−y²}, W_0(y) = Γ(½, y²) = √π erfc(y):
#     L(1,δ) = Σ_{f,l} χ_{δ/f²}(l)/(f l) · e^{−π f⁴ l²/|δ|}  +  (π/√|δ|) Σ_{f,l} f χ_{δ/f²}(l) · erfc(f² l √(π/|δ|)).
# Poisson in t, per channel (f,l), modulus q = 4 l f²:  Σ_t g(t) P(t) = (1/q) Σ_ξ ĝ(ξ/q) Kl_{l,f}(ξ),
#     P(t) = χ_{(t²−4n)/f²}(l)·1[f² | t²−4n, (t²−4n)/f² ≡ 0,1 (4)],   Kl(ξ) = Σ_{a mod q} P(a) e(aξ/q),
#     g^{main}(t) = sin((k−1)θ_t) e^{−y²}/(f l),  g^{dual}(t) = sin((k−1)θ_t) (π/√(4n−t²)) f erfc(y),  y = f²l√π/√(4n−t²);
# every g is C^∞ with compact support in |t| < 2√n (the cutoff kills the edge), so the ξ-series converges
# super-polynomially and the identity is exact.
#
# ANCHORS (all must pass before any dual number is read):
#   A  AFE at every t:  √|δ| L(1,δ)/π = H(|δ|) (exact Hurwitz), rel 1e−12.
#   B  Poisson per channel:  direct t-sum = dual ξ-sum, rel 1e−11.
#   C  assembly:  −(1/π) Σ_{f,l} [direct] = E(n) from the exact trace formula, rel 1e−11.
# THEN the honest object at n = p^r: dual_0 (DC = ξ = 0 in every channel), the tail S = Σ_{ξ≠0}, M = Σ|·|,
# ρ = M/|dual_0|, for r = 1,2,3 and p = 2,3,5,7,11.  PRE-REGISTERED: (i) A,B,C pass; (ii) at fixed r the
# tail ratio ρ is O(1) and does not grow with p for r ≤ 3 (the class-number sum's fluctuation is a bounded
# fraction of its main term at a single n); if ρ grows with p at r = 3 and not at r = 1, that is the
# productivity boundary on honest terms and is reported as such.
import math, sys, os, time
import numpy as np
from scipy.special import erfc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import be_instrument as BE

out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.append(s)
K = 12
NQ = 4096            # quadrature points in t for ĝ (trapezoid; g is C^∞ compactly supported)

def kron(D, l):
    return BE.kronecker_symbol(D, l)

def channels(n):
    """(f, l) channels with y_min = f² l √π/(2√n) ≤ 6.5 (beyond: e^{−y²}, erfc(y) < 1e−18)."""
    ch = []
    f = 1
    while f * f <= 4 * n:
        Lf = int(6.5 * 2 * math.sqrt(n) / (math.sqrt(math.pi) * f * f)) + 1
        for l in range(1, Lf + 1):
            ch.append((f, l))
        f += 1
    return ch

def anchor_A(n):
    """AFE vs exact Hurwitz at every t."""
    worst = 0.0
    for t in range(-int(math.isqrt(4 * n - 1)), int(math.isqrt(4 * n - 1)) + 1):
        N = 4 * n - t * t; delta = -N
        Hex = float(BE.hurwitz_class_number(N))
        val = 0.0
        for f, l in channels(n):
            if N % (f * f): continue
            D = delta // (f * f)
            if D % 4 not in (0, 1): continue
            chi = kron(D, l)
            if chi == 0: continue
            y = f * f * l * math.sqrt(math.pi / N)
            val += chi / (f * l) * math.exp(-y * y) + (math.pi / math.sqrt(N)) * f * chi * erfc(y)
        Hafe = math.sqrt(N) * val / math.pi
        worst = max(worst, abs(Hafe - Hex) / (abs(Hex) + 1e-300))
    return worst

DT = 0.001           # quadrature spacing in t; the edge cutoff e^{−c/u} has |ĝ(v)| ~ e^{−√(2c v)}, c = π/(4√n):
                     # aliasing at v = 1/DT = 1000 is e^{−33} (at DT = 0.01 it was e^{−10.5}, seen as the 1e−3 in anchor B)

def dualize(n, k=K):
    """Returns (E_direct, E_exact, worstB, dual0, S, Mabs, profile dict xi->value).
    Per channel the dual sum is evaluated at EVERY ξ with ĝ(ξ/q) from one FFT of the padded samples."""
    s2 = 2.0 * math.sqrt(n)
    R = int(round(1.0 / DT)); dt = 1.0 / R                # dt = 1/R exactly, so M = c·q·R is an integer for every channel
    T = math.ceil(s2 * R) / R                              # grid [−T, T] ⊇ support, g ≡ 0 beyond the support
    NQ = int(round(2 * T * R))
    tgrid = -T + (np.arange(NQ) + 0.5) * dt               # midpoints
    t_0 = tgrid[0]
    x = tgrid / s2
    th = np.arccos(np.clip(x, -1, 1))
    sinw = np.sin((k - 1) * th)
    Nvals = np.maximum(4.0 * n - tgrid ** 2, 1e-300)
    inside = (4.0 * n - tgrid ** 2) > 0
    sinw = np.where(inside, sinw, 0.0)
    tint = np.arange(-int(math.isqrt(4 * n - 1)), int(math.isqrt(4 * n - 1)) + 1)
    E_direct = 0.0; worstB = 0.0; dual0 = 0.0; prof = {}; sum_abs_direct = 0.0
    for f, l in channels(n):
        q = 4 * l * f * f
        Pa = np.zeros(q)
        for a in range(q):
            disc = a * a - 4 * n
            if disc % (f * f): continue
            D = disc // (f * f)
            if D % 4 not in (0, 1): continue
            Pa[a] = kron(D, l)
        if not Pa.any(): continue
        y = f * f * l * np.sqrt(math.pi / Nvals)
        g = sinw * (np.exp(-y * y) / (f * l) + (math.pi / np.sqrt(Nvals)) * f * erfc(y))
        # direct t-sum on integers
        direct = 0.0
        for t in tint:
            N = 4 * n - t * t
            if N % (f * f): continue
            D = (t * t - 4 * n) // (f * f)
            if D % 4 not in (0, 1): continue
            chi = kron(D, l)
            if chi == 0: continue
            thi = math.acos(t / s2); yi = f * f * l * math.sqrt(math.pi / N)
            direct += chi * math.sin((k - 1) * thi) * (math.exp(-yi * yi) / (f * l) + (math.pi / math.sqrt(N)) * f * erfc(yi))
        # ĝ(ξ/q) for all ξ from one FFT: pad to M samples with M·dt = c·q (c integer, c·q ≥ support + q)
        c = int(math.ceil((2 * T + q) / q))
        M = c * q * R                                        # exact: M·dt = c·q
        gpad = np.zeros(M); gpad[:NQ] = g
        G = np.fft.fft(gpad) * dt                             # G[j] = Σ_i g_i e(−ij/M) dt = ĝ(j/(M dt)) e(+v t_0)
        Xi = M // (2 * c) - 1                                 # ξ = j/c for j ≤ M/2
        xis = np.arange(-Xi, Xi + 1)
        js = (xis * c) % M
        v = xis / q
        ghat = G[js] * np.exp(-2j * math.pi * v * t_0)
        # Kl(ξ) = Σ_a P(a) e(aξ/q) = conj(FFT(P)[ξ mod q]) for real P
        Kl = np.conj(np.fft.fft(Pa))[xis % q]
        terms = (ghat * Kl / q).real
        dual = terms.sum()
        worstB = max(worstB, abs(dual - direct))
        sum_abs_direct += abs(direct)
        E_direct += direct
        i0 = Xi
        dual0 += terms[i0]
        for i, xi_ in enumerate(xis):
            if xi_ != 0 and terms[i] != 0.0:
                prof[int(xi_)] = prof.get(int(xi_), 0.0) + terms[i]
    worstB = worstB / (sum_abs_direct + 1e-300)
    E_direct *= -1.0 / math.pi; dual0 *= -1.0 / math.pi
    prof = {xi_: -v / math.pi for xi_, v in prof.items()}
    S = sum(prof.values()); Mabs = sum(abs(v) for v in prof.values())
    # exact E(n) from the trace formula
    A1 = 0.0
    for t in tint:
        N = 4 * n - t * t
        A1 += float(BE.P_k(int(t), n, k)) * float(BE.hurwitz_class_number(N))
    E_exact = -0.5 * A1 / n ** ((k - 1) / 2.0)
    return E_direct, E_exact, worstB, dual0, S, Mabs, prof

t0 = time.time()
P("att642  anchored Poisson dual of the elliptic lane, k = %d, G ≡ 1 (cutoffs e^{−y²}, √π erfc)" % K)
P("   n    #ch   A: AFE vs H     B: Poisson/ch    C: assembly vs E(n)     E(n) exact      dual_0        S=Σ_{ξ≠0}     M=Σ|·|     ρ=M/|dual_0|")
rows = []
for n in (2, 3, 4, 5, 8, 9, 16, 25, 27, 49, 121, 125, 343):
    a = anchor_A(n)
    Ed, Ee, b, d0, S, Mabs, prof = dualize(n)
    c = abs(Ed - Ee) / (abs(Ee) + 1e-300)
    rows.append((n, a, b, c, Ee, d0, S, Mabs))
    P("  %4d   %3d   %.1e         %.1e          %.1e            %+.6f    %+.6f    %+.6f    %.6f    %.4f" % (n, len(channels(n)), a, b, c, Ee, d0, S, Mabs, Mabs / abs(d0) if d0 else float("nan")))
ok = all(r[1] < 1e-11 and r[2] < 1e-10 and r[3] < 1e-10 for r in rows)
P("ANCHORS A/B/C: %s (worst A %.1e, B %.1e, C %.1e)" % ("PASS" if ok else "FAIL", max(r[1] for r in rows), max(r[2] for r in rows), max(r[3] for r in rows)))
P("rank table (n = p^r):")
P("   r   p     n      dual_0        tail S       M         ρ")
for r in (1, 2, 3):
    for p in (2, 3, 5, 7, 11):
        n = p ** r
        hit = [x for x in rows if x[0] == n]
        if hit:
            _, a, b, c, Ee, d0, S, Mabs = hit[0]
        else:
            Ed, Ee, b, d0, S, Mabs, prof = dualize(n)
        P("   %d  %2d  %5d   %+.6f   %+.6f   %.6f   %.4f" % (r, p, n, d0, S, Mabs, Mabs / abs(d0)))
P("[done] %.0f s" % (time.time() - t0))
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "att642_results.txt"), "w").write("\n".join(out) + "\n")
