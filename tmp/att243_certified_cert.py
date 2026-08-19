#!/usr/bin/env python3
"""
att243 — CERTIFIED floor certificate for unconditional Weil positivity at
support L = 0.90 and 0.95 (past Yoshida/CC log 2 = 0.6931), both parity sectors.

Chain (Lemmas A/B proven in-session; this file executes the finite check with
an explicit error ledger):
  Q(G) = 2P+P- + (1/2pi) int sigma |Ghat|^2,  sigma = d(r) - sqrt2*log2*cos(r log2)
  d(r) = psi(1/4) - log(pi) + sum_{n>=0} b_n(r),
  b_n(r) = (r^2/4) / ((n+1/4) ((n+1/4)^2 + r^2/4))     [ALL TERMS >= 0, monotone]
  psi(1/4) = -gamma - 3 log 2 - pi/2.
  Lemma C: b_n increasing in r => d increasing => inf_{r>=R2} sigma >= d(R2) - sqrt2 log2 =: s0.
  Lemma B: Q >= <G, (s0 I +- Pole + Band(sigma - s0; R2)) G>;  PSD of that operator
  (per parity sector) implies Weil positivity at support L.

RIGOR BUDGET (all explicit, printed):
  * series tail: monotone bracket  int_N^inf b dx <= tail <= int_{N-1}^inf b dx,
    int_T^inf b dx = (1/2) log(1 + r^2/(4(T+1/4)^2))       [closed form]
  * derivative lemmas: |d'| <= psi'(1/4)/2 <= 8.58, |d''| <= (3/2) sum (n+1/4)^-3 <= 97,
    |phat_m| <= sqrt(2a), |phat_m'| <= a sqrt(2a), |phat_m''| <= a^2 sqrt(2a)   [Cauchy-Schwarz]
  * midpoint rule error per entry <= (R2 h^2/24) * F2bound
  * Legendre tail (m > Mhead): |j_m(x)| <= x^m/(2m+1)!!  => blocks < 1e-20
  * eigen bottom: mpmath dps-30 eigsy on the center matrix + Weyl for enclosure widths
"""
import numpy as np, math, sys
from fractions import Fraction
from scipy.special import spherical_jn
import mpmath as mp

mp.mp.dps = 30

# ---------------------------------------------------------------- constants
GAMMA  = 0.5772156649015328606
LOG2   = math.log(2.0)
LOGPI  = math.log(math.pi)
PSI14  = -GAMMA - 3.0 * LOG2 - math.pi / 2.0
C2     = math.sqrt(2.0) * LOG2                      # sqrt2 log2 = 0.980258...
DCONST = PSI14 - LOGPI
R2     = 45.3
NSER   = 3000            # series terms on the quadrature grid
H      = 8e-6            # midpoint-rule step
D1B, D2B = 8.60, 97.0    # |d'| <= psi'(1/4)/2 = 8.5991 <= 8.60; |d''| <= 97 (lemma)
S1B = D1B + C2 * LOG2            # |sigma'|
S2B = D2B + C2 * LOG2 * LOG2     # |sigma''|

def tail_int(T, r2over4):
    """int_T^inf b(x) dx = 1/2 log(1 + (r^2/4)/(T+1/4)^2)  (vector in r)."""
    return 0.5 * np.log1p(r2over4 / (T + 0.25) ** 2)

def d_enclosure(r, nser):
    """certified bracket [d_lo, d_hi] via partial sum + monotone tail bracket."""
    r2o4 = 0.25 * r * r
    s = np.zeros_like(r)
    for n in range(nser):
        y = n + 0.25
        s += r2o4 / (y * (y * y + r2o4))
    lo = DCONST + s + tail_int(nser, r2o4)
    hi = DCONST + s + tail_int(nser - 1, r2o4)
    pad = 1e-12          # float accumulation pad (nser * eps * term-scale, generous)
    return lo - pad, hi + pad

def d_at(rval, nser):
    """scalar-r version, vectorized over n (for large nser)."""
    r2o4 = 0.25 * rval * rval
    y = np.arange(nser) + 0.25
    s = float(np.sum(r2o4 / (y * (y * y + r2o4))))
    lo = DCONST + s + float(tail_int(nser, np.float64(r2o4)))
    hi = DCONST + s + float(tail_int(nser - 1, np.float64(r2o4)))
    pad = 1e-11
    return lo - pad, hi + pad

# ---------------------------------------------------------------- self-tests
def self_tests():
    print("== SELF-TESTS ==", flush=True)
    from scipy.special import digamma
    for rv in [1.0, 9.0, 20.0, 45.3]:
        lo, hi = d_at(rv, 100000)
        ref = float(np.real(digamma(0.25 + 0.5j * rv))) - LOGPI
        ok = lo - 1e-9 <= ref <= hi + 1e-9
        print(f"  d({rv:5.1f}) bracket [{lo:.10f},{hi:.10f}] width {hi-lo:.1e}  "
              f"scipy {ref:.10f}  contained={ok}")
    for (n, x) in [(10, 15.0), (20, 21.0), (30, 21.5), (40, 21.5)]:
        sp = spherical_jn(n, x)
        mpv = float(mp.sqrt(mp.pi / (2 * x)) * mp.besselj(n + 0.5, x))
        print(f"  j_{n}({x}) scipy {sp:.6e} mpmath {mpv:.6e} rel "
              f"{abs(sp-mpv)/max(abs(mpv),1e-300):.1e}")

# ---------------------------------------------------------------- pole vectors
def legendre_moments(max_m, max_pow):
    """exact Fractions: x^k = sum_m c[k][m] P_m(x); returns c up to max_pow."""
    c = [{0: Fraction(1)}]
    for k in range(max_pow):
        new = {}
        for m, cm in c[-1].items():
            # x P_m = ((m+1) P_{m+1} + m P_{m-1}) / (2m+1)
            new[m + 1] = new.get(m + 1, Fraction(0)) + cm * Fraction(m + 1, 2 * m + 1)
            if m >= 1:
                new[m - 1] = new.get(m - 1, Fraction(0)) + cm * Fraction(m, 2 * m + 1)
        c.append(new)
    return c

def pole_vector_float(a, ms, parity):
    """same as above but float assembly of the exact series (rounding ~1e-15):
    p_m = sum_k a^{k+1} sqrt((2m+1)/(2a)) * (2 c_k[m]/(2m+1)) / (2^k k!)   over
    k even (cosh) or odd (sinh), k <= KMAX; tail bound printed."""
    KMAX = 28
    c = legendre_moments(max(ms) + 1, KMAX + 1)
    p = np.zeros(len(ms))
    for i, m in enumerate(ms):
        acc = 0.0
        for k in range(KMAX + 1):
            if parity == "even" and k % 2 != 0: continue
            if parity == "odd" and k % 2 != 1: continue
            cm = c[k].get(m)
            if cm is None: continue
            acc += (a ** (k + 1)) * float(cm) * (2.0 / (2 * m + 1)) \
                   / (2.0 ** k * math.factorial(k))
        p[i] = math.sqrt((2 * m + 1) / (2 * a)) * acc
    # series tail bound: sum_{k>KMAX} a^{k+1} sqrt((2m+1)/2a) * (2/(2m+1)) / (2^k k!)
    tail = (a ** (KMAX + 2)) / (2.0 ** (KMAX + 1) * math.factorial(KMAX + 1)) * 4.0
    return p, tail

# ---------------------------------------------------------------- main build
def build_and_certify(Ls=(0.90, 0.95), Mhead=60):
    print("== GRID PASS: certified sigma on the midpoint grid ==", flush=True)
    npts = int(R2 / H)
    print(f"  R2 = {R2}, h = {H}, points = {npts}, series N = {NSER}")
    CH = 200000
    # rigorous s0 via Lemma C
    d_lo_R2, d_hi_R2 = d_at(R2, 2 * 10 ** 6)
    s0 = d_lo_R2 - C2 * (1 + 1e-15)
    s0_width = d_hi_R2 - d_lo_R2
    print(f"  d({R2}) in [{d_lo_R2:.12f}, {d_hi_R2:.12f}]  ->  s0 = {s0:.12f} "
          f"(width {s0_width:.1e})", flush=True)

    results = {}
    sigma_chunks = []          # cache (r, sigma_mid, width) per chunk
    maxw = 0.0; maxabsw = 0.0; l1w = 0.0
    for c0 in range(0, npts, CH):
        idx = np.arange(c0, min(c0 + CH, npts))
        r = (idx + 0.5) * H
        dlo, dhi = d_enclosure(r, NSER)
        sig_mid = 0.5 * (dlo + dhi) - C2 * np.cos(r * LOG2)
        w = sig_mid - s0
        width = (dhi - dlo)
        sigma_chunks.append((r, w, width))
        maxw = max(maxw, width.max())
        maxabsw = max(maxabsw, np.abs(w).max())
        l1w += np.sum(np.abs(w)) * H
        if c0 == 0:
            print(f"  first chunk done ({len(idx)} pts)", flush=True)
    print(f"  sigma enclosure max width = {maxw:.2e}; max|w| = {maxabsw:.3f}; "
          f"int|w| ~= {l1w:.2f}", flush=True)

    for L in Ls:
        a = L / 2.0
        ms_e = list(range(0, Mhead + 1, 2))
        ms_o = list(range(1, Mhead + 2, 2))
        ne, no = len(ms_e), len(ms_o)
        Be = np.zeros((ne, ne)); Bo = np.zeros((no, no))
        for (r, w, _) in sigma_chunks:
            x = a * r
            Je = np.stack([spherical_jn(m, x) for m in ms_e])
            Jo = np.stack([spherical_jn(m, x) for m in ms_o])
            se = np.array([math.sqrt((2 * m + 1) * 2 * a) * (-1) ** (m // 2) for m in ms_e])
            so = np.array([math.sqrt((2 * m + 1) * 2 * a) * (-1) ** ((m - 1) // 2) for m in ms_o])
            Pe = se[:, None] * Je
            Po = so[:, None] * Jo
            hw = (H / math.pi) * w
            Be += (Pe * hw[None, :]) @ Pe.T
            Bo += (Po * hw[None, :]) @ Po.T
        pe, pe_tail = pole_vector_float(a, ms_e, "even")
        po, po_tail = pole_vector_float(a, ms_o, "odd")
        He = s0 * np.eye(ne) + 2.0 * np.outer(pe, pe) + Be
        Ho = s0 * np.eye(no) - 2.0 * np.outer(po, po) + Bo
        # eigen bottoms at high precision (solver error negligible; Weyl for widths)
        lam_e = min(mp.eigsy(mp.matrix(He.tolist()), eigvals_only=True))
        lam_o = min(mp.eigsy(mp.matrix(Ho.tolist()), eigvals_only=True))
        lam_e, lam_o = float(lam_e), float(lam_o)

        # ---------------- ERROR LEDGER (explicit, conservative) ----------------
        F0sq = 2 * a                                   # |phat|^2 sup bound
        W0, W1, W2 = maxabsw, S1B, S2B
        f2 = W2 * F0sq + 4 * W1 * a * F0sq + W0 * 4 * a * a * F0sq
        eps_quad_entry = (R2 * H * H / 24.0) * f2
        n_h = max(ne, no)
        eps1 = n_h * eps_quad_entry                    # Frobenius bound, quadrature
        eps2 = n_h * maxw                              # sigma enclosure (per-entry <= width via int phat^2 <= pi)
        eps3 = n_h * (2e-12 * (l1w / math.pi) * F0sq)  # scipy bessel relative error pad
        eps4 = 4.0 * (abs(pe).max() + abs(po).max()) * max(pe_tail, po_tail) + 1e-12
        eps5 = s0_width                                # floor bracket
        eps6 = 1e-20                                   # mp eigensolver
        # Legendre tail block m > Mhead: |j_m(aR2)| <= (aR2)^m/(2m+1)!!
        x0 = a * R2
        m = Mhead + 2
        ljt = m * math.log(x0) - sum(math.log(2 * k + 1) for k in range(m + 1))
        eps7 = (l1w / math.pi) * (2 * a * (2 * m + 1)) * math.exp(2 * ljt) + \
               2 * math.sqrt(F0sq) * math.exp(ljt)     # tail entries + pole tail coupling (crude, tiny)
        ledger = eps1 + eps2 + eps3 + eps4 + eps5 + eps6 + eps7
        print(f"== L = {L:.2f} (support [e^-{a:.3f}, e^{a:.3f}], f-window e^L = {math.exp(L):.4f}) ==")
        print(f"  head bottoms:   even {lam_e:+.6e}   odd {lam_o:+.6e}")
        print(f"  ledger: quad {eps1:.2e}  sigma-enc {eps2:.2e}  bessel {eps3:.2e}  "
              f"pole {eps4:.2e}  s0 {eps5:.2e}  eig {eps6:.2e}  tailblock {eps7:.2e}")
        print(f"  TOTAL ledger = {ledger:.3e}")
        ce, co = lam_e - ledger, lam_o - ledger
        print(f"  CERTIFIED:      even {ce:+.6e}   odd {co:+.6e}   "
              f"{'*** BOTH POSITIVE — CERTIFICATE HOLDS ***' if ce > 0 and co > 0 else '!!! NOT CLOSED !!!'}",
              flush=True)
        results[L] = (ce, co)
    return results

def head_convergence(L=0.90):
    print("== HEAD-SIZE CHECK (float, Mhead 40 vs 60, even) ==", flush=True)
    # cheap float pass at coarse h for compression-convergence evidence
    global H, NSER
    Hs, Ns = H, NSER
    H, NSER = 5e-4, 800
    try:
        for Mh in (40, 60):
            r = build_and_certify(Ls=(L,), Mhead=Mh)
            print(f"  Mhead = {Mh}: certified-shape even bottom {r[L][0]:+.3e} (coarse pass)")
    finally:
        H, NSER = Hs, Ns

if __name__ == "__main__":
    self_tests()
    if "--coarse" in sys.argv:
        head_convergence()
    else:
        build_and_certify()
