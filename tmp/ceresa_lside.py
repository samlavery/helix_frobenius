"""The Ceresa L-side landing for the Klein quartic -- grade-3 rung of the house
matching law (leading central jet <-> admissible height pairing; Zhang/YZZ: the
Gross-Schoen cycle's Beilinson-Bloch height <-> the triple-product central
derivative L'(1/2, H^1(C)^{otimes 3})).

LITERATURE VERDICT (the falsifiable prediction).  The Klein quartic
    C : x^3 y + y^3 z + z^3 x = 0    (genus 3, = the modular curve X(7))
has a NON-TORSION Ceresa cycle: C - C^- is not algebraically equivalent to 0 in
J(C).  Proven by Tadokoro, "A nontrivial algebraic cycle in the Jacobian variety
of the Klein quartic," Math. Z. 260 (2008) 265-275, via B. Harris' harmonic volume
and special values of the hypergeometric 3F2 -- the analogue of Harris' Fermat-
quartic result (Harris, PNAS 1983 / Ann. Math.).  This is a foundational example:
computations with the Ceresa cycle of Fermat/Klein quartics motivated the
Beilinson-Bloch conjectures.  So, under Beilinson-Bloch nondegeneracy, the Ceresa
channel's central L-DERIVATIVE must be NONZERO.  (If it were zero, or if the
channel had even sign with nonvanishing central value forcing torsion, that would
contradict Tadokoro -- a published falsification.  None is seen here.)

DECOMPOSITION (Elkies, "The Klein Quartic in Number Theory").  Jac(C) is isogenous
over Qbar to E^3 with E of conductor 49 and CM by K = Q(sqrt(-7)) (class number 1).
[The naive plane model above is NOT Q-isogenous to E^3 -- a quadratic twist stands
in the way -- but Elkies' model C7^0 is, with E = 49a3; the Ceresa non-triviality
is a geometric (Qbar) statement so it is model-independent.]  Writing f2 for the
weight-2 level-49 CM newform (L(f2,s) = L(49a,s) = L(psi,s)), the triple-product
motive decomposes as

    H^1(C)^{otimes 3}  =  Ind_K^Q(psi^3)  (+)  3 . M_{f2}(-1),
    L(s, H^1(C)^{otimes 3})  =  L(s, psi^3) . L(s-1, 49a)^3,

by Clebsch-Gordan (V^{ot3} = Sym^3 V (+) 2 V(det)) and the CM splitting
Sym^3(Ind psi) = Ind(psi^3) (+) M_{f2}(-1).  The genuinely-new, non-decorated piece
-- the Ceresa channel -- is L(psi^3, s): the weight-4 level-49 CM newform 49.4.a.a.
The three copies of M_{f2}(-1) are the "elliptic/decorated" even channel, with
central value L(49a, 1) at their center.

THIS FILE builds L(psi^m, s) for K = Q(sqrt(-7)) FROM SCRATCH (ideals via the norm
form a^2 + ab + 2b^2; explicit Hecke character psi with the Legendre normalization),
and reads the center with the house split-vs-direct self-certificate (center_reading
method): the completed Lambda(s) = Q^{s/2} G_inf(s) L(s) satisfies
Lambda(s) = eps Lambda(1-s), and

    Lambda(s0) = sum_n lam_n [ H(s0,n) + eps H(1-s0,n) ],   H(s,y)=(1/2pi i)int G y^-w/(w-s),

certified against the direct Euler-Dirichlet value at s0 = 2.2, 2.5 (two-point).
The center then reads eps, and for eps=+1 the value  L(1/2) = 2 sum lam_n H(1/2,n)/G(1/2),
for eps=-1 the derivative  L'(1/2) = 2 sum lam_n H'(1/2,n)/G(1/2)  (H' has (w-s)^2 in
the denominator).  Unitary normalization (center 1/2); the derivative w.r.t. s is
invariant under the (k-1)/2 shift, so L'_unitary(1/2) = L'_arith(center).

VALIDATION is threefold and independent of the reader:
  * a_p(psi) reproduced by BRUTE-FORCE point counts on E = 49a1 over F_p;
  * a_p(C) of the Klein quartic by BRUTE-FORCE point counts, exhibiting the
    E^3 (CM by sqrt(-7)) shape: 0 at inert p, a full triple at split p;
  * the from-scratch center readings cross-checked against a PARI oracle
    (lfuncreate/lfunrootres, an independent code path): eps(psi^3) = -1,
    L(psi^3, center) = 0, L'(psi^3, center) = 0.82988636.

Run: python3 ceresa_lside.py     (~2-4 min)
"""
import os, math
from fractions import Fraction as Q
import numpy as np
import mpmath as mp

mp.mp.dps = 25

# ---- PARI oracle constants (independent code path; see module docstring / report).
#      lfuncreate([a_n, 1, [0,1], 4, 49, 0]); lfunrootres -> w = -1; lfun(.,2), lfun(.,2,1).
ORACLE_EPS_PSI3   = -1
ORACLE_LVAL_PSI3  = 0.0
ORACLE_LDER_PSI3  = 0.82988635877461538   # L'(49.4.a.a, center) = L'(psi^3, center)
ORACLE_L_49a_1    = 0.966655852808406     # L(49a, 1) = even-channel central value


# ============================================================ K = Q(sqrt(-7))
# Elements written x + y*sqrt(-7) with x, y in Q (half-integers allowed: the ring
# of integers is Z[w], w = (1+sqrt(-7))/2, so a + b*w = (a+b/2) + (b/2) sqrt(-7)).
def kmul(A, B):
    (x1, y1), (x2, y2) = A, B
    return (x1 * x2 - 7 * y1 * y2, x1 * y2 + x2 * y1)   # sqrt(-7)^2 = -7


def kpow(A, m):
    R = (Q(1), Q(0))
    for _ in range(m):
        R = kmul(R, A)
    return R


def legendre7(n):
    """Legendre symbol (n/7), n a rational integer."""
    r = n % 7
    return 0 if r == 0 else (1 if r in (1, 2, 4) else -1)


def split_generator(p):
    """For a rational prime p split in K (p mod 7 in {1,2,4}), return the
    normalized Hecke generator pi0 = chi * alpha as a K-element (x, y), where
    alpha = a + b*w has norm a^2+ab+2b^2 = p and chi = (a+4b / 7).  Then
    a_p(psi^m) = pi0^m + conj = 2 Re(pi0^m) = 2 * (rational part of pi0^m)."""
    for b in range(-int(2 * math.sqrt(p)) - 2, int(2 * math.sqrt(p)) + 3):
        # a^2 + a b + 2 b^2 = p  ->  a = (-b +- sqrt(b^2 - 8b^2 + 4p))/2
        disc = b * b - 8 * b * b + 4 * p
        if disc < 0:
            continue
        r = math.isqrt(disc)
        if r * r != disc:
            continue
        for a in ((-b + r) // 2, (-b - r) // 2):
            if a * a + a * b + 2 * b * b == p:
                chi = legendre7(a + 4 * b)
                alpha = (Q(a) + Q(b, 2), Q(b, 2))              # a + b w
                return (chi * alpha[0], chi * alpha[1])
    raise ValueError(f"no generator for split prime {p}")


def ap_hecke(p, m):
    """a_p of L(psi^m, s) from the Hecke character of K = Q(sqrt(-7)).
    Ramified p=7: a_7 = 0.  Inert p (p mod 7 in {3,5,6}): a_p = 0.
    Split p: 2 * Re(pi0^m)."""
    if p == 7:
        return 0
    if p % 7 in (3, 5, 6):
        return 0
    x, _ = kpow(split_generator(p), m)
    val = 2 * x
    assert val.denominator == 1
    return int(val)


# ------------------------------------------------------- Dirichlet coefficients
def sieve_primes(n):
    s = np.ones(n + 1, bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0].tolist()


def bank_hecke_unitary(m, nmax):
    """Unitary lambda_n of L(psi^m): weight k = m+1, lam_n = a_n / n^{(k-1)/2}.
    Multiplicative from a_p via the Hecke recursion a_{p^{j+1}} = a_p a_{p^j}
    - p^m a_{p^{j-1}} (good split p); inert p: a_{p^2}=-p^m, a_{p^{2j}}=(-p^m)^j,
    odd powers 0; p=7 ramified in K: odd m (level 49, psi^m ramified) a_{7^j}=0, but
    even m (level 7, psi^m UNRAMIFIED) a_{7^j}=(sqrt-7)^{mj}=(-7)^{mj/2} (lam_7=i^m).
    Returns arithmetic a_n and unitary lam_n."""
    a = np.zeros(nmax + 1)
    a[1] = 1.0
    for p in sieve_primes(nmax):
        kmax = int(math.log(nmax) / math.log(p))
        c = np.zeros(kmax + 1)
        c[0] = 1.0
        if p == 7:
            if m % 2 == 0:                         # even m: psi^m UNRAMIFIED at 7 (level 7),
                a7 = (-7.0) ** (m // 2)            # degree-1 factor a_{7^j}=psi^m(p_7)^j=(sqrt-7)^{mj}
                for j in range(1, kmax + 1):       # -> lam_7=(-1)^{m/2}=i^m (matches 7.3.b.a a_7=-7)
                    c[j] = a7 ** j
            # odd m: level 49, psi^m RAMIFIED at 7 -> a_{7^j}=0 (c stays zero)
        elif p % 7 in (3, 5, 6):                   # inert
            for j in range(2, kmax + 1, 2):
                c[j] = (-float(p) ** m) ** (j // 2)
        else:                                      # split
            ap = float(ap_hecke(p, m))
            c[1] = ap
            for j in range(2, kmax + 1):
                c[j] = ap * c[j - 1] - (float(p) ** m) * c[j - 2]
        for k in range(kmax, 0, -1):
            pk = p ** k
            for mm in range(1, nmax // pk + 1):
                if mm % p:
                    a[mm * pk] += c[k] * a[mm]
    n = np.arange(0, nmax + 1, dtype=float)
    lam = np.zeros(nmax + 1)
    lam[1:] = a[1:] / n[1:] ** (m / 2.0)           # (k-1)/2 = m/2, k=m+1
    return a, lam


# ================================================== AFE evaluator (house method)
def make_G(Qc, factors):
    def G(s):
        out = mp.mpf(Qc) ** (s / 2)
        for typ, sh in factors:
            if typ == 'R':
                out *= mp.pi ** (-(s + sh) / 2) * mp.gamma((s + sh) / 2)
            else:
                out *= 2 * (2 * mp.pi) ** (-(s + sh)) * mp.gamma(s + sh)
        return out
    return G


def _kernels(G, s, ys, T=60, NODES=12001, M=1600, order=1):
    """H(s,y)=(1/2pi)int G(c+it) y^-(c+it)/(c+it-s)^order dt over a fixed Simpson
    grid in t, y-dependence vectorized (log-grid + interpolation).  order=1 -> H,
    order=2 -> H' (dH/ds).

    Auto-scales the interpolation resolution (NODES, M) with the y-range, which tracks
    sqrt(conductor).  The fixed defaults are calibrated for the base conductor; at large
    conductor they UNDER-RESOLVE the kernel and the interpolation error can fit the WRONG
    sign decisively (root cause of the twist-sign artifacts).  Scaling is one-directional
    (never below the passed values), so it is a strict improvement; the small-conductor
    path (log y-range <= 8.5) is untouched."""
    _ys = np.asarray(ys, float)
    _extra = max(0.0, math.log(_ys.max() / _ys.min()) - 8.5)
    NODES = max(NODES, (12001 + int(26000 * _extra)) | 1)      # keep odd for Simpson
    M = max(M, 1600 + int(6500 * _extra))
    c = max(float(mp.re(s)) + 1.5, 0.8)
    ts = np.linspace(-T, T, NODES)
    Gv = np.array([complex(G(mp.mpc(c, t))) for t in ts])
    w = np.ones(NODES)
    w[1:-1:2], w[2:-1:2] = 4.0, 2.0
    w *= (ts[1] - ts[0]) / 3.0
    sc = complex(s)
    denom = ((c + 1j * ts) - sc) ** order
    base = Gv / denom * w
    ys = np.asarray(ys, float)
    lo, hi = np.log(ys.min()) - 0.05, np.log(ys.max()) + 0.05
    gl = np.linspace(lo, hi, M)
    vals = np.zeros(M, complex)
    CH = 200
    for i in range(0, M, CH):
        blk = gl[i:i + CH]
        phase = np.exp(-1j * np.outer(blk, ts))
        vals[i:i + CH] = np.exp(-c * blk) * (phase @ base) / (2 * math.pi)
    re = np.interp(np.log(ys), gl, vals.real)
    im = np.interp(np.log(ys), gl, vals.imag)
    return re + 1j * im


def certify(G, lam, s0, T=60):
    """Return (eps, rel_match, rel_other) from the split-vs-direct identity at s0."""
    n = np.arange(1, len(lam))
    keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float)
    lk = lam[1:][keep]
    H1 = _kernels(G, mp.mpf(s0), ys, T=T)
    H2 = _kernels(G, 1 - mp.mpf(s0), ys, T=T)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    res = {e: abs((a + e * b) - d) / max(abs(d), 1e-30) for e in (+1, -1)}
    eps = +1 if res[+1] < res[-1] else -1
    return eps, res[eps], res[-eps]


def central_value(G, lam, eps, T=60):
    """L(1/2) = Lambda(1/2)/G(1/2), Lambda(1/2) = (1+eps) sum lam_n H(1/2,n).
    For eps=-1 this is EXACTLY 0 (the sign forces the central value to vanish)."""
    n = np.arange(1, len(lam))
    keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float)
    H1 = _kernels(G, mp.mpf("0.5"), ys, T=T)
    lam_val = (1.0 + eps) * (lam[1:][keep] * H1).sum()
    return complex(lam_val) / complex(G(mp.mpf("0.5")))


def central_deriv(G, lam, eps, T=60):
    """L'(1/2) = Lambda'(1/2)/G(1/2), Lambda'(1/2) = (1-eps) sum lam_n H'(1/2,n).
    The leading term when eps=-1 (factor 2); it vanishes formally when eps=+1."""
    n = np.arange(1, len(lam))
    keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float)
    Hp = _kernels(G, mp.mpf("0.5"), ys, T=T, order=2)
    lam_der = (1.0 - eps) * (lam[1:][keep] * Hp).sum()
    return complex(lam_der) / complex(G(mp.mpf("0.5")))


# ============================================ point-count decomposition oracles
def ap_curve_49a1(p):
    """a_p(E), E = 49a1 : y^2 + xy = x^3 - x^2 - 2x - 1, by brute force over F_p."""
    if p == 7:
        return 0                                   # additive reduction
    cnt = 1                                         # point at infinity
    for x in range(p):
        rhs = (x * x * x - x * x - 2 * x - 1) % p    # x^3 - x^2 - 2x - 1
        for y in range(p):
            if (y * y + x * y - rhs) % p == 0:
                cnt += 1
    return p + 1 - cnt


def ap_klein_quartic(p):
    """a_p(C), C : x^3 y + y^3 z + z^3 x = 0 in P^2, brute force projective count."""
    if p == 7:
        return None
    def F(x, y, z):
        return (x * x * x * y + y * y * y * z + z * z * z * x) % p
    cnt = 0
    for x in range(p):                              # z = 1 patch
        for y in range(p):
            if F(x, y, 1) == 0:
                cnt += 1
    for x in range(p):                              # z = 0, y = 1
        if F(x, 1, 0) == 0:
            cnt += 1
    if F(1, 0, 0) == 0:                             # z = 0, y = 0, x = 1
        cnt += 1
    return p + 1 - cnt


# ================================================================== main
def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# CERESA L-SIDE -- Klein quartic X(7), CM by Q(sqrt(-7)); the grade-3")
    P("# matching-law rung.  L(psi^3, .) = weight-4 CM newform 49.4.a.a is the")
    P("# Ceresa channel; non-torsion (Tadokoro, Math.Z. 260 (2008)) predicts a")
    P("# NONZERO central derivative.")
    P("#" * 78)
    P()

    # ---- (A) point-count validation of the Hecke character and the E^3 shape
    P("(A) DECOMPOSITION CHECK -- brute-force point counts (independent path):")
    P("    p   split?  a_p(E=49a1)  a_p(psi)[Hecke]   a_p(Klein C)   3*a_p(E)")
    okA = True
    for p in [2, 3, 5, 11, 13, 23, 29, 37, 43, 53, 71, 79]:
        cls = {1: "split", 2: "split", 4: "split", 3: "inert",
               5: "inert", 6: "inert", 0: "ramif"}[p % 7]
        aE = ap_curve_49a1(p)
        aH = ap_hecke(p, 1)
        aC = ap_klein_quartic(p)
        okA = okA and (aE == aH)
        P(f"   {p:>3d}  {cls:>6s}   {aE:>10d}   {aH:>13d}   {aC:>12d}   {3 * aE:>8d}")
    P(f"    a_p(psi) == a_p(49a1) point counts: {'OK' if okA else 'FAIL'}")
    P("    (Klein a_p(C) vanishes at every inert p -- the CM-by-sqrt(-7) shape.  At")
    P("     split p it reads 3 a_p(E) exactly when p = 1 mod 7 and 0 when p = 2,4 mod 7:")
    P("     the three factors are CONJUGATE twists of E (cubic character of conductor 7,")
    P("     from the order-3 coordinate permutation), so the naive model is not itself")
    P("     Q-isogenous to E^3 -- Elkies' model C7^0 is.  Geometrically (Qbar) all agree.)")
    P()

    # ---- (B) gate: weight-2 psi = L(49a), even channel value
    P("(B) GATE / EVEN CHANNEL -- L(psi, s) = L(49a, s), Q = 49, GammaC(s+1/2):")
    _, lam2 = bank_hecke_unitary(1, 2000)
    G2 = make_G(49, [('C', 0.5)])
    e2a, r2a, _ = certify(G2, lam2, 2.5)
    e2b, r2b, _ = certify(G2, lam2, 2.2)
    L2 = central_value(G2, lam2, e2a)
    okB = (e2a == e2b == +1) and max(r2a, r2b) < 1e-4 and \
        abs(L2.real - ORACLE_L_49a_1) < 2e-3 and abs(L2.imag) < 1e-5
    P(f"    eps = {e2a:+d}/{e2b:+d}  two-point match {r2a:.1e}, {r2b:.1e}")
    P(f"    L(49a, center)_unitary = {L2.real:.7f}   (oracle L(49a,1) = {ORACLE_L_49a_1:.7f})")
    P(f"    This is the psi^2.psibar = psi.N even channel central value (mult 3),")
    P(f"    eps = +1: the elliptic/decorated piece, nonvanishing.   {'PASS' if okB else 'FAIL'}")
    P()

    # ---- (C) the Ceresa channel: weight-4 psi^3 = 49.4.a.a
    P("(C) CERESA CHANNEL -- L(psi^3, s) = L(49.4.a.a, s), Q = 49, GammaC(s+3/2):")
    _, lam4 = bank_hecke_unitary(3, 4000)
    G4 = make_G(49, [('C', 1.5)])
    e4a, r4a, o4a = certify(G4, lam4, 2.5)
    e4b, r4b, o4b = certify(G4, lam4, 2.2)
    agree = (e4a == e4b)
    P(f"    self-certified sign:  eps = {e4a:+d}/{e4b:+d}  (two-point {'AGREE' if agree else 'DISAGREE'})")
    P(f"    split-vs-direct match {r4a:.2e}, {r4b:.2e}  (wrong sign {o4a:.2e}, {o4b:.2e})")
    eps4 = e4a if agree else +1
    okC_sign = agree and eps4 == ORACLE_EPS_PSI3 and max(r4a, r4b) < 1e-4
    P(f"    sign certificate: {'PASS  eps = -1 (odd)' if okC_sign else 'CHECK'}"
      f"   [oracle eps = {ORACLE_EPS_PSI3:+d}]")
    Lval = central_value(G4, lam4, eps4)
    P(f"    central VALUE  L(psi^3, center) = {Lval.real:+.3e}  (forced 0 by eps=-1;"
      f" oracle {ORACLE_LVAL_PSI3:.0e})")
    Lder = central_deriv(G4, lam4, eps4)
    rel = abs(Lder.real - ORACLE_LDER_PSI3) / ORACLE_LDER_PSI3
    okC_der = abs(Lder.imag) < 1e-3 and rel < 5e-3 and Lder.real > 0.1
    P(f"    central DERIV  L'(psi^3, center) = {Lder.real:.7f}   (imag {Lder.imag:+.1e})")
    P(f"    oracle (PARI lfuncreate/lfun, independent) = {ORACLE_LDER_PSI3:.7f}"
      f"   rel {rel:.1e}   {'PASS' if okC_der else 'CHECK'}")
    P()

    # ---- verdict
    P("VERDICT (grade-3 matching law):")
    allok = okA and okB and okC_sign and okC_der
    if allok:
        P("  The Ceresa channel of the Klein quartic -- the weight-4 CM newform")
        P("  L(psi^3,.) = 49.4.a.a, the genuinely-new piece of L(H^1(C)^{ot3}) -- has")
        P("  ROOT NUMBER eps = -1 (self-certified split-vs-direct, two-point), so its")
        P("  central value is forced to zero and the leading term is the DERIVATIVE")
        P(f"  L'(center) = {Lder.real:.6f} != 0 (oracle {ORACLE_LDER_PSI3:.6f}).")
        P("  This MATCHES the literature: Tadokoro proved C - C^- is NON-torsion in")
        P("  J(Klein), so under Beilinson-Bloch nondegeneracy the Ceresa height, hence")
        P("  the central derivative of its channel, must be nonzero -- and it is.")
        P("  The even (decorated) channel L(49a, center) = %.6f != 0 sits with eps=+1;"
          % L2.real)
        P("  the total triple-product sign is (-1)(+1)^3 = -1, so the Gross-Schoen")
        P("  cycle is a DERIVATIVE, consistent throughout.")
        P()
        P("  Falsifier register (grade 3): a zero derivative here, or eps=+1 with a")
        P("  nonvanishing central value (forcing torsion), would contradict Tadokoro.")
        P("  Neither occurs.  The matching law reads true at grade 3.")
    else:
        P(f"  status: A {okA}  B {okB}  C-sign {okC_sign}  C-deriv {okC_der}"
          " -- investigate before claiming the landing.")
    P()
    P("  Scope: L(psi^m) built from scratch (K=Q(sqrt-7) ideals, explicit Hecke")
    P("  character, house AFE split-vs-direct certificate); a_p validated by point")
    P("  counts on 49a1; center cross-checked against a PARI oracle.  The")
    P("  proportionality h(Ceresa) ~ L'(center) (Beilinson-Bloch / Zhang-YZZ) is the")
    P("  consumed theorem; the nondegeneracy is the one hypothesis, isolated here.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "ceresa_lside_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to ceresa_lside_results.txt]")


if __name__ == "__main__":
    main()
