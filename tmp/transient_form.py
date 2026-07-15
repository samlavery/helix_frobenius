"""Pin the value-registration transient's functional form BY DERIVATION.

Thesis (from the census, GRADE4 item 11): the on-lattice (unwarped-window)
registration defect R0(Y) - 1 is NOT a statistical object -- it is the EXACT
smoothed-AFE truncation error of the windowed read against the completed-L
structure, and it is DERIVABLE per object from the FE sheet G(s) alone, with
ZERO fitted parameters.

THE DERIVATION (one page of classical analysis; see transient_form_notes.md).
The census reader is the C-infinity window sum

    V_Y(1/2) = sum_n lambda_n n^{-1/2} w(log n / log Y),   R0 = V_Y(1/2)/L(1/2).

By Mellin inversion of the window (w~(z) = its Mellin transform, a kernel with a
single simple pole at z=0, residue 1),

    V_Y(1/2) = (1/2pi i) int_{(c)} w~(z) L(1/2 + z) dz,    c > 1/2.

Shift the contour left past z=0 (picking up L(1/2)) to Re z = -c', then use the
functional equation Lambda(s) = eps Lambda(1-s), Lambda = G.L, to fold the tail
into the DUAL (mirror) sum.  The EXACT identity:

    V_Y(1/2) - L(1/2)  =  eps * sum_m lambda_m m^{-1/2} M_m(Y),                (T)

    M_m(Y) = (1/2pi i) int_{Re z = -c'} w~(z) [G(1/2 - z)/G(1/2 + z)] m^{z} dz.

So the transient IS the mirror sum against the FE chi-factor chi(z)=G(1/2-z)/G(1/2+z).
Everything on the right is on the SHEET (Q and the Gamma-shifts) plus the SAME
arithmetic coefficients -- no L-value, no fit.

Leading closed form (chi(z) ~ Q_an^{-z}):  M_m ~ w(log(Q_an/m)/log Y) - 1, a
COMPLEMENTARY window -- the transient is (minus) the smoothed dual partial sum up
to m ~ Q_an/sqrt(Y).  Its shape (decay exponent, oscillation phase) is set by the
Gamma-shape of G: this is exactly WHY no single cross-object predictor survived
the census CV (different sheets => different kernels) while each is deterministic.

We compute the EXACT M_m(Y) (true Gamma-ratio, not the leading approx) by the
center_reading H-grid trick (contour sampled once, m-dependence a vectorized FT
on a log-grid + interpolation), sum against the bank, and compare to the measured
transient V_Y - L on all 24 census rows.

Run: python3 transient_form.py      (~10-15 min; banks in RAM)
"""
import sys, os, math, cmath
import numpy as np
from scipy.special import loggamma

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
from theta_cache import theta_table

# ---------------------------------------------------------------- census sheet
# Unitary normalization, center s = 1/2.  G(s) = Q^{s/2} * prod Gamma-factors.
# All six certified objects carry eps = +1 (center_reading / carrier_center /
# deg6_center certificates).  legs: list of ('C'|'R', shift a).
TH11 = theta_table("11a1")
TH37 = theta_table("37a1")
A11 = 1.0 / math.sqrt(11.0)
A37 = 1.0 / math.sqrt(37.0)


def _th(TH, p):
    v = float(TH[p])
    return 0.0 if math.isnan(v) else v


def eigs_gl2(p):
    if p == 11:
        return [A11]
    t = _th(TH11, p)
    return [cmath.exp(1j * t), cmath.exp(-1j * t)]


def eigs_sym(r):
    def fn(p):
        if p == 11:
            return [A11 ** r]
        t = _th(TH11, p)
        return [cmath.exp(1j * (r - 2 * j) * t) for j in range(r + 1)]
    return fn


def eigs_rs4(p):
    if p == 11:
        t2 = _th(TH37, p)
        return [A11 * cmath.exp(1j * s * t2) for s in (1, -1)]
    if p == 37:
        t1 = _th(TH11, p)
        return [A37 * cmath.exp(1j * s * t1) for s in (1, -1)]
    t1, t2 = _th(TH11, p), _th(TH37, p)
    return [cmath.exp(1j * (s1 * t1 + s2 * t2)) for s1 in (1, -1) for s2 in (1, -1)]


def eigs_deg6(p):
    if p == 11:
        t2 = _th(TH37, p)
        return [cmath.exp(1j * s * t2) / 11.0 for s in (1, -1)]
    if p == 37:
        t1 = _th(TH11, p)
        return [cmath.exp(2j * s * t1) / math.sqrt(37.0) for s in (1, 0, -1)]
    t1, t2 = _th(TH11, p), _th(TH37, p)
    return [cmath.exp(1j * (2 * s1 * t1 + s2 * t2))
            for s1 in (1, 0, -1) for s2 in (1, -1)]


OBJECTS = [
    # name, degree, Q, L(1/2)_unitary, eps, eigs_fn, G-legs
    ("L(11a1)",              2, 11,             0.2538417,  +1, eigs_gl2,
     [('C', 0.5)]),
    ("L(Sym2 11a1)",         3, 11**2,          0.8933980,  +1, eigs_sym(2),
     [('C', 1.0), ('R', 1.0)]),
    ("L(Sym3 11a1)",         4, 11**3,          1.1402380,  +1, eigs_sym(3),
     [('C', 1.5), ('C', 0.5)]),
    ("L(11a1 x 37a1) RS4",   4, (11*37)**2,     5.0227652,  +1, eigs_rs4,
     [('C', 1.0), ('R', 0.0), ('R', 1.0)]),
    ("L(Sym4 11a1)",         5, 11**4,          0.6058010,  +1, eigs_sym(4),
     [('C', 2.0), ('C', 1.0), ('R', 0.0)]),
    ("L(Sym2(11a1) x 37a1)", 6, 11**4 * 37**3,  0.61570486, +1, eigs_deg6,
     [('C', 1.5), ('C', 0.5), ('C', 0.5)]),
]

Y_LADDER = [40000.0, 130000.0, 420000.0, 1_350_000.0]

# measured census transient R0 (unwarped window, real) -- from
# value_registration_results.txt, Table B, the R_0 column.  Cross-check only;
# the script recomputes V_Y directly from its own bank.
CENSUS_R0 = {
    ("L(11a1)", 40000.0): 1.0000, ("L(11a1)", 130000.0): 1.0000,
    ("L(11a1)", 420000.0): 1.0000, ("L(11a1)", 1350000.0): 1.0000,
    ("L(Sym2 11a1)", 40000.0): 1.0002, ("L(Sym2 11a1)", 130000.0): 1.0000,
    ("L(Sym2 11a1)", 420000.0): 1.0000, ("L(Sym2 11a1)", 1350000.0): 1.0000,
    ("L(Sym3 11a1)", 40000.0): 1.0015, ("L(Sym3 11a1)", 130000.0): 0.9998,
    ("L(Sym3 11a1)", 420000.0): 0.9999, ("L(Sym3 11a1)", 1350000.0): 1.0001,
    ("L(11a1 x 37a1) RS4", 40000.0): 1.0186,
    ("L(11a1 x 37a1) RS4", 130000.0): 1.0305,
    ("L(11a1 x 37a1) RS4", 420000.0): 1.0307,
    ("L(11a1 x 37a1) RS4", 1350000.0): 1.0267,
    ("L(Sym4 11a1)", 40000.0): 0.9908, ("L(Sym4 11a1)", 130000.0): 0.9949,
    ("L(Sym4 11a1)", 420000.0): 1.0048, ("L(Sym4 11a1)", 1350000.0): 0.9977,
    ("L(Sym2(11a1) x 37a1)", 40000.0): 0.0405,
    ("L(Sym2(11a1) x 37a1)", 130000.0): 0.5224,
    ("L(Sym2(11a1) x 37a1)", 420000.0): 0.9984,
    ("L(Sym2(11a1) x 37a1)", 1350000.0): 1.1815,
}


# ------------------------------------------------------------------ FE sheet
def log_gamma_factor(typ, s):
    """log of a single archimedean factor at complex s (vectorized)."""
    if typ == 'C':                                    # Gamma_C(s) = 2 (2pi)^{-s} Gamma(s)
        return math.log(2.0) - s * math.log(2.0 * math.pi) + loggamma(s)
    return -(s / 2.0) * math.log(math.pi) + loggamma(s / 2.0)   # Gamma_R


def log_chi(z, Q, legs):
    """log chi(z) = log[ G(1/2 - z) / G(1/2 + z) ],  G(s)=Q^{s/2} prod Gamma-factors.
    z complex array.  chi analytic on Re z < 1/2 + min shift (our contour Re z<0)."""
    out = -z * math.log(Q)                            # Q^{(1/2-z)/2 - (1/2+z)/2} = Q^{-z}
    for typ, a in legs:
        out = out + log_gamma_factor(typ, 0.5 - z + a) - log_gamma_factor(typ, 0.5 + z + a)
    return out


def log_conductor_analytic(Q, legs):
    """Leading exponential rate of chi: chi(z) = Q_an^{-z}(1+O(z^3)).  Uses the
    small-z digamma expansion -- UNRELIABLE when a leg sits near a Gamma pole
    (Gamma_R shift 0 => argument 1/4, digamma large); reported, not trusted."""
    from scipy.special import digamma
    lg = math.log(Q)
    for typ, a in legs:
        if typ == 'C':
            lg += -2.0 * math.log(2.0 * math.pi) + 2.0 * float(digamma(0.5 + a))
        else:
            lg += -math.log(math.pi) + float(digamma((0.5 + a) / 2.0))
    return lg


# ------------------------------------------------------------------ the bank
def local_coeffs(eigs, kmax):
    poly = np.array([1.0 + 0j])
    for e in eigs:
        poly = np.convolve(poly, np.array([1.0, -e]))
    c = np.zeros(kmax + 1, dtype=complex)
    c[0] = 1.0
    for k in range(1, kmax + 1):
        acc = 0j
        for j in range(1, min(k, len(poly) - 1) + 1):
            acc -= poly[j] * c[k - j]
        c[k] = acc
    return c


def fast_bank(eigs_fn, nmax, primes):
    lam = np.zeros(nmax + 1, dtype=complex)
    lam[1] = 1.0
    for p in primes:
        p = int(p)
        kmax = int(math.log(nmax) / math.log(p))
        c = local_coeffs(eigs_fn(p), kmax)
        for k in range(kmax, 0, -1):
            pk = p ** k
            m = np.arange(1, nmax // pk + 1)
            m = m[m % p != 0]
            lam[m * pk] += c[k] * lam[m]
    return lam.real.copy()


# ------------------------------------------------------------------ the window
def wsmooth_vec(u):
    w = np.zeros_like(u)
    w[u <= 0.5] = 1.0
    mid = (u > 0.5) & (u < 1.0)
    xx = (u[mid] - 0.5) / 0.5
    a = np.exp(-1.0 / (1.0 - xx))
    b = np.exp(-1.0 / xx)
    w[mid] = a / (a + b)
    return w


def wprime(u):
    """Analytic derivative of the C-infinity window on (0.5, 1); 0 elsewhere."""
    out = np.zeros_like(u)
    mid = (u > 0.5) & (u < 1.0)
    x = (u[mid] - 0.5) / 0.5
    a = np.exp(-1.0 / (1.0 - x))
    b = np.exp(-1.0 / x)
    dwdx = -a * b * (1.0 / (1.0 - x) ** 2 + 1.0 / x ** 2) / (a + b) ** 2
    out[mid] = 2.0 * dwdx                              # du = dx/2
    return out


# ------------------------------------------------------------ the mirror kernel
def mirror_kernel_on_grid(Q, legs, Y, gl, cprime=0.75, T=90.0, NODES=14001, NU=1200):
    """M_m(Y) on a log-grid gl = log m, via the H-grid trick.

    M_m(Y) = (1/2pi) int_{-T}^{T} F(t) e^{i t log m} dt * m^{-c'},
    F(t) = w~(-c'+i t) chi(-c'+i t),
    w~(z) = -psi(z)/z,  psi(z) = int_{0.5}^{1} w'(u) e^{u z log Y} du.
    Returns M_m real on the grid (F is Hermitian => integral real)."""
    L = math.log(Y)
    ts = np.linspace(-T, T, NODES)
    z = -cprime + 1j * ts

    # psi(z) = int w'(u) e^{u z L} du  (Simpson over u in (0.5,1))
    us = np.linspace(0.5, 1.0, NU + 1)
    wp = wprime(us)
    sw = np.ones(NU + 1)
    sw[1:-1:2], sw[2:-1:2] = 4.0, 2.0
    sw *= (us[1] - us[0]) / 3.0
    # e^{u z L} = e^{-u c' L} e^{i u ts L}; matrix (NODES x NU)
    amp = (wp * sw) * np.exp(-us * cprime * L)          # (NU,)
    phase = np.exp(1j * np.outer(ts * L, us))           # (NODES, NU)
    psi = phase @ amp                                   # (NODES,)
    wtilde = -psi / z

    chi = np.exp(log_chi(z, Q, legs))
    F = wtilde * chi

    # Simpson weights in t
    wt = np.ones(NODES)
    wt[1:-1:2], wt[2:-1:2] = 4.0, 2.0
    wt *= (ts[1] - ts[0]) / 3.0
    base = F * wt

    M = np.zeros(len(gl))
    CH = 128
    for i in range(0, len(gl), CH):
        blk = gl[i:i + CH]
        E = np.exp(1j * np.outer(blk, ts))              # (chunk, NODES)
        Iform = (E @ base) / (2.0 * math.pi)
        M[i:i + CH] = (np.exp(-cprime * blk) * Iform).real
    return M


def predict_transient(Q, legs, eps, Y, lam, logn, nm05, gl):
    """T_pred(Y) = eps * sum_m lambda_m m^{-1/2} M_m(Y)."""
    Mgrid = mirror_kernel_on_grid(Q, legs, Y, gl)
    Mn = np.interp(logn, gl, Mgrid)
    return eps * float((lam * nm05 * Mn).sum()), Mgrid


def leading_transient(Qan, eps, Y, lam, logn, nm05):
    """Leading closed form: M_m ~ w(log(Qan/m)/log Y) - 1."""
    u = (math.log(Qan) - logn) / math.log(Y)
    M = wsmooth_vec(u) - 1.0
    return eps * float((lam * nm05 * M).sum())


# ==============================================================================
def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# VALUE-REGISTRATION TRANSIENT -- DERIVED FUNCTIONAL FORM (zero fit params)")
    P("# transient = eps * mirror sum against the FE chi-factor chi=G(1/2-z)/G(1/2+z)")
    P("#" * 78)
    P()

    # bank sizing: mirror sum needs m up to ~ Q/sqrt(Y_min).  theta cache caps at
    # 2e6, so deg6's two smallest-Y rows (m_cut > 2e6) are flagged TRUNCATED.
    MAXBANK = 2_000_000
    for name, deg, Q, L, eps, efn, legs in OBJECTS:
        need = int(min(MAXBANK, max(1_500_000, 4.0 * Q / math.sqrt(min(Y_LADDER)))))
        primes = SH.sieve_primes(need)
        P(f"building {name:24s} (deg {deg}) bank to {need} ...")
        lam = fast_bank(efn, need, primes)[1:]
        n = np.arange(1, need + 1, dtype=float)
        logn = np.log(n)
        nm05 = n ** -0.5
        gl = np.linspace(-0.05, math.log(need) + 0.05, 2200)

        # leading-form scale: use the TRUE conductor Q.  The small-z digamma
        # "analytic conductor" (log_conductor_analytic) collapses to O(1) for
        # degree >= 4 -- the Gamma-ratio's higher-order structure dominates near
        # the poles -- so it is NOT the transient scale; reported for the record.
        Qan = float(Q)
        Qdig = math.exp(log_conductor_analytic(Q, legs))
        P(f"  Q = {Q};  sqrt(Q) = {math.sqrt(Q):.1f};  "
          f"digamma Q_an = {Qdig:.3g} (UNRELIABLE for deg>=4; leading scale uses Q)")

        for Y in Y_LADDER:
            # measured transient: recompute V_Y directly (window fully within bank)
            w = wsmooth_vec(logn / math.log(Y))
            VY = float((lam * nm05 * w).sum())
            T_meas = VY - L
            R0 = VY / L
            # dual cutoff m ~ Q/sqrt(Y); flag if it exceeds the bank
            mcut = Q / math.sqrt(Y)
            trunc = mcut > need
            T_pred, _ = predict_transient(Q, legs, eps, Y, lam, logn, nm05, gl)
            T_lead = leading_transient(Qan, eps, Y, lam, logn, nm05)
            rec = VY - T_pred                          # subtracted (accelerated) reader
            flag = "  [mirror TRUNCATED: m_cut>bank]" if trunc else ""
            P(f"    Y={Y:>9.0f}  Y/sqQ={Y/math.sqrt(Q):>8.1f}  m_cut={mcut:>10.0f}  "
              f"R0={R0:+.4f}")
            P(f"       T_meas={T_meas:+.5f}  T_pred={T_pred:+.5f}  "
              f"resid={T_meas-T_pred:+.2e}  (lead {T_lead:+.4f}){flag}")
            P(f"       raw|V-L|/L={abs(T_meas)/abs(L):.4f}   "
              f"subtracted|V-Tpred-L|/L={abs(rec-L)/abs(L):.4f}")
        P()

    # ---------------------------------------------------------------- summary
    P("=" * 78)
    P("SUMMARY (24-row comparison consolidated in the table above)")
    P("=" * 78)
    P("Pre-registered criterion: T_pred (from the sheet, zero fit params)")
    P("reproduces T_meas = V_Y - L to the census measurement floor, INCLUDING")
    P("sign/phase.  A row PASSES when |T_meas - T_pred| is at the bank-truncation")
    P("floor (mirror rows flagged TRUNCATED are m_cut>bank; not a failure of the")
    P("derivation -- the mirror sum is simply cut short, same as V_Y at small Y).")

    outp = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "transient_form_results.txt")
    with open(outp, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    P()
    P(f"[results written to {outp}]")


if __name__ == "__main__":
    main()
