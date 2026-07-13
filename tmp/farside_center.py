"""Stage 2: the windowed center-reading -- calibration, then the far-side value.

The primitive quadruple's conductor is (11*37*53*61)^8 ~ 1e49: no exact series
evaluation can ever reach its center.  The only road is the smoothed reading

    V_X(1/2) = sum_n lambda_n n^{-1/2} e^{-n/X},

whose X-dependence is fully structured: shifting the Mellin contour,

    V_X(1/2) = [pole terms] + L(1/2) + (decaying),

where the pole terms exist iff the DC occupancy does -- for the DEGENERATE
f^{x4} the zeta^2 factor gives a double edge pole, so
V_X = A sqrt(X) log X + B sqrt(X) + C + o(1) and C must land on the
independently computed factored center 0.921258569 (center_reading.py, every
factor self-certified).  That landing calibrates the protocol.  The PRIMITIVE
quadruple has measured occupancy zero -- no poles -- so the same fit must find
A, B ~ 0 (an independent value-level confirmation of pole-freeness), and its C
is THE FAR-SIDE VALUE: the center of an L-function with no classical
definition, no functional equation, and no framework to predict it.

Banks carry EXACT bad-prime local factors (the calibration target includes
them): degenerate at p=11 the tensor degree drops to 6 with eigenvalues
{1, 1, a^2, a^2, a^2, a^4}, a = a_11/sqrt(11) (the zeta^2 Sym2^3 Sym4
factorization of sp(2)^{x4}); primitive at each level p the Steinberg leg
tensors three unramified legs: 8 eigenvalues a_p u_j.

Run: python3 farside_center.py      (~4-6 min)
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH

CURVES = [("11a1", 11, (0, -1, 1, -10, -20), 1),
          ("37a1", 37, (0, 0, 1, -1, 0), 1),
          ("53a1", 53, (1, -1, 1, 0, 0), 1),
          ("61a1", 61, (1, 0, 0, -2, 1), 1)]   # (label, N, ainv, a_N Steinberg)

NMAX = 300000
TARGET = 0.921258569      # the certified factored center (center_reading.py)


def theta_of(ainv, p):
    b = max(-2.0, min(2.0, SH.ap_general(p, *ainv) / math.sqrt(p)))
    return math.acos(b / 2.0)


def local_coeffs_eigs(eigs, kmax):
    """c_k of prod_j (1 - e_j z)^{-1} for an arbitrary eigenvalue list."""
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
    return c.real


def build_bank(mode, nmax):
    """lambda_n unitary for the degenerate (11a1^{x4}) or primitive quadruple,
    with EXACT bad-prime locals."""
    lam = np.zeros(nmax + 1)
    lam[1] = 1.0
    levels = {N: (ainv, aN) for _, N, ainv, aN in CURVES}
    curves = [CURVES[0]] * 4 if mode == "degenerate" else CURVES
    for p in SH.sieve_primes(nmax):
        kmax = int(math.log(nmax) / math.log(p))
        if p in levels and (mode == "primitive" or p == 11):
            if mode == "degenerate":
                a = 1 / math.sqrt(11)          # a_11 = 1
                eigs = [1.0, 1.0, a * a, a * a, a * a, a ** 4]
            else:
                # Steinberg leg at p, three unramified legs
                ainvp, aN = levels[p]
                alpha = aN / math.sqrt(p)
                thetas = [theta_of(c[2], p) for c in curves if c[1] != p]
                eigs = []
                for s1 in (1, -1):
                    for s2 in (1, -1):
                        for s3 in (1, -1):
                            ph = (s1 * thetas[0] + s2 * thetas[1]
                                  + s3 * thetas[2])
                            eigs.append(alpha * cmath.exp(1j * ph))
        else:
            thetas = [theta_of(c[2], p) for c in curves]
            eigs = []
            for s1 in (1, -1):
                for s2 in (1, -1):
                    for s3 in (1, -1):
                        for s4 in (1, -1):
                            ph = (s1 * thetas[0] + s2 * thetas[1]
                                  + s3 * thetas[2] + s4 * thetas[3])
                            eigs.append(cmath.exp(1j * ph))
        c = local_coeffs_eigs(eigs, kmax)
        for k in range(kmax, 0, -1):
            pk = p ** k
            for m in range(1, nmax // pk + 1):
                if m % p:
                    lam[m * pk] += c[k] * lam[m]
    return lam


def V_of(lam, X, s0=0.5):
    n = np.arange(1, len(lam), dtype=float)
    return float((lam[1:] * n ** (-s0) * np.exp(-n / X)).sum())


def fit_and_report(P, name, lam, Xs, with_poles):
    Vs = np.array([V_of(lam, X) for X in Xs])
    sX = np.sqrt(Xs)
    # pole terms + Gamma(w)-pole tail terms at w = -1/2, -1
    basis = np.column_stack([sX * np.log(Xs), sX, np.ones(len(Xs)),
                             1.0 / sX, 1.0 / Xs])
    coef, res, _, _ = np.linalg.lstsq(basis, Vs, rcond=None)
    fitres = Vs - basis @ coef
    A, B, C = coef[0], coef[1], coef[2]
    P(f"  {name}:")
    for X, V in list(zip(Xs, Vs))[::3]:
        P(f"    X = {X:8.0f}   V_X(1/2) = {V:14.6f}")
    P(f"    fit V = A sqrt(X) log X + B sqrt(X) + C + D/sqrt(X) + E/X:")
    P(f"    A = {A:+.6f}  B = {B:+.6f}  C = {C:+.9f}  D = {coef[3]:+.4f}  "
      f"E = {coef[4]:+.3f}  (rms {np.sqrt((fitres ** 2).mean()):.2e})")
    return A, B, C, float(np.sqrt((fitres ** 2).mean()))


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# STAGE 2 -- the windowed center-reading: calibration, then the far side")
    P("#" * 78)
    P()
    Xs = np.array([100.0 * 2 ** (k / 2.0) for k in range(15)])  # 100..12800, 12 pts/decade-ish

    P("building the degenerate bank (exact 11-local, degree drop 16 -> 6)...")
    lam_d = build_bank("degenerate", NMAX)
    P("building the primitive bank (exact Steinberg legs at 11,37,53,61)...")
    lam_p = build_bank("primitive", NMAX)
    P()

    P("CALIBRATION (degenerate f^{x4}; the zeta^2 double pole is the A,B terms;")
    P(f"C must land on the certified factored center {TARGET}):")
    A, B, C, rms = fit_and_report(P, "degenerate", lam_d, Xs, True)
    err = abs(C - TARGET)
    okC = err < 0.02
    P(f"    C vs certified target: |{C:.6f} - {TARGET}| = {err:.2e}   "
      f"{'CALIBRATED' if okC else 'FAIL'}")
    P()

    P("THE FAR SIDE (primitive quadruple; occupancy 0 => A, B must vanish;")
    P("C is the prediction):")
    A2, B2, C2, rms2 = fit_and_report(P, "primitive", lam_p, Xs, False)
    okP = abs(A2) < 0.02 and abs(B2) < 0.5
    P(f"    pole-freeness at the value level: A = {A2:+.4f}, B = {B2:+.4f}   "
      f"{'CONFIRMED' if okP else 'NOT CONFIRMED'}")
    P()

    P("VERDICT:")
    if okC and okP:
        P(f"  The protocol calibrates on the factorable case (C lands on the")
        P(f"  certified assembly within {err:.1e}) and the primitive fit")
        P(f"  confirms pole-freeness independently.  THE FAR-SIDE VALUE:")
        P(f"    L(f1 x f2 x f3 x f4, 1/2)_unitary  ~=  {C2:.6f}  (+/- ~{max(err, rms2):.0e})")
        P(f"  -- the center of an L-function with no classical definition, no")
        P(f"  functional equation, and no prior numerical value: the first")
        P(f"  entry in grade four's ledger, published as a falsifiable")
        P(f"  prediction with its calibration pedigree attached.")
    else:
        P(f"  Calibration status: degenerate {okC}, primitive pole-freeness")
        P(f"  {okP} -- do not read the prediction until both hold.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "farside_center_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to farside_center_results.txt]")


if __name__ == "__main__":
    main()
