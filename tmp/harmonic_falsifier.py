"""The wrong-harmonic falsifier: every reading must FAIL when mis-clocked.

Sam's design (2026-07-12): scale the battery up a regular harmonic ladder with
increasing roots of unity, and falsify each reading by deliberately using the
WRONG harmonic or the WRONG root.  A reading procedure that lands regardless of
the clock it is read with is fabricating its own signal (the unit-1 false-null
method law, turned into a control column).  Three controls, all in-house:

(F1) WRONG ROOT OF UNITY -- the CM clock relations, swapped.
     27a1's clock satisfies tau^2 - tau + 1 = 0 (the mu_6 / disc -3 relation);
     32a1's satisfies tau^2 + 1 = 0 (the mu_4 / disc -4 relation).  Reading
     each curve with its OWN root must land at ~0; reading it with the OTHER
     curve's root must miss by O(1).

(F2) WRONG HARMONIC (tower placement) -- the silence certificate.
     A placement k is admissible only if the sub-ladder below k is silent
     (max |jet_<k| < FLOOR * |jet_k|).  For every curve exactly ONE k in 0..4
     may pass -- the measured k*.  Every wrong harmonic must be REJECTED by
     the silence certificate, and for the rank-0 curves the Sha square-landing
     must succeed at k = 0 only.

(F3) WRONG HARMONIC RATE (FE shape) -- the eps certificate, detuned.
     The split-vs-direct Lambda(3) certificate matches at ~1e-8 with the true
     conductor scale sqrt(N); rerun with the detuned scale sqrt(2N): NO sign
     may match.  (The certificate must certify the harmonic rate, not just
     the sign.)

Ladder context: mu_2/mu_1 = the rational-rank census (drift_observability),
mu_3/mu_4/mu_6 = the CM clocks here, mu_7/mu_3 = the F21 rung already landed
(f21_gl3_multirail.py, exact zeta_7/zeta_3 focal closure); the mu_5 rung
(Jacobi-sum point counts, genus 2) is the named next build.

Run: python3 harmonic_falsifier.py     (~3 min, oracle-free)
"""
import sys, os, math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
import jet_census as JC
import hodge_clock_demo as HC
import drift_observability as DO

FLOOR = 5e-4


def eps_certificate_scaled(N_arith, ainv, scale_N, s0=3.0):
    """The split-vs-direct certificate with the y-normalization read at
    sqrt(scale_N) -- scale_N = N_arith is the true rate; anything else is a
    detuned rate and must fail for BOTH signs.  a_n always from the true curve."""
    import mpmath as mp
    nmax = max(4000, int(50 * math.sqrt(N_arith)) + 200)
    a, _ = JC._bank_for(N_arith, ainv, nmax)
    an = a[1:]
    n = np.arange(1, nmax + 1, dtype=np.float64)
    y = 2.0 * math.pi * n / math.sqrt(scale_N)
    direct = float(np.sum(an * math.gamma(s0) * y ** (-s0)))
    mask = y < 45.0
    ym, am = y[mask], an[mask]
    g3 = (ym ** 2 + 2 * ym + 2) * np.exp(-ym)
    gm1 = np.array([float(mp.gammainc(2 - s0, mp.mpf(v))) for v in ym])
    A = float(np.sum(am * ym ** (-s0) * g3))
    B = float(np.sum(am * ym ** (s0 - 2.0) * gm1))
    return {e: abs((A + e * B) - direct) / max(abs(direct), 1e-30)
            for e in (+1, -1)}


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# HARMONIC FALSIFIER -- every reading must fail when mis-clocked")
    P("#" * 78)
    P()

    # ---------------- F1: wrong root of unity (CM clock relations) ----------
    P("(F1) WRONG ROOT OF UNITY -- CM clock relations, right vs swapped:")
    tau27, _ = HC.curve_tau(HC.CURVES["27a1"][1])
    tau32, _ = HC.curve_tau(HC.CURVES["32a1"][1])
    # disc -3 has two fundamental-domain corners (zeta_3 and zeta_6, SL2-equal):
    # the invariant is the DISCRIMINANT, so the relation residual takes the min
    # over the integer quadratics of that discriminant.
    rel_disc3 = lambda t: min(abs(t * t - t + 1), abs(t * t + t + 1))
    rel_disc4 = lambda t: abs(t * t + 1)
    r27_right, r27_wrong = rel_disc3(tau27), rel_disc4(tau27)
    r32_right, r32_wrong = rel_disc4(tau32), rel_disc3(tau32)
    P(f"    27a1 (mu_6 clock): own root residual {r27_right:.2e}   "
      f"wrong root {r27_wrong:.2e}")
    P(f"    32a1 (mu_4 clock): own root residual {r32_right:.2e}   "
      f"wrong root {r32_wrong:.2e}")
    f1_ok = (r27_right < 1e-8 and r32_right < 1e-8
             and r27_wrong > 0.5 and r32_wrong > 0.5)
    P(f"    => right root lands, wrong root misses by O(1): "
      f"{'PASS' if f1_ok else 'FAIL'}")
    P()

    # ---------------- F2: wrong harmonic placement (silence certificate) ----
    P("(F2) WRONG HARMONIC -- the silence certificate rejects every k != k*:")
    P(f"    {'curve':8s} {'admissible k (of 0..4)':>24s} {'k*':>4s} "
      f"{'sq-land k=0':>12s} {'sq-land at wrong k':>19s}")
    f2_ok = True
    for label, N, ainv, ddim, sha_known in DO.CURVES:
        eps, _, _ = DO.eps_certificate(N, ainv)
        jets = DO.ladder(N, ainv, eps)
        scale = max(abs(v) for v in jets)
        admissible = []
        for k in range(5):
            if abs(jets[k]) < FLOOR * scale:
                continue
            silent = all(abs(jets[j]) < FLOOR * abs(jets[k]) for j in range(k))
            if silent:
                admissible.append(k)
        kstar = admissible[0] if admissible else None
        unique = (len(admissible) == 1)
        f2_ok = f2_ok and unique and (kstar == ddim)
        # square-landing: normalized response at k=0 vs at a wrong k
        Om = SH.real_period(ainv)
        prodcp, _ = SH.tamagawa_product(N, ainv)
        T, _ = SH.torsion_order(N, ainv)
        norm = T * T / (Om * prodcp)
        if ddim == 0:
            right = jets[0] * norm
            wrongk = 1
            wrong = jets[wrongk] * norm
            dr = abs(right - round(math.sqrt(abs(right))) ** 2)
            sq = round(math.sqrt(abs(wrong)))
            dw = min(abs(wrong - sq * sq), abs(wrong - (sq + 1) ** 2))
            land_r = dr < 1e-2 and right > 0
            land_w = dw < 1e-2 and wrong > 0
            f2_ok = f2_ok and land_r and not land_w
            P(f"    {label:8s} {str(admissible):>24s} {str(kstar):>4s} "
              f"{right:8.4f} {'OK' if land_r else 'NO':>3s} "
              f"   k={wrongk}: {wrong:8.4f} {'LANDS (bad)' if land_w else 'rejected':>12s}")
        else:
            P(f"    {label:8s} {str(admissible):>24s} {str(kstar):>4s} "
              f"{'-':>12s} {'(dim>=1: silence cert only)':>19s}")
    P(f"    => exactly one admissible harmonic per curve, = drift dim; "
      f"square-landing only at the right one: {'PASS' if f2_ok else 'FAIL'}")
    P()

    # ---------------- F3: wrong harmonic rate (detuned FE scale) ------------
    P("(F3) WRONG RATE -- the eps certificate at the true vs detuned scale:")
    f3_ok = True
    for label, N, ainv, _, _ in DO.CURVES[:4]:
        res_true = eps_certificate_scaled(N, ainv, N)
        res_wrong = eps_certificate_scaled(N, ainv, 2 * N)
        bt, bw = min(res_true.values()), min(res_wrong.values())
        # the criterion is RELATIVE: the detuned rate must miss by orders of
        # magnitude against the true rate's match (>= 1e3 separation)
        ok = bt < 1e-6 and bw > 1e3 * bt
        f3_ok = f3_ok and ok
        P(f"    {label:8s} true-scale best match {bt:.1e}   "
          f"detuned-scale best {bw:.1e}   separation {bw / max(bt, 1e-300):.1e}x"
          f"   {'PASS' if ok else 'FAIL'}")
    P(f"    => the certificate certifies the harmonic rate itself: "
      f"{'PASS' if f3_ok else 'FAIL'}")
    P()

    P("VERDICT:")
    if f1_ok and f2_ok and f3_ok:
        P("  Every reading lands with its own harmonic and root, and FAILS with")
        P("  the wrong root (F1), the wrong tower harmonic (F2), and the wrong")
        P("  rate (F3).  The readings are properties of the objects, not of the")
        P("  reading procedure -- the mis-clocked controls all bit.")
    else:
        P(f"  A CONTROL FAILED (F1 {f1_ok}, F2 {f2_ok}, F3 {f3_ok}) -- either an")
        P("  instrument defect or a reading that lands regardless of its clock.")
        P("  Publish per the falsifiability register and investigate.")
    P()
    P("  Ladder state: mu_1/mu_2 rungs = the drift census; mu_3/mu_4/mu_6 = the")
    P("  CM clocks (F1); mu_7/mu_3 = the F21 GL(3) rung (f21_gl3_multirail.py,")
    P("  exact zeta_7 focal closure, already landed).  Next build: the mu_5 rung")
    P("  (Jacobi-sum point counts, genus-2 superelliptic), then regular scaling")
    P("  in the order of the root with the same three falsifier columns.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "harmonic_falsifier_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to harmonic_falsifier_results.txt]")


if __name__ == "__main__":
    main()
