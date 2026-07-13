"""The decisive experiment, part 1: carrier-window center readings vs the wall.

Wall four: the primitive quadruple's center needs ~sqrt(Q) ~ 3e24 coefficients
under ANY black-box linear method -- unreachable.  The carrier's counter-claim
is that the coefficients are NOT black-box (four curves' local data generate
all of them), realized by cell machinery at the fiber's own harmonic scale.

This instrument tests the LINEAR half of that claim, with gates on reachable
truths and the wrong-harmonic falsifier attached:

  READER: the log-scale carrier window
      R(Y) = sum_n lambda_n n^{-1/2} w(log n / log Y),
  w the canonical C-infinity window (smooth entry, no clipped edge -- the
  never-clip method law), evaluated on an ASCENDING Y-ladder; convergence of
  R(Y) to the true center at Y-scales ~ sqrt(Q) is the calibration.

  GATE RS4:  L(11a1 x 37a1, 1/2) -- degree 4, pole-free, Q = (11*37)^2,
             sqrt(Q) = 407: the exact center is computed by the certified
             evaluator (shape scanned, two-point split-vs-direct), and the
             reader must converge to it within the reachable ladder.
  GATE S4:   L(Sym4 11a1, 1/2) = 0.6058010 (certified): same test, degree 5,
             sqrt(Q) = 121.
  FALSIFIER: cell-alignment -- the same reader with the window cut at
             pi/3-cell-aligned vs deliberately misaligned boundaries; and the
             unit-1 comparison (e^{-n/X}) from stage 2.
  THE WALL:  the primitive quadruple bank under the same reader ladder --
             REPORTED HONESTLY: if R(Y) is transient-dominated at every
             reachable Y (as the information bound demands for any linear
             reader), that is the measured content of wall four, and the
             no-sqrt(Q) claim is thereby located PRECISELY in the nonlinear
             adapted machinery (forcible closure with solved warp weights),
             the named follow-on experiment.

Run: python3 carrier_center.py     (~5-8 min)
"""
import sys, os, math, cmath
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
import center_reading as CR
import farside_center as FC

mp.mp.dps = 25


# ---------------------------------------------------------------- the window
def wsmooth(u):
    """Canonical C-infinity window: 1 on [0, 1/2], smooth to 0 at 1."""
    if u <= 0.5:
        return 1.0
    if u >= 1.0:
        return 0.0
    x = (u - 0.5) / 0.5
    a = math.exp(-1.0 / max(1e-12, 1.0 - x))
    b = math.exp(-1.0 / max(1e-12, x))
    return a / (a + b)


def reader(lam, Y, s0=0.5, align=None):
    """R(Y) = sum lambda_n n^{-s0} w(log n / log Y); align = (h, offset) cuts
    the window argument at cell boundaries (quantized) for the alignment test."""
    n = np.arange(1, len(lam), dtype=float)
    u = np.log(n) / math.log(Y)
    if align is not None:
        h, off = align
        u = (np.floor((np.log(n) - off) / h) * h + off) / math.log(Y)
        u = np.clip(u, 0.0, 2.0)
    w = np.array([wsmooth(x) for x in u])
    return float((lam[1:] * n ** (-s0) * w).sum())


# ------------------------------------------------------------ RS degree-4 bank
def bank_rs(nmax):
    """lambda_n of L(11a1 x 37a1), unitary, exact Steinberg legs."""
    A1, A2 = (0, -1, 1, -10, -20), (0, 0, 1, -1, 0)
    lam = np.zeros(nmax + 1)
    lam[1] = 1.0
    for p in SH.sieve_primes(nmax):
        kmax = int(math.log(nmax) / math.log(p))
        if p == 11:
            alpha = 1 / math.sqrt(11)
            t2 = FC.theta_of(A2, p)
            eigs = [alpha * cmath.exp(1j * s * t2) for s in (1, -1)]
        elif p == 37:
            alpha = 1 / math.sqrt(37)      # a_37(37a1) = 1
            t1 = FC.theta_of(A1, p)
            eigs = [alpha * cmath.exp(1j * s * t1) for s in (1, -1)]
        else:
            t1, t2 = FC.theta_of(A1, p), FC.theta_of(A2, p)
            eigs = [cmath.exp(1j * (s1 * t1 + s2 * t2))
                    for s1 in (1, -1) for s2 in (1, -1)]
        c = FC.local_coeffs_eigs(eigs, kmax)
        for k in range(kmax, 0, -1):
            pk = p ** k
            for m in range(1, nmax // pk + 1):
                if m % p:
                    lam[m * pk] += c[k] * lam[m]
    return lam


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# CARRIER CENTER READINGS -- gates on reachable truth, then the wall")
    P("#" * 78)
    P()

    # ---- exact RS center via the certified evaluator (shape scanned)
    P("GATE RS4 setup: exact L(11a1 x 37a1, 1/2) via the evaluator:")
    lam4 = bank_rs(20000)
    Q4 = (11 * 37) ** 2
    best = None
    for d1 in (0.0, 1.0):
        for d2 in (0.0, 1.0):
            if d2 < d1:
                continue
            G4 = CR.make_G(Q4, [('C', 1.0), ('R', d1), ('R', d2)])
            e_a, r_a, _ = CR.certify(G4, lam4, s0=2.5, T=60)
            e_b, r_b, _ = CR.certify(G4, lam4, s0=2.2, T=60)
            r = max(r_a, r_b)
            P(f"  shape GammaC(s+1) GammaR(s+{d1:.0f}) GammaR(s+{d2:.0f}): "
              f"eps {e_a:+d}/{e_b:+d}, match {r_a:.2e}, {r_b:.2e}")
            if e_a == e_b and (best is None or r < best[0]):
                best = (r, d1, d2, e_a, G4)
    r, d1, d2, e4, G4 = best
    ok_shape = r < 1e-4
    LRS = CR.central_value(G4, e4, lam4, T=60) if ok_shape else None
    if LRS is not None:
        P(f"  CERTIFIED shape (deltas {d1:.0f},{d2:.0f}, eps {e4:+d}); "
          f"L_RS(1/2) = {LRS.real:.7f}")
    P()

    # ---- reader ladders
    def ladder(P, name, lam, Ys, truth=None):
        P(f"  {name}:")
        vals = []
        for Y in Ys:
            R = reader(lam, Y)
            vals.append(R)
            t = f"   (truth {truth:.6f}, err {abs(R - truth):.2e})" if truth else ""
            P(f"    Y = {Y:9.0f}   R(Y) = {R:12.6f}{t}")
        return vals

    P("GATE RS4 (sqrt(Q) = 407; the ladder crosses it):")
    Ys4 = [200, 800, 3200, 12800, 18000]
    v4 = ladder(P, "RS 11a1 x 37a1", lam4, Ys4, LRS.real if LRS else None)
    err4 = abs(v4[-1] - LRS.real) if LRS else 9e9
    stab4 = abs(v4[-1] - v4[-2])
    okRS = LRS is not None and err4 < 0.05 and stab4 < 0.05
    P(f"  top-of-ladder error {err4:.3f}, stability {stab4:.3f}   "
      f"GATE RS4: {'PASS' if okRS else 'FAIL'}")
    P()

    P("GATE S4 (Sym4, sqrt(Q) = 121, truth 0.6058010):")
    lam5 = CR.bank_sym_unitary(4, 20000)
    v5 = ladder(P, "Sym4 11a1", lam5, Ys4, 0.6058010)
    err5, stab5 = abs(v5[-1] - 0.6058010), abs(v5[-1] - v5[-2])
    okS4 = err5 < 0.05 and stab5 < 0.05
    P(f"  top-of-ladder error {err5:.3f}, stability {stab5:.3f}   "
      f"GATE S4: {'PASS' if okS4 else 'FAIL'}")
    P()

    P("ALIGNMENT FALSIFIER (RS4 at Y = 12800): pi/3-cell-aligned vs misaligned:")
    h = math.pi / 3
    Ra = reader(lam4, 12800, align=(h, 0.0))
    Rm = reader(lam4, 12800, align=(h, h / 2))
    Rs = reader(lam4, 12800)
    P(f"  smooth {Rs:.6f}   cell-aligned {Ra:.6f}   misaligned {Rm:.6f}")
    P(f"  (alignment sensitivity {abs(Ra - Rm):.2e} -- reported, two-sided)")
    P()

    P("THE WALL (primitive quadruple, sqrt(Q) ~ 3e24; ladder tops at 2e5):")
    lam16 = FC.build_bank("primitive", 300000)
    Ys16 = [1000, 4000, 16000, 64000, 200000]
    v16 = ladder(P, "primitive quadruple", lam16, Ys16)
    drift = abs(v16[-1] - v16[-2])
    P(f"  top-of-ladder drift {drift:.3f}")
    P()

    P("VERDICT:")
    if okRS and okS4:
        P("  The linear carrier window CONVERGES on every reachable truth (RS4")
        P("  crossing its sqrt(Q), Sym4 well past it) -- the reader is sound.")
        if drift < 0.05:
            P(f"  And the primitive reading is STABLE: R = {v16[-1]:.6f} --")
            P("  investigate immediately; stability far below sqrt(Q) would be")
            P("  extraordinary and demands hostile checks before any claim.")
        else:
            P(f"  The primitive reading is transient-dominated at every reachable")
            P(f"  Y (drift {drift:.3f}), exactly as the information bound demands")
            P("  for ANY linear reader: wall four is measured, not assumed.  The")
            P("  no-sqrt(Q) claim is hereby located PRECISELY: it lives in the")
            P("  nonlinear adapted machinery -- forcible closure with solved warp")
            P("  weights, consuming the fiber's structural law rather than its")
            P("  coefficient stream.  That is the named follow-on experiment, now")
            P("  with its calibration gates already passing.")
    else:
        P(f"  A gate failed (RS4 {okRS}, S4 {okS4}) -- fix the reader before")
        P("  interpreting anything at the wall.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "carrier_center_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to carrier_center_results.txt]")


if __name__ == "__main__":
    main()
