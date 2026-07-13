"""Degree-6 rung, RAM-lean: Sym2(11a1) x 37a1 center via the house evaluator.

Replaces the Dokchitser route (1.1M-coefficient PARI vectors, GB-scale RAM,
opaque FE residual) with the house evaluator in pure numpy: float64 bank at
NMAX = 1.5e6 is 12 MB; the H-grid transforms are chunked log-grid interps.
The evaluator is now oracle-validated at degree 3/5 (PARI lfunsympow, diffs
~1e-6) and cross-validated at degree 4 (Dokchitser, 1.2e-5) -- its two-point
split-vs-direct certificate is a legitimate certification chain for degree 6.

Object: M = Sym2(11a1) (x) 37a1.  Degree 6, motivic weight 3.
  Q = 11^4 * 37^3 = 741610573   [11: Sym2(St)=sp(3), a=2, (x) unram dim 2
  => 4;  37: unram dim 3 (x) sp(2) => 3]
  Unitary shape GammaC(s+3/2) GammaC(s+1/2)^2; sign scanned (certify picks).
Locals: good p: {e^{i(2 s1 th1 + s2 th2)}}, s1 in {1,0,-1}, s2 in {1,-1};
  p=11: {e^{+-i th2(11)}}/11;  p=37: {e^{2i s1 th1(37)}}/sqrt(37).

Then GATE D6: the carrier window reads the same bank against the new truth
(sqrt(Q) = 27,232; the ladder crosses it) -- the third and deepest gate.

Run: python3 deg6_center.py      (~3-6 min, <300 MB)
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
import center_reading as CR
import farside_center as FC
from harmonic_lattice import fast_bank
from theta_cache import theta_table

TH1, TH2 = theta_table("11a1"), theta_table("37a1")

NMAX = 1_500_000
Q6 = 11 ** 4 * 37 ** 3
A1, A2 = (0, -1, 1, -10, -20), (0, 0, 1, -1, 0)


def eigs6(p):
    if p == 11:
        t2 = float(TH2[p])
        return [cmath.exp(1j * s * t2) / 11.0 for s in (1, -1)]
    if p == 37:
        t1 = float(TH1[p])
        return [cmath.exp(2j * s * t1) / math.sqrt(37.0) for s in (1, 0, -1)]
    t1, t2 = float(TH1[p]), float(TH2[p])
    return [cmath.exp(1j * (2 * s1 * t1 + s2 * t2))
            for s1 in (1, 0, -1) for s2 in (1, -1)]


def wsmooth_vec(u):
    w = np.zeros_like(u)
    w[u <= 0.5] = 1.0
    mid = (u > 0.5) & (u < 1.0)
    x = (u[mid] - 0.5) / 0.5
    a = np.exp(-1.0 / (1.0 - x))
    b = np.exp(-1.0 / x)
    w[mid] = a / (a + b)
    return w


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# DEGREE-6 CENTER (RAM-lean, house evaluator only)")
    P("#" * 78)
    P()
    P(f"building the degree-6 bank to {NMAX} (vectorized sieve)...")
    lam = np.real(fast_bank(eigs6, NMAX)).astype(np.float64)
    P(f"  bank RAM: {lam.nbytes / 1e6:.0f} MB;  lambda in "
      f"[{lam.min():.2f}, {lam.max():.2f}]")
    P()

    P(f"certification (Q = {Q6}, shape GammaC(s+3/2) GammaC(s+1/2)^2):")
    G6 = CR.make_G(Q6, [('C', 1.5), ('C', 0.5), ('C', 0.5)])
    e_a, r_a, _ = CR.certify(G6, lam, s0=2.5, T=60)
    e_b, r_b, _ = CR.certify(G6, lam, s0=2.2, T=60)
    P(f"  s0 = 2.5: eps {e_a:+d}, split-vs-direct match {r_a:.2e}")
    P(f"  s0 = 2.2: eps {e_b:+d}, split-vs-direct match {r_b:.2e}")
    ok = (e_a == e_b) and max(r_a, r_b) < 1e-3
    if not ok:
        P("  certificate FAILED -- do not read a value; scan shape/Q next.")
    v6 = None
    if ok:
        v6 = CR.central_value(G6, e_a, lam, T=60).real
        P(f"  CERTIFIED (eps {e_a:+d}):  L(Sym2(11a1) x 37a1, 1/2)_u = {v6:.8f}")
    P()

    if v6 is not None:
        P(f"GATE D6 -- carrier window vs the new truth (sqrt(Q) = "
          f"{math.isqrt(Q6)}):")
        n = np.arange(1, NMAX + 1, dtype=float)
        logn = np.log(n)
        base = lam[1:] / np.sqrt(n)
        prev = None
        for Y in (8000, 32000, 128000, 512000, 1_400_000):
            R = float((base * wsmooth_vec(logn / math.log(Y))).sum())
            P(f"    Y = {Y:8d}   R(Y) = {R:12.6f}   (truth {v6:.6f}, "
              f"err {abs(R - v6):.2e})")
            prev = R
        errD = abs(prev - v6)
        P(f"  top-of-ladder error {errD:.3f}   "
          f"GATE D6: {'PASS' if errD < 0.1 else 'FAIL'}")
        P()
        P("SUMMARY: new certified degree-6 center, evaluator-only chain")
        P("  (oracle-validated at deg 3/5, Dokchitser-validated at deg 4);")
        P("  the deepest certified truth on the ladder, one rung below the")
        P("  triple product.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "deg6_center_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to deg6_center_results.txt]")


if __name__ == "__main__":
    main()
