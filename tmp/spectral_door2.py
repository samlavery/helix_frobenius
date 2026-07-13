"""Spectral door, second pass: FIXED-HEAD lane-balance scan.

Diagnosis from pass 1 (spectral_door.py, gate 1/12): the house locator's
diagonal schedule Z = e^y oversamples conductor-1 fibers (zeta at y=14: 1.2M
terms vs AFE need ~2) but STARVES higher conductor at low ordinates (Sym3
first zero y=2.32: 10 terms vs need ~5 -- 2x margin where Delta/E11 had
~200x).  The rails and the closure measure are right; the head schedule is
the conductor-1 special case.  Fix: park the head at maximum data (Z fixed)
and scan the ordinate -- the horizontal slice of the same geometry:

    F(t) = sum_lane u_lane sum_{n in lane} |lam_n| w(n/Z) x^{-1/2} e^{-it log x},
    closure c(t) = |F|/max|R_lane|,   x = (pi/3) n,  Z = const.

Gate: Sym3(11a1) vs the 12 PARI oracle zeros, Z = 2e5.  Falsifier: unit arrow
scale.  Target: quadruple at max feasible head (pre-registered: no events --
AFE scale 3e24; the gate calibrates what a passing instrument looks like).

Run: python3 spectral_door2.py    (~2-4 min)
"""
import sys, os, math
import numpy as np

TMP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TMP)
sys.path.insert(0, os.path.dirname(TMP))
import focal_closure as FL
from harmonic_lattice import fast_bank, sym_eigs
from spectral_door import ORACLE_S3, quad_eigs_factory

PI3 = math.pi / 3.0


class FixedHead:
    def __init__(self, lam, Z, arrow=PI3):
        lam = np.real(lam)
        N = min(len(lam) - 1, int(Z))
        n = np.arange(1, N + 1, dtype=np.float64)
        w = FL.growth_window(n / Z)
        x = arrow * n
        self.base = np.abs(lam[1:N + 1]) * w * x ** -0.5
        self.logx = np.log(x)
        self.pos = lam[1:N + 1] > 0
        self.neg = lam[1:N + 1] < 0

    def closure(self, t):
        ph = np.exp(-1j * t * self.logx)
        Rp = complex((self.base * ph)[self.pos].sum())
        Rm = complex((self.base * ph)[self.neg].sum())
        F = Rp - Rm
        m = max(abs(Rp), abs(Rm))
        return abs(F) / m if m > 0 else 1.0


def scan_fixed(fh, t0, t1, per_unit=300, cut=2e-2):
    ts = np.linspace(t0, t1, max(9, int((t1 - t0) * per_unit)))
    cs = np.array([fh.closure(float(t)) for t in ts])
    med = float(np.median(cs))
    step = ts[1] - ts[0]
    out = []
    for i in range(1, len(ts) - 1):
        if cs[i] < cs[i - 1] and cs[i] < cs[i + 1] and cs[i] < 0.25 * med:
            y = FL._golden(fh.closure, float(ts[i]) - 1.5 * step,
                           float(ts[i]) + 1.5 * step)
            d = fh.closure(y)
            if d < cut:
                out.append((y, d))
    return out, cs, med


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# SPECTRAL DOOR 2 -- fixed-head lane-balance scan")
    P("#" * 78)
    P()
    lam3 = fast_bank(sym_eigs(3), 200000)
    lamq = fast_bank(quad_eigs_factory(), 200000)
    P("banks built (Sym3, quadruple to 2e5)")
    P()

    P("GATE S3 -- fixed head Z = 2e5, t in [1.8, 12.2]:")
    fh3 = FixedHead(lam3, 2e5)
    ev, cs, med = scan_fixed(fh3, 1.8, 12.2)
    used, hits = set(), 0
    for y, d in ev:
        best, bd = None, 9e9
        for i, z in enumerate(ORACLE_S3):
            if i not in used and abs(y - z) < bd:
                best, bd = i, abs(y - z)
        if best is not None and bd < 0.05:
            used.add(best)
            hits += 1
            P(f"    t = {y:10.6f}   depth {d:.2e}   = oracle "
              f"{ORACLE_S3[best]:.6f}   |diff| {bd:.2e}")
        else:
            P(f"    t = {y:10.6f}   depth {d:.2e}   SPURIOUS?")
    missed = [f"{ORACLE_S3[i]:.4f}" for i in range(len(ORACLE_S3))
              if i not in used]
    P(f"  matched {hits}/12; missed: {missed if missed else 'none'}; "
      f"median closure {med:.3f}")
    pair = sum(1 for y, _ in ev if abs(y - 7.7516) < 0.05) and \
        sum(1 for y, _ in ev if abs(y - 8.0052) < 0.05)
    P(f"  close-pair 7.75/8.01: {'SPLIT' if pair else 'not split'}")
    P()

    P("FALSIFIER -- unit arrow scale, same head:")
    fhu = FixedHead(lam3, 2e5, arrow=1.0)
    evu, csu, medu = scan_fixed(fhu, 1.8, 12.2)
    hitsu = sum(1 for y, d in evu if min(abs(y - z) for z in ORACLE_S3) < 0.05)
    P(f"  events {len(evu)}, oracle-matched {hitsu}, median closure {medu:.3f}")
    P()

    P("TARGET -- quadruple, fixed head Z = 2e5, t in [0.05, 6.0]:")
    fhq = FixedHead(lamq, 2e5)
    evq, csq, medq = scan_fixed(fhq, 0.05, 6.0, per_unit=400)
    P(f"  events below cut: {len(evq)}")
    for y, d in evq[:12]:
        P(f"    t = {y:10.6f}   depth {d:.2e}")
    P(f"  profile: median {medq:.4f}, min {csq.min():.4f}")
    verdict = "EVENTS -- hostile checks next" if evq else \
        "no resolvable events, as pre-registered (the spectral toll, measured)"
    P(f"  {verdict}")

    with open(os.path.join(TMP, "spectral_door2_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to spectral_door2_results.txt]")


if __name__ == "__main__":
    main()
