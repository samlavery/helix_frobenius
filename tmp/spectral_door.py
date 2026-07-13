"""The spectral door: the canonical focal locator, multi-rail, at degree 4 and 16.

Uses the HOUSE locator (focal_closure.py -- Family/lane_state/scan, unchanged)
per the method law: growth-window head at Z = e^y, pi/3 arrow scale, projective
lane closure |sum u R|/max|R|, events = deep minima.  Rails = the lane split
(Sam: the helix supports multiple rails; sign lanes carried Delta/E11, the
same split carries the wider banks here).

GATE S3 (first locator test beyond degree 2): Sym3(11a1), degree 4, Q = 1331.
  Oracle zeros (PARI lfunzeros, fetched 2026-07-12): 2.3200, 3.5919, 4.6226,
  5.5086, 6.8911, 7.7516, 8.0052, 8.8906, 9.3743, 10.3713, 11.1165, 11.7101.
  Includes the close pair 7.7516/8.0052 (gap 0.25 < naive resolution 2pi/y
  ~ 0.79 at y = 8): does nonlinear lane-balance beat linear resolution?

FALSIFIER: the same scan at unit arrow scale (the method-law wrong scale) --
  events must degrade (unit-1 misses the closure).

TARGET: the primitive quadruple, degree 16, sign rails.  PRE-REGISTERED
  expectation: NO deep events at reachable head heights -- the truncated
  readout is not yet the function (AFE scale sqrt(Q) ~ 3e24) and zero spacing
  2pi/log Q ~ 0.056 is beneath reach: the spectral form of the toll, measured.
  Any structure found instead is the surprise to chase.

Run: python3 spectral_door.py     (~2-5 min)
"""
import sys, os, math, cmath
import numpy as np

TMP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TMP)
sys.path.insert(0, os.path.dirname(TMP))
import focal_closure as FL
from harmonic_lattice import fast_bank, sym_eigs
from theta_cache import theta_table

ORACLE_S3 = [2.32002097235490, 3.59188107722661, 4.62262661360576,
             5.50863312034553, 6.89114051738631, 7.75161236436357,
             8.00520424119355, 8.89055564767432, 9.37430446132835,
             10.3713293439151, 11.1164766128061, 11.7101444785548]
LABS = ["11a1", "37a1", "53a1", "61a1"]
LEVELS = [11, 37, 53, 61]


def quad_eigs_factory():
    TH = {l: theta_table(l) for l in LABS}

    def eigs(p):
        if p in LEVELS:
            i = LEVELS.index(p)
            alpha = 1 / math.sqrt(p)
            ths = [float(TH[LABS[j]][p]) for j in range(4) if j != i]
            out = []
            for s1 in (1, -1):
                for s2 in (1, -1):
                    for s3 in (1, -1):
                        ph = s1 * ths[0] + s2 * ths[1] + s3 * ths[2]
                        out.append(alpha * cmath.exp(1j * ph))
            return out
        ths = [float(TH[l][p]) for l in LABS]
        return [cmath.exp(1j * (s1 * ths[0] + s2 * ths[1] + s3 * ths[2]
                                + s4 * ths[3]))
                for s1 in (1, -1) for s2 in (1, -1)
                for s3 in (1, -1) for s4 in (1, -1)]
    return eigs


def sign_family(name, lam_full):
    lam_full = np.real(lam_full)

    def make(N):
        lam = lam_full[:N + 1]
        return lam.astype(np.complex128), np.sign(lam).astype(np.int64)
    return FL.Family(name, "cusp", make, max_N=len(lam_full) - 1)


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# SPECTRAL DOOR -- house focal locator, sign rails, degree 4 then 16")
    P("#" * 78)
    P()
    P("building banks (vectorized sieve + theta cache)...")
    S3 = sign_family("sym3", fast_bank(sym_eigs(3), 210000))
    QD = sign_family("quad", fast_bank(quad_eigs_factory(), 10000))
    P()

    P("GATE S3 -- scan y in [1.8, 12.2] (pi/3 arrow scale, house defaults):")
    ev = FL.scan(S3, 1.8, 12.2, per_unit=240)
    P(f"  events found: {len(ev)} (oracle count in window: {len(ORACLE_S3)})")
    used = set()
    hits = 0
    for e in ev:
        best, bd = None, 9e9
        for i, z in enumerate(ORACLE_S3):
            if i not in used and abs(e.y - z) < bd:
                best, bd = i, abs(e.y - z)
        tag = ""
        if best is not None and bd < 0.05:
            used.add(best)
            hits += 1
            tag = f"= oracle {ORACLE_S3[best]:.6f}   |diff| {bd:.2e}"
        else:
            tag = "SPURIOUS?"
        P(f"    y = {e.y:10.6f}   depth {e.depth:.2e}   {tag}")
    missed = [f"{ORACLE_S3[i]:.4f}" for i in range(len(ORACLE_S3))
              if i not in used]
    P(f"  matched {hits}/{len(ORACLE_S3)}; missed: {missed if missed else 'none'}")
    pair_ok = any(abs(e.y - 7.7516) < 0.05 for e in ev) and \
        any(abs(e.y - 8.0052) < 0.05 for e in ev)
    P(f"  close-pair 7.75/8.01 (gap 0.25 < linear resolution 0.79): "
      f"{'SPLIT' if pair_ok else 'not split'}")
    P()

    P("FALSIFIER -- same object, unit arrow scale (wrong harmonic):")
    ys = np.linspace(1.8, 12.2, 1200)
    cs_u = np.array([FL.closure(S3, float(t), arrow_scale=1.0) for t in ys])
    cs_h = np.array([FL.closure(S3, float(t)) for t in ys])
    deep_u = int(np.sum((cs_u[1:-1] < cs_u[:-2]) & (cs_u[1:-1] < cs_u[2:])
                        & (cs_u[1:-1] < 2e-2)))
    P(f"  deep minima (< 2e-2): pi/3 scale grid-level "
      f"{int(np.sum((cs_h[1:-1] < cs_h[:-2]) & (cs_h[1:-1] < cs_h[2:]) & (cs_h[1:-1] < 2e-2)))}, "
      f"unit scale {deep_u}   (median closure: pi/3 {np.median(cs_h):.3f}, "
      f"unit {np.median(cs_u):.3f})")
    P()

    P("TARGET -- primitive quadruple, sign rails, y in [1.8, 9.0]:")
    evq = FL.scan(QD, 1.8, 9.0, per_unit=300)
    ysq = np.linspace(1.8, 9.0, 1500)
    csq = np.array([FL.closure(QD, float(t)) for t in ysq])
    P(f"  events below house depth cut: {len(evq)}")
    for e in evq[:10]:
        P(f"    y = {e.y:10.6f}   depth {e.depth:.2e}")
    P(f"  closure profile: median {np.median(csq):.4f}, min {csq.min():.4f} "
      f"at y = {ysq[csq.argmin()]:.3f}")
    P(f"  (gate depths were ~1e-6..1e-3; quadruple minima at "
      f"{csq.min():.2e} => {'EVENTS - investigate' if csq.min() < 2e-2 else 'no resolvable events, as pre-registered'})")
    P()

    P("READING:")
    if hits >= 10:
        P("  GATE PASSES: the house locator, unchanged, locates degree-4 zeros")
        P("  on sign rails -- first validation beyond degree 2, conductor 1331.")
    else:
        P(f"  GATE PARTIAL ({hits}/12): locator behavior at degree 4 measured;")
        P("  interpret the target only through what the gate supports.")
    P("  The quadruple row is the measured content of the spectral toll at")
    P("  pi/3 scale and reachable head heights; the multi-rail adapted scan")
    P("  (per-lane rails, conductor-adapted arrow scale) is the named next")
    P("  step if the door is to open wider.")

    with open(os.path.join(TMP, "spectral_door_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to spectral_door_results.txt]")


if __name__ == "__main__":
    main()
