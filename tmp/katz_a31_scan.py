"""RUNG 3 — in-house self-consistency scan for a_31(h) (the ramified U_31 eigenvalue,
31 | 124, outside the good-prime a_p engine).

Include h, h' at rung 0 with each trial a_31 = zeta^j (or 0), rebuild the Katz basis +
ordinary projector, and measure whether h then lands CLEAN-ORDINARY (h in O).  The correct
a_31 is the unique self-consistent one: h in-O residual = m' (full precision) AND the a_31
read back from the ordinary projection equals the trial value (fixed point).
"""
import sys
import time

import numpy as np

import katz_engine as K


class Quiet:
    def __call__(self, s=""):
        pass


def measure_h_in_O(cfg, ordk, a31_exp):
    """For h and h' built with a31_exp, return (in-O residual val, a_31 read-back exponent,
    is-zero) on the 31-coprime footprint."""
    p, MOD, W = cfg.p, cfg.MOD, cfg.window
    O_win, qpiv, invq = ordk["O_win"], ordk["qpiv"], ordk["invq"]
    al, be = ordk["hroots"]
    okcols = np.array([n for n in range(1, W) if n % 31 != 0], dtype=np.int64)
    out = []
    for conj in (False, True):
        hh = K.h_qexp(cfg, W, conj=conj, a31_exp=a31_exp)
        hs = K.stabilized(cfg, hh, be, W)
        c = K.vmod(hs[qpiv].astype(np.int64), invq, cfg)
        pred = K.vmod(c, O_win, cfg)
        vres = K.val_arr((pred[okcols] - hs[okcols]) % MOD, p, cfg.mp)
        a31read = int(pred[31]) % MOD
        land = [k for k in range(12) if (a31read - cfg.zpow[k]) % MOD == 0]
        out.append(dict(vres=vres, read=(land[0] if land else None),
                        zero=(a31read == 0)))
    return out


def main():
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    cfg = K.Cfg(13, m, zeta_res=7)
    log = Quiet()
    print(f"a_31 self-consistency scan  p=13 m={m}  (mp={cfg.mp}, D expected ~ ordinary rank)")
    print(f"{'a31_exp':>8} | {'D':>4} | gate3(i,ii,iii) | h vres  read  | hp vres read | self-consistent?")
    print("-" * 84)
    cands = [None] + list(range(12))
    rows = []
    for a in cands:
        t0 = time.time()
        trial = "0" if a is None else f"z{a}"
        # A WRONG a_31 makes h non-modular: E_12.h and its products leave M_13, so GATE 2's
        # overshoot probe fires and build_basis raises SystemExit.  The CORRECT a_31 builds
        # cleanly (span stays exactly dim M_13).  So a clean build IS the self-consistency
        # signal; we still confirm h then lands clean-ordinary in O.
        try:
            ctx = K.build_all(cfg, log, cache_tag=f"SCAN_p13_m{m}", a31_exp=a)
        except SystemExit:
            rows.append((a, None, None, None, None, False))
            print(f"{trial:>8} |    - |  GATE2 OVERSHOOT (non-modular: wrong a_31)          "
                  f"| no        [{time.time()-t0:.0f}s]", flush=True)
            continue
        ordk = ctx["ordk"]
        h, hp = measure_h_in_O(cfg, ordk, a)
        g3 = ordk["gate3"]
        readh = "0" if h["zero"] else (f"z{h['read']}" if h["read"] is not None else "??")
        readhp = "0" if hp["zero"] else (f"z{hp['read']}" if hp["read"] is not None else "??")
        consistent = (g3 == (True, True, True) and h["vres"] >= cfg.m and hp["vres"] >= cfg.m and
                      ((a is None and h["zero"]) or (a is not None and h["read"] == a)))
        rows.append((a, ordk["D"], g3, h, hp, consistent))
        print(f"{trial:>8} | {ordk['D']:>4} | {str(g3):>15} | "
              f"{h['vres']:>4}   {readh:>5} | {hp['vres']:>4}  {readhp:>5} | "
              f"{'*** YES ***' if consistent else 'no'}   [{time.time()-t0:.0f}s]",
              flush=True)
    winners = [r for r in rows if r[5]]
    print("-" * 84)
    if len(winners) == 1:
        a = winners[0][0]
        print(f"UNIQUE self-consistent a_31 = {'0' if a is None else 'zeta^%d' % a}  "
              f"[in-house determination]")
    elif not winners:
        print("NO self-consistent candidate — the rung-0 inclusion did not make h clean-ordinary; "
              "the fix needs rethinking.")
    else:
        print(f"AMBIGUOUS: {len(winners)} candidates self-consistent: "
              f"{[('0' if r[0] is None else 'z%d' % r[0]) for r in winners]}")


if __name__ == "__main__":
    main()
