#!/usr/bin/env python3
"""
collatz_pi3_global.py  --  Sam's test: scale EVERYTHING by pi/3, integers included,
no unit-1 anywhere, so 'no gaps anywhere'.  Does the divergence picture dissolve?

The faithful 'everything on pi/3' frame is the completely-multiplicative winding
    phase(m) = (pi/3) * Omega(m),   Omega = big-omega (prime factors w/ multiplicity),
i.e. the phasor beta^Omega(m), beta = e^{i pi/3} (the paper's chart-conversion clock).
On this frame the MULTIPLICATIVE ops are exact, gap-free root-of-unity steps:
    /2  ->  Omega -= 1  ->  phase -= pi/3
    x3  ->  Omega += 1  ->  phase += pi/3
The ONLY place a gap can survive is the +1 (3n -> 3n+1), which is additive, not
multiplicative, so it can change Omega unpredictably:
    delta_i := Omega(3 n_i + 1) - Omega(3 n_i) = Omega(3 n_i + 1) - 1 - Omega(n_i).

This script measures, on the global-pi/3 frame:
  A) is delta_i identically 0 (NO gap anywhere -- Sam's hypothesis) or nonzero?
  B) the phase step decomposes as (pi/3)(1 + delta_i - v_i): +1(x3), gap(delta), -v(/2).
  C) does the Omega-phasor bank  B(orbit) = sum_i beta^{Omega(n_i)}  CLOSE (bounded)
     -- so 'divergence' is a unit-1 magnitude artifact and there is nothing to diverge
     on the carrier -- or does it fail to close (residual), i.e. the +1 gap is
     irreducible even after global rescaling?

No oracle.  Omega via a smallest-prime-factor sieve sized to the orbit maximum.
"""

import math
import numpy as np

BETA = math.pi / 3.0


def v2(m):
    v = 0
    while (m & 1) == 0:
        m >>= 1; v += 1
    return v


def orbit_values(n):
    """Odd-step Syracuse orbit n -> 1; return the list of odd values n_0..n_{k-1}
       and the valuation list."""
    vals = []; vs = []
    x = n
    while x != 1:
        vals.append(x)
        m = 3 * x + 1; v = v2(m); vs.append(v)
        x = m >> v
    return vals, vs


def build_spf(M):
    spf = np.zeros(M + 1, dtype=np.int64)
    i = 2
    while i <= M:
        if spf[i] == 0:
            block = spf[i::i]
            block[block == 0] = i
        i += 1
    return spf


def make_omega(spf):
    cache = {}

    def omega(m):
        if m <= 1:
            return 0
        c = cache.get(m)
        if c is not None:
            return c
        v = m; cnt = 0
        while v > 1:
            p = int(spf[v])
            while v % p == 0:
                v //= p; cnt += 1
        cache[m] = cnt
        return cnt
    return omega


def main(N):
    print("=" * 74)
    print("COLLATZ ON THE GLOBAL pi/3 FRAME  (beta^Omega, beta=e^{i pi/3})")
    print("=" * 74)
    # pass 1: orbits, find max value we must factor (n_i and 3 n_i + 1)
    orbits = []
    M = 2
    for n in range(3, N, 2):
        vals, vs = orbit_values(n)
        orbits.append((n, vals, vs))
        for x in vals:
            if 3 * x + 1 > M:
                M = 3 * x + 1
    print(f"  odd starts in [3,{N}):  {len(orbits)} orbits;  max integer to factor = {M}")
    print(f"  sieving smallest-prime-factor to {M} ...")
    spf = build_spf(M)
    omega = make_omega(spf)

    # ---- A) the +1 gap in the Omega frame ----
    dsum = 0; dsq = 0; dcnt = 0; dzero = 0
    dhist = {}
    for (n, vals, vs) in orbits:
        for x in vals:
            d = omega(3 * x + 1) - 1 - omega(x)      # delta_i
            dsum += d; dsq += d * d; dcnt += 1
            dzero += (d == 0)
            dhist[d] = dhist.get(d, 0) + 1
    dmean = dsum / dcnt
    dvar = dsq / dcnt - dmean * dmean
    print()
    print("A) THE +1 GAP  delta_i = Omega(3n+1) - Omega(3n)  (the only possible gap):")
    print(f"    steps={dcnt}   mean(delta)={dmean:+.4f}   var(delta)={dvar:.4f}"
          f"   P(delta=0)={dzero/dcnt:.4%}")
    top = sorted(dhist.items(), key=lambda kv: -kv[1])[:7]
    print("    delta histogram (value:frac): "
          + "  ".join(f"{d}:{c/dcnt:.3f}" for d, c in sorted(top)))
    if dzero == dcnt:
        print("    -> delta == 0 EVERYWHERE: no gap survives.  Sam's hypothesis holds.")
    else:
        print("    -> delta is NONZERO and spread: the +1 injects an IRREDUCIBLE gap even")
        print("       on the global pi/3 frame.  x3 and /2 are gap-free; the +1 is not.")

    # ---- B) phase-step decomposition sanity ----
    print()
    print("B) phase step / (pi/3) = 1(x3) + delta(+1 gap) - v(/2)  -- x3,/2 exact by")
    print("   construction; the gap lives entirely in delta (part A).")

    # ---- C) does the Omega-phasor bank close? ----
    # B(orbit) = sum_i beta^{Omega(n_i)} ; magnitude vs sqrt(k) (partial) vs O(1) (closure)
    ratios_sqrt = []          # |B| / sqrt(k)
    ratios_lin = []           # |B| / k
    modhist = np.zeros(6)
    for (n, vals, vs) in orbits:
        k = len(vals)
        s = 0j
        for x in vals:
            r = omega(x) % 6
            modhist[r] += 1
            s += complex(math.cos(BETA * r), math.sin(BETA * r))
        mag = abs(s)
        if k > 0:
            ratios_sqrt.append(mag / math.sqrt(k))
            ratios_lin.append(mag / k)
    rs = np.array(ratios_sqrt); rl = np.array(ratios_lin)
    print()
    print("C) Omega-phasor bank  B = sum_i beta^{Omega(n_i)}  per orbit:")
    print(f"    |B|/sqrt(k):  median={np.median(rs):.3f}  mean={rs.mean():.3f}"
          f"  95%={np.quantile(rs,0.95):.3f}")
    print(f"    |B|/k     :  median={np.median(rl):.4f}  mean={rl.mean():.4f}"
          f"  95%={np.quantile(rl,0.95):.4f}")
    tot = modhist.sum()
    print("    Omega(n_i) mod 6 histogram: "
          + " ".join(f"{int(r)}:{modhist[r]/tot:.3f}" for r in range(6)))
    print("    -> |B|/sqrt(k) ~ O(1) with |B|/k -> 0  means PARTIAL (sqrt-k) cancellation,")
    print("       NOT exact closure: the residual is the delta-gap noise.  |B|/k not -> 0")
    print("       would mean a biased (accumulating) bank.")

    print()
    print("=" * 74)
    print("READING")
    print("=" * 74)
    print("""  On the global pi/3 frame the multiplicative ops (x3, /2) are exact gap-free
  root-of-unity steps -- the unit-1 <-> pi/3 'S(t) gap' is gone, as Sam predicted.
  What survives is decided by delta (part A) and the bank closure (part C):
    * if delta==0 and |B|=O(1): global rescaling removes EVERYTHING; divergence is a
      pure unit-1 magnitude artifact with no carrier counterpart.
    * if delta!=0 and |B|~sqrt(k): the +1 injects an irreducible Omega-jump the pi/3
      frame cannot absorb (it is additive, not multiplicative), and the old sqrt(k)
      wander reappears as sqrt(k) NON-closure of the bank -- same object, new frame.
  The numbers above decide which, without any 1D/zero-statistics language.""")


if __name__ == "__main__":
    import sys
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
    main(N)
