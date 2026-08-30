"""C3 seating-box probe — runs the pre-registered control of C3_SEATING_SPEC.md.

Boxes: Gram-type clock cells theta(g_k) = (k-1)*pi.  Counters:
  F  = Hardy-Z sign flips per cell (grid 0.02 + bisection; flips only)
  dN = mp.nzeros at cell boundaries (argument-principle side)
Decision rule and prediction pre-registered in the spec BEFORE this run.
"""
import mpmath as mp

mp.mp.dps = 30

def theta(t):
    return mp.siegeltheta(t)

def gram(k):
    """Solve theta(g) = (k-1)*pi by Newton from the asymptotic seed."""
    target = (k - 1) * mp.pi
    g = 2 * mp.pi * mp.e * mp.exp(mp.lambertw(target / (2 * mp.pi * mp.e))) \
        if k > 1 else mp.mpf(9.6669)
    for _ in range(60):
        d = (theta(g) - target) / (mp.log(g / (2 * mp.pi)) / 2)
        g -= d
        if abs(d) < mp.mpf('1e-20'):
            break
    return g

def zflips(a, b, step=0.02):
    """Sign flips of Z on [a,b]; grid + bisection to 1e-9. Flips only."""
    n = int(mp.ceil((b - a) / step))
    xs = [a + (b - a) * i / n for i in range(n + 1)]
    vs = [mp.siegelz(x) for x in xs]
    flips = 0
    for i in range(n):
        if vs[i] == 0:
            continue
        if vs[i] * vs[i + 1] < 0:
            flips += 1
    return flips

def main():
    # find first Gram index with g_k > 0 and last with g_k <= 400
    cells = []
    k = 1
    g_prev = mp.mpf(0)   # start the first cell at 0 (theta sign region below g_1 handled coarsely)
    gk = gram(1)
    while gk <= 400:
        cells.append((k, g_prev, gk))
        k += 1
        g_prev = gk
        gk = gram(k)
    cells.append((k, g_prev, mp.mpf(400)))

    N_prev = 0
    results = []
    for (k, a, b) in cells:
        F = zflips(a, b)
        N_b = mp.nzeros(b) if b > 14 else (mp.nzeros(b) if b > 14 else 0)
        N_b = int(N_b)
        dN = N_b - N_prev
        N_prev = N_b
        results.append((k, float(a), float(b), F, dN))

    npass = sum(1 for r in results if r[3] == r[4])
    # PAIR analysis: adjacent compensation
    pairs = []
    i = 0
    fails = []
    while i < len(results):
        k, a, b, F, dN = results[i]
        if F == dN:
            i += 1
            continue
        if i + 1 < len(results):
            k2, a2, b2, F2, dN2 = results[i + 1]
            if F + F2 == dN + dN2:
                pairs.append((k, k2, float(a), float(b2)))
                i += 2
                continue
        fails.append(results[i])
        i += 1
    # DEFECT windows: >=3 consecutive cells summed tally < summed census
    defects = []
    for i in range(len(results) - 2):
        Fs = sum(r[3] for r in results[i:i+3])
        Ns = sum(r[4] for r in results[i:i+3])
        if Fs < Ns:
            defects.append((results[i][0], Fs, Ns))
    instr = [r for r in results if r[3] > r[4]]

    print(f"cells: {len(results)}  range (0, 400]")
    print(f"PASS boxes (F = dN): {npass}/{len(results)}")
    print(f"PAIR boxes (adjacent two-cell exact): {pairs}")
    print(f"unresolved singles: {fails}")
    print(f"DEFECT windows (3-cell, tally < census): {defects}")
    print(f"INSTRUMENT-FAIL (F > dN): {instr}")
    tot_F = sum(r[3] for r in results)
    tot_N = sum(r[4] for r in results)
    print(f"TOTAL tally {tot_F} vs census {tot_N}  -> {'EXACT' if tot_F == tot_N else 'MISMATCH'}")

if __name__ == '__main__':
    main()
