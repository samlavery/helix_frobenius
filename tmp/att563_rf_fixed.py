# Corrected: SAME statistic as att561 -- max within each mu6 cycle, then min over cycles.
# A mu6 cycle = 2 consecutive gaps (phase 2pi) = 4 interior third-point anchors.
from mpmath import mp, mpf, siegelz, zetazero, sqrt
mp.dps = 15
print(f"{'height':>9} {'min-cycle max|Z| (register-free)':>33} {'A_eff':>8} {'theta-anchored':>15}")
prev = {1000: 1.0145, 10000: 0.7497, 100000: 1.0008, 1000000: 0.7358}
idx = {1000: 649, 10000: 10142, 100000: 138069, 1000000: 1747146}
for T0, n0 in idx.items():
    gs = [zetazero(n0 + i).imag for i in range(0, 26)]
    anch = []
    for k in range(len(gs)-1):
        a, b = gs[k], gs[k+1]
        anch += [abs(siegelz(a + (b-a)*mpf(j)/3)) for j in (1, 2)]
    cyc = [max(anch[4*c:4*c+4]) for c in range(len(anch)//4)]
    m = min(cyc)
    print(f"{T0:>9} {float(m):>33.4f} {float(m/(sqrt(3)/2)):>8.3f} {prev[T0]:>15.4f}")
