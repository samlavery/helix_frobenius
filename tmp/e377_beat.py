"""THE BEAT.  Two rails with nearly equal periods beat at frequency |q-p|.

The mode (alpha,beta)=(1,-1) has A = q-p and contributes ~ M/(8|q-p|) to the bound.
At (101,103): 10403/16 = 650.2, and 650.2/(p+q) = 3.19 = the worst ratio in the
entire 38-config sweep.  So the sweep's outlier IS the beat.

Decisive question: is the beat real in the TRUTH, or only in the bound?
If real, the additive law needs a beat term and "sum over rails" is incomplete.
Test twin primes (gap 2) against controls with the same size but larger gap.
"""
import math

def rho(p): return (p + 1) / (2 * p)

def true_err(N, p, q):
    Dp, Dq = (p - 1) // 2, (q - 1) // 2
    c = 0
    rp = rq = 0
    for n in range(N):
        if rp <= Dp and rq <= Dq: c += 1
        rp += 1
        if rp == p: rp = 0
        rq += 1
        if rq == q: rq = 0
    return c - N * rho(p) * rho(q)

pairs = [
    # twins
    (11, 13, "twin"), (29, 31, "twin"), (101, 103, "twin"), (191, 193, "twin"),
    (419, 421, "twin"), (1019, 1021, "twin"), (1481, 1483, "twin"),
    # controls: comparable size, larger gap
    (89, 127, "gap 38"), (181, 233, "gap 52"), (401, 439, "gap 38"),
    (1009, 1103, "gap 94"), (1451, 1553, "gap 102"),
    # very close relative to size handled by sexy/cousin primes
    (1021, 1031, "gap 10"), (1487, 1489, "twin"),
]

print(f"{'(p,q)':>14} {'kind':>9} {'gap':>5} {'N':>10} {'M/N':>7} {'|truth|':>10} "
      f"{'p+q':>6} {'truth/(p+q)':>12} {'M/8g':>10} {'M/8g/(p+q)':>11}")
print("-" * 112)
for (p, q, kind) in pairs:
    M = p * q
    N = 4 * M                      # several full beat periods, M/N = 0.25
    g = q - p
    t = abs(true_err(N, p, q))
    beat = M / (8 * g)
    print(f"{'('+str(p)+','+str(q)+')':>14} {kind:>9} {g:>5} {N:>10} {M/N:>7.2f} {t:>10.1f} "
          f"{p+q:>6} {t/(p+q):>12.3f} {beat:>10.1f} {beat/(p+q):>11.2f}")
