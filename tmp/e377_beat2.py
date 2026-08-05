"""Beat test, done right: sup over N (the previous run put N at exact multiples of
the period M, where the error vanishes identically).

The beat mode (1,-1) has frequency theta = 1/p - 1/q = g/M, g = q-p, so it peaks at
N ~ M/(2g).  Report sup_{N<=M} |err(N)| and where it occurs.
"""
import math

def rho(p): return (p + 1) / (2 * p)

def sup_err(p, q):
    M = p * q
    Dp, Dq = (p - 1) // 2, (q - 1) // 2
    dens = rho(p) * rho(q)
    c = 0.0
    rp = rq = 0
    best, bestN = 0.0, 0
    for n in range(M):
        if rp <= Dp and rq <= Dq: c += 1
        rp += 1
        if rp == p: rp = 0
        rq += 1
        if rq == q: rq = 0
        e = abs(c - (n + 1) * dens)
        if e > best: best, bestN = e, n + 1
    return best, bestN

pairs = [
    (11, 13, "twin"), (29, 31, "twin"), (101, 103, "twin"), (191, 193, "twin"),
    (419, 421, "twin"), (1019, 1021, "twin"), (1481, 1483, "twin"),
    (89, 127, "gap 38"), (181, 233, "gap 52"), (401, 439, "gap 38"),
    (1009, 1103, "gap 94"), (1451, 1553, "gap 102"), (1021, 1031, "gap 10"),
    (13, 1009, "far"), (11, 1481, "far"),
]

print(f"{'(p,q)':>14} {'kind':>9} {'g':>5} {'sup|err|':>10} {'at N':>10} {'M/(2g)':>10} "
      f"{'p+q':>6} {'sup/(p+q)':>10} {'M/8g':>10} {'sup/(M/8g)':>11}")
print("-" * 118)
for (p, q, kind) in pairs:
    M = p * q
    g = q - p
    s, nAt = sup_err(p, q)
    beat = M / (8 * g)
    print(f"{'('+str(p)+','+str(q)+')':>14} {kind:>9} {g:>5} {s:>10.1f} {nAt:>10} "
          f"{M/(2*g):>10.0f} {p+q:>6} {s/(p+q):>10.3f} {beat:>10.1f} {s/beat:>11.3f}")
