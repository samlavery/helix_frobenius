import mpmath as mp
mp.mp.dps = 30

# eta partial sums: S_N = sum_{n<=N} (-1)^{n-1} n^{-s}.  eta(1/2+i g)=0 at a zeta zero.
def eta_partial(s, N):
    tot = mp.mpc(0)
    for n in range(1, N+1):
        tot += ((-1)**(n-1)) * mp.power(n, -s)
    return tot

print(f"{'k':>2} {'gamma':>12} {'e^gamma':>12} {'g/2pi':>8} {'sqrt(g/2pi)':>11}  first N with |S_N|<tol")
for k in range(1, 6):
    g = mp.im(mp.zetazero(k))
    s = mp.mpc(0.5, g)
    egam = mp.e**g
    rs   = g/(2*mp.pi)
    hits = {}
    tot = mp.mpc(0)
    for n in range(1, 20001):
        tot += ((-1)**(n-1)) * mp.power(n, -s)
        for tol in (0.1, 0.03, 0.01):
            if tol not in hits and abs(tot) < tol:
                hits[tol] = n
    print(f"{k:>2} {float(g):12.5f} {float(egam):12.4g} {float(rs):8.3f} {float(mp.sqrt(rs)):11.3f}  "
          + "  ".join(f"<{t}:N={hits.get(t,'>20000')}" for t in (0.1,0.03,0.01)))
