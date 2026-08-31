from mpmath import mp, mpf, siegelz, siegeltheta, findroot, pi
mp.dps = 15
def t_of_theta(target, t0): return findroot(lambda t: siegeltheta(t) - target, t0)
print(f"{'height':>11} {'min cycle max|Z| (pi/3)':>24} {'Gram':>8} {'worst cell':>11}")
for T0 in [10**6, 10**7, 10**8]:
    th0 = siegeltheta(mpf(T0)); k0 = int(th0/(pi/3)) + 1
    ts = []
    for k in range(k0, k0+72):
        t = t_of_theta(k*pi/3, mpf(T0) + (k-k0)*mpf(T0)/2000 + 1)
        ts.append((k, t, abs(siegelz(t))))
    cellmax = [max(ts[6*c+j][2] for j in range(6)) for c in range(12)]
    grammax = [max([ts[6*c+j][2] for j in range(6) if ts[6*c+j][0] % 3 == 0]) for c in range(12)]
    print(f"{T0:>11} {float(min(cellmax)):>24.4f} {float(min(grammax)):>8.4f} {float(min(t[2] for t in ts)):>11.5f}")
