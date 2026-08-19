"""att228: energy split, CORRECTED.  The bottom edge sits at Re s = -1 (series
divergent) and is the FE image of the top; measured top == bottom exactly
(att221), so windowing = 2 x top, computed entirely at Re s = 2 from prime +
archimedean data.  Boundary = total - windowing, total = sum over the actual
zeros (argument principle)."""
from mpmath import mp, mpf, mpc, quad, matrix, eighe, nstr, log, pi, psi, mangoldt

mp.dps = 20
Y = mpf('1.5'); A_, B_ = mpf('10'), mpf('30'); KTOP = 9
ZS = [mpf('14.134725141734693790'), mpf('21.022039638771554993'),
      mpf('25.010857580145688763')]
LAM = [(n, mpf(mangoldt(n))) for n in range(2, 12000) if mangoldt(n) != 0]
print(f"prime powers: {len(LAM)}", flush=True)

def top_moment(k, part):
    def f(x):
        z = mpc(x, Y); s = mpf(1)/2 - mpc(0,1)*z
        g = (1/s + 1/(s-1) - log(pi)/2 + psi(0, s/2)/2) if part=='arch' \
            else -sum(L*mp.power(n, -s) for n, L in LAM)
        return (z**k) * (-mpc(0,1)*g)
    return -(quad(f, [A_, (A_+B_)/2, B_]) / (2*pi*mpc(0,1)))

mu_tot, mu_pr, mu_ar, mu_bd = [], [], [], []
for k in range(KTOP):
    t = sum(z**k for z in ZS)
    p = 2*top_moment(k,'prime').real
    a = 2*top_moment(k,'arch').real
    mu_tot.append(t); mu_pr.append(p); mu_ar.append(a); mu_bd.append(t-p-a)
    print(f"  k={k}: tot {nstr(t,7):>12} = prime {nstr(p,7):>12} + arch "
          f"{nstr(a,7):>11} + bdry {nstr(t-p-a,7):>12}", flush=True)

def H(mu,n):
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    return M
for n in [3,4]:
    ev, V = eighe(H(mu_tot,n))
    i0 = min(range(n), key=lambda i: ev[i].real)
    v = [V[j,i0].real for j in range(n)]
    def E(mu):
        M = H(mu,n); return sum(v[i]*M[i,j]*v[j] for i in range(n) for j in range(n))
    et,ep,ea,eb = E(mu_tot),E(mu_pr),E(mu_ar),E(mu_bd)
    print(f"\nn={n} min-eig {nstr(ev[i0].real,5)} — energy on the near-null direction:")
    print(f"   TOTAL {nstr(et,6):>12}")
    print(f"   prime {nstr(ep,6):>12}   arch {nstr(ea,6):>12}   boundary {nstr(eb,6):>12}")
