"""att227: WHERE DOES THE POSITIVITY COME FROM?  Decompose the assembled
window-Hankel energy on its near-null direction into prime / archimedean /
boundary contributions.

Fast exact route: total moments = sum over the 3 actual zeros (argument
principle, exact); windowing = prime + archimedean (computable at Re s = 2,
no zero data); boundary = total - windowing.  Then find the minimizing
eigenvector of the total Hankel and evaluate each block's quadratic form."""
from mpmath import mp, mpf, mpc, quad, matrix, eighe, nstr, log, pi, psi, mangoldt

mp.dps = 25
Y = mpf('1.5'); A_, B_ = mpf('10'), mpf('30'); KMAX = 5
ZS = [mpf('14.134725141734693790'), mpf('21.022039638771554993'),
      mpf('25.010857580145688763')]
LAM = [(n, mpf(mangoldt(n))) for n in range(2, 40000) if mangoldt(n) != 0]

def arch_logderiv(s):
    return 1/s + 1/(s-1) - log(pi)/2 + psi(0, s/2)/2
def prime_logderiv(s):
    return -sum(L * mp.power(n, -s) for n, L in LAM)

def horiz_part(k, sign, part):
    """top(sign=+1)/bottom(sign=-1) edge moment of the chosen part."""
    def f(x):
        z = mpc(x, sign*Y)
        s = mpf(1)/2 - mpc(0,1)*z
        g = arch_logderiv(s) if part == 'arch' else prime_logderiv(s)
        return (z**k) * (-mpc(0,1) * g)
    v = quad(f, [A_, (A_+B_)/2, B_]) / (2*pi*mpc(0,1))
    return -v if sign > 0 else v

mu_tot, mu_pr, mu_ar = [], [], []
for k in range(2*KMAX):
    mu_tot.append(sum(z**k for z in ZS))
    mu_pr.append((horiz_part(k,+1,'prime') + horiz_part(k,-1,'prime')).real)
    mu_ar.append((horiz_part(k,+1,'arch') + horiz_part(k,-1,'arch')).real)
    print(f"  k={k}: total {nstr(mu_tot[k],8):>13}  prime {nstr(mu_pr[k],8):>13}"
          f"  arch {nstr(mu_ar[k],8):>13}  bdry {nstr(mu_tot[k]-mu_pr[k]-mu_ar[k],8):>13}",
          flush=True)
mu_bd = [mu_tot[k] - mu_pr[k] - mu_ar[k] for k in range(2*KMAX)]

def H(mu, n):
    M = matrix(n,n)
    for i in range(n):
        for j in range(n): M[i,j] = mu[i+j]
    return M

for n in [3,4]:
    Ht = H(mu_tot,n)
    ev, V = eighe(Ht)
    i0 = min(range(n), key=lambda i: ev[i].real)
    v = [V[j,i0].real for j in range(n)]
    def energy(mu):
        M = H(mu,n)
        return sum(v[i]*M[i,j]*v[j] for i in range(n) for j in range(n))
    et, ep, ea, eb = energy(mu_tot), energy(mu_pr), energy(mu_ar), energy(mu_bd)
    print(f"\nn={n}: min-eig {nstr(ev[i0].real,5)}  energy split on that direction:")
    print(f"   TOTAL      {nstr(et,6):>14}")
    print(f"   prime      {nstr(ep,6):>14}   ({nstr(100*ep/et,4)}% of total)")
    print(f"   archimedean{nstr(ea,6):>14}   ({nstr(100*ea/et,4)}%)")
    print(f"   boundary   {nstr(eb,6):>14}   ({nstr(100*eb/et,4)}%)", flush=True)
