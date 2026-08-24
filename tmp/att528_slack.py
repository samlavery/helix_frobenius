"""att528 — slack of Weil positivity vs support width, on the validated Weil form."""
import mpmath as mp
mp.mp.dps = 25
b = mp.mpf('0.15'); sq = mp.sqrt(mp.pi); CUT = 16*b

def lam_pairs(nmax):
    spf = list(range(nmax+1))
    i = 2
    while i*i <= nmax:
        if spf[i] == i:
            for j in range(i*i, nmax+1, i): spf[j] = min(spf[j], i)
        i += 1
    out = []
    for n in range(2, nmax+1):
        p, x, k = spf[n], n, 0
        while x % p == 0: x //= p; k += 1
        if x == 1: out.append((mp.log(p), mp.log(n)))
    return out

def weil(nodes, pr):
    N = len(nodes); M = mp.matrix(N, N)
    for j in range(N):
        for k in range(j, N):
            d = nodes[j] - nodes[k]
            A = b**2*mp.quad(lambda r: mp.e**(-b**2*r**2)*mp.cos(r*d)*
                (mp.re(mp.digamma(mp.mpf(1)/4+1j*r/2))-mp.log(mp.pi)), [-mp.inf,0,mp.inf])
            P = 4*mp.pi*b**2*mp.e**(b**2/4)*mp.cosh(d/2)
            PR = 2*mp.fsum(L_*mp.e**(-ln/2)*b*sq*
                 (mp.e**(-(ln-d)**2/(4*b**2))+mp.e**(-(ln+d)**2/(4*b**2)))/2
                 for (L_, ln) in pr if abs(abs(ln)-abs(d)) < CUT or abs(ln) < CUT)
            M[j,k] = M[k,j] = A + P - PR
    return M

print("   2L      lambda_min        lambda_max      lmin/lmax       verdict")
for Lh in ('0.25','0.5','1.0','1.5','2.0','2.5','3.0'):
    Lh = mp.mpf(Lh); N = 8
    nodes = [(-Lh + 2*Lh*i/(N-1)) for i in range(N)]
    umax = 2*Lh + CUT + 1
    pr = lam_pairs(int(mp.floor(mp.e**umax))+1)
    M = weil(nodes, pr)
    ev = mp.eigsy(M, eigvals_only=True)
    lo, hi = min(ev), max(ev)
    print("  %-6s  %-17s %-15s %-15s %s"
          % (mp.nstr(2*Lh,3), mp.nstr(lo,8), mp.nstr(hi,8),
             mp.nstr(lo/hi,6), "PSD" if lo >= 0 else "INDEFINITE"))

print("\n### basis-invariant: generalized lambda_min(G^-1 M), G = basis Gram, CUT=16b")
print("   2L      gen lambda_min      cond(G)         verdict")
for Lh in ('0.5','1.0','1.5','2.0','2.5','3.0'):
    Lh = mp.mpf(Lh); N = 8
    nodes = [(-Lh + 2*Lh*i/(N-1)) for i in range(N)]
    pr = lam_pairs(int(mp.floor(mp.e**(2*Lh+CUT+1)))+1)
    M = weil(nodes, pr)
    G = mp.matrix(N, N)
    for j in range(N):
        for k in range(N):
            G[j,k] = b*sq*mp.e**(-(nodes[j]-nodes[k])**2/(4*b**2))
    Lc = mp.cholesky(G); Li = mp.inverse(Lc)
    W = Li*M*Li.T
    ev = mp.eigsy(mp.matrix([[(W[i,j]+W[j,i])/2 for j in range(N)] for i in range(N)]), eigvals_only=True)
    ge = mp.eigsy(G, eigvals_only=True)
    print("  %-6s  %-18s %-15s %s"
          % (mp.nstr(2*Lh,3), mp.nstr(min(ev),8), mp.nstr(max(ge)/min(ge),6),
             "PSD" if min(ev) >= 0 else "INDEFINITE"))
