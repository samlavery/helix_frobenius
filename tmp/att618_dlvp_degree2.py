# The dlVP (3,4,1) combination of the degree-2 seat form at anchors s_k = sigma0 + i k gamma0.
#   Q_2(s) = sum_rho [(s-rho)(rho-1+conj(s))]^{-2}   (zero side; on-line terms = |x|^4 >= 0)
#   DC_2(s) = 2[ c2 Re g2(s) + c1 Re g1(s) ],  c2 = 1/d^2, c1 = 2/d^3, d = 2 sigma0 - 1,
#   g1 = G, g2 = -G',  G(s) = 1/s + 1/(s-1) - log(pi)/2 + psi(s/2)/2.
#   Identity: Q_2 = DC_2 - 2 sum_n Lambda(n) n^{-sigma0} cos(gamma log n) (c2 log n + c1).
#   Manifest: 3Q(s0)+4Q(s1)+Q(s2) <= 3DC(s0)+4DC(s1)+DC(s2)   [3+4cos+cos2 >= 0].
import mpmath as mp
mp.mp.dps = 20
K = 400
zeros = [mp.zetazero(k).imag for k in range(1, K+1)]
def Q2(s):
    tot = mp.mpc(0)
    for g in zeros:
        for sg in (1, -1):
            rho = mp.mpc(0.5, sg*g)
            w = (s - rho) * (rho - 1 + mp.conj(s))
            tot += 1 / w**2
    return tot
def G(s):  return 1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.psi(0, s/2)/2
def Gp(s): return -1/s**2 - 1/(s-1)**2 + mp.psi(1, s/2)/4
def DC2(s):
    d = 2*s.real - 1
    return 2*((1/d**2)*mp.re(-Gp(s)) + (2/d**3)*mp.re(G(s)))
def prime2_direct(s, X=200000):
    # -2 sum Lambda(n) n^{-sigma0} cos(gamma log n) (c2 log n + c1), truncated (only for sigma0 well above 1)
    d = 2*s.real - 1
    tot = mp.mpf(0)
    for n in range(2, X):
        # von Mangoldt
        m = n; p = None
        for q in range(2, int(n**0.5)+1):
            if m % q == 0:
                p = q; break
        if p is None: p = n
        mm = n
        while mm % p == 0: mm //= p
        if mm != 1: continue
        L = mp.log(p)
        tot += L * n**(-s.real) * mp.cos(s.imag*mp.log(n)) * ((1/d**2)*mp.log(n) + 2/d**3)
    return -2*tot
print("identity check Q_2 = DC_2 + prime_2 (sigma0 = 1.5 so the prime sum converges fast):")
for s in [mp.mpc(1.5, 0.0), mp.mpc(1.5, 14.1347), mp.mpc(1.5, 30.0)]:
    q = Q2(s); dc = DC2(s); pr = prime2_direct(s)
    print("  s=%s  Q2(zeros)=%.6f  DC2+prime2=%.6f  (DC2=%.6f prime2=%.6f)" % (s, mp.re(q), dc+pr, dc, pr))
print()
print("dlVP combination at eta = sigma0-1, gamma0 = first zero 14.1347:")
for eta in [0.5, 0.2, 0.1, 0.05, 0.02]:
    sig = 1 + eta; g0 = mp.mpf('14.134725141734693790')
    s0, s1, s2 = mp.mpc(sig, 0), mp.mpc(sig, g0), mp.mpc(sig, 2*g0)
    L = 3*mp.re(Q2(s0)) + 4*mp.re(Q2(s1)) + mp.re(Q2(s2))
    R = 3*DC2(s0) + 4*DC2(s1) + DC2(s2)
    own = 4*2*((eta+0.5)*(eta+0.5))**(-2)   # the on-line zero at gamma0 counted once: (x x')^2 = (eta+1/2)^{-4}; weight 4, one zero
    print("  eta=%.2f  LHS=%.4f  RHS=%.4f  (pole part 3*2/(d^2 eta^2)=%.4f, own-zero term 4(eta+1/2)^-4=%.4f)" %
          (eta, L, R, 6/((2*sig-1)**2*eta**2), 4*(eta+0.5)**(-4)))
print()
print("sign of a hypothetical bad zero's degree-2 term at the anchor of a neighbouring bad zero:")
print("  zero at beta=1-eps', height gamma0+v; anchor sigma0=1+eta at gamma0; term 2Re(x x')^2 = 2cos(2phi)/|w|^2")
for eta, epsp in [(0.01, 0.001), (0.05, 0.01)]:
    a = eta + epsp; ap = 1 + eta - epsp; delta = 0.5 - epsp
    for v in [0.0, 0.5*(a*ap)**0.5, (a*ap)**0.5, 2*(a*ap)**0.5, 0.2, 0.5]:
        w = mp.mpc(a*ap + v*v, -2*v*delta)
        t = 2*mp.re(1/w**2)
        print("   eta=%.3f eps'=%.3f v=%.4f : 2Re(xx')^2 = %+.3f   (own term at v=0: %.3f)" % (eta, epsp, v, t, 2/(a*ap)**2))
