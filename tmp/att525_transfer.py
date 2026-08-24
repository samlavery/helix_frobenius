"""
att525 — does kernel positivity transfer to the zero side?

EXACT BRIDGE (both sides are functions of ONE data set):
  Xi(z) = int Phi(u) e^{izu} du  =>  Taylor coeffs of Xi ARE Phi's even moments:
      Xi(z) = sum_j (-1)^j m_{2j} z^{2j} / (2j)!
  log(Xi(z)/Xi(0)) = sum_rho log(1 - z^2/t_rho^2) = - sum_k (z^{2k}/k) P_k,
      P_k := sum_rho t_rho^{-2k}
  => P_k = -k * [z^{2k}] log(Xi(z)/Xi(0)).

ZERO-SIDE TEST: atoms w_rho = 1/t_rho^2, moments P_k (k>=1).  Shifted Hankel
      H_{ij} = P_{i+j+1}   =  sum_rho w_rho * v(w_rho) v(w_rho)^T,  v = (1,w,w^2,...)
is PSD when every w_rho > 0, i.e. every t_rho real.  Complex t_rho => indefinite.

TEST FAMILY: Phi_a = (1/2)(delta_1 + delta_{-1}) + a*delta_0, positive for a>0.
      F_a(z) = cos z + a.
      For a > 1, cos z = -a has NO real solution: EVERY zero is complex.
      Weight sequence (1/2, a, 1/2) is log-concave iff a^2 >= 1/4, i.e. a >= 1/2.
      So a in (1, inf) is a POSITIVE, LOG-CONCAVE kernel with all-complex zeros.

PRE-REGISTERED:
  kernel-side Hankel of Phi_a moments ....... PSD for all a>0
  zero-side shifted Hankel .................. PSD for a<1, INDEFINITE for a>1
  Xi reference .............................. PSD
CROSS-VALIDATION: for F_a the zeros are exact (z = +-arccos(-a) + 2 pi k), so P_k
is computed BOTH from the Taylor coefficients and by direct summation over zeros.
"""
import mpmath as mp

mp.mp.dps = 40
NP = 7          # number of P_k used
KMAX = 2 * NP + 2


def P_from_taylor(F, npk=NP):
    """P_k = -k * [z^{2k}] log(F(z)/F(0)), k = 1..npk."""
    F0 = F(0)
    g = lambda z: mp.log(F(z) / F0)
    c = mp.taylor(g, 0, 2 * npk + 1)
    return [-(k) * c[2 * k] for k in range(1, npk + 1)]


def P_direct_cos(a, npk=NP, KZ=4000):
    """Exact zeros of cos z + a: z = +- z0 + 2 pi k, z0 = arccos(-a) (complex ok).
    Sum over distinct zeros with positive 'index', pairing +-z as one t^2."""
    z0 = mp.acos(-mp.mpf(a))
    out = []
    for k in range(1, npk + 1):
        s = mp.mpc(0)
        for m in range(-KZ, KZ + 1):
            for zz in (z0 + 2 * mp.pi * m, -z0 + 2 * mp.pi * m):
                if abs(zz) < mp.mpf('1e-12'):
                    continue
                s += zz ** (-2 * k)
        out.append(s / 2)          # +-z counted once
    return out


def shifted_hankel_eigs(P, n):
    H = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            H[i, j] = mp.re(P[i + j])
    return mp.eigsy(H, eigvals_only=True)


def kernel_hankel_eigs(a, n):
    """Hankel of Phi_a moments: m_0 = 1+a, m_{2j}=1 (j>=1), m_odd = 0."""
    def m(k):
        if k == 0:
            return mp.mpf(1) + a
        if k % 2 == 1:
            return mp.mpf(0)
        return mp.mpf(1)
    H = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            H[i, j] = m(i + j)
    return mp.eigsy(H, eigvals_only=True)


def verdict(ev):
    lo = min(ev)
    sc = max(abs(e) for e in ev)
    return ("INDEFINITE" if lo < -mp.mpf('1e-15') * max(sc, 1) else "PSD"), lo


def xi(s):
    return 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


if __name__ == "__main__":
    print("### CROSS-VALIDATION of P_k (Taylor vs direct zero sum), F_a = cos z + a")
    for a in ('0.5', '2.0'):
        Pt = P_from_taylor(lambda z, a=a: mp.cos(z) + mp.mpf(a))
        Pd = P_direct_cos(mp.mpf(a), npk=3)
        print("  a=%s  P1 taylor=%s  direct=%s  |diff|=%s"
              % (a, mp.nstr(Pt[0], 12), mp.nstr(Pd[0], 12),
                 mp.nstr(abs(Pt[0] - Pd[0]), 4)))
        print("        P2 taylor=%s  direct=%s  |diff|=%s"
              % (mp.nstr(Pt[1], 12), mp.nstr(Pd[1], 12),
                 mp.nstr(abs(Pt[1] - Pd[1]), 4)))

    print("\n### the transfer test")
    print("   a     log-concave?  kernel Hankel      zero-side shifted Hankel")
    for a in ('0.3', '0.5', '0.9', '1.1', '2.0', '5.0'):
        av = mp.mpf(a)
        lc = "yes" if av * av >= mp.mpf('0.25') else "no "
        vk, lok = verdict(kernel_hankel_eigs(av, 5))
        P = P_from_taylor(lambda z, av=av: mp.cos(z) + av)
        vz, loz = verdict(shifted_hankel_eigs(P, 4))
        print("  %-5s   %s          %-5s %-12s  %-11s %s"
              % (a, lc, vk, mp.nstr(lok, 5), vz, mp.nstr(loz, 6)))

    print("\n### Xi reference")
    Pxi = P_from_taylor(lambda z: xi(mp.mpf(1) / 2 + 1j * z))
    vz, loz = verdict(shifted_hankel_eigs(Pxi, 4))
    print("  Xi   zero-side shifted Hankel -> %-11s lambda_min = %s"
          % (vz, mp.nstr(loz, 8)))
    print("  P_k(Xi) =", [mp.nstr(mp.re(p), 8) for p in Pxi[:4]])
