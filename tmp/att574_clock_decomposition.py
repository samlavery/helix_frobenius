#!/usr/bin/env python3
"""
att574 — THE TANGENCY FUNCTIONAL AT t = 0 IS THE PRIME CLOCK SAMPLING THE GROWTH CURVE (2026-09-03).
  p_n = n^{−½}e^{i(ϑ−γ log n)}, P(y) = Σ_{n≤y}p_n, ω_n = log(N/n).  Since log n = Σ_{d|n}Λ(d) and p_{dm} = d^{−½−iγ}p_m:
     Σ_{n≤N} ω_n p_n = log N · P(N) − Σ_{d≤N} Λ(d) d^{−½−iγ} P(N/d)          (exact algebra, multiplicativity)
  Z′(γ) = −2 Im[Σ ω_n p_n] + clock + R′.  At a zero Re P(N) ≈ 0, so Z′ ≈ −2[log N·Im P(N) − Im Σ_d c_d P(N/d)].
  Ratio r := Im Σ_d c_d P(N/d) / (log N · Im P(N)).  Tangency ⟺ r = 1.  Endpoint dominates ⟺ r < 1.
PRE-REGISTERED: identity to 1e-20; report fraction r < 1 and max r over ~360 zeros in four height bands; P1: r < 1 at
  ≥ 95% of zeros (prediction, not a theorem); Lehmer-type zeros (small |Z′|) should show r near 1.
"""
import mpmath as mp, math, sys
mp.mp.dps = 20
def lam_table(N):
    lam = [0.0]*(N+1)
    for p in range(2, N+1):
        if all(p % q for q in range(2, int(p**0.5)+1)):
            q = p
            while q <= N: lam[q] = math.log(p); q *= p
    return lam
out = []
for band in ((1000, 1090), (3000, 3090), (10000, 10090), (30000, 30090)):
    rs = []; ident = 0; zps = []
    for k in range(band[0], band[1]):
        g = mp.zetazero(k).imag; th = mp.siegeltheta(g); N = int(mp.floor(mp.sqrt(g/(2*mp.pi))))
        p = [n**(-mp.mpf(1)/2)*mp.expj(th - g*mp.log(n)) for n in range(1, N+1)]
        P = lambda y: sum(p[:int(y)])
        lam = lam_table(N)
        lhs = sum(mp.log(mp.mpf(N)/n)*p[n-1] for n in range(1, N+1))
        clock = sum(lam[d]*d**(-mp.mpf(1)/2)*mp.expj(-g*mp.log(d))*P(N//d) for d in range(2, N+1))
        rhs = mp.log(N)*P(N) - clock
        ident = max(ident, abs(lhs - rhs))
        r = clock.imag/(mp.log(N)*P(N).imag)
        rs.append(float(r)); zps.append(float(mp.diff(mp.siegelz, g, 1)))
    frac = sum(1 for r in rs if r < 1)/len(rs)
    i_small = min(range(len(zps)), key=lambda i: abs(zps[i]))
    print("zeros %d–%d (N≈%d): identity max err %.1e ; r<1 fraction %.3f ; max r %.3f ; min r %.3f ; smallest |Z′| = %.3f at r = %.3f" % (
        band[0], band[1]-1, N, ident, frac, max(rs), min(rs), abs(zps[i_small]), rs[i_small]))
