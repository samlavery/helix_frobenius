#!/usr/bin/env python3
"""
att573 — TRANSVERSALITY AS THE LOG-AVERAGED GROWTH CURVE (2026-09-03).
  Riemann–Siegel: Z(x) = 2 Re P_x(N) + R,  P_x(y) := Σ_{n≤y} n^{−½} e^{i(ϑ(x) − x log n)},  N = ⌊√(x/2π)⌋.
  Z′(x) = −2 Σ_{n≤N} n^{−½}(ϑ′(x) − log n) sin(ϑ − x log n) + R′ = −2 Im Σ_{n≤N} (ϑ′ − log n) p_n + R′.
  Abel: Σ_{n≤N} log(N/n) p_n = ∫_1^N P(y) dy/y  (exact), so with ϑ′ = log N + (ϑ′ − log N):
     Z′(γ) = −2 Im ∫_1^N P_γ(y) dy/y  −  2(ϑ′ − log N)·Im P_γ(N)  +  R′(γ).
PRE-REGISTERED: at zeros γ with N ≥ 10 the growth-curve term reproduces Z′(γ) to within the remainder-derivative
  size (|R′| ≲ N^{−3/2}·few); report the three pieces and the residual.
"""
import mpmath as mp, math
mp.mp.dps = 25
def theta(x): return mp.siegeltheta(x)
for k in (1000, 3000, 10000, 30000):
    g = mp.zetazero(k).imag
    th = theta(g); thp = mp.diff(theta, g, 1)
    N = int(mp.floor(mp.sqrt(g/(2*mp.pi)))); Nr = mp.sqrt(g/(2*mp.pi))
    p = [n**(-mp.mpf(1)/2)*mp.expj(th - g*mp.log(n)) for n in range(1, N+1)]
    P = [sum(p[:m]) for m in range(1, N+1)]       # P(y) on integers
    # ∫_1^N P(y) dy/y with P piecewise constant on [n, n+1): Σ_{n<N} P(n) log((n+1)/n)  = Σ_{n≤N} log(N/n) p_n  (check both)
    riesz_sum = sum(mp.log(mp.mpf(N)/n)*p[n-1] for n in range(1, N+1))
    abel = sum(P[n-1]*mp.log(mp.mpf(n+1)/n) for n in range(1, N))
    main = -2*riesz_sum.imag
    corr = -2*(thp - mp.log(N))*P[-1].imag
    Zp = mp.diff(mp.siegelz, g, 1)
    print("zero #%d γ=%.3f N=%d (√=%.2f): Z′(γ) = %+.6f ; −2Im∫P dy/y = %+.6f ; (ϑ′−log N) term = %+.6f ; residual (R′) = %+.6f ; |Abel−Riesz| = %.1e ; Re P(N) = %+.5f (=−R/2)" % (
        k, g, N, Nr, Zp, main, corr, Zp - main - corr, abs(abel - riesz_sum), P[-1].real))
