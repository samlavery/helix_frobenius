#!/usr/bin/env python3
"""att658d — site-pair decomposition of the Laguerre form with TWO-ENDED sites g̃_m(u) = g_m(|u|)
(helix end u > 0, anti-helix end u < 0; Φ = Σ_m g̃_m exactly).  Each site's own real fiber
Ξ_m(t) = 2∫_0^∞ g_m(u) cos(tu) du; J^{(m,m)} = 2(Ξ_m′² − Ξ_m Ξ_m″) is the site's own Laguerre form.
PRE-REGISTERED: (a) m,m′ ≤ 6 reproduces J_1 to 1e−6 at every t; (b) the site's own Laguerre form J^{(m,m)}(t) is
NOT ≥ 0 for all t ∈ [0.5, 60] (prediction: the two-ended site kernel has a cusp at u = 0, its transform decays like
1/t² and is not real-rooted); (c) the positivity of J_1 is collective."""
import mpmath as mp
mp.mp.dps = 20
out = open("tmp/att658d_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def g(m, u):
    u = mp.mpf(u)
    return (2*mp.pi**2*m**4*mp.exp(mp.mpf(9)/2*u) - 3*mp.pi*m**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-mp.pi*m**2*mp.exp(2*u))
def Fk(m, k, t):   # ∫ u^k g̃_m e^{itu} du, g̃_m even
    if k % 2 == 0: return 2*mp.quad(lambda u: u**k*g(m, u)*mp.cos(t*u), [0, 0.25, 0.5, 1, 1.5, 2, 3, 4])
    return 2j*mp.quad(lambda u: u**k*g(m, u)*mp.sin(t*u), [0, 0.25, 0.5, 1, 1.5, 2, 3, 4])
M = 6
say("site m : cusp slope g_m′(0⁺) (sum over m should vanish since Φ is smooth and even):")
slopes = [mp.diff(lambda u: g(m, u), 0) for m in range(1, 9)]
say("   " + " ".join("%+.3e" % s for s in slopes) + "  sum(m≤8) = %+.2e" % sum(slopes))
neg_seen = {m: [] for m in range(1, M+1)}
for t in [0.5*i for i in range(1, 121)]:
    F = {(m, k): Fk(m, k, t) for m in range(1, M+1) for k in range(3)}
    J = lambda m, n: sum(mp.binomial(2, k)*F[(m, k)]*mp.conj(F[(n, 2-k)]) for k in range(3)).real
    diag = [J(m, m) for m in range(1, M+1)]
    for m in range(1, M+1):
        if diag[m-1] < 0: neg_seen[m].append(t)
    if t in (2.0, 10.0, 14.0, 21.0, 30.0, 45.0, 60.0):
        total = sum(J(m, n) for m in range(1, M+1) for n in range(1, M+1))
        Phi = lambda u: sum(g(mm, abs(mp.mpf(u))) for mm in range(1, 9))
        Fref = [2*mp.quad(lambda u: u**k*Phi(u)*(mp.cos(t*u) if k % 2 == 0 else 1j*mp.sin(t*u)), [0, 0.25, 0.5, 1, 1.5, 2, 3, 4]) for k in range(3)]
        J1 = sum(mp.binomial(2, k)*Fref[k]*mp.conj(Fref[2-k]) for k in range(3)).real
        say("t=%5.1f  J_1=%+.3e  pair-sum(m,m′≤6)=%+.3e rel.diff %.1e ; diagonal: %s ; off-diag total %+.2e (%.0f%% of J_1)"
            % (t, J1, total, abs(total-J1)/abs(J1), " ".join("%+.1e" % d for d in diag), total-sum(diag), 100*(total-sum(diag))/J1))
for m in range(1, M+1):
    say("site %d own Laguerre form negative at %d of 120 grid points%s" % (m, len(neg_seen[m]), ("; first at t=%.1f" % neg_seen[m][0]) if neg_seen[m] else ""))
