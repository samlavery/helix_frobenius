#!/usr/bin/env python3
"""att658c — is the Laguerre form J_1(t) = ∬(u+v)²Φ(u)Φ(v)cos(t(u−v)) positive SITE BY SITE on the helix?
Φ = Σ_m g_m, g_m(u) = (2π²m⁴e^{9u/2} − 3πm²e^{5u/2})e^{−πm²e^{2u}} (site m; NOT even, changes sign at
u_m = ½log(3/(2πm²))).  J_1 = Σ_{m,m′} J^{(m,m′)}, J^{(m,m′)} = Re Σ_k C(2,k) F_k^{(m)} conj F_{2−k}^{(m′)},
F_k^{(m)}(t) = ∫ u^k g_m(u) e^{itu} du over the full line.
PRE-REGISTERED: the diagonal J^{(m,m)}(t) is NOT ≥ 0 for all t (prediction: site kernels change sign, the
positivity is collective); the full sum over m, m′ ≤ 6 reproduces J_1 to 1e−6."""
import mpmath as mp
mp.mp.dps = 20
out = open("tmp/att658c_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def g(m, u):
    u = mp.mpf(u)
    return (2*mp.pi**2*m**4*mp.exp(mp.mpf(9)/2*u) - 3*mp.pi*m**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-mp.pi*m**2*mp.exp(2*u))
def F(m, k, t):
    return mp.quad(lambda u: u**k*g(m, u)*mp.expj(t*u), [-14, -8, -4, -2, -1, 0, 0.5, 1, 1.5, 2, 3, 4])
M = 6
for t in (2.0, 10.0, 14.1347, 21.0, 30.0):
    Fs = {(m, k): F(m, k, t) for m in range(1, M+1) for k in range(3)}
    def Jmm(m, mp_):
        return sum(mp.binomial(2, k)*Fs[(m, k)]*mp.conj(Fs[(mp_, 2-k)]) for k in range(3)).real
    diag = [Jmm(m, m) for m in range(1, M+1)]
    total = sum(Jmm(m, mp_) for m in range(1, M+1) for mp_ in range(1, M+1))
    # reference J_1 from the even Φ (u ≥ 0 only, doubled)
    def Phi(u):
        u = abs(mp.mpf(u)); return sum(g(m, u) for m in range(1, 9))
    Fk = [2*mp.quad(lambda u: u**k*Phi(u)*(mp.cos(t*u) if k % 2 == 0 else 1j*mp.sin(t*u)), [0, 0.5, 1, 2, 3, 4]) for k in range(3)]
    J1 = sum(mp.binomial(2, k)*Fk[k]*mp.conj(Fk[2-k]) for k in range(3)).real
    say("t=%7.4f  J_1 = %+.4e ; site-pair sum (m,m′≤%d) = %+.4e (rel.diff %.1e) ; diagonal terms m=1..%d: %s ; off-diagonal total %+.4e"
        % (t, J1, M, total, abs(total - J1)/abs(J1), M, " ".join("%+.2e" % d for d in diag), total - sum(diag)))
