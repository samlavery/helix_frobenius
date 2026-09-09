# att625b — the Γ far field's coherent common mode M = −ω_1 + Σ_n ω_{−2n} in closed form, and the skew-sign norm.
from mpmath import mp, mpf, mpc, psi, conj, re, im, fabs, pi, cot, nsum, inf
import numpy as np
mp.dps = 40
def omega(s, a):  # 1/((s−a)(a−c)), c = 1 − conj(s)
    c = 1 - conj(s); return 1/((s-a)*(a-c))
for s in [mpc('0.40','23.02'), mpc('0.45','30.47'), mpc('0.30','39.25'), mpc('0.40','100')]:
    sig = s.real; t = s.imag
    direct = -omega(s, 1) + nsum(lambda n: omega(s, -2*n), [1, inf])
    # closed form: Σ_{n≥1} ω_{−2n} = −Σ 1/((2n+s)(2n+1−s̄)) = −[ψ(1+(1−s̄)/2) − ψ(1+s/2)]/(2(1−2σ))·... derive: 1/((2n+s)(2n+1−s̄)) = [1/(2n+s) − 1/(2n+1−s̄)]/(1−s̄−s)
    closed = -omega(s, 1) - (psi(0, 1 + (1-conj(s))/2) - psi(0, 1 + s/2)) / (2*(1 - conj(s) - s))
    print("s=%s  M direct=%s  closed=%s  |diff|=%.1e   1/(2t)=%.5f   Im M=%.5f Re M=%.2e" % (s, mp.nstr(direct,8), mp.nstr(closed,8), fabs(direct-closed), 1/(2*t), im(direct), re(direct)))
    for N in (64, 128, 256):
        # coherent-limit matrix: T_{jl} = (−1)^{j−l} (M if j>l, conj M if j<l), 0 diag; its min eigenvalue
        Mc = complex(direct)
        T = np.zeros((N,N), dtype=complex)
        for j in range(N):
            for l in range(N):
                if j > l: T[j,l] = ((-1)**(j-l))*Mc
                elif j < l: T[j,l] = ((-1)**(j-l))*np.conj(Mc)
        ev = np.linalg.eigvalsh(T)
        print("   N=%d  coherent-limit min eig = %+.4f   skew bound (2N/π)|Im M| = %.4f  cot(π/2N)|Im M| = %.4f" % (N, ev.min(), 2*N/np.pi*abs(Mc.imag), float(cot(pi/(2*N)))*abs(Mc.imag)))
