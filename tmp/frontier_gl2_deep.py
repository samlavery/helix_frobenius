"""Deep GL(2) test: Sym^5 Delta x f16, degree 12, with the coefficient bank pushed PAST
the kernel support (n ~ 15547 ~ sqrt(analytic conductor)) using FFT-fast Satake, to test
whether the emergent eps stabilises once the high-conductor coefficient truncation is gone.
Runs at two N to check convergence.  Non-circular: local Satake + tensor + arch type only."""
import sys, time, math
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")
import numpy as np
import sym5_close as S
import focal_closure as fc

def sigma3_sieve(N):
    sig = np.zeros(N + 1, dtype=float)
    for d in range(1, N + 1):
        sig[d::d] += float(d) ** 3
    return sig

class Form:
    def __init__(self, k, theta): self.k = k; self.theta = theta

def build_forms(N):
    lam_d = fc.delta_lambda(N)                       # tau(n)/n^5.5 = 2cos th (FFT-fast, ~1e-15)
    n = np.arange(N + 1, dtype=float)
    tau_f = np.zeros(N + 1); tau_f[1:] = lam_d[1:] * n[1:] ** 5.5      # tau(n) as float
    E4 = np.zeros(N + 1); E4[0] = 1.0; E4[1:] = 240.0 * sigma3_sieve(N)[1:]
    primes = S.sieve_primes(N)
    # Delta Satake straight from lam_d; f16 Satake by SHORT per-prime convolution (well-conditioned)
    th_d = {int(p): math.acos(max(-1.0, min(1.0, lam_d[p] / 2.0))) for p in primes}
    th_f = {}
    bad = []
    for p in primes:
        ap = float(np.dot(tau_f[1:p + 1], E4[p - 1::-1]))   # a_p(f16) = (Delta*E4)_p, exact-ish
        lam = ap / p ** 7.5
        if abs(lam) > 2.0 + 1e-6:
            bad.append((int(p), round(lam, 4)))
        th_f[int(p)] = math.acos(max(-1.0, min(1.0, lam / 2.0)))
    return Form(12, th_d), Form(16, th_f), bad[:6]

for N in (int(sys.argv[1]) if len(sys.argv) > 1 else 8000,
          int(sys.argv[2]) if len(sys.argv) > 2 else 20000):
    t = time.time()
    Delta, f16, bad = build_forms(N)
    print(f"\n########## N = {N}   (forms {time.time()-t:.1f}s; Deligne violations: {bad}) ##########",
          flush=True)
    S.analyze(Delta, 5, ("sym", f16, 1), N, f"Sym^5(Delta) x f16 [GL(2)]  N={N}",
              note=f"(deep, d=12, coeff bank {N})",
              s0_list=[1.05, 1.08, 1.12, 1.2, 1.35])
