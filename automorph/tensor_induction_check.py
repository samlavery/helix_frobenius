#!/usr/bin/env python3
"""
tensor_induction_check.py -- EMPIRICALLY test the tensor-induction chain I asserted for A1.
Every link is checked on real Delta Satake data. If a link fails, the argument is wrong.

Chain (for Sym^5 = top block of pi (x) Sym^4 = Sym^5 (+) Sym^3):
  (L1) coefficient factorization:  a_{pi x Sym^4}(n) == (a_{Sym^5} * a_{Sym^3})(n)  [Dirichlet convolution]
       -- i.e. L(pi x Sym^4) = L(Sym^5) L(Sym^3).  If this fails, the Clebsch-Gordan factorization I used is wrong.
  (L2) Rankin-Selberg base has mean 0:  (1/N) sum_{n<=N} a_{pi x Sym^4}(n) -> 0   [Jacquet-Shalika input]
  (L3) inductive block has mean 0:       (1/N) sum a_{Sym^3}(n) -> 0                [IH]
  (L4) non-vanishing at 1:               L(Sym^3)(1) = sum a_{Sym^3}(n)/n != 0      [Jacquet-Shalika non-vanishing]
  (L5) CONCLUSION mean(Sym^5) = 0:       (1/N) sum a_{Sym^5}(n) -> 0                [what the chain must yield]
  (L6) LOGIC test -- the convolution-mean identity is NOT vacuous: replace Sym^5 by the TRIVIAL rep Sym^0=1
       (mean 1).  Then mean(1 * a_{Sym^3}) must equal L(Sym^3)(1) != 0, NOT 0.  This proves the identity can
       detect a nonzero mean, so (L5)=0 is a real deduction, not "everything is small so it works".
Run: python3 tmp/tensor_induction_check.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_closure_3d as S
from gl4_rankin import channel_lambda

def dirichlet_conv(f, g, N):
    """(f*g)(n) for n=1..N, f,g indexed 1..N."""
    out = np.zeros(N + 1)
    for d in range(1, N + 1):
        if f[d] == 0.0:
            continue
        out[d:N + 1:d] += f[d] * g[1:N // d + 1]
    return out

def main():
    N = 100000
    spf = S.spf_sieve(N)
    primes = [p for p in range(2, N + 1) if spf[p] == p]
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    th = {p: math.acos(max(-1, min(1, lam_d[p].real / 2))) for p in primes}

    s5 = S.sym_r_lambda(5, th, spf, N)      # a_{Sym^5}(n), n=0..N
    s3 = S.sym_r_lambda(3, th, spf, N)      # a_{Sym^3}(n)
    # a_{pi x Sym^4}: tensor channels {+-1 + (4-2j)} * theta, j=0..4  (10 channels) -- INDEPENDENT of s5,s3
    chan = {p: [(sgn + (4 - 2 * j)) * th[p] for sgn in (1, -1) for j in range(5)] for p in th}
    tens = channel_lambda(chan, spf, N)     # a_{pi x Sym^4}(n) from the tensor Satake directly

    print("TENSOR-INDUCTION CHAIN, checked on real Delta data (N=%d)" % N)
    print("=" * 74)

    # (L1) factorization: a_{pi x Sym^4} == a_{Sym^5} * a_{Sym^3}
    conv = dirichlet_conv(s5, s3, N)
    maxerr = np.max(np.abs(conv[1:N + 1] - tens[1:N + 1]))
    print(f"(L1) a_(pi x Sym^4) == a_Sym5 * a_Sym3 (convolution): max|diff| over n<=N = {maxerr:.2e}  "
          f"-> {'HOLDS' if maxerr < 1e-6 else 'FAILS'}")

    X = np.arange(1, N + 1)
    def mean(a): return np.cumsum(a[1:N + 1]) / X
    m_t, m5, m3 = mean(tens), mean(s5), mean(s3)
    print(f"(L2) mean a_(pi x Sym^4): |.|/N at N/2={abs(m_t[N//2]):.2e}, N={abs(m_t[-1]):.2e}  -> {'->0' if abs(m_t[-1])<abs(m_t[N//2]) or abs(m_t[-1])<1e-2 else '??'}")
    print(f"(L3) mean a_Sym3        : |.|/N at N/2={abs(m3[N//2]):.2e}, N={abs(m3[-1]):.2e}")
    Ls3_1 = np.sum(s3[1:N + 1] / X)                                   # L(Sym^3)(1) ~ sum a/n (partial)
    print(f"(L4) L(Sym^3)(1) ~ sum a_Sym3(n)/n (partial to N) = {Ls3_1:.4f}  -> {'!= 0' if abs(Ls3_1)>0.05 else 'NEAR 0 (!)'} ")
    print(f"(L5) CONCLUSION mean a_Sym5: |.|/N at N/2={abs(m5[N//2]):.2e}, N={abs(m5[-1]):.2e}  -> {'->0' if abs(m5[-1])<1e-2 else '??'}")

    # (L6) non-vacuity: trivial rep (mean 1) convolved with a_Sym3 -> mean should be L(Sym^3)(1) != 0, not 0
    one = np.zeros(N + 1); one[1:] = 1.0
    triv_conv = dirichlet_conv(one, s3, N)
    m_triv = np.cumsum(triv_conv[1:N + 1]) / X
    print(f"(L6) mean (1 * a_Sym3) at N = {m_triv[-1]:.4f}  vs  L(Sym^3)(1) = {Ls3_1:.4f}  "
          f"-> {'MATCH (identity detects nonzero mean; L5=0 is a real deduction)' if abs(m_triv[-1]-Ls3_1)<0.15 else 'MISMATCH'}")
    print("\n[read] L1 HOLDS => factorization real. L2,L3,L5 ->0 => means vanish as claimed. L4 !=0 =>")
    print("       non-vanishing input holds. L6 MATCH => the convolution-mean identity is non-vacuous:")
    print("       mean(base)=0 & L(Sym^{r-2})(1)!=0 FORCES mean(Sym^r)=0, not coincidence.")

if __name__ == "__main__":
    main()
