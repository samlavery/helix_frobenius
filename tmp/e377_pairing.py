"""TEST A: the two-rail pairing (hodge_companion §rails) applied to #377.

Pairing rail p with its EXACT conjugate = autocorrelation of the digit set.
Fourier side: |chat|^2 (squared kernel, alpha^-2 decay) instead of |chat|.
Real side: the shift-variance of the joint count,

  V = (1/M) sum_h ( #{n<N : n+h admissible} - N prod rho )^2
    = sum_{alpha != 0} prod_i |chat_i(alpha_i)|^2 |S_N(theta)|^2 .

V factors by CRT through the per-rail autocorrelations R_i, so it is EXACTLY
computable with no lattice count and no Diophantine input:

  V = sum_{|d|<N} (N-|d|) prod_i R_i(d mod P_i)/P_i  -  (N prod rho)^2.

Claim under test: sqrt(V) << sum_i P_i  (additive law on the pairing, proven
unconditionally) -- including in the deep regime M >> N where CRT is vacuous
and Corso-Shmerkin is currently invoked.
"""
import math

def Dset(p, d):
    """admissible residues mod p^d (all d base-p digits <= (p-1)/2)"""
    P = p ** d
    D = (p - 1) // 2
    out = []
    for a in range(P):
        m, ok = a, True
        for _ in range(d):
            if m % p > D: ok = False; break
            m //= p
        if ok: out.append(a)
    return out, P

def autocorr(p, d):
    """R(t) = #{a in D : a+t mod P in D}, as a list of length P"""
    D, P = Dset(p, d)
    ind = bytearray(P)
    for a in D: ind[a] = 1
    R = [0] * P
    for a in D:
        for b in D:
            R[(b - a) % P] += 1
    return R, P, len(D)

def shift_variance(N, rails):
    tabs = []
    M = 1
    dens = 1.0
    for (p, d) in rails:
        R, P, sz = autocorr(p, d)
        tabs.append((R, P))
        M *= P
        dens *= sz / P
    tot = 0.0
    for dd in range(-(N - 1), N):
        w = N - abs(dd)
        pr = 1.0
        for (R, P) in tabs:
            pr *= R[dd % P] / P
            if pr == 0.0: break
        tot += w * pr
    return tot - (N * dens) ** 2, M, dens

configs = [
    # (rails, label) -- last three are the DEEP regime M >> N
    ([(3, 2), (5, 2)],                 "shallow"),
    ([(5, 2), (7, 2)],                 "shallow"),
    ([(11, 2), (13, 2)],               "shallow"),
    ([(101, 1), (103, 1)],             "twin (worst beat)"),
    ([(419, 1), (421, 1)],             "twin (worst beat)"),
    ([(3, 4), (5, 3), (7, 2)],         "3 rails"),
    ([(3, 6), (5, 4), (7, 3)],         "3 rails DEEP"),
    ([(3, 7), (5, 5), (7, 4)],         "3 rails DEEP"),
    ([(3, 5), (5, 4), (7, 3), (11, 2)], "4 rails DEEP"),
    ([(3, 6), (5, 5), (7, 4), (11, 3)], "4 rails DEEPEST"),
]

N = 20000
print(f"N = {N}\n")
print(f"{'rails':<28} {'label':<18} {'M/N':>10} {'sqrt(V)':>10} {'sum P_i':>9} "
      f"{'ratio':>7} {'sqrt(MN)':>10}")
print("-" * 100)
for rails, lab in configs:
    V, M, dens = shift_variance(N, rails)
    sp = sum(p ** d for (p, d) in rails)
    sv = math.sqrt(max(V, 0.0))
    print(f"{str(rails):<28} {lab:<18} {M/N:>10.2f} {sv:>10.2f} {sp:>9} "
          f"{sv/sp:>7.3f} {math.sqrt(M*N):>10.3g}")
