#!/usr/bin/env python3
"""Phase 2b: the empirical converse-requirement curve.

Add chi-twisted closure rows to the rigidity map and measure corank as
GL(1)-twist channels accumulate.  Twisted row for primitive real chi mod q,
rank-(r+1) stack, conductor scale C = q^{(r+1)/2}:
    D_chi(x) = sum_n c_n chi(n) [ K_chi(n/(C x)) - s * x * K_chi(n x / C) ]
with s = eps_chi (a sign, measured), and K_chi the Gamma-stack kernel with
the zero-channel parity flipped when chi is odd (even r only).

Runs:
  calibrate r q Ntail   -- measure eps_chi on the true vector (tail-complete)
  curve r N q1,q2,...   -- corank after 0,1,2,... channels
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from adapter_sym_probe import tau_coeffs, sym_coeffs, gammaR_params, kernel_factory

mp.mp.dps = 30
KM1 = 11

# real primitive characters: q -> (table, parity chi(-1))
CHARS = {
    3: ([0, 1, -1], -1),
    4: ([0, 1, 0, -1], -1),
    5: ([0, 1, -1, -1, 1], 1),
    7: ([0, 1, 1, -1, 1, -1, -1], -1),
    8: ([0, 1, 0, -1, 0, -1, 0, 1], 1),
}

def chi_val(q, n):
    tab, _ = CHARS[q]
    return tab[n % q]

def stack_params(r, q=None, delta=1):
    """Gamma-stack params; odd chi flips the even-r zero channel."""
    if q is None:
        return gammaR_params(r, delta)
    _, par = CHARS[q]
    d = delta if par == 1 else (delta + 1) % 2
    return gammaR_params(r, d)

def true_lam(r, N):
    tau = tau_coeffs(N)
    if r == 1:
        return [mp.mpf(0)] + [mp.mpf(tau[n]) / mp.mpf(n) ** (mp.mpf(KM1) / 2)
                              for n in range(1, N + 1)]
    return sym_coeffs(r, N, tau)

def twisted_defect(r, N, q, s, lam, xs, delta=1):
    K = kernel_factory(stack_params(r, q, delta))
    C = mp.mpf(q) ** (mp.mpf(r + 1) / 2)
    out = []
    for x in xs:
        T1 = mp.fsum(lam[n] * chi_val(q, n) * K(n / (C * x))
                     for n in range(1, N + 1) if lam[n] != 0 and chi_val(q, n) != 0)
        T2 = mp.fsum(lam[n] * chi_val(q, n) * K(n * x / C)
                     for n in range(1, N + 1) if lam[n] != 0 and chi_val(q, n) != 0)
        out.append((x, T1 - s * x * T2, T2))
    return out

def calibrate(r, q, Ntail, delta=1):
    lam = true_lam(r, Ntail)
    xs = [mp.mpf('1.1'), mp.mpf('1.4')]
    print(f"# calibrate eps_chi: Sym^{r}, q={q} (parity {CHARS[q][1]}), N={Ntail}")
    for s in (1, -1):
        rows = twisted_defect(r, Ntail, q, s, lam, xs, delta)
        rels = [abs(D) / (abs(T) + mp.mpf('1e-40')) for _, D, T in rows]
        print(f"#   s={s:+d}: rel defects", [mp.nstr(rl, 3) for rl in rels])

def channel_rows(r, N, M, q, s, delta=1):
    """Rows of the twisted closure map on coefficient space n<=N."""
    K = kernel_factory(stack_params(r, q, delta) if q else stack_params(r, None, delta))
    C = mp.mpf(q) ** (mp.mpf(r + 1) / 2) if q else mp.mpf(1)
    xs = [mp.mpf(1) + mp.mpf('0.8') * i / (M - 1) for i in range(M)]
    A = mp.zeros(M, N)
    for i, x in enumerate(xs):
        for n in range(1, N + 1):
            ch = chi_val(q, n) if q else 1
            if ch == 0:
                continue
            A[i, n - 1] = ch * (K(n / (C * x)) - s * x * K(n * x / C))
    return A

def stack_maps(mats):
    M = sum(A.rows for A in mats)
    N = mats[0].cols
    B = mp.zeros(M, N)
    r0 = 0
    for A in mats:
        for i in range(A.rows):
            for j in range(N):
                B[r0 + i, j] = A[i, j]
        r0 += A.rows
    return B

def corank_curve(r, N, qs, s=1, delta=1):
    M = 2 * N
    mats = [channel_rows(r, N, M, None, 1, delta)]
    labels = ['FE']
    def report():
        B = stack_maps(mats)
        U, S, V = mp.svd_r(B)
        svals = sorted([S[i] for i in range(N)], reverse=True)
        smax = svals[0]
        nul = {t: sum(1 for sv in svals if sv / smax < mp.mpf(t))
               for t in ('1e-8', '1e-14', '1e-20')}
        print(f"#  channels={labels}: nullity {nul['1e-8']}/{nul['1e-14']}/{nul['1e-20']} of {N}"
              f"  (rel<1e-8/-14/-20)")
    print(f"# corank curve Sym^{r}, N={N}, M={M}/channel")
    report()
    for q in qs:
        mats.append(channel_rows(r, N, M, q, s, delta))
        labels.append(f"q{q}")
        report()

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'calibrate':
        r, q, Ntail = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        calibrate(r, q, Ntail)
    elif mode == 'curve':
        r, N = int(sys.argv[2]), int(sys.argv[3])
        qs = [int(t) for t in sys.argv[4].split(',')]
        corank_curve(r, N, qs)
