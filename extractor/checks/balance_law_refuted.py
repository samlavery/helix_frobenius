"""Is AngleSectorBalanceLaw TRUE?  Direct numerical test.

imbalance(N,t) = ||S0-S3|| + ||S1-S4|| + ||S2-S5||,  S_j = sum over n<=N in sector j of
Lambda(n) n^{-1/2-it}.  The law claims imbalance(N,t) -> 0 as N -> oo at every on-line zero.

PENCIL ARGUMENT (to be checked, not assumed): every phasor in sector j lies in a closed
arc of width 2pi/6 = pi/3, so all of them are within +-pi/6 of that arc's midpoint u_j.
Hence <S_j, u_j> >= cos(pi/6) * M_j where M_j = sum of |terms| in sector j.  The antipodal
arc has midpoint -u_j, so <S_{j+3}, u_j> <= -cos(pi/6) M_{j+3}.  Therefore
   ||S_j - S_{j+3}|| >= <S_j - S_{j+3}, u_j> >= (sqrt3/2)(M_j + M_{j+3}),
and summing j=0,1,2:  imbalance >= (sqrt3/2) * sum_{n<=N} Lambda(n)/sqrt(n) ~ sqrt(3) sqrt(N).
So imbalance DIVERGES, at every t.

PRE-REGISTERED: if imbalance(N,t) grows like sqrt(N) at a genuine zero, the law as stated is
FALSE.  If it decays toward 0, the pencil argument is wrong and the law stands.
"""
import numpy as np, math

def von_mangoldt(N):
    lam = np.zeros(N+1)
    sieve = np.ones(N+1, dtype=bool); sieve[:2] = False
    for i in range(2, int(N**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= N:
            lam[q] = math.log(p); q *= int(p)
    return lam

def imbalance(N, t, lam):
    n = np.arange(1, N+1)
    w = lam[1:N+1]/np.sqrt(n)
    keep = w > 0
    n, w = n[keep], w[keep]
    ang = -t*np.log(n)
    frac = np.mod(t*np.log(n)/(2*math.pi), 1.0)
    sec = np.floor(6*frac).astype(int) % 6
    z = w*np.exp(1j*ang)
    S = np.array([z[sec == j].sum() for j in range(6)])
    M = np.array([w[sec == j].sum() for j in range(6)])
    imb = sum(abs(S[j]-S[j+3]) for j in range(3))
    return imb, w.sum(), M

G1 = 14.134725141734693      # a genuine on-line zero
NZ = 20.0                    # not a zero
lam = von_mangoldt(4_000_000)

for label, t in [("ZERO  gamma_1 = 14.1347", G1), ("non-zero t = 20", NZ)]:
    print(f"=== {label} ===")
    print(f"{'N':>10} {'imbalance':>14} {'total mass':>12} {'imb/mass':>10} {'imb/sqrt(N)':>12}")
    for N in [10**3, 10**4, 10**5, 10**6, 4*10**6]:
        imb, mass, M = imbalance(N, t, lam)
        print(f"{N:>10} {imb:>14.4f} {mass:>12.4f} {imb/mass:>10.4f} {imb/math.sqrt(N):>12.4f}")
    print()
print("lower bound predicted by the pencil argument: imb/mass >= sqrt(3)/2 =", math.sqrt(3)/2)
