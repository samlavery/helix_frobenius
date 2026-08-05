"""Test the S(t) theory ON the digit fiber: is the top-window mass ledger a
COMPENSATING registration gap (S(t) signature: running integral confined to a
tight band, like B_N width 1.489 in the zeta fiber) or a random walk (no
compensation)?  D(x) = running sum of (M(x)-mean); compare max|D| to the
random-walk prediction sigma*sqrt(L)."""
import numpy as np, math
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
Y=2000; c=2.0
P=[p for p in primes_to(Y) if p>=3]
N0=10**6; L=300_000
x=np.arange(N0,N0+L,dtype=np.int64)
M=np.zeros(L)
for p in P:
    d=int(math.log(N0)/math.log(p))
    J=max(1,int(c*math.log(math.log(p+2))))
    J=min(J,d)
    ok=np.ones(L,bool)
    for i in range(J):
        ok &= (x//p**(d-1-i))%p <= (p-1)//2
    # guard: d shifts within window for x crossing p^d — window chosen inside one block
    M += ok/p
mean=M.mean()
D=np.cumsum(M-mean)
sig=M.std()
rw=sig*np.sqrt(np.arange(1,L+1))
print(f"rails={len(P)} mean M={mean:.4f}  sup M={M.max():.4f}  sigma={sig:.4f}")
print(f"max|D| = {np.abs(D).max():.1f}   random-walk prediction sigma*sqrt(L) = {sig*L**0.5:.1f}")
print(f"ratio max|D|/RW = {np.abs(D).max()/(sig*L**0.5):.3f}   (<<1 = compensation/S(t) signature)")
# band structure: quantiles of D
q=np.percentile(np.abs(D),[50,90,99,100])
print(f"|D| quantiles 50/90/99/100: {q[0]:.1f} {q[1]:.1f} {q[2]:.1f} {q[3]:.1f}")
