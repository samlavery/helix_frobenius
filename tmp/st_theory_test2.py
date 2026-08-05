"""Carrier-time S(t) test: log-uniform ticks u_k on [log 1e6, log 1e12],
M(x)=sum 1/p * [top-J_p digits lower-half], deviation integrated in du.
S(t) signature = band-confined integral vs sqrt random-walk prediction."""
import numpy as np, math
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
Y=2000; c=2.0
P=[p for p in primes_to(Y) if p>=3]
logs={p:math.log(p) for p in P}
J={p:max(1,int(c*math.log(math.log(p+2)))) for p in P}
rng=np.random.default_rng(377)
K=40000
u=np.sort(rng.uniform(math.log(1e6), math.log(1e12), K))
xs=np.exp(u).astype(np.int64)
M=np.zeros(K)
for k,xv in enumerate(xs):
    lx=math.log(xv); m=0.0
    for p in P:
        d=int(lx/logs[p])
        Jp=min(J[p],d)
        q=xv//p**(d-Jp)   # top Jp digits = digits of q (q < p^Jp * p ... take q's low Jp digits? q = x/p^{d-Jp}: q in [p^{Jp-?}..) — its digits ARE x's top digits
        ok=True
        for _ in range(Jp):
            if q%p > (p-1)//2: ok=False; break
            q//=p
        if ok: m+=1.0/p
    M[k]=m
mean=M.mean(); sig=M.std()
du=np.diff(u, prepend=u[0])
D=np.cumsum((M-mean)*du)
T=u[-1]-u[0]
# random-walk prediction for integral of iid noise sampled at K points over span T:
rw=sig*T/np.sqrt(K)*np.sqrt(np.arange(1,K+1))
print(f"K={K} rails={len(P)}  mean M={mean:.4f} sup M={M.max():.4f} sigma={sig:.4f}")
print(f"max|D| = {np.abs(D).max():.4f}   RW prediction at end = {sig*T/np.sqrt(K)*np.sqrt(K):.4f} = sigma*T/sqrt(K)*sqrt(K)")
print(f"proper RW: sigma*sqrt(sum du^2)*... -> use sigma*sqrt(T*mean_du)={sig*math.sqrt(T*T/K):.4f}")
print(f"ratio max|D| / (sigma*T/sqrt(K)) = {np.abs(D).max()/(sig*T/math.sqrt(K)):.3f}  (~sqrt(K)=200 if random walk, <<sqrt(K) if compensated)")
print(f"|D| quantiles 50/90/100: {np.percentile(np.abs(D),50):.3f} {np.percentile(np.abs(D),90):.3f} {np.abs(D).max():.3f}")
# autocorrelation of M at log-lags (compensation = negative correlation structure)
for lag in (1,5,20,100):
    r=np.corrcoef(M[:-lag],M[lag:])[0,1]
    print(f"autocorr lag~{lag} (du~{T*lag/K:.4f}): {r:+.3f}")
