"""PER-BAND HARMONIC CONTENT.
   gamma_k(n) = (balanced Mertens mass of band k) / (full Mertens mass of band k).
   DC prediction: gamma_k ~ cos^{k+1}(theta_p) ~ 2^{-(k+1)}.
   THE QUESTION: is max_n gamma_k small (per-band mechanism, E bounded band by band),
   or is max_n gamma_k ~ 1 for every k separately (so boundedness is a JOINT
   constraint -- no single n can max out many bands)?  Different proofs entirely."""
import numpy as np, random
def sieve(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0].astype(np.int64)
def balmask(nv,P):
    D=(P-1)//2; ok=np.ones(len(P),bool); q=np.full(len(P),nv,dtype=np.int64)
    while True:
        liv=np.nonzero(ok&(q>0))[0]
        if liv.size==0: break
        ok[liv[(q[liv]%P[liv])>D[liv]]]=False
        q[liv]=q[liv]//P[liv]
    return ok
random.seed(3)
N=10**6; allp=sieve(N)
lo,hi=N//2,N
ns=[random.randrange(lo,hi) for _ in range(1500)]
bands={}
for k in range(1,7):
    a,b=N**(1.0/(k+1)),N**(1.0/k)
    idx=np.nonzero((allp>a)&(allp<=b))[0]
    if len(idx)==0: continue
    bands[k]=(idx, float(np.sum(1.0/allp[idx])))
print(f"N={N}, window [{lo},{hi}], {len(ns)} sampled n\n")
print(f"{'k':>3} {'#p':>7} {'band mass':>10} {'mean g_k':>9} {'max g_k':>9} "
      f"{'2^-(k+1)':>9} {'max/DC':>8} {'argmax n':>10}")
print("-"*82)
G={}
for k,(idx,mass) in bands.items():
    P=allp[idx]; g=[]
    for nv in ns:
        ok=balmask(nv,P); g.append(float(np.sum(1.0/P[ok]))/mass)
    g=np.array(g); G[k]=g
    dc=2.0**-(k+1)
    print(f"{k:>3} {len(P):>7} {mass:>10.5f} {g.mean():>9.5f} {g.max():>9.5f} "
          f"{dc:>9.5f} {g.max()/dc:>8.2f} {ns[int(g.argmax())]:>10}")
print("\nJOINT: for each sampled n, how many bands have g_k > 2 * DC_k ?")
ks=sorted(G)
M=np.array([G[k] for k in ks])            # bands x samples
dcs=np.array([2.0**-(k+1) for k in ks])[:,None]
hits=(M>2*dcs).sum(axis=0)
print(f"   bands hit:  {np.bincount(hits, minlength=len(ks)+1)}   (index = #bands over 2xDC)")
print(f"   max simultaneous = {hits.max()} of {len(ks)} bands")
E=np.array([sum(G[k][i]*bands[k][1] for k in ks) for i in range(len(ns))])
print(f"\n   E over these 6 bands: mean {E.mean():.4f}  max {E.max():.4f}  "
      f"(sum of band masses = {sum(bands[k][1] for k in ks):.4f})")
