"""Full E(n) on the {3,5,7}-balanced census (enumerated, not scanned) vs random control."""
import numpy as np, random
def sieve(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0].astype(np.int64)
def bal(n,p):
    D=(p-1)//2
    while n:
        if n%p>D: return False
        n//=p
    return True
def E(n,P,Dh):
    ok=np.ones(len(P),bool); q=np.full(len(P),n,dtype=np.int64)
    while True:
        live=np.nonzero(ok&(q>0))[0]
        if live.size==0: break
        r=q[live]%P[live]
        ok[live[r>Dh[live]]]=False
        q[live]=q[live]//P[live]
    return float(np.sum(1.0/P[ok]))
def census(N):
    """n <= N with all base-3 digits in {0,1}, then balanced at 5 and 7."""
    pw=[]; x=1
    while x<=N: pw.append(x); x*=3
    out=[]
    for mask in range(1<<len(pw)):
        n=0; mm=mask; i=0
        while mm:
            if mm&1: n+=pw[i]
            mm>>=1; i+=1
        if 0<n<=N and bal(n,5) and bal(n,7): out.append(n)
    return sorted(out)
random.seed(7); C=1/3+1/5+1/7
print(f"{'N':>9} {'#census':>8} {'maxE census':>12} {'argmax':>11} {'E_small there':>13} "
      f"{'maxE random':>12} {'meanE rand':>11}")
print("-"*94)
for N in [10**5,10**6,10**7,10**8]:
    allp=sieve(N); cen=census(N); cen=[n for n in cen if n>N//10]
    ctl=[random.randrange(N//2,N) for _ in range(250)]
    def scan(ns):
        best=-1;arg=None
        for n in ns:
            k=np.searchsorted(allp,n,'right')
            v=E(n,allp[:k],(allp[:k]-1)//2)
            if v>best: best,arg=v,n
        return best,arg
    bc,ac=scan(cen) if cen else (float('nan'),None)
    br,ar=scan(ctl)
    vals=[]
    for n in ctl[:120]:
        k=np.searchsorted(allp,n,'right'); vals.append(E(n,allp[:k],(allp[:k]-1)//2))
    es=sum(1/p for p in [3,5,7,11,13,17,19,23,29,31] if ac and bal(ac,p)) if ac else float('nan')
    print(f"{N:>9} {len(cen):>8} {bc:>12.6f} {str(ac):>11} {es:>13.6f} {br:>12.6f} {np.mean(vals):>11.6f}")
print(f"\n  1/3+1/5+1/7 = {C:.6f}      C0 (mean) = 0.507834")
