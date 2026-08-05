import numpy as np, math
def indic(base,d):
    mod=base**d; v=np.zeros(mod)
    for r in range(mod):
        x=r; ok=True
        for _ in range(d):
            if x%base>(base-1)//2: ok=False; break
            x//=base
        v[r]=1.0 if ok else 0.0
    return v
def run(p,dp,q,dq,N):
    Pm,Qm=p**dp,q**dq; M=Pm*Qm
    cp,cq=indic(p,dp),indic(q,dq)
    Cp=np.fft.fft(cp)/Pm; Cq=np.fft.fft(cq)/Qm
    a=np.arange(Pm)[:,None]; b=np.arange(Qm)[None,:]
    A=(Qm*a+Pm*b)%M; A=np.where(A>M//2,A-M,A)            # signed distance to the common mode
    th=A/M
    with np.errstate(divide='ignore',invalid='ignore'):
        z=np.exp(2j*np.pi*th); S=np.where(A==0,N,(z*(z**N-1)/(z-1)))
    W=np.abs(Cp[:,None]*Cq[None,:])                       # harmonic weight
    T=(Cp[:,None]*Cq[None,:]*S).real
    mask=~((a==0)&(b==0))
    # exact count
    n=np.arange(1,N+1); m=np.ones(N,bool); x=n.copy()
    for _ in range(dp): m &= (x%p)<=(p-1)//2; x=x//p
    x=n.copy()
    for _ in range(dq): m &= (x%q)<=(q-1)//2; x=x//q
    err=m.sum()-N*cp.mean()*cq.mean()
    return dict(M=M,Pm=Pm,Qm=Qm,err=err,recon=T[mask].sum(),A=A[mask],W=W[mask],T=T[mask],
                S=np.abs(S)[mask],sump=Pm+Qm)
for (p,dp,q,dq,N) in [(3,3,5,2,100000),(3,4,5,3,100000),(7,2,11,2,200000)]:
    r=run(p,dp,q,dq,N)
    print("p=%d^%d q=%d^%d   M=%d   sum p^d=%d   N=%d"%(p,dp,q,dq,r['M'],r['sump'],N))
    print("   exact err = %+.4f    Fourier reconstruction = %+.4f"%(r['err'],r['recon']))
    aA=np.abs(r['A']); order=np.argsort(aA)
    print("   defect mass by distance |A| to the common mode:")
    cum=0.0; tot=np.abs(r['T']).sum()
    for lo,hi in [(1,1),(2,3),(4,7),(8,15),(16,63),(64,255),(256,r['M'])]:
        sel=(aA>=lo)&(aA<=hi)
        if not sel.any(): continue
        mt=np.abs(r['T'][sel]).sum(); cum+=mt
        print("      |A| in [%4d,%6d] : %5d modes, weight sum %.3e, |contrib| %8.3f  (cum %5.1f%%)"
              %(lo,hi,sel.sum(),r['W'][sel].sum(),mt,100*cum/tot))
    print("   total |contrib| = %.3f   vs  sum p^d = %d   vs  M = %d"%(tot,r['sump'],r['M']))
    print("   sum over modes of W*min(N,M/2|A|) = %.3f\n"%(r['W']*np.minimum(N,r['M']/(2*np.maximum(aA,1)))).sum())
