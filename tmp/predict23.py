"""SUBGOAL: is S removable for PREDICTING?
gamma_n = theta^-1( (n - 3/2 - S_smooth(gamma_n)) pi ),  S_smooth = prime sum.
Full sum diverges (high frequencies decorrelate under the position error).
Harmonic truncation (2^k, 3^k only) should CONVERGE: low frequency, 73% of S."""
import numpy as np, mpmath as mp, sys
mp.mp.dps=15
def P(*a): print(*a); sys.stdout.flush()
def mk(sel,X=4000):
    L=np.zeros(X+1)
    for p in range(2,X+1):
        if all(p%q for q in range(2,int(p**0.5)+1)):
            q=p
            while q<=X: L[q]=np.log(p); q*=p
    idx=np.nonzero(L)[0]
    def isp(n,p):
        while n%p==0: n//=p
        return n==1
    if sel=='23':  m=np.array([isp(int(n),2) or isp(int(n),3) for n in idx])
    elif sel=='2': m=np.array([isp(int(n),2) for n in idx])
    else:          m=np.ones(len(idx),bool)
    i2=idx[m]; return L[i2]/(np.sqrt(i2)*np.log(i2)), np.log(i2)
def invth(y,g): return float(mp.findroot(lambda t: mp.siegeltheta(t)-y, g))
true=[float(mp.im(mp.zetazero(k))) for k in range(1,301)]
NN=len(true)
sp=np.array([2*np.pi/np.log(t/(2*np.pi)) for t in true])
base=np.array([invth((n-1.5)*np.pi, max(true[n-1],14.0)) for n in range(1,NN+1)])
P(f"baseline constructor (index only):  sd/spacing = {((base-np.array(true))/sp).std():.5f}\n")
for sel,lab in (('23','2^k and 3^k only  (23 terms)'),('2','2^k only'),('all','ALL prime powers X<=4000')):
    w,ln=mk(sel)
    S=lambda t: -(1/np.pi)*np.sum(w*np.sin(t*ln))
    gam=base.copy()
    P(f"{lab}")
    for it in range(1,6):
        Sv=np.array([S(t) for t in gam])
        gam=np.array([invth((n-1.5-Sv[n-1])*np.pi, gam[n-1]) for n in range(1,NN+1)])
        e=(gam-np.array(true))/sp
        P(f"   iter {it}: sd/spacing = {e.std():.5f}   mean {e.mean():+.5f}   max|e| {np.abs(e).max():.4f}")
    P("")
