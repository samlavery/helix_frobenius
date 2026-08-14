"""Work in the HARMONIZED TAPE: theta measured in pi/3 cells, x = 3 theta / pi.
Zeros sit at cell edges (9.7 sigma, measured).  After the 2,3-correction the
residual is 0.116 spacings -- is it STRUCTURED on the pi/3 tape or random?"""
import numpy as np, mpmath as mp, sys
mp.mp.dps=15
def P(*a): print(*a); sys.stdout.flush()
X=4000
Lm=np.zeros(X+1)
for p in range(2,X+1):
    if all(p%q for q in range(2,int(p**0.5)+1)):
        q=p
        while q<=X: Lm[q]=np.log(p); q*=p
IDX=np.nonzero(Lm)[0]
def isp(n,p):
    while n%p==0: n//=p
    return n==1
m=np.array([isp(int(n),2) or isp(int(n),3) for n in IDX])
w=Lm[IDX][m]/(np.sqrt(IDX[m])*np.log(IDX[m])); ln=np.log(IDX[m])
S=lambda t: -(1/np.pi)*np.sum(w*np.sin(t*ln))
def invth(y,g): return float(mp.findroot(lambda t: mp.siegeltheta(t)-y, g))
true=np.array([float(mp.im(mp.zetazero(k))) for k in range(1,501)])
ns=np.arange(1,501)
sp=np.array([2*np.pi/np.log(t/(2*np.pi)) for t in true])
gam=np.array([invth((n-1.5)*np.pi, max(true[i],14.0)) for i,n in enumerate(ns)])
for _ in range(3):
    Sv=np.array([S(t) for t in gam])
    gam=np.array([invth((n-1.5-Sv[i])*np.pi, gam[i]) for i,n in enumerate(ns)])
res=(gam-true)/sp
P(f"residual after 2,3-correction: sd {res.std():.5f} spacings, mean {res.mean():+.5f}\n")
# harmonized tape coordinate: x = 3 theta / pi  (pi/3 cells)
th=np.array([float(mp.siegeltheta(t)) for t in true])
x=3*th/np.pi
P("STRUCTURE OF THE RESIDUAL ON THE pi/3 TAPE:")
for lab,ph in (('frac(x)   [pi/3 cell]', np.mod(x,1.0)),
               ('frac(x/3) [pi cell]',   np.mod(x/3,1.0)),
               ('frac(x/6) [mu6 loop]',  np.mod(x/6,1.0))):
    R=abs(np.mean(res*np.exp(2j*np.pi*ph)))/ (res.std()/np.sqrt(len(res)))
    c=abs(np.mean(np.exp(2j*np.pi*ph)))
    P(f"  {lab:<24} |<res * e^(2pi i phase)>| / noise = {R:6.2f} sigma   (phase conc {c:.3f})")
P()
P("  and the residual vs the CELL INDEX parity (which third of the pi cell):")
third=np.floor(np.mod(x,3)).astype(int)
for k in (0,1,2):
    s=res[third==k]
    P(f"    third {k}: n={len(s):>4}  mean {s.mean():+.5f}  sd {s.std():.5f}")
P()
P(f"  residual autocorrelation at lag 1..4 (is it index-structured?):")
r=res-res.mean()
for L in (1,2,3,4):
    P(f"    lag {L}: {np.corrcoef(r[:-L],r[L:])[0,1]:+.4f}")
