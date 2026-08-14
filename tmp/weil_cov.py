"""Coverage law and whether the harmonic lattice improves its constant.
coverage(L,d) = fraction of ordinates where Re[hhat(g-id)^2] < 0.
Conjecture from the sinc data: coverage ~ min(k * L * d, 1/2).  Measure k per lattice."""
import numpy as np
np.seterr(all='ignore')
G=np.linspace(0.05,60.0,3000)
def cov(hh,d):
    v=hh(G-1j*d); return float(np.mean(np.real(v*v)<0))

SC={'pi/3':np.pi/3,'pi/6':np.pi/6,'unit1':1.0,'pi/2':np.pi/2,'2pi/3':2*np.pi/3}
CO={'flat':lambda R: np.ones(R),
    'alt' :lambda R: np.array([(-1)**(r-1) for r in range(1,R+1)],float),
    'mu6' :lambda R: np.array([1.0 if r%6 in (1,5) else (-1.0 if r%6==3 else 0.0)
                               for r in range(1,R+1)]),
    'fej' :lambda R: np.array([1-(r-1)/R for r in range(1,R+1)])}
print("coverage / (L*d)   -- the constant k, measured in the unsaturated regime L*d < 0.3")
print(f"{'coef':>6}" + ''.join(f'{s:>10}' for s in SC))
tries=0; best=(0,None)
for cname,cf in CO.items():
    row=[]
    for sname,s in SC.items():
        ks=[]
        for L in (4.0,8.0,16.0):
            R=max(1,int(round(L/s))); c=cf(R)
            f=lambda z,c=c,s=s: sum(c[r-1]*np.cos(r*s*z) for r in range(1,len(c)+1))
            for d in (0.005,0.01,0.02):
                tries+=1
                if L*d>0.3: continue
                cv=cov(f,d)
                if cv>0: ks.append(cv/(L*d))
        k=np.median(ks) if ks else np.nan
        row.append(k)
        if np.isfinite(k) and k>best[0]: best=(k,f'{cname}/{sname}')
    print(f"{cname:>6}" + ''.join(f'{v:>10.3f}' for v in row))
print(f"\nattempts: {tries}")
print(f"best constant k = {best[0]:.3f}  ({best[1]})")
print("\nSATURATION CHECK -- does coverage cap at 1/2 ?")
f=lambda z: sum(np.cos(r*(np.pi/3)*z) for r in range(1,20))
for d in (0.01,0.05,0.2,1.0,5.0): print(f"   d={d:<5} coverage={cov(f,d):.3f}")
print("\nCONSEQUENCE: bandwidth L <= log(T/2pi), so at depth d the covered fraction")
print("is ~ k*L*d <= k*d*log T.  Blind fraction 1 - that.  k is what a better lattice buys.")
