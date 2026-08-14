"""Does building the Weil test function on the HARMONIC lattice lower d_min?

d_min = shallowest depth any test fn of bandwidth L can detect (Re[hhat(g-id)^2] < 0).
Measured for generic sincs: L * d_min ~ 0.003.  Now compare test functions whose
Fourier support sits on the pi/3 (and pi/6) lattice against the unit-1 lattice,
AT MATCHED BANDWIDTH so the prime-side cost is identical.

   hhat(z) = sum_{r=1..R} c_r cos(r * s * z),   bandwidth L = R * s
   scales s = pi/3, pi/6, 1 (control);  R = round(L/s) to match L.
GATE: hhat must be real on the real axis (c_r real, cosines) -- admissible.
"""
import numpy as np, itertools
np.seterr(all='ignore')
G=np.linspace(0.05,20.0,400)

def d_min(hh, lo=1e-5, hi=5.0):
    def cov(d):
        v=hh(G-1j*d); r=np.real(v*v)
        return np.mean(r<0)
    if cov(hi)<=0: return np.nan
    a,b=lo,hi
    if cov(a)>0: return a
    for _ in range(60):
        m=np.sqrt(a*b)
        if cov(m)>0: b=m
        else: a=m
    return b

SCALES={'pi/3':np.pi/3,'pi/6':np.pi/6,'unit1':1.0,'2pi/3':2*np.pi/3,'pi/2':np.pi/2}
COEF={'flat':lambda R: np.ones(R),
      'fejer':lambda R: np.array([1-(r-1)/R for r in range(1,R+1)]),
      'alt':lambda R: np.array([(-1)**(r-1) for r in range(1,R+1)],float),
      'mu6':lambda R: np.array([1.0 if r%6 in (1,5) else (-1.0 if r%6==3 else 0.0)
                                for r in range(1,R+1)])}
print(f"{'L':>5}{'coef':>7}" + ''.join(f'{k:>12}' for k in SCALES))
print(f"{'':>5}{'':>7}" + ''.join('     L*d_min' for k in SCALES))
tries=0; best=(np.inf,None)
for L in (3.0,6.0,9.0,12.0,18.0):
    for cname,cf in COEF.items():
        row=[]
        for sname,s in SCALES.items():
            R=max(1,int(round(L/s)))
            c=cf(R)
            f=lambda z,c=c,s=s: sum(c[r-1]*np.cos(r*s*z) for r in range(1,len(c)+1))
            tries+=1
            dm=d_min(f); prod=L*dm if np.isfinite(dm) else np.nan
            row.append(prod)
            if np.isfinite(prod) and prod<best[0]: best=(prod,f'L={L:g} {cname} {sname} R={R}')
        print(f"{L:>5g}{cname:>7}" + ''.join(f'{v:>12.5f}' for v in row))
print(f"\nattempts: {tries}")
print(f"generic sinc baseline:  L*d_min ~ 0.00300")
print(f"best found:             L*d_min = {best[0]:.5f}   ({best[1]})")
print(f"improvement factor:     {0.003/best[0]:.2f}x" if np.isfinite(best[0]) else "")
