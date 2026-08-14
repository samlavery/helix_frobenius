"""F(a) = d*delta(a) + Fc(a).  delta -> DIAGONAL (gives d/lam); Fc=|a| -> OFF-DIAGONAL (lam/3).
   M2/M1 = (1/lam^2)[ d*lam + int_{-lam}^{lam} (lam-|a|) Fc(a) da ],   H = 2 - M2/M1
Rescaling the Euler product touches BOTH: the diagonal weight d (from sum Lambda(n)^2/n)
and the support c of Fc (the range where the pair correlation is known)."""
import numpy as np
from scipy.integrate import quad
CAP=0.68185
def H(lam, d=1.0, c=1.0):
    Fc=lambda a: (abs(a/c) if abs(a/c)<=1 else 1.0)/c
    I=quad(lambda a:(lam-abs(a))*Fc(a), -lam, lam, limit=400)[0]
    return 2.0 - (d*lam + I)/lam**2

print("GATE  d=1, c=1 must give  2 - 1/lam - lam/3")
ok=True
for lam in (0.5,0.7,0.85,1.0):
    g,w=H(lam),2-1/lam-lam/3; p=abs(g-w)<1e-9; ok&=p
    print(f"   lam={lam:4.2f}  {g:.9f} vs {w:.9f}  {'PASS' if p else 'FAIL'}")
assert ok
print("   gate PASSED -- scan is calibrated\n")

NAMED={np.pi/6:'pi/6',1.0:'unit1',3/np.pi:'3/pi',np.pi/3:'pi/3',np.pi/2:'pi/2',
       np.sqrt(3):'sqrt3',np.pi:'pi',2*np.pi/3:'2pi/3',6/np.pi:'6/pi',1/3:'1/3'}
def nm(x):
    for v,n in NAMED.items():
        if abs(x-v)<1e-9: return n
    return ''
ds=np.concatenate([np.linspace(0.3,1.2,19),[3/np.pi,6/np.pi,np.pi/3,1/3,np.pi/6]])
cs=np.concatenate([np.linspace(0.6,2.4,19),[np.pi/3,np.pi/6,np.pi/2,np.sqrt(3),np.pi]])
lams=np.linspace(0.3,2.6,24)
res=[];tries=0
for d in ds:
    for c in cs:
        for lam in lams:
            tries+=1
            if lam>c: continue          # Fc unknown past |a|<=c
            res.append((H(lam,d,c),d,c,lam))
res.sort(reverse=True)
print(f"TRIALS: {tries}   admissible: {len(res)}")
print(f"\n{'H':>9}{'d(diag)':>9}{'c(supp)':>9}{'lam':>7}   names")
for h,d,c,l in res[:15]:
    print(f"{h:>9.5f}{d:>9.5f}{c:>9.5f}{l:>7.3f}   d={nm(d):<6} c={nm(c)}")
print(f"\nbaseline H(1,1,1) = {H(1.0):.5f}      cap = {CAP}")
print("\nHOLDING THE OFF-DIAGONAL AT THE PROVEN c=1, VARYING ONLY THE DIAGONAL d:")
print(f"  {'d':>10}{'name':>7}{'best H (lam<=1)':>17}{'':>4}")
for d in (1.0,3/np.pi,np.pi/3,6/np.pi,np.pi/6,1/3):
    b=max(H(l,d,1.0) for l in np.linspace(0.3,1.0,200))
    print(f"  {d:>10.5f}{nm(d):>7}{b:>17.5f}    {'ABOVE CAP' if b>CAP else ''}")
