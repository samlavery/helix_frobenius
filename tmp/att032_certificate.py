"""ATTEMPT 032 G5 -- the certificate value itself, MAIN TERMS ONLY (no taper constants a,b,
no error terms; Remark 5.9 warns the w=1 finite-T certificate is weaker than these numbers).
Prop 4.4(ii):  N_0 >= (4 tr G^ - ||G^||_F^2 - 2N) = (2 - mu_2) N  since mu_1 = 1 + o(1).
NULL: DH's certificate value stays positive at every accessible T, i.e. the two-moment data
does not know DH is different."""
import numpy as np, math
from scipy.optimize import brentq
TMP='/Users/samuellavery/work/helix_frobenius/tmp/'
LamZ=np.load(TMP+'att032_lam_vm.npy'); LamD=np.load(TMP+'att032_lam_DH.npy')
NM=min(len(LamZ),len(LamD))-1; n=np.arange(1,NM+1); logn=np.log(n)
def S2(Lam,X,L):
    m=n<=X; return float(np.sum(Lam[1:NM+1][m]**2*np.maximum(L-logn[m],0.0)/n[m]))
def mu2(Lam,T,lam,cond=1.0):
    l=math.log(T/(2*math.pi)); lc=math.log(cond*T/(2*math.pi)); L=lam*l; X=math.exp(L)
    return lc/L+2*S2(Lam,X,L)/(L*L*lc)
print(f"{'T':>10} {'2-mu2 zeta':>12} {'2-mu2 DH':>10}")
for T in (1e4,3e4,1e5,3e5,1e6,3e6,1e7):
    print(f"{T:10.1e} {2-mu2(LamZ,T,1.0):12.4f} {2-mu2(LamD,T,1.0,5.0):10.4f}")
r=brentq(lambda lT: 2-mu2(LamD,10**lT,1.0,5.0),4.0,7.0)
print(f"\nDH certificate main term crosses zero at T = 10^{r:.4f} = {10**r:.3e}")
print("H(lambda)=2-1/lambda-lambda/3:",{l:round(2-1/l-l/3,5) for l in (1.0,0.7,0.55,0.5)})
