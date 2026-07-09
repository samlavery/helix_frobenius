"""Independent L-evaluator via the theta/Mellin integral form (self-contained).

Lambda(s) = N^{s/2} prod_j Gamma_R(s+mu_j) L(s),  Gamma_R(s)=pi^{-s/2}Gamma(s/2).
FE: Lambda(s)=eps Lambda(1-s).  Entire Lambda:
    Lambda(s) = int_1^inf Theta(u)[u^s+eps u^{1-s}] du/u,   Theta(u)=sum a_n K(n u/sqrt(N)),
    K(y)=(1/2pi i) int prod_j Gamma_R(w+mu_j) y^{-w} dw.
Uses only a_n,N,mu_j,eps. No zeros/L-values fed in.
"""
import numpy as np, mpmath as mp

def make_K(mus, sigma=None, dv=0.02, Uw=None):
    d=len(mus)
    if sigma is None: sigma=max(2.5, 1.0-min(mus)+2.0)
    if Uw is None:    Uw=60.0/d+20.0
    vs=np.arange(-Uw,Uw+1e-9,dv)
    def gR(w):
        p=mp.mpc(1)
        for mu in mus:
            a=(w+mu)/2; p*=mp.pi**(-a)*mp.gamma(a)
        return p
    gv=np.array([complex(gR(mp.mpc(sigma,v))) for v in vs])
    def K(y):
        y=np.asarray(y,dtype=np.float64); ly=np.log(y)
        base=y**(-sigma)
        val=(np.exp(-1j*np.outer(ly,vs))*gv[None,:]).sum(axis=1)*dv/(2*np.pi)
        return (base*val).real
    # find support
    yy=np.exp(np.linspace(-4,6,4000)); kk=np.abs(K(yy))
    m=kk.max(); good=yy[kk>1e-17*m]
    K.ymin=float(good.min()); K.ymax=float(good.max()); K.peak=float(yy[np.argmax(kk)])
    return K

def make_L(a_n, N, mus, eps, nv=9000):
    K=make_K(mus)
    sqrtN=float(mp.sqrt(N)); d=len(mus)
    nn=np.arange(1,len(a_n)); an=np.asarray(a_n[1:],dtype=np.float64)
    umax=K.ymax*sqrtN/1.0            # n=1 term reaches K.ymax
    Vmax=np.log(umax)
    vs=np.linspace(0.0,Vmax,nv); us=np.exp(vs)
    Theta=np.zeros(nv)
    for j,u in enumerate(us):
        amin=K.ymin*sqrtN/u; amax=K.ymax*sqrtN/u
        nlo=max(1,int(np.floor(amin))); nhi=min(len(an),int(np.ceil(amax)))
        if nhi<nlo: continue
        idx=slice(nlo-1,nhi)
        Theta[j]=np.dot(an[idx], K(nn[idx]*u/sqrtN))
    def Lambda(s):
        s=complex(s)
        integ=Theta*(np.exp(vs*s)+eps*np.exp(vs*(1-s)))   # du/u=dv
        return np.trapezoid(integ, vs)
    Lambda.data=(vs,us,Theta); Lambda.eps=eps; Lambda.N=N; Lambda.mus=mus; Lambda.K=K
    return Lambda

def _real_on_line(Lam,y):
    v=Lam(complex(0.5,y))
    return (v*(-1j)).real if Lam.eps<0 else v.real

def find_zeros(Lam,y0,y1,ng=800):
    ys=np.linspace(y0,y1,ng); re=np.array([_real_on_line(Lam,y) for y in ys]); zs=[]
    for i in range(ng-1):
        if re[i]*re[i+1]<0:
            a,b,fa=ys[i],ys[i+1],re[i]
            for _ in range(80):
                m=0.5*(a+b); fm=_real_on_line(Lam,m)
                if fa*fm<=0: b=m
                else: a,fa=m,fm
            zs.append(0.5*(a+b))
    return zs

if __name__=="__main__":
    import sys; sys.path.insert(0,"/Users/samuellavery/work/helix_frobenius")
    import focal_closure as fc
    mp.mp.dps=22; N=20000
    lam=fc.delta_lambda(N); a=np.zeros(N+1); a[1:]=lam[1:N+1]
    Ld=make_L(a,1,[5.5,6.5],+1)
    zd=find_zeros(Ld,8,15,400)
    print("Delta   K-support[%.3f,%.1f] zeros[8,15]:"%(Ld.K.ymin,Ld.K.ymax),[round(t,6) for t in zd]," ref 9.222379,13.907550")
    lam=fc.e11_lambda(N); a=np.zeros(N+1); a[1:]=lam[1:N+1]
    Le=make_L(a,11,[0.5,1.5],+1)
    ze=find_zeros(Le,5,12,400)
    print("E11     K-support[%.3f,%.1f] zeros[5,12]:"%(Le.K.ymin,Le.K.ymax),[round(t,6) for t in ze]," ref 6.362614,8.603540,10.035509")
