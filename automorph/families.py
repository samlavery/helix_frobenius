"""Coefficient builders (oracle-free) for the family-universality test.
All analytic-normalized lambda_n; lanes = sign(lambda_n).  Plus AFE params (N,mus,eps).
"""
import numpy as np, sys
sys.path.insert(0,"/Users/samuellavery/work/helix_frobenius")
import focal_closure as fc

# ---------- primes / sieve ----------
def primes_upto(N):
    s=np.ones(N+1,bool); s[:2]=False
    for p in range(2,int(N**0.5)+1):
        if s[p]: s[p*p::p]=False
    return np.flatnonzero(s)

def spf_sieve(N):
    spf=np.zeros(N+1,dtype=np.int64)
    for i in range(2,N+1):
        if spf[i]==0:
            spf[i::i]=np.where(spf[i::i]==0,i,spf[i::i])
    return spf

# ---------- elliptic curve a_p by point counting ----------
def ap_ec(p, ainv):
    a1,a2,a3,a4,a6=ainv
    x=np.arange(p,dtype=np.int64)
    disc=((a1*x+a3)**2+4*(x**3+a2*x**2+a4*x+a6))%p
    sq=np.zeros(p,dtype=np.int8); sq[(np.arange(p,dtype=np.int64)**2)%p]=1
    leg=np.where(disc==0,0,np.where(sq[disc]==1,1,-1))
    return int(-leg.sum())

def build_multiplicative(N, ap_of, conductor):
    """a_n (integer) from a_p via Hecke; bad p|conductor use a_{p^k}=a_p^k."""
    spf=spf_sieve(N)
    a=np.zeros(N+1,dtype=np.float64); a[1]=1.0
    ap_cache={}
    def a_pe(p,e):
        ap=ap_cache.get(p)
        if ap is None: ap=ap_cache[p]=ap_of(p)
        if conductor%p==0:
            return float(ap)**e
        # recurrence
        vals=[1.0, float(ap)]
        for k in range(2,e+1):
            vals.append(ap*vals[-1]-p*vals[-2])
        return vals[e]
    for n in range(2,N+1):
        p=int(spf[n]); m=n; e=0
        while m%p==0: m//=p; e+=1
        a[n]=a_pe(p,e)*a[m]
    return a

def ec_lambda(N, ainv, conductor):
    a=build_multiplicative(N, lambda p: ap_ec(p,ainv), conductor)
    n=np.arange(N+1,dtype=np.float64); lam=np.zeros(N+1); lam[1:]=a[1:]/np.sqrt(n[1:])
    return lam, a

# ---------- S3 dihedral weight-1 level-23 via eta product ----------
def s3_lambda(N):
    def eta(M):
        c=np.zeros(M); k=0
        while True:
            done=True
            for kk in ((k,-k) if k else (0,)):
                m=kk*(3*kk-1)//2
                if m<M: c[m]+=(-1)**kk; done=False
            if k and done: break
            k+=1
        return c
    A=eta(N+1); B=np.zeros(N+1); small=eta((N)//23+2)
    idx=np.arange(len(small))*23; keep=idx<N+1; B[idx[keep]]=small[keep]
    L=1
    while L<2*(N+1): L*=2
    prod=np.round(np.fft.irfft(np.fft.rfft(A,L)*np.fft.rfft(B,L),L)[:N+1])
    lam=np.zeros(N+1); lam[1:]=prod[:N]      # a_n=prod[n-1]; weight 1 => lambda_n=a_n
    return lam, lam.copy()

# ---------- Rankin-Selberg Delta x E11 (degree 4) ----------
def rs_lambda(N):
    lamf=fc.delta_lambda(N)       # analytic lambda_Delta
    lamg=fc.e11_lambda(N)         # analytic lambda_E11
    spf=spf_sieve(N)
    # precompute c_{p^k} per prime up to N
    c=np.zeros(N+1,dtype=np.float64); c[1]=1.0
    cpe_cache={}
    def cpe(p):
        if p in cpe_cache: return cpe_cache[p]
        kmax=1
        pk=p
        while pk*p<=N: pk*=p; kmax+=1
        # roots of f: alpha,1/alpha with alpha+1/alpha=lamf(p); same for g
        lf=lamf[p]; lg=lamg[p]
        if p==11:   # Steinberg for g: degree-2 local factor c_{11^k}=lamf(11^k)*lamg(11)^k
            seq=[1.0]
            for k in range(1,kmax+1):
                seq.append(lamf[p**k]*(lg**k))
            cpe_cache[p]=seq; return seq
        # four roots gamma = exp(i(±tf±tg)); e1=e3=lf*lg, e4=1, e2 from numerics
        import cmath
        af=cmath.exp(1j*cmath.acos(complex(lf/2))); bg=cmath.exp(1j*cmath.acos(complex(lg/2)))
        roots=[af*bg, af/bg, bg/af, 1/(af*bg)]
        e1=sum(roots).real
        e2=sum(roots[i]*roots[j] for i in range(4) for j in range(i+1,4)).real
        e3=sum(roots[i]*roots[j]*roots[k] for i in range(4) for j in range(i+1,4) for k in range(j+1,4)).real
        e4=(roots[0]*roots[1]*roots[2]*roots[3]).real
        seq=[1.0, e1]
        for k in range(2,kmax+1):
            v=e1*seq[k-1]-e2*seq[k-2]+ (e3*seq[k-3] if k>=3 else 0.0) - (e4*seq[k-4] if k>=4 else 0.0)
            seq.append(v)
        cpe_cache[p]=seq; return seq
    for n in range(2,N+1):
        p=int(spf[n]); m=n; e=0
        while m%p==0: m//=p; e+=1
        c[n]=cpe(p)[e]*c[m]
    return c, c.copy()

# ---------- registry ----------
# ainv, conductor, AFE mus, eps, rank
EC = {
 "ec37a":  dict(ainv=(0,0,1,-1,0), cond=37,  mus=[0.5,1.5], eps=-1, rank=1),
 "ec389a": dict(ainv=(0,1,1,-2,0), cond=389, mus=[0.5,1.5], eps=+1, rank=2),
 "cm32a":  dict(ainv=(0,0,0,-1,0), cond=32,  mus=[0.5,1.5], eps=+1, rank=0),  # CM by Q(i)
}
S3   = dict(cond=23, mus=[0.0,1.0], eps=+1, rank=0)
RS   = dict(cond=121, mus=[5.0,6.0,6.0,7.0], eps=+1, rank=0)

def make_family(name, lam):
    def make(Nreq):
        M=len(lam)-1
        if Nreq>M: raise ValueError(f"{name}: need N={Nreq} but built to {M}")
        c=lam[:Nreq+1].astype(np.complex128); keys=np.sign(lam[:Nreq+1]).astype(np.int64)
        return c, keys
    return fc.Family(name,"cusp",make)

if __name__=="__main__":
    for name,cfg in EC.items():
        lam,a=ec_lambda(60,cfg["ainv"],cfg["cond"]); print(name,"a[1..12]=",[int(a[n]) for n in range(1,13)])
    lam,a=s3_lambda(60); print("s3    a[1..12]=",[int(a[n]) for n in range(1,13)])
    c,_=rs_lambda(60); print("rs    c[1..8] =",[round(float(c[n]),4) for n in range(1,9)])
    print("rs    |c_p|<=4 check:", all(abs(c[p])<=4.0001 for p in [2,3,5,7,13,17,19,23]))
