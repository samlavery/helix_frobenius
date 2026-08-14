"""CORRECTED.  Weil summand: m_rho * h(gamma_rho) * conj( h(conj gamma_rho) ).
On-line: gamma_rho real -> outer(v, conj v) = PSD rank 1.
Off-line: gamma_rho = gamma - i(beta-1/2) complex; conj(gamma_rho) is the FE PARTNER's
gamma.  The pair contributes outer(v_+, conj v_-) + outer(v_-, conj v_+)  -> SIGNATURE (1,1).
"""
import numpy as np, mpmath as mp
mp.mp.dps = 20
def ph(r,L,w):
    r=np.asarray(r,dtype=complex); r=np.where(np.abs(r)<1e-12,1e-12,r)
    return (2.0/r)*np.sin(r*(L-w)/2.0)*np.sin(r*w/2.0)/(r*w/2.0)
T=200.0; l=np.log(T/(2*np.pi)); L=l; w=0.05*l/2
h=2*np.pi/L; d=int(T/h); tau=T+np.arange(d)*h
g=np.array([float(mp.im(mp.zetazero(k))) for k in range(1,400)])
g=g[(g>T-150)&(g<2*T+150)]

def G_of(gams, betas):
    G=np.zeros((d,d),dtype=complex)
    for gam,b in zip(gams,betas):
        if abs(b-0.5)<1e-14:
            v=ph(gam-tau,L,w); G+=np.outer(v,np.conj(v))
        else:
            gp=gam-1j*(b-0.5); gm=np.conj(gp)          # rho and its FE partner
            vp=ph(gp-tau,L,w); vm=ph(gm-tau,L,w)
            G+=np.outer(vp,np.conj(vm))+np.outer(vm,np.conj(vp))
    return (G+G.conj().T)/2

def rep(tag,G):
    ev=np.linalg.eigvalsh(G); neg=ev[ev<-1e-9]
    print(f"  {tag:32s} n_neg={len(neg):3d}  min_ev={ev.min():+.4e}  "
          f"neg_mass={abs(neg.sum()) if len(neg) else 0.0:.4e}")
betas=np.full(len(g),0.5)
rep("ALL ON-LINE", G_of(g,betas))
for delta in (0.01,0.02,0.05,0.10,0.25,0.49):
    b=betas.copy(); b[len(b)//2]=0.5+delta
    rep(f"one off-line, delta={delta:.2f}", G_of(g,b))
print("\n  two off-line zeros:")
b=betas.copy(); b[len(b)//2]=0.6; b[len(b)//2+7]=0.7
rep("two off-line (0.6, 0.7)", G_of(g,b))
