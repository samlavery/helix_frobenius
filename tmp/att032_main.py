"""ATTEMPT 032 -- MAIN.  G3 (moment separation zeta vs DH) and G4 (the depth law).
Pre-registration is in att032_moment_blindness.py; nulls repeated inline.
"""
import numpy as np, math, sys
def P(*a): print(*a); sys.stdout.flush()
TMP='/Users/samuellavery/work/helix_frobenius/tmp/'
LamZ=np.load(TMP+'att032_lam_vm.npy'); LamD=np.load(TMP+'att032_lam_DH.npy')
NMAX=min(len(LamZ),len(LamD))-1
n=np.arange(1,NMAX+1); logn=np.log(n)

def S2(Lam,X,L):
    m=n<=X
    return float(np.sum(Lam[1:NMAX+1][m]**2*np.maximum(L-logn[m],0.0)/n[m]))
def S1abs(Lam,X):
    m=n<=X
    return float(np.sum(np.abs(Lam[1:NMAX+1][m])/np.sqrt(n[m])))

P("="*100)
P("G2  summatory function of Lambda_DH  (abscissa sigma_c = limsup log|Psi_f(x)|/log x)")
P("    NULL: sigma_c <= 1, i.e. no growth beyond the zeta-like  Psi(x) ~ x.")
PsD=np.cumsum(LamD[1:NMAX+1]); PsZ=np.cumsum(LamZ[1:NMAX+1])
P(f"    {'x':>10} {'Psi_DH(x)':>14} {'log|Psi_DH|/log x':>18} {'Psi_zeta(x)':>14} {'log Psi_z/log x':>16}")
for x in (10**3,10**4,10**5,10**6,NMAX):
    P(f"    {x:>10} {PsD[x-1]:14.4f} {math.log(abs(PsD[x-1]))/math.log(x):18.4f} "
      f"{PsZ[x-1]:14.1f} {math.log(PsZ[x-1])/math.log(x):16.4f}")

P("\n"+"="*100)
P("G3  THE TWO MOMENTS, zeta vs Davenport-Heilbronn, at MATCHED (T, lambda, X)")
P("    mu_1 = tr G^/N = 1 + O(err_1),  err_1 bound (Prop 5.3 P-part) = sum_{n<=X}|Lam(n)|/sqrt n /(N log 2)")
P("    mu_2 = ||G^||_F^2/N = l_c/L + 2 S_2/(L^2 l_c),  S_2 = sum_{n<=X} Lam(n)^2 (L-log n)/n")
P("    DECISION RULE (pre-registered): |mu_2^DH - mu_2^zeta|/mu_2^zeta <= E_T  =>  BLIND;")
P("                                    > E_T  =>  NOT BLIND, stated null holds.")
P("    E_T = w/L + (l^2+X) log l/(T l) + T^{lambda/2-1},  w=1  (Thm 5.8)")
P("")
hdr=(f"    {'T':>9} {'lam':>4} {'X':>10} {'l_c':>7} {'L':>7} | {'mu2 zeta':>9} {'mu2 DH':>12} "
     f"{'ratio':>10} | {'E_T':>7} {'sep/E_T':>10} | {'mu1-1 z':>9} {'mu1-1 DH':>9}")
P(hdr); P("    "+"-"*(len(hdr)-4))
rows=[]
for T in (1e4,1e5,1e6,1e7):
    for lam in (1.0,0.7,0.5):
        l_z=math.log(T/(2*math.pi)); l_d=math.log(5*T/(2*math.pi))
        L=lam*l_z; X=math.exp(L)
        if X>NMAX: continue
        m2z=l_z/L+2*S2(LamZ,X,L)/(L*L*l_z)
        m2d=l_d/L+2*S2(LamD,X,L)/(L*L*l_d)
        Nz=T*l_z/(2*math.pi); Nd_=T*l_d/(2*math.pi)
        e1z=S1abs(LamZ,X)/(Nz*math.log(2)); e1d=S1abs(LamD,X)/(Nd_*math.log(2))
        ET=1/L+(l_z**2+X)*math.log(l_z)/(T*l_z)+T**(lam/2-1)
        sep=abs(m2d-m2z)/m2z
        rows.append((T,lam,X,m2z,m2d,ET,sep))
        P(f"    {T:9.0e} {lam:4.1f} {X:10.4g} {l_z:7.3f} {L:7.3f} | {m2z:9.4f} {m2d:12.4f} "
          f"{m2d/m2z:10.2f} | {ET:7.4f} {sep/ET:10.1f} | {e1z:9.2e} {e1d:9.2e}")
P("")
worst=min(r[6]/r[5] for r in rows)
P(f"    smallest separation over all (T,lambda) = {worst:.1f} x E_T   "
  f"=>  {'BLIND' if worst<=1 else 'NOT BLIND: STATED NULL HOLDS'}")

P("\n"+"="*100)
P("G4  THE DEPTH LAW  Delta(y) = 2[sinh^2(Ly)/(Ly)^2 - 1]   (derived before running)")
P("    and the blinding depth  y*(T) = (1/L) sqrt( 3 E_T / (2 p/N) ).")
def Delta(y,L):
    u=L*y
    return 2*((np.sinh(u)/u)**2-1) if np.ndim(u)==0 else 2*((np.sinh(u)/np.where(u==0,1,u))**2-1)
P(f"\n    {'T':>9} {'L':>7} {'E_T':>8} {'p/N':>6} {'y*':>10} {'y* * L':>8} {'y*/(mean gap)':>14} "
  f"{'X^{2y*}':>10}")
for T in (1e5,1e7,1e12,1e30,1e100):
    l=math.log(T/(2*math.pi)); L=l; X=math.exp(L)
    ET=1/L+(l*l+X)*math.log(l)/(T*l)+T**(-0.5)
    for pN in (1/6,):
        ys=(1/L)*math.sqrt(3*ET/(2*pN))
        gap=2*math.pi/l
        P(f"    {T:9.0e} {L:7.3f} {ET:8.4f} {pN:6.3f} {ys:10.5f} {ys*L:8.4f} {ys/gap:14.5f} "
          f"{X**(2*ys):10.3g}")
P("    asymptotics: E_T ~ log l/(2 pi l)  =>  y* ~ (3/l) sqrt(log l/(2 pi l)) "
  "= (log log T)^{1/2}(log T)^{-3/2} up to constants")

P("\n"+"="*100)
P("G4b INJECTION POSITIVE CONTROL (rule 3: must fail by MISSING STRUCTURE).")
P("    Take zeta's cached zeros at T=1e6.  Replace a fraction 2p/N of them by p off-line")
P("    pairs {rho,1-rhobar} at depth y (SAME ordinates, so the count N is unchanged and the")
P("    archimedean part is unchanged).  Recompute the zero-side mu_2 with the COMPLEX")
P("    differences of Remark 5.10.  PREDICTED shift = (p/N) Delta(y), to 2 percent.")
P("    Failure shape demanded: at small y the injection is INVISIBLE (shift -> 0).")
z=np.sort(np.load(TMP+'att010_zeros_1e+06.npy'))
marg=60.0; g_in=z[(z>z[0]+marg)&(z<z[-1]-marg)]
Tc=0.5*(g_in[0]+g_in[-1]); l_c=math.log(Tc/(2*math.pi)); L=l_c
Nn=len(g_in); Na=len(z)
P(f"    T_c={Tc:.6g}  L={L:.4f}  N_inner={Nn}  N_all={Na}")

def mu2_complex(rows_g, rows_b, all_g, all_b, L, chunk=250):
    """rows/all are ordinates gamma and depths y (beta-1/2).  Remark 5.10: the kernel argument
       is gamma_rho - gamma_rho' = -i(rho-rho') = (gamma-gamma') - i(y-y').
       Off-line zeros come as CONJUGATE-REFLECTED PAIRS: a pair at (g,y) supplies the two
       points y and -y at the same ordinate g."""
    tot=0.0
    for i in range(0,len(rows_g),chunk):
        dg=rows_g[i:i+chunk][:,None]-all_g[None,:]
        dy=rows_b[i:i+chunk][:,None]-all_b[None,:]
        x=dg-1j*dy
        s=np.sin(L*x/2.0)
        v=np.where(np.abs(x)<1e-13, L*L+0j, (s/(x/2.0))**2)
        tot+=np.real(v).sum()
    return tot/(L*L*len(rows_g))

base=mu2_complex(g_in,np.zeros(Nn),z,np.zeros(Na),L)
ETc=1/L+(l_c**2+math.exp(L))*math.log(l_c)/(Tc*l_c)+Tc**(-0.5)
P(f"    baseline mu_2 (all on line) = {base:.6f}   (prime side gave 1.3184)   E_T={ETc:.4f}")
P(f"\n    {'y':>9} {'L*y':>7} {'p/N':>6} {'measured shift':>15} {'predicted (p/N)Delta':>21} "
  f"{'ratio':>8} {'shift/E_T':>10} {'verdict':>9}")
rng=np.random.default_rng(32)
for pN in (1/6,):
    npair=int(round(pN*Na))
    idx=rng.choice(Na,size=2*npair,replace=False)
    keep=np.setdiff1d(np.arange(Na),idx)
    pair_g=z[idx[:npair]]                       # ordinates that become off-line pairs
    for y in (0.0005,0.001,0.002,0.005,0.01,0.02,0.05,0.1,0.2,0.3085):
        ag=np.concatenate([z[keep],pair_g,pair_g]); ab=np.concatenate([np.zeros(len(keep)),
                                                     np.full(npair,y),np.full(npair,-y)])
        # inner rows: same construction restricted to the inner window
        mi=(ag>z[0]+marg)&(ag<z[-1]-marg)
        m=mu2_complex(ag[mi],ab[mi],ag,ab,L)
        shift=m-base
        u=L*y; pred=pN*2*((math.sinh(u)/u)**2-1)
        vis='SEEN' if abs(shift)>ETc else 'BLIND'
        P(f"    {y:9.4f} {u:7.3f} {pN:6.3f} {shift:15.6f} {pred:21.6f} "
          f"{(shift/pred if pred!=0 else float('nan')):8.4f} {abs(shift)/ETc:10.4f} {vis:>9}")
