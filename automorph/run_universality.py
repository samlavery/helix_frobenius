import numpy as np, mpmath as mp, sys, math, time
sys.path.insert(0,".")
sys.path.insert(0,"/Users/samuellavery/work/helix_frobenius")
import focal_closure as fc
import families as F
import afe
mp.mp.dps=20
PI3=fc.PI3

def L_from_Lambda(Lam, s):
    """Extract L(s)=Lambda(s)/(N^{s/2} prod Gamma_R(s+mu))."""
    s=mp.mpc(s)
    g=mp.mpc(1)
    for mu in Lam.mus:
        a=(s+mu)/2; g*=mp.pi**(-a)*mp.gamma(a)
    comp=mp.mpf(Lam.N)**(s/2)*g
    return complex(Lam(complex(s))/comp)

def dirichlet_direct(lam, s, M):
    """convergent-ish direct partial sum sum_{n<=M} lam_n n^{-s} (no window)."""
    n=np.arange(1,M+1); return complex(np.dot(lam[1:M+1], n**(-complex(s))))

def windowed_D(lam, y, Z):
    N=int(Z); n=np.arange(1,N+1,dtype=np.float64)
    w=fc.growth_window(n/Z)
    return complex(np.dot(lam[1:N+1]*w, n**(-(0.5+1j*y))))

def run_family(name, lam, cfg, y_lo, y_hi, deep_targets, test_y=3.0):
    print("="*88); print("FAMILY:", name, " conductor",cfg["cond"]," degree",len(cfg["mus"])," eps",cfg["eps"]," rank",cfg.get("rank"))
    Nbuilt=len(lam)-1
    # AFE oracle
    a=np.zeros(Nbuilt+1); a[1:]=lam[1:]  # lam already analytic; AFE wants a_n=lam_n
    Lam=afe.make_L(a, cfg["cond"], cfg["mus"], cfg["eps"])
    true_zeros=afe.find_zeros(Lam, y_lo, y_hi, ng=int((y_hi-y_lo)*80))
    print("  AFE true zeros in [%.1f,%.1f]:"%(y_lo,y_hi), [round(z,6) for z in true_zeros])

    # ---- C1 readout ----
    Ztest=math.exp(test_y)
    Fl,_,_=fc.lane_state(fc.Family(name,"cusp",lambda M:(lam[:M+1].astype(complex),np.sign(lam[:M+1]).astype(int))), test_y)
    D=windowed_D(lam, test_y, Ztest)
    gauge=(PI3)**(-0.5)*np.exp(-1j*test_y*np.log(PI3))
    c1_identity=abs(Fl-gauge*D)/max(abs(Fl),1e-30)
    # convergence to classical L(s)
    Ltrue=L_from_Lambda(Lam, complex(0.5,test_y))
    convs=[]
    for yy in [test_y]:
        for zpow in [4,6,8,10]:
            Z=math.exp(zpow); Dz=windowed_D(lam,yy,Z)/gauge*(PI3)**(-0.0)  # unnormalize gauge? compare D to L
            # windowed_D already = sum lam n^{-s} w  -> compare directly to L(s)
    # direct: compare windowed_D (no gauge) to Ltrue
    conv={}
    for zpow in [4,6,8, math.log(Nbuilt)]:
        Z=min(math.exp(zpow), Nbuilt)
        Dz=windowed_D(lam, test_y, Z)
        conv[round(math.log(Z),2)]=abs(Dz-Ltrue)/abs(Ltrue)
    print("  C1 identity |F-gauge*D|/|F| = %.2e"%c1_identity)
    print("  C1 readout  |D_Z - L(1/2+%.1fi)|/|L| vs logZ:"%test_y, {k:'%.2e'%v for k,v in conv.items()}, " L=%.4f%+.4fj"%(Ltrue.real,Ltrue.imag))

    # ---- C2 functional equation ----
    # confirm eps via direct Dirichlet series at Re(s)=1.7
    s2=complex(1.7,0.7)
    Ldir=dirichlet_direct(lam, s2, min(Nbuilt,200000))
    Lgood=L_from_Lambda(Lam,s2)
    # flipped eps
    Lam_flip=afe.make_L(a,cfg["cond"],cfg["mus"],-cfg["eps"])
    Lflip=L_from_Lambda(Lam_flip,s2)
    e_good=abs(Lgood-Ldir)/abs(Ldir); e_flip=abs(Lflip-Ldir)/abs(Ldir)
    Lcentral=L_from_Lambda(Lam, complex(0.5,1e-9))
    print("  C2 FE eps=%+d: |L_afe - L_dirichlet|/|L| = %.2e   (flipped eps: %.2e)"%(cfg["eps"],e_good,e_flip))
    print("  C2 central L(1/2) = %.3e%+.3ej  |L(1/2)|=%.2e"%(Lcentral.real,Lcentral.imag,abs(Lcentral)))

    # ---- C3 / C4 locator ----
    fam=fc.Family(name,"cusp",lambda M:(lam[:M+1].astype(complex),np.sign(lam[:M+1]).astype(int)))
    results=[]
    for (tlo,thi) in deep_targets:
        if math.exp(thi)>Nbuilt:
            print("  [skip window %.2f-%.2f : needs N=%d > built %d]"%(tlo,thi,int(math.exp(thi)),Nbuilt)); continue
        evs=fc.scan(fam, tlo, thi, per_unit=300)
        for e in evs:
            nz=min(true_zeros, key=lambda z:abs(z-e.y)) if true_zeros else float('nan')
            results.append((e.y, e.height, e.depth, nz, abs(e.y-nz)))
    print("  C3/C4 located events (y | Z | depth=residual | nearest true zero | |Dy|):")
    for y,Z,dep,nz,dz in results:
        print("      y=%.6f Z=%.0f depth=%.2e  true=%.6f |Dy|=%.2e"%(y,Z,dep,nz,dz))
    if results:
        print("  --> C3 min residual = %.2e ; C4 max |Re-1/2|=0 by construction, max |Dy to true zero| = %.2e"%(
            min(r[2] for r in results), max(r[4] for r in results)))
    return dict(name=name, true_zeros=true_zeros, c1_id=c1_identity, c1_conv=min(conv.values()),
                c2_egood=e_good, c2_eflip=e_flip, central=abs(Lcentral),
                results=results, cfg=cfg)

if __name__=="__main__":
    which=sys.argv[1] if len(sys.argv)>1 else "all"
    OUT={}
    if which in ("ec37a","all"):
        t=time.time(); lam,_=F.ec_lambda(27000,(0,0,1,-1,0),37); print("[build %.1fs]"%(time.time()-t))
        OUT["ec37a"]=run_family("ec37a",lam,F.EC["ec37a"],3.0,10.3,[(4.7,5.3),(7.7,8.3),(9.6,10.2)],test_y=3.3)
    if which in ("ec389a","all"):
        t=time.time(); lam,_=F.ec_lambda(27000,(0,1,1,-2,0),389); print("[build %.1fs]"%(time.time()-t))
        OUT["ec389a"]=run_family("ec389a",lam,F.EC["ec389a"],2.0,10.3,[(2.6,3.2),(5.5,6.1),(9.6,10.2)],test_y=1.5)
    if which in ("cm32a","all"):
        t=time.time(); lam,_=F.ec_lambda(27000,(0,0,0,-1,0),32); print("[build %.1fs]"%(time.time()-t))
        OUT["cm32a"]=run_family("cm32a",lam,F.EC["cm32a"],3.0,10.3,[(4.5,6.5),(7.5,8.5),(9.5,10.2)],test_y=3.5)
    if which in ("s3","all"):
        t=time.time(); lam,_=F.s3_lambda(60000); print("[build %.1fs]"%(time.time()-t))
        OUT["s3"]=run_family("s3",lam,F.S3,3.0,11.0,[(3.5,5.5),(7.5,8.5),(9.5,10.9)],test_y=3.5)
    if which in ("rs","all"):
        t=time.time(); lam,_=F.rs_lambda(36000); print("[build %.1fs]"%(time.time()-t))
        OUT["rs"]=run_family("rs",lam,F.RS,3.0,10.4,[(4.0,6.0),(6.5,8.0),(8.5,10.3)],test_y=3.5)
    import pickle; pickle.dump(OUT, open("univ_results_%s.pkl"%which,"wb"))
