"""ATTEMPT 011, stage 3 -- D4 (H_avg out of sample), D5 (the quartic L(s,chi) specimen),
D6b (off-line census of DH by the argument principle).

Stage 2 established, exactly:  Z_DH(t) = |A| ( Z_chi(t) + Z_chibar(t) ),  A = (1 - i XI)/2,
chi the quartic character mod 5 with chi(2) = i.  So DH is a SUM OF TWO EULER PRODUCTS,
not a structureless FE object.

============================ PRE-REGISTERED =================================
D4  H_avg : DH's tape lines carry  Lambda_eff(n) = Lambda(n) Re chi(n).
      => present at FULL strength for prime powers n = +-1 mod 5,
         ABSENT (noise floor) for prime powers n = +-2 mod 5.
    Fitted on n <= 32 at T = 1e5.  Tested here OUT OF SAMPLE at T = 1e6 on n = 33..60,
    i.e. primes 37,41,43,47,49,53,59 -- never inspected.
    NULL: no split; the ratio obs/(full Euler strength) is the same in both classes.

D5  L(s,chi), chi quartic mod 5.  Euler product, COMPLEX coefficients, |chi(n)| = 1 for
    (n,5) = 1, root number eps = tau(chi)/(i sqrt5), Z_chi(t) = e^{i(theta - psi)} L(1/2+it,chi).
    PREDICT: FULL lines K = U Lambda(n)^2/(L^2 n) at EVERY n coprime to 5, both residue
    classes, since |Lambda(n) chi(n)| = Lambda(n).
    NULL: lines only at n = +-1 mod 5 -- then D4's split is not caused by the linear
    combination, and H_avg is wrong.

D6b OFF-LINE CENSUS of DH.  Winding number of f_DH on sub-boxes
      sigma in [1,2]  (zeros right of the 1-line),
      sigma in [0.5+d, 1] (off-line, right half),
      sigma in [-1,2]  (all),
    against the sign-change count of Z_DH, over t in [1000,2000].
    NULL: winding(all) == sign changes, i.e. the tape's 11% deficit is a zero-finder artifact.
=============================================================================
"""
import numpy as np, mpmath as mp, math, os, sys, time
def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
A_DH = (4/np.sqrt(5))*np.sin(2*np.pi/5); B_DH = (4/np.sqrt(5))*np.sin(4*np.pi/5)
XI   = (np.sqrt(A_DH**2+B_DH**2)-A_DH)/B_DH
CHI4 = np.array([0, 1, 1j, -1j, -1]); Acst = (1-1j*XI)/2
tau_chi = sum(CHI4[r]*np.exp(2j*np.pi*r/5) for r in range(1,5))
PSI = np.angle(tau_chi/(1j*np.sqrt(5)))/2

_B = [1/6, -1/30, 1/42, -1/30, 5/66]
def logGamma_asym(z):
    z = np.asarray(z, complex); out = (z-0.5)*np.log(z)-z+0.5*np.log(2*np.pi); zp = z.copy()
    for k in range(1,6): out += _B[k-1]/(2*k*(2*k-1)*zp); zp = zp*z*z
    return out
def theta_f(t,q,a):
    t = np.asarray(t,float)
    return np.imag(logGamma_asym((0.5+a+1j*t)/2)) + (t/2)*math.log(q/np.pi)

def Zmain_c(t, coef, q, a, psi):
    """Z(t) = 2 Re[ e^{i(theta-psi)} sum_{n<=sqrt(qt/2pi)} c_n n^{-1/2-it} ]."""
    t = np.asarray(t,float); Nn = np.floor(np.sqrt(q*t/(2*np.pi))).astype(np.int64)
    th = theta_f(t,q,a)-psi; Nmax = int(Nn.max()); s = np.zeros_like(t)
    for n in range(1, Nmax+1):
        c = coef[n % q]
        if c == 0: continue
        m = Nn >= n; ph = th[m]-t[m]*math.log(n)
        s[m] += (c.real*np.cos(ph) - c.imag*np.sin(ph))/math.sqrt(n)
    return 2*s

def zeros_of(coef,q,a,psi,T,W,h,nbis=45):
    g = np.arange(T,T+W,h); sb = np.empty(len(g),bool)
    for i in range(0,len(g),400000): sb[i:i+400000] = np.signbit(Zmain_c(g[i:i+400000],coef,q,a,psi))
    idx = np.nonzero(sb[:-1]!=sb[1:])[0]; A,Bb = g[idx].copy(), g[idx+1].copy()
    for _ in range(nbis):
        m = (A+Bb)/2
        left = np.signbit(Zmain_c(A,coef,q,a,psi)) != np.signbit(Zmain_c(m,coef,q,a,psi))
        Bb = np.where(left,m,Bb); A = np.where(left,A,m)
    return (A+Bb)/2

# ---------- verify Z_DH = |A| (Z_chi + Z_chibar) ---------------------------
P("VERIFY  Z_DH(t) = |A| ( Z_chi(t) + Z_chibar(t) )   [exact consequence of D1]")
ts = np.array([317.77, 1000.5, 5000.25, 100000.75])
cDH  = np.array([0,1.0,XI,-XI,-1.0], complex)
cX   = CHI4.astype(complex); cXb = np.conj(CHI4).astype(complex)
lhs = Zmain_c(ts,cDH,5,1,0.0)
rhs = abs(Acst)*(Zmain_c(ts,cX,5,1,PSI) + Zmain_c(ts,cXb,5,1,-PSI))
for t,l,r in zip(ts,lhs,rhs): P(f"    t={t:>10}  Z_DH={l:+.10f}  |A|(Zchi+Zchibar)={r:+.10f}  diff={l-r:+.2e}")

# ---------- run the two specimens at T = 1e6 -------------------------------
T, W, h = 1e6, 3000.0, 0.015
NS = list(range(2,61))
def isPP(n):
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59):
        m = n
        while m % p == 0: m //= p
        if m == 1: return p
    return 0
def spec(u,taus): return np.abs(np.exp(2j*np.pi*np.outer(taus,u)).sum(axis=1))**2

RUN = {}
for nm, coef, psi in (('chi5q', cX, PSI), ('DH', cDH, 0.0)):
    fn = TMP+f'att011_z3_{nm}.npy'
    if os.path.exists(fn): g = np.load(fn); gate='cached'
    else:
        t0=time.time(); g = zeros_of(coef,5,1,psi,T,W,h); g2 = zeros_of(coef,5,1,psi,T,W,h/2)
        gate = 'PASS' if len(g)==len(g2) else f'FAIL {len(g)} vs {len(g2)}'
        if len(g2)!=len(g): g=g2
        np.save(fn,g); P(f"\n  [{nm}] {len(g)} zeros, refine-gate {gate}, {time.time()-t0:.0f}s")
    u = theta_f(g,5,1)/np.pi; u -= u[0]; U = u[-1]
    tc = (g[0]+g[-1])/2; L = theta_f(tc+1.0,5,1)-theta_f(tc-1.0,5,1)
    RUN[nm] = dict(g=g,u=u,U=U,L=L,nz=len(g),A=spec(u,[math.log(n)/L for n in NS])/U)
    P(f"  {nm}: zeros={len(g)}  tape U={U:.1f}  L={L:.4f}  census deficit U-nz={U-len(g):+.1f}"
      f"  ({100*(U-len(g))/U:.2f}%)")

P("\nD4/D5  tape lines, T=1e6, W=3000, n = 2..60.  'full' = U Lambda(n)^2/(L^2 n).")
P(f"    {'n':>3}{'p':>3}{'n%5':>5}{'full K':>9} | {'chi5q obs':>10}{'/full':>7} | "
  f"{'DH obs':>9}{'/full':>7}{'H_avg pred':>11}{'obs/Havg':>9}   R")
rows=[]
for i,n in enumerate(NS):
    p = isPP(n)
    if p == 0 or n % 5 == 0: continue
    Lm = math.log(p)
    for nm in ('chi5q','DH'): pass
    r1, r2 = RUN['chi5q'], RUN['DH']
    full1 = r1['U']*Lm**2/(r1['L']**2*n); full2 = r2['U']*Lm**2/(r2['L']**2*n)
    havg  = full2*(CHI4[n%5].real)**2
    R = r2['U']*math.log(n)*math.log(1+W/T)/(r2['L']**2)
    o1, o2 = r1['A'][i], r2['A'][i]
    P(f"    {n:>3}{p:>3}{n%5:>5}{full1:>9.2f} | {o1:>10.3f}{o1/full1:>7.3f} | "
      f"{o2:>9.3f}{o2/full2:>7.3f}{havg:>11.2f}"
      f"{(o2/havg if havg>1e-9 else float('nan')):>9.3f}   {R:.2f}")
    rows.append((n,p,n%5,o1/full1,o2/full2))
rows = np.array(rows)
for lbl, mask in (('n = +-1 mod 5', (rows[:,2]==1)|(rows[:,2]==4)),
                  ('n = +-2 mod 5', (rows[:,2]==2)|(rows[:,2]==3))):
    P(f"\n    {lbl}:  chi5q obs/full  median {np.median(rows[mask,3]):.3f}  "
      f"[{rows[mask,3].min():.3f},{rows[mask,3].max():.3f}]   |   "
      f"DH obs/full  median {np.median(rows[mask,4]):.3f}  "
      f"[{rows[mask,4].min():.3f},{rows[mask,4].max():.3f}]   (n={mask.sum()})")
oos = rows[rows[:,0] > 32]
for lbl, mask in (('n = +-1 mod 5', (oos[:,2]==1)|(oos[:,2]==4)),
                  ('n = +-2 mod 5', (oos[:,2]==2)|(oos[:,2]==3))):
    if mask.sum():
        P(f"    OUT OF SAMPLE (n>32) {lbl}: chi5q median {np.median(oos[mask,3]):.3f}, "
          f"DH median {np.median(oos[mask,4]):.3f}   n = {oos[mask,0].astype(int).tolist()}")

# ---------- D6b : off-line census -------------------------------------------
P("\nD6b  OFF-LINE CENSUS of DH, t in [1000,2000].")
_BER = [1/6,-1/30,1/42,-1/30,5/66,-691/2730,7/6]
def hurwitz(s,a,M=8000,J=7):
    s = np.asarray(s,complex); k = np.arange(M)
    tot = np.exp(-s[:,None]*np.log((k+a)[None,:])).sum(axis=1)
    Ma = M+a; tot += Ma**(1-s)/(s-1)+0.5*Ma**(-s)
    for j in range(1,J+1):
        p = np.ones_like(s)
        for i in range(2*j-1): p = p*(s+i)
        tot += _BER[j-1]/math.factorial(2*j)*p*Ma**(-s-2*j+1)
    return tot
def f_DH(s):
    s = np.atleast_1d(np.asarray(s,complex)); tot = np.zeros_like(s)
    for r,c in ((1,1.0),(2,XI),(3,-XI),(4,-1.0)): tot += c*hurwitz(s,r/5.0)
    return 5.0**(-s)*tot
def wind(f,s0,s1,npts=3000):
    a,b,c,d = s0.real,s1.real,s0.imag,s1.imag
    xs = np.linspace(a,b,npts); ys = np.linspace(c,d,npts)
    path = np.concatenate([xs+1j*c, b+1j*ys[1:], xs[::-1][1:]+1j*d, a+1j*ys[::-1][1:]])
    v = f(path); return np.sum(np.diff(np.unwrap(np.angle(v))))/(2*np.pi), np.abs(v).min()
tot_all=tot_gt1=tot_off=tot_sc=0; dth=0.0
for T0 in range(1000,2000,100):
    T1 = T0+100
    wa,_  = wind(f_DH, -1+1j*T0, 2+1j*T1)
    w1,_  = wind(f_DH, 1.0+1j*T0, 2+1j*T1)
    wo,mo = wind(f_DH, 0.5+1e-4+1j*T0, 2+1j*T1)
    gz = zeros_of(cDH,5,1,0.0,float(T0),100.0,0.004)
    d = (theta_f(float(T1),5,1)-theta_f(float(T0),5,1))/np.pi
    tot_all+=wa; tot_gt1+=w1; tot_off+=wo; tot_sc+=len(gz); dth+=d
    P(f"    t in [{T0},{T1}]  dtheta/pi={d:7.2f}   winding(all)={wa:6.2f}  "
      f"winding(sigma>1/2)={wo:5.2f}  winding(sigma>1)={w1:5.2f}   sign changes={len(gz):4d}")
P(f"    TOTAL t in [1000,2000]:  dtheta/pi={dth:.1f}   all={tot_all:.0f}   "
  f"sigma>1/2: {tot_off:.0f}   sigma>1: {tot_gt1:.0f}   on-line sign changes={tot_sc}")
P(f"    => off-line zeros = 2 x {tot_off:.0f} = {2*tot_off:.0f};  "
  f"all - sign changes = {tot_all-tot_sc:.0f}  ({100*(tot_all-tot_sc)/tot_all:.1f}% of zeros)")
