"""ODD-CHANNEL rewrite of divisor-class coherence.

Magnitude form (DC, sign-blind):   sum_{gcd(n,q)=d} a_n n^-s  ->  0
Sign form      (AC, sign-carrying): V_r = -V_{-r}  exactly, i.e. the EVEN part dies
                                    and the channel vector goes PURELY ODD.

Observable:  e_r = |V_r + V_{-r}| / (|V_r| + |V_{-r}|)   in [0,1]
             0  <=> exact sign flip between conjugate cells
             1  <=> perfectly in phase (no sign structure)

PRECHECK -- what does it return if the hypothesis is FALSE?
  If sign-flip structure is NOT tied to the midpoint, DH's ON-line and OFF-line zeros
  return the SAME values.  Different inputs -> possibly different outputs, so the test
  has discriminating power.  (If it returned 0 everywhere it would be a tautology.)
"""
import mpmath as mp, sys
mp.mp.dps = 25
def P(*a): print(*a); sys.stdout.flush()

A=(4/mp.sqrt(5))*mp.sin(2*mp.pi/5); B=(4/mp.sqrt(5))*mp.sin(4*mp.pi/5)
XI=(mp.sqrt(A**2+B**2)-A)/B
aDH=[1,XI,-XI,-1,0]

def V_zeta(s,r,q=6):                     # a_n = 1
    a = mp.mpf(r)/q if r % q else mp.mpf(1)
    return mp.power(q,-s)*mp.zeta(s,a)
def V_dh(s,r,q=5):
    a = mp.mpf(r)/q if r % q else mp.mpf(1)
    return aDH[(r-1)%5]*mp.power(q,-s)*mp.zeta(s,a)
def dh(s): return sum(V_dh(s,r) for r in range(1,6))

def evenness(V,s,pairs):
    out=[]
    for r,rm in pairs:
        v1,v2=V(s,r),V(s,rm)
        out.append(float(abs(v1+v2)/(abs(v1)+abs(v2))))
    return out

P("=== ZETA (Euler product), q=6, pairs (1,5) and (2,4) ===")
for k in (1,2,3,5,10):
    g=mp.im(mp.zetazero(k)); s=mp.mpc(0.5,g)
    e=evenness(V_zeta,s,[(1,5),(2,4)])
    P(f"  zero #{k:2d} t={float(g):8.4f}   e(1,5)={e[0]:.3e}   e(2,4)={e[1]:.3e}")
P("  CONTROL, non-zeros on the line:")
for t in (17.0,27.5,45.0):
    e=evenness(V_zeta,mp.mpc(0.5,t),[(1,5),(2,4)])
    P(f"    t={t:6.2f}              e(1,5)={e[0]:.4f}     e(2,4)={e[1]:.4f}")

P("\n=== DAVENPORT-HEILBRONN (no Euler product), q=5, pairs (1,4) and (2,3) ===")
P("  --- its ON-LINE zeros ---")
on=[]
t=6.0
while t<60 and len(on)<5:
    try:
        z=mp.findroot(lambda x: mp.re(dh(mp.mpc(0.5,x))), t)
        zz=mp.mpc(0.5,z)
        if abs(dh(zz))<1e-14 and all(abs(zz-w)>1e-6 for w in on) and mp.im(zz)>5:
            on.append(zz)
    except Exception: pass
    t+=3.0
for z in on:
    e=evenness(V_dh,z,[(1,4),(2,3)])
    P(f"    t={float(mp.im(z)):8.4f}  |f|={float(abs(dh(z))):.1e}   e(1,4)={e[0]:.4f}   e(2,3)={e[1]:.4f}")
P("  --- its OFF-LINE zero ---")
zoff=mp.findroot(dh, mp.mpc('0.808517','85.699348'))
e=evenness(V_dh,zoff,[(1,4),(2,3)])
P(f"    Re={float(mp.re(zoff)):.6f} t={float(mp.im(zoff)):8.4f}  |f|={float(abs(dh(zoff))):.1e}"
  f"   e(1,4)={e[0]:.4f}   e(2,3)={e[1]:.4f}")
P("  CONTROL, DH at non-zeros on the line:")
for t in (10.0,30.0,50.0):
    e=evenness(V_dh,mp.mpc(0.5,t),[(1,4),(2,3)])
    P(f"    t={t:6.2f}                        e(1,4)={e[0]:.4f}   e(2,3)={e[1]:.4f}")
