"""LABELED DATA: Davenport-Heilbronn has zeros BOTH on and off the critical line.
That makes it the only specimen where a proposed criterion can be tested against
ground truth for the SAME function.  Any candidate must separate these two classes.
Build and certify the dataset."""
import mpmath as mp, sys
mp.mp.dps = 25
A=(4/mp.sqrt(5))*mp.sin(2*mp.pi/5); B=(4/mp.sqrt(5))*mp.sin(4*mp.pi/5)
XI=(mp.sqrt(A**2+B**2)-A)/B
a=[1,XI,-XI,-1,0]
def f(s): return mp.power(5,-s)*sum(a[r-1]*mp.zeta(s,mp.mpf(r)/5) for r in range(1,6))

# certify xi: sine-transform eigenvector => genuine functional equation
print(f"xi = {mp.nstr(XI,15)}   eigencheck |B xi^2+2A xi-B| = {float(abs(B*XI**2+2*A*XI-B)):.1e}")

on, off = [], []
# on-line: scan sign changes of the real-valued-on-line function
prev=None
t=5.0
while t < 105.0:
    s=mp.mpc(0.5,t); v=f(s)
    cur = mp.sign(mp.re(v/abs(v))) if abs(v)>0 else 0
    if prev is not None and mp.re(f(mp.mpc(0.5,t-0.5)))*mp.re(v) < 0:
        try:
            z=mp.findroot(lambda x: mp.re(f(mp.mpc(0.5,x))), t-0.25)
            zz=mp.mpc(0.5,z)
            if abs(f(zz))<1e-12 and all(abs(zz-w)>1e-6 for w in on): on.append(zz)
        except Exception: pass
    prev=cur; t+=0.5
# off-line: 2D search seeded near the literature values and a coarse grid
seeds=[mp.mpc('0.808517','85.699348'), mp.mpc('0.65','22.0'), mp.mpc('0.7','35.0'),
       mp.mpc('0.85','48.0'), mp.mpc('0.72','62.0'), mp.mpc('0.79','74.0'),
       mp.mpc('0.66','95.0'), mp.mpc('0.75','101.0')]
for sd in seeds:
    try:
        z=mp.findroot(f, sd)
        if abs(f(z))<1e-12 and abs(mp.re(z)-0.5)>0.02 and mp.im(z)>0 \
           and all(abs(z-w)>1e-6 for w in off): off.append(z)
    except Exception: pass
print(f"\nON-LINE zeros found: {len(on)}")
for z in on[:12]: print(f"   {mp.nstr(z,14)}   |f|={float(abs(f(z))):.1e}")
print(f"\nOFF-LINE zeros found: {len(off)}")
for z in off: print(f"   {mp.nstr(z,14)}   Re={float(mp.re(z)):.6f}  |f|={float(abs(f(z))):.1e}")
import pickle; pickle.dump({'xi':str(XI),'on':[str(z) for z in on],'off':[str(z) for z in off]},
                            open('dh_zeros.pkl','wb'))
