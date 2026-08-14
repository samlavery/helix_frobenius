"""SPEISER SWEEP: RH <=> zeta' has no zeros in 0 < Re s < 1/2.
Winding of zeta' around boxes strictly left of the critical line, over a long range.
Any nonzero winding is a Speiser violation = a disproof of RH."""
import mpmath as mp, sys, time
mp.mp.dps = 20
def P(*a): print(*a); sys.stdout.flush()
zp = lambda s: mp.diff(mp.zeta, s)
def winding(F, s0, s1, n=400):
    pts=[]
    for k in range(n): pts.append(mp.mpc(mp.re(s0)+(mp.re(s1)-mp.re(s0))*k/n, mp.im(s0)))
    for k in range(n): pts.append(mp.mpc(mp.re(s1), mp.im(s0)+(mp.im(s1)-mp.im(s0))*k/n))
    for k in range(n): pts.append(mp.mpc(mp.re(s1)-(mp.re(s1)-mp.re(s0))*k/n, mp.im(s1)))
    for k in range(n): pts.append(mp.mpc(mp.re(s0), mp.im(s1)-(mp.im(s1)-mp.im(s0))*k/n))
    tot=mp.mpf(0); prev=None
    for p in pts+[pts[0]]:
        a=mp.arg(F(p))
        if prev is not None:
            d=a-prev
            while d>mp.pi: d-=2*mp.pi
            while d<-mp.pi: d+=2*mp.pi
            tot+=d
        prev=a
    return float(tot/(2*mp.pi))
P("SPEISER SWEEP: zeta' zeros in 0.02 < Re s < 0.49")
P(f"  {'t block':>18}{'winding':>11}{'zeros':>8}{'[s]':>7}")
tot=0; blocks=0
t=10.0
while t < 2000.0:
    t0=time.time()
    w=winding(zp, mp.mpc('0.02',t), mp.mpc('0.49',t+40.0))
    n=int(round(w)); tot+=n; blocks+=1
    flag='  <-- VIOLATION' if n!=0 else ''
    P(f"  {f'{t:.0f}..{t+40:.0f}':>18}{w:>11.4f}{n:>8}{time.time()-t0:>7.0f}{flag}")
    t += 40.0
P(f"\n  blocks: {blocks}   total zeta' zeros left of the line: {tot}")
P(f"  {'SPEISER HOLDS in range -> RH consistent' if tot==0 else 'VIOLATION FOUND'}")
