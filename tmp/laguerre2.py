"""Second Laguerre inequality for Xi(t) = xi(1/2+it), real on the line.
   L1 = (f')^2 - f f''            >= 0
   L2 = 3(f'')^2 - 4 f' f''' + f f''''  >= 0      (x12 of the standard normalisation)
Both are necessary for Xi in Laguerre-Polya, hence for RH.
GATE: verify the derivative stencil on a known LP function first."""
import mpmath as mp, sys
mp.mp.dps=40
def P(*a): print(*a); sys.stdout.flush()
def derivs(f,t,h):
    v=[f(t+k*h) for k in (-3,-2,-1,0,1,2,3)]
    d1=(-v[0]+9*v[1]-45*v[2]+45*v[4]-9*v[5]+v[6])/(60*h)
    d2=(2*v[0]-27*v[1]+270*v[2]-490*v[3]+270*v[4]-27*v[5]+2*v[6])/(180*h**2)
    d3=(v[0]-8*v[1]+13*v[2]-13*v[4]+8*v[5]-v[6])/(8*h**3)
    d4=(-v[0]+12*v[1]-39*v[2]+56*v[3]-39*v[4]+12*v[5]-v[6])/(6*h**4)
    return v[3],d1,d2,d3,d4
def L12(f,t,h):
    f0,f1,f2,f3,f4=derivs(f,t,h)
    return f1*f1-f0*f2, 3*f2*f2-4*f1*f3+f0*f4
h=mp.mpf('1e-4')
P("GATE on a known LP function  g(t)=cos(t)  (all zeros real): L1,L2 must be >= 0")
g=lambda t: mp.cos(t)
for t in ('0.3','1.1','2.0','3.5'):
    a,b=L12(g,mp.mpf(t),h); P(f"   t={t:>5}  L1={float(a):+.6f}  L2={float(b):+.6f}")
P("  CONTROL  u(t)=t^2+1 (zeros at +-i, NOT LP): L1 or L2 should go negative")
u=lambda t: t*t+1
for t in ('0.0','0.3','1.0'):
    a,b=L12(u,mp.mpf(t),h); P(f"   t={t:>5}  L1={float(a):+.6f}  L2={float(b):+.6f}")
P()
def Xi(t): 
    s=mp.mpc(mp.mpf(1)/2,t)
    return mp.re(mp.mpf('0.5')*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s))
P("XI on the critical line:")
P(f"  {'t':>8}{'L1':>18}{'L2':>18}{'signs':>10}")
neg1=neg2=0; n=0
t=mp.mpf('5')
while t<mp.mpf('120'):
    a,b=L12(Xi,t,h); n+=1
    neg1+= a<0; neg2+= b<0
    if float(t)%15<0.6:
        P(f"  {float(t):>8.2f}{float(a):>18.6e}{float(b):>18.6e}{('+' if a>0 else '-')+('+' if b>0 else '-'):>10}")
    t+=mp.mpf('0.5')
P(f"\n  sampled {n} points on t in [5,120]")
P(f"  L1 < 0 at {neg1} points   L2 < 0 at {neg2} points")
P(f"  -> {'BOTH Laguerre inequalities hold' if neg1==0 and neg2==0 else 'VIOLATION FOUND'}")
