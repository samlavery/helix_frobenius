#!/usr/bin/env python3
"""
C3 batch 17 -- numerical block 1.  REJECTION GATES, run before any proof decomposition.

Target: C3B14.Rker antitone on [0,inf),  Rker v = int p^2 Phi(v+p) Phi(v-p) dp.

The reduction found on paper, to be tested here BEFORE it is formalised:
  for fixed p, G_p(w) := log Phi(w+p) + log Phi(w-p) is EVEN in w (Phi even), and CONCAVE in
  w if log Phi is concave (sum of concave-after-affine).  Even + concave => antitone on
  [0,inf).  Exponentiating and integrating against p^2 >= 0 gives Rker antitone POINTWISE in
  p -- no Prekopa, no marginal theorem.
So the whole question is: IS log Phi CONCAVE?

  R1  is Rker antitone?  dense + hostile, log-space (underflow-controlled), derivative signs
  R2  IS log Phi CONCAVE?  the load-bearing hypothesis -- dense scan of (log Phi)''
  R3  is Phi antitone on [0,inf)?
  R4  the FOUR-POINT inequality Phi(v+p)Phi(v-p) <= Phi(u+p)Phi(u-p) directly, hostile (u,v,p)
  R5  is Rker log-concave?
  R6  nested-quadrature cross-check of Rker at high precision

REJECTION GATE: any stable increase of Rker on [0,inf), or any stable positive (log Phi)'',
kills the corresponding route immediately and is reported as such.
"""
from mpmath import mp, mpf, exp, pi, log, quad, fabs, diff, nstr, inf

mp.dps = 50

def Phi(t, nmax=200):
    """Repo kernel 4*sum_n(...), evaluated at |t| (Phi is even: riemannXiKernel_neg)."""
    t = fabs(mpf(t))
    e2 = exp(2*t); e92 = exp(9*t/2); e52 = exp(5*t/2)
    s = mpf(0)
    for n in range(1, nmax+1):
        r = mpf(n)
        a = (2*pi**2*r**4*e92 - 3*pi*r**2*e52) * exp(-pi*r**2*e2)
        s += a
        if n > 3 and fabs(a) < mpf(10)**(-(mp.dps+20)):
            break
    return 4*s

print("="*78); print("R2 -- IS log Phi CONCAVE?  (the load-bearing hypothesis)"); print("="*78)
print("  If yes, the pointwise pairing argument closes Rker antitone with no Prekopa.")
print("  (log Phi)'' computed by mpmath.diff at 50 dps on a dense grid.")
print()
print(f"{'t':>8} {'Phi(t)':>22} {'d1 logPhi':>20} {'d2 logPhi':>20}")
lp = lambda t: log(Phi(t))
worst = None; worstt = None; npos = 0; ntot = 0
grid = [mpf(k)/200 for k in range(0, 401)]        # 0 .. 2.0 step 0.005
grid += [mpf(k)/50 for k in range(100, 176)]      # 2.0 .. 3.5 step 0.02
for t in grid:
    ntot += 1
    d2 = diff(lp, t, 2)
    if d2 > 0: npos += 1
    if worst is None or d2 > worst: worst, worstt = d2, t
for ts in ['0','0.05','0.1','0.25','0.5','0.75','1.0','1.5','2.0','2.5','3.0']:
    t = mpf(ts)
    print(f"{ts:>8} {nstr(Phi(t),14):>22} {nstr(diff(lp,t,1),12):>20} {nstr(diff(lp,t,2),12):>20}")
print()
print(f"  points scanned: {ntot} on [0, 3.5]")
print(f"  (log Phi)'' > 0 at {npos} points;  max (log Phi)'' = {nstr(worst,12)} at t = {nstr(worstt,8)}")
if npos == 0:
    print("  ==> log Phi is CONCAVE on the scanned range.  The pairing route is ALIVE.")
else:
    print("  ==> log Phi is NOT concave somewhere on the scanned range.")
    print("      REJECTION GATE FIRES for the log-concavity route.  Reported as measured.")

print(); print("="*78); print("R3 -- is Phi antitone on [0,inf)?"); print("="*78)
inc = 0; prev = None; firstinc = None
for t in grid:
    v = Phi(t)
    if prev is not None and v > prev:
        inc += 1
        if firstinc is None: firstinc = t
    prev = v
print(f"  Phi increases at {inc}/{len(grid)-1} consecutive steps"
      + (f", first at t = {nstr(firstinc,8)}" if firstinc is not None else ""))
print(f"  Phi(0) = {nstr(Phi(mpf(0)),16)},  Phi'(0) = {nstr(diff(lambda s: Phi(s), mpf(0), 1),8)}")

print(); print("="*78); print("R4 -- the FOUR-POINT inequality, directly"); print("="*78)
print("  CLAIM: for 0 <= u <= v and every p,  Phi(v+p)Phi(v-p) <= Phi(u+p)Phi(u-p).")
print("  This is what the pairing argument delivers; test it WITHOUT assuming log-concavity.")
print(f"{'u':>7} {'v':>7} {'p':>7} {'Phi(u+p)Phi(u-p)':>24} {'Phi(v+p)Phi(v-p)':>24} {'ok':>5}")
bad4 = 0; tot4 = 0
for us in ['0','0.1','0.3','0.7']:
    for vs in ['0.2','0.5','1.0','2.0']:
        for ps in ['0.05','0.3','0.9','1.8']:
            u, v, p = mpf(us), mpf(vs), mpf(ps)
            if u > v: continue
            tot4 += 1
            A = Phi(u+p)*Phi(u-p); B = Phi(v+p)*Phi(v-p)
            if B > A*(1+mpf(10)**(-30)): bad4 += 1
            if us in ('0','0.3') and ps in ('0.05','0.9') and vs in ('0.5','2.0'):
                print(f"{us:>7} {vs:>7} {ps:>7} {nstr(A,14):>24} {nstr(B,14):>24}"
                      f" {str(B<=A*(1+mpf(10)**(-30))):>5}")
print(f"  violations: {bad4}/{tot4}")

print(); print("="*78); print("R1 -- IS Rker ANTITONE?  (the target itself)"); print("="*78)
def Rker(v, umax=None):
    v = mpf(v)
    lim = mpf(4) + fabs(v)
    f = lambda p: p**2 * Phi(v+p) * Phi(v-p)
    return quad(f, [-lim, -fabs(v), 0, fabs(v), lim], maxdegree=7)
print("  computed by mpmath adaptive quadrature at 50 dps; log-space comparison so that")
print("  the doubly-exponential decay does not underflow.")
print(f"{'v':>8} {'Rker(v)':>26} {'log Rker(v)':>20} {'decreasing?':>12}")
vs_list = ['0','0.05','0.1','0.15','0.2','0.3','0.4','0.5','0.6','0.75','0.9','1.1','1.3']
prev = None; incR = 0
for vs in vs_list:
    v = mpf(vs); R = Rker(v)
    lr = log(R) if R > 0 else mpf('-inf')
    dec = (prev is None) or (lr <= prev)
    if prev is not None and lr > prev: incR += 1
    print(f"{vs:>8} {nstr(R,16):>26} {nstr(lr,12):>20} {str(dec):>12}")
    prev = lr
print(f"  increases: {incR}/{len(vs_list)-1}")
print()
print("  derivative sign, by exact differentiation under the integral:")
print("    Rker'(v) = int p^2 [Phi'(v+p)Phi(v-p) + Phi(v+p)Phi'(v-p)] dp")
def dRker(v):
    v = mpf(v)
    lim = mpf(4) + fabs(v)
    dPhi = lambda s: diff(lambda z: Phi(z), s, 1)
    f = lambda p: p**2 * (dPhi(v+p)*Phi(v-p) + Phi(v+p)*dPhi(v-p))
    return quad(f, [-lim, -fabs(v), 0, fabs(v), lim], maxdegree=5)
print(f"{'v':>8} {'Rker-prime(v)':>26} {'sign':>8}")
for vs in ['0.05','0.2','0.5','0.9']:
    d = dRker(vs)
    print(f"{vs:>8} {nstr(d,14):>26} {('NEG ok' if d < 0 else 'POSITIVE'):>8}")

print(); print("="*78); print("R5 -- is Rker log-concave?"); print("="*78)
lR = lambda v: log(Rker(v))
print(f"{'v':>8} {'d2 log Rker':>24}")
for vs in ['0.1','0.3','0.6','0.9']:
    print(f"{vs:>8} {nstr(diff(lR, mpf(vs), 2),12):>24}")

print(); print("="*78); print("R6 -- nested-quadrature CROSS-CHECK of Rker"); print("="*78)
print("  Rker(0) against the compiled identity cosMom Rker 0 = (1/4)(int Phi)(int t^2 Phi):")
I0 = 2*quad(lambda t: Phi(t), [0, mpf('0.2'), mpf('0.6'), mpf('1.5'), mpf(4)], maxdegree=8)
I2 = 2*quad(lambda t: t**2*Phi(t), [0, mpf('0.2'), mpf('0.6'), mpf('1.5'), mpf(4)], maxdegree=8)
massR = 2*quad(lambda v: Rker(v), [0, mpf('0.1'), mpf('0.3'), mpf('0.8'), mpf(3)], maxdegree=5)
print(f"    int_R Rker            = {nstr(massR,16)}")
print(f"    (1/4)(int Phi)(int t^2 Phi) = {nstr(I0*I2/4,16)}")
print(f"    reldiff               = {nstr(fabs(massR-I0*I2/4)/massR,6)}")
print("="*78)
