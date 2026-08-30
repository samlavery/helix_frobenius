# Adjudicator test: derive D_B twice.
#  strip side (unconditional): (1/2pi i) contour of xi'/xi(z) * (s-z)^-1 over
#    rectangle [-1,2] x [T1,T2]  (no trivial zeros, no s=1 pole issues; s OUTSIDE R)
#  ledger side: sum of m*(s-rho)^-1 over census zeros in the box (verified range:
#    all on-line, m=1) -- this doubles as the LINE/detector side here.
# Pre-registered: |contour - ledger| < 1e-8 => the strip-side identity is exact
# (argument principle), i.e. the second derivation has NO residual term beyond
# the zero sum; any nonzero residual would be isolated immediately.
from mpmath import mp, mpc, mpf, zeta, digamma, log, pi, quad, zetazero, j
mp.dps = 25
def xilog(z):
    return 1/z + 1/(z-1) - log(pi)/2 + digamma(z/2)/2 + zeta(z, derivative=1)/zeta(z)
T1, T2 = mpf(50), mpf(60)
s = mpc(0.3, 45)      # outside R, below the box
# contour: counterclockwise rectangle corners a=-1+iT1, b=2+iT1, c=2+iT2, d=-1+iT2
a, b, c, d = mpc(-1,T1), mpc(2,T1), mpc(2,T2), mpc(-1,T2)
f = lambda z: xilog(z)/(s - z)
I = quad(lambda t: f(a+(b-a)*t)*(b-a), [0,1]) + quad(lambda t: f(b+(c-b)*t)*(c-b), [0,1]) \
  + quad(lambda t: f(c+(d-c)*t)*(d-c), [0,1]) + quad(lambda t: f(d+(a-d)*t)*(a-d), [0,1])
contour = I/(2*pi*j)
# ledger: zeros with T1 < gamma <= T2  (zetazero indices near: N(50)~10)
zs = []
n = 8
while True:
    g = zetazero(n).imag
    if g > T2: break
    if g > T1: zs.append(g)
    n += 1
ledger = sum(1/(s - mpc(0.5, g)) for g in zs)
# contour counts poles of xi'/xi INSIDE R = zeros with T1<gamma<T2, residue m,
# times kernel value; sign: 1/(s-z) with z the pole: residue of f at rho = m * 1/(s-rho)
print("zeros in box:", [float(g) for g in zs])
print("contour  :", contour)
print("ledger   :", ledger)
print("residual :", abs(contour - ledger))
