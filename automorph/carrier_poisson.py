import mpmath as mp
mp.mp.dps = 25
# CARRIER-level test: the FE from the CARRIER's Poisson self-duality, fiber = trivial.
# 1D carrier (double helix / Z):   theta(1/t)=sqrt(t) theta(t)   -> gives zeta FE.
# 2D carrier (tensor of 2 helices / Z^2 = Z[i]): Theta(1/t)= t Theta(t) -> gives a degree-2 (CM) FE,
#    with NO fiber automorphy -- purely the carrier self-duality of the tensor lattice.
def th(t):  # 1D
    return mp.nsum(lambda n: mp.e**(-mp.pi*n*n*t), [-mp.inf, mp.inf])
def Th(t):  # 2D = th(t)^2 (Z^2 lattice)
    return th(t)**2
for t in [0.3, 1.7]:
    print(f"  2D carrier Poisson: Theta(1/{t}) - {t}*Theta({t}) = {mp.nstr(Th(1/mp.mpf(t))-t*Th(mp.mpf(t)),3)}")
# the 2D carrier's completed L via Mellin of (Theta-1)/4 is the completed Dedekind zeta of Q(i)
# = zeta(s) L(s,chi4);  FE Lambda(s)=Lambda(1-s) with NO fiber input, purely carrier Poisson:
psi2 = lambda t: (Th(t)-1)/4   # r2(n)/4 counts, sum over ideals of Z[i]
def LamQi(s):
    return mp.quad(lambda t:(t**s+t**(1-s))*psi2(t)/t,[1,mp.inf]) - 1/(2*s) - 1/(2*(1-s))
for s in [mp.mpf('0.7')+2j, mp.mpf('0.3')-1j]:
    print(f"  Q(i) (CM, degree 2, carrier-only): Lambda({mp.nstr(s,4)})-Lambda(1-s) = {mp.nstr(LamQi(s)-LamQi(1-s),3)}")
