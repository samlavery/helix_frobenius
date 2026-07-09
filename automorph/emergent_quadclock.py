import mpmath as mp
mp.mp.dps = 22
# THE EMERGENT CLOCK: the carrier's own QUADRATIC (arclength n^2) phase.  A quadratic warp
# e^{i pi c n^2} on the carrier is NOT a translation -- it SHIFTS THE MODULAR PARAMETER:
#   sum_n e^{i pi c n^2} e^{-pi n^2 t} = sum_n e^{-pi n^2 (t - i c)} = theta(t - i c).
# So: linear clock = translation (T on the dual, mu6 shift);  QUADRATIC clock = tau->tau+c (the
# modular T-generator);  Poisson = tau->-1/tau (the S-generator).  T and S generate SL(2,Z) --
# the MODULAR GROUP -- i.e. the automorphy machinery, emergent from the carrier's own arclength.
def th(tau):  # theta(tau) = sum e^{i pi n^2 tau}  (tau in upper half plane)
    return mp.nsum(lambda n: mp.e**(1j*mp.pi*n*n*tau), [-mp.inf, mp.inf])
# 1) quadratic clock == tau-shift (T):
for c in [1, mp.mpf('0.5')]:
    tau = 1j*mp.mpf('0.8')
    warp = mp.nsum(lambda n: mp.e**(1j*mp.pi*c*n*n)*mp.e**(1j*mp.pi*n*n*tau), [-mp.inf,mp.inf])
    print(f"  quad-clock(c={c}) - theta(tau+{c}) = {mp.nstr(warp - th(tau+c),3)}   (= modular T generator)")
# 2) Poisson == S generator tau->-1/tau:  theta(-1/tau) = sqrt(tau/i) theta(tau)
tau = mp.mpf('0.3')*1j + mp.mpf('0.2')
S = th(-1/tau) - mp.sqrt(tau/1j)*th(tau)
print(f"  Poisson = S generator: theta(-1/tau) - sqrt(tau/i)theta(tau) = {mp.nstr(S,3)}")
# 3) T and S generate SL(2,Z): compose (ST)^3 = identity check on tau  (order-6 elt, (ST)^6=1)
def T(t): return t+1
def Sm(t): return -1/t
tau0 = mp.mpf('0.4')*1j+mp.mpf('0.1'); t=tau0
for _ in range(6): t = Sm(T(t))
print(f"  (S T)^6 on tau: {mp.nstr(t,6)} vs tau0 {mp.nstr(tau0,6)}  -> modular group closes (order 6)")
print("  => the emergent quadratic (arclength) clock = modular T; Poisson = S; together SL(2,Z).")
