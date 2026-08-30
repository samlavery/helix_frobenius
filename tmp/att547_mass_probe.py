# (1) Channel floor via the ORDERED readout (eta route, Re s > 0): no convergence gate.
# (2) Mass M = F/(sigma-1/2): positivity + Poisson balance against actual zeros.
# Pre-registered: eta-route floor must match continuation to >=10 digits (else the
# ordered-readout claim is wrong); M > 0 on grid; M ~ sum of Poisson kernels over
# nearby zeros + tail (same order, shape tracks).
from mpmath import mp, mpc, mpf, zeta, digamma, log, pi, re, nsum, power, zetazero, inf
mp.dps = 25

def xilog_cont(s):   # continuation route (reference)
    return 1/s + 1/(s-1) - log(pi)/2 + digamma(s/2)/2 + zeta(s, derivative=1)/zeta(s)

def zplog_eta(s):    # ordered readout: zeta'/zeta = eta'/eta + log2 * 2^(1-s)/(1-2^(1-s))
    eta  = nsum(lambda n: (-1)**(n-1) * power(n, -s), [1, inf], method='a')
    etap = nsum(lambda n: (-1)**n * log(n) * power(n, -s), [2, inf], method='a')
    corr = log(2) * power(2, 1-s) / (1 - power(2, 1-s))
    return etap/eta + corr

def xilog_eta(s):
    return 1/s + 1/(s-1) - log(pi)/2 + digamma(s/2)/2 + zplog_eta(s)

# --- (1) ordered-readout validation at channel points
print("== ordered readout vs continuation (channel points) ==")
for (sig, t) in [(0.3, 700.0), (0.45, 1000.0), (0.1, 800.0)]:
    s = mpc(sig, t)
    a, b = xilog_eta(s), xilog_cont(s)
    print(f"  s={sig}+{t}i   |eta-route - continuation| = {float(abs(a-b)):.3e}")

# --- (2) mass positivity + Poisson balance at t0=1000
t0 = mpf(1000)
# collect zeros with |gamma - t0| < 15   (N(1000) ~ 649)
zs = []
n = 600
while True:
    g = zetazero(n).imag
    if g > t0 + 15: break
    if g > t0 - 15: zs.append(g)
    n += 1
print(f"== zeros near t=1000: {len(zs)} in window ±15 ==")
dens = float(log(t0/(2*pi))/(2*pi))   # RvM local density
print(f"{'sigma':>6} {'M measured':>12} {'Poisson sum':>12} {'tail est':>9} {'sum+tail':>10}")
for sig in [0.05, 0.25, 0.40, 0.475, 0.499]:
    s = mpc(sig, t0)
    F = re(xilog_cont(s))
    M = float(F / (sig - 0.5))
    x = 0.5 - sig
    ps = float(sum(x/(x**2 + float(t0-g)**2) for g in zs) / x)  # sum 1/(x^2+(t-g)^2)
    # tail: integral of density/( (t-g)^2 ) outside window ~ 2*dens/15
    tail = 2*dens/15
    print(f"{sig:>6.3f} {M:>12.6f} {ps:>12.6f} {tail:>9.6f} {ps+tail:>10.6f}")
print(f"chi-clock check: pi*density = {float(pi)*dens:.6f}  vs  0.5*log(t/2pi) = {float(0.5*log(t0/(2*pi))):.6f}")
