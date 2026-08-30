# Follow-up to att547's fired rule: separate the COMPILED identity
# (etaLim = (1-2^{1-s})zeta on Re s > 0) from the SCHEME (alternating-series
# acceleration).  Pre-registered: at moderate t the same scheme must converge
# to the continuation value (digits improving with dps); the identity is not
# on trial, the scheme is.
from mpmath import mp, mpc, zeta, log, power, nsum, inf
for t in [5, 30, 60, 120]:
    s = mpc(0.3, t)
    mp.dps = 40
    eta_acc = nsum(lambda n: (-1)**(n-1)*power(n, -s), [1, inf], method='a')
    eta_ref = (1 - power(2, 1-s)) * zeta(s)
    print(f"t={t:>4}: |scheme - identity| = {float(abs(eta_acc - eta_ref)):.3e}")
