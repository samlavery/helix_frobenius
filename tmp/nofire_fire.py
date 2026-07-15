"""
Order 3, first slice: get the carrier to NO-FIRE, then to FIRE -- controlled by the arithmetic.
Family: quadratic twists of the CERESA channel f = psi^3 / Q(sqrt-7) = 49.4.a.a (weight 4, eps=-1).
Twist by chi_d (Kronecker (d/.), d a fundamental discriminant coprime to 7):
  lambda_n -> lambda_n * chi_d(n),  conductor 49 -> 49 d^2,  gamma shift 3/2 (weight 4).
Sign prediction (to TEST, not assume -- eps read by the split-vs-direct certify):
  eps(f (x) chi_d) = eps(f) * chi_d(-1) = -sign(d)
  => d<0 (imaginary): eps=+1 -> L(1/2)!=0 = NO-FIRE (no forced cycle)
     d>0 (real):      eps=-1 -> L(1/2)=0, L'(1/2)!=0 = FIRE (forced delayed signature)
The no-fire -> fire crossing sits exactly on the arithmetic (sign) locus at d: - to +.
DISCIPLINE: eta=twisted conductor, roots=Kronecker char, sign=certify (empirical), harmonics=k=1.
"""
import importlib.util, sys, math
import numpy as np
from mpmath import mp
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try:
    spec.loader.exec_module(cl)
except SystemExit:
    pass
mp.dps = 30

def kronecker(a, n):
    """Kronecker symbol (a/n)."""
    if n == 0:
        return 1 if a in (1, -1) else 0
    if a % 2 == 0 and n % 2 == 0:
        return 0
    # remove sign of n
    r = 1
    if n < 0:
        n = -n
        if a < 0: r = -r
    # factor out 2s from n
    while n % 2 == 0:
        n //= 2
        if a % 8 in (3, 5): r = -r
    a %= n
    # Jacobi symbol (a/n), n odd positive
    result = r
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: result = -result
        a %= n
    return result if n == 1 else 0

def chi_d_arr(d, nmax):
    return np.array([kronecker(d, n) for n in range(nmax + 1)], dtype=float)

m = 3                                   # Ceresa grade
DISCS = [-3, -4, -8, -11, -19, 5, 8, 12, 13, 17]   # fundamental discs coprime to 7
print("== NO-FIRE -> FIRE: quadratic twists of the Ceresa channel psi^3 / Q(sqrt-7) ==")
print("  d    sign(d)  eps  |  L(1/2)      L'(1/2)     reading           predicted")
for d in DISCS:
    nmax = 2000 + 700 * abs(d)          # AFE needs ~ sqrt(49 d^2)*few = 7|d|*few terms
    _, lam0 = cl.bank_hecke_unitary(m, nmax)
    chi = chi_d_arr(d, nmax)
    lam = lam0 * chi                    # twisted coefficients
    G = cl.make_G(49 * d * d, [('C', m / 2.0)])
    eps, r, _ = cl.certify(G, lam, 2.5)
    L = cl.central_value(G, lam, eps).real
    if eps < 0 and abs(L) < 1e-2:
        Ld = cl.central_deriv(G, lam, eps).real
        reading = "FIRE  (L=0, L'!=0)" if abs(Ld) > 0.02 else "deeper (L'=0)"
        lds = "%+.4f" % Ld
    else:
        reading = "NO-FIRE (L!=0)"
        lds = "   --   "
    pred = "no-fire" if d < 0 else "FIRE"
    ok = "ok" if (pred == "FIRE") == (eps < 0) else "MISMATCH"
    print("  %+3d    %+d     %+d  |  %+.4e  %s   %-18s %s(%s)"
          % (d, (1 if d > 0 else -1), eps, L, lds, reading, pred, ok))
print("\n  => sweeping d from negative (no-fire) to positive (fire) crosses the carrier's")
print("     detection boundary at the arithmetic (sign) locus; fire = forced cycle, eps=-1.")
