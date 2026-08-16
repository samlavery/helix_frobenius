"""att206c: resolution frontier via the Hadamard zero-sum jets (fast engine; also
the germ of obligation (T)'s closed form). For k >= 1:
  m^reg_k(s0) = -k! * [ sum_rho (s0-rho)^{-(k+1)} + sum_m (s0+2m)^{-(k+1)} ],
zeros in conjugate pairs (real part sums), trivial zeros at -2m, tail of the zero
sum corrected by the RvM density integral. m_0 from direct f_reg evaluation."""
import numpy as np
from mpmath import mp, zeta, zetazero, mpf, log, pi, quad

mp.dps = 30
NZ = 100
print("computing %d zeros..." % NZ, flush=True)
G = [float(zetazero(j).imag) for j in range(1, NZ + 1)]
GMAX = G[-1]
KTOP = 24

def mreg(s0, K):
    out = [float(-zeta(s0, derivative=1) / zeta(s0) - 1 / (s0 - 1))]
    a = s0 - 0.5
    for k in range(1, K + 1):
        p = k + 1
        zsum = sum(float(2 * ((a - 1j * g) ** p).real / abs(a - 1j * g) ** (2 * p))
                   for g in G)          # 2 Re (s0-rho)^{-p} summed over pairs
        # tail: 2 Re int_{GMAX}^inf (a+ig)^{-p} dN,  dN = log(g/2pi)/2pi dg
        tail = float(quad(lambda g: 2 * ((a + 1j * g) ** (-p)).real
                          * log(g / (2 * pi)) / (2 * pi), [GMAX, mp.inf]).real) \
               if p <= 4 else 0.0
        tsum = sum((s0 + 2 * m) ** (-p) for m in range(1, 200000))
        out.append(-float(mp.factorial(k)) * (zsum + tail + tsum))
    return np.array(out)

# engine check against direct jets at s0=1.3 (att206 values, k<=8)
mc = mreg(1.3, 8)
from mpmath import diff
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)
md = np.array([float(((-1) ** k) * diff(f_reg, mpf(1.3), k)) for k in range(9)])
print("engine check s0=1.3 max rel err (k<=8): %.2e"
      % np.max(np.abs((mc - md) / md)), flush=True)

print("\n n \\ s0 :   1.30        0.999       0.80        0.60")
M = {s0: mreg(s0, KTOP) for s0 in [1.3, 0.999, 0.8, 0.6]}
for n in [4, 6, 8, 10, 12]:
    row = []
    for s0 in [1.3, 0.999, 0.8, 0.6]:
        m = M[s0]
        G0 = np.array([[m[j + k] for k in range(n)] for j in range(n)])
        ev = np.linalg.eigvalsh(G0)
        scale = np.max(np.abs(ev))
        npos = int(np.sum(ev > 1e-11 * scale))
        nneg = int(np.sum(ev < -1e-11 * scale))
        row.append("(%d,%d)" % (npos, nneg))
    print("  %2d    :   %-10s  %-10s  %-10s  %-10s" % (n, *row), flush=True)
