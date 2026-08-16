"""att202: the margin probe (GOAL_HP_UNCONDITIONAL step (a)).

On a Platt-Trudgian-verified window W=(10,32) (four zeros, q=0 known), sweep the
erf-smoothed-indicator homotopy w_tau -> 1_W and measure, in the rescaled chart
u = (gamma-21)/11:

  margin(tau)  = v*^T H(tau) v*  = sum_rho w_tau(gamma_rho) P*(u_rho)^2,
                 P* = prod over the 4 in-window zeros (the terminal null direction),
  lam_min(tau) of the 5x5 Hankel H(tau),
  per-zero source decomposition of margin(tau),
  monotonicity of margin in tau (flow sign through the dying direction),
  Rayleigh tracking ratio lam_min / (margin/||v*||^2).

Claim under test (null-cone condition, seat attack): mass only enters/leaves the
dead direction through the explicit out-of-window weights -- no sign anomaly; the
margin is a nearest-neighbor tail sum dominated by the boundary-nearest zero.
"""
import numpy as np
from mpmath import mp, zetazero, erf, sqrt, mpf

mp.dps = 20
NZ = 60                       # zeros used; Gaussian tails make the rest negligible
A, B = 10.0, 32.0             # the window
C, S = 21.0, 11.0             # chart u = (gamma - C)/S
N = 5                         # pencil size = mu0 + 1 = 4 + 1

print("computing %d zeros..." % NZ, flush=True)
gammas = np.array([float(zetazero(k).imag) for k in range(1, NZ + 1)])
u = (gammas - C) / S
inw = (gammas > A) & (gammas < B)
print("in-window zeros:", np.round(gammas[inw], 4), flush=True)

# terminal null polynomial P*(u) = prod (u - u_i) over in-window zeros
ui = u[inw]
coeff = np.poly(ui)[::-1]            # ascending: coeff[k] * u^k, degree 4
vstar = coeff / np.linalg.norm(coeff)
Pstar2 = np.array([np.polyval(coeff[::-1], x) ** 2 for x in u])


def w_tau(g, tau):
    r2 = float(sqrt(2))
    return 0.5 * (float(erf((B - g) / (tau * r2))) - float(erf((A - g) / (tau * r2))))


def hankel(tau):
    w = np.array([w_tau(g, tau) for g in gammas])
    mom = np.array([np.sum(w * u ** k) for k in range(2 * N - 1)])
    H = np.array([[mom[j + k] for k in range(N)] for j in range(N)])
    return H, w


taus = [8.0, 4.0, 2.0, 1.0, 0.5, 0.25, 0.1, 0.05]
print("\n tau     lam_min       margin        rayleigh      ratio   top sources (gamma:share)")
prev_margin = None
mono_ok = True
for tau in taus:
    H, w = hankel(tau)
    lam = np.linalg.eigvalsh(H)
    margin = float(vstar @ H @ vstar)
    contrib = w * Pstar2 / (np.linalg.norm(coeff) ** 2)
    order = np.argsort(contrib)[::-1][:3]
    top = "  ".join("%.2f:%.1f%%" % (gammas[i], 100 * contrib[i] / margin) for i in order)
    rayleigh = margin                      # vstar is unit, so Rayleigh bound = margin
    ratio = lam[0] / rayleigh if rayleigh > 0 else float("nan")
    if prev_margin is not None and margin > prev_margin + 1e-15:
        mono_ok = False
    prev_margin = margin
    print(" %5.2f  %.4e  %.4e  %.4e  %6.4f   %s"
          % (tau, lam[0], margin, rayleigh, ratio, top), flush=True)

# flow sign: d(margin)/d tau by central difference at a mid value
tau0, h = 1.0, 1e-4
m_p = float(vstar @ hankel(tau0 + h)[0] @ vstar)
m_m = float(vstar @ hankel(tau0 - h)[0] @ vstar)
dm = (m_p - m_m) / (2 * h)
print("\nflow sign  d(margin)/d tau at tau=1: %+.4e  (positive = mass enters the"
      " dead direction as the weight broadens; no sign anomaly expected)" % dm)
print("margin monotone decreasing toward sharp limit:", "YES" if mono_ok else "NO")

# tail-truncation audit: weight of the last used zero at the broadest tau
wlast = w_tau(gammas[-1], taus[0])
print("truncation audit: w_tau(gamma_%d=%.2f) at tau=%.1f -> %.2e"
      % (NZ, gammas[-1], taus[0], wlast))
print("VERDICT:", "PASS" if (mono_ok and dm > 0) else "FAIL")
