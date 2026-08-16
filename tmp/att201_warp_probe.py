"""att201: adversarial probe of the bank-warp theorems before print.

Claims under test (hp_pencil.tex, new Sec. warp):
  (iii) exact covariance: the flow of the interpolated bank velocity field
        V_t (Lagrange through (lambda_a(t), drift_a(t))) carries the initial
        nodes onto the eigenvalue paths of the transported pencil, exactly.
  (ii)  order preservation: characteristics never cross (a strictly interior
        test point stays strictly interior).
  drift formula: lambda_dot_a = w^T (G1dot - lambda_a G0dot) w, w^T G0 w = 1.

Transport path: s0(t) = 1.5 - 0.3 t (convergent segment), N = 4.
Jets: m_k(s0) = (-1)^k d^k/ds^k [-zeta'/zeta](s0) = sum Lambda(n) n^{-s0} log^k n >= 0.
d m_k / d s0 = -m_{k+1}  =>  dG_l/dt = 0.3 * m_{j+k+l+1}  (analytic, no FD in t).
"""
import numpy as np
from mpmath import mp, zeta, diff

mp.dps = 25
N = 4
S0A, S0B = 1.5, 1.2          # s0(t) = S0A + (S0B-S0A)*t
DS0DT = S0B - S0A            # -0.3
KMAX = 2 * N                 # m_0..m_{2N-1} for G, one more for Gdot

_f = lambda s: -zeta(s, derivative=1) / zeta(s)
_jets_cache = {}


def jets(s0):
    key = round(float(s0), 12)
    if key not in _jets_cache:
        _jets_cache[key] = [float(((-1) ** k) * diff(_f, mp.mpf(s0), k))
                            for k in range(KMAX + 1)]
    return _jets_cache[key]


def nodes_drifts(t):
    m = jets(S0A + DS0DT * t)
    G0 = np.array([[m[j + k] for k in range(N)] for j in range(N)])
    G1 = np.array([[m[j + k + 1] for k in range(N)] for j in range(N)])
    G0d = np.array([[-DS0DT * m[j + k + 1] for k in range(N)] for j in range(N)])
    G1d = np.array([[-DS0DT * m[j + k + 2] for k in range(N)] for j in range(N)])
    L = np.linalg.cholesky(G0)
    Linv = np.linalg.inv(L)
    S = Linv @ G1 @ Linv.T
    lam, Y = np.linalg.eigh(S)
    Wv = Linv.T @ Y                      # generalized eigenvectors, w^T G0 w = 1
    drift = np.array([Wv[:, a] @ (G1d - lam[a] * G0d) @ Wv[:, a] for a in range(N)])
    return lam, drift


def V(x, lam, drift):
    """Lagrange interpolation of degree <= N-1 through (lam_a, drift_a)."""
    out = 0.0
    for a in range(N):
        term = drift[a]
        for b in range(N):
            if b != a:
                term *= (x - lam[b]) / (lam[a] - lam[b])
        out += term
    return out


lam0, drift0 = nodes_drifts(0.0)
print("anchor nodes      :", np.round(lam0, 6), flush=True)
print("anchor drifts     :", np.round(drift0, 6), flush=True)

# drift-formula sanity: central difference of eigenpaths vs perturbation formula
h = 1e-6
lp, _ = nodes_drifts(h)
lm, _ = nodes_drifts(-h)
fd = (lp - lm) / (2 * h)
print("drift check (FD)  :", np.round(fd, 6), " max err %.2e" % np.max(np.abs(fd - drift0)),
      flush=True)

# RK4 the flow  x_dot = V_t(x)  from the anchor nodes + one interior test point
xmid = 0.5 * (lam0[0] + lam0[1])
X = np.concatenate([lam0, [xmid]])
STEPS = 24
dt = 1.0 / STEPS
t = 0.0
for step in range(STEPS):
    nd1 = nodes_drifts(t)
    ndh = nodes_drifts(t + dt / 2)
    nd2 = nodes_drifts(t + dt)
    k1 = np.array([V(x, *nd1) for x in X])
    k2 = np.array([V(x, *ndh) for x in (X + dt / 2 * k1)])
    k3 = np.array([V(x, *ndh) for x in (X + dt / 2 * k2)])
    k4 = np.array([V(x, *nd2) for x in (X + dt * k3)])
    X = X + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    t += dt
    if (step + 1) % 6 == 0:
        print("  t=%.3f  X=%s" % (t, np.round(X, 6)), flush=True)

lam1, _ = nodes_drifts(1.0)
print("terminal nodes    :", np.round(lam1, 8), flush=True)
print("flowed nodes      :", np.round(X[:N], 8), flush=True)
err = np.max(np.abs(X[:N] - lam1))
print("covariance error  : %.3e" % err, flush=True)
inside = lam1[0] < X[N] < lam1[1]
print("interior point    : %.8f in (%.8f, %.8f) -> %s"
      % (X[N], lam1[0], lam1[1], "ORDER PRESERVED" if inside else "ORDER VIOLATED"),
      flush=True)
print("VERDICT:", "PASS" if err < 1e-5 and inside else "FAIL", flush=True)
