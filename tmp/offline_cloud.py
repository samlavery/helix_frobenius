"""Does an OFF-LINE zero create an eigencloud / indefinite direction?

Weil form on a Gabor family.  A zero rho contributes phihat(gamma-tau_k)phihat(gamma-tau_l).
ON-LINE  (rho = 1/2+i g):  contributes a real rank-1 PSD block  -> spectrum >= 0
OFF-LINE (rho = b+i g, b != 1/2): the FE forces the partner 1-b+i g; Zeta23's (Z) says the
pair contributes a block of SIGNATURE (1,1) -> a NEGATIVE eigenvalue must appear.
Test: build G from real zeros, then displace one zero off the line and watch the inertia.
"""
import numpy as np, mpmath as mp
mp.mp.dps = 20

def phihat_c(r, L, w):
    r = np.asarray(r, dtype=complex)
    r = np.where(np.abs(r) < 1e-12, 1e-12, r)
    return (2.0/r)*np.sin(r*(L-w)/2.0)*np.sin(r*w/2.0)/(r*w/2.0)

T = 200.0; l = np.log(T/(2*np.pi)); L = l; w = 0.05*l/2
h = 2*np.pi/L; d = int(T/h); tau = T + np.arange(d)*h
g = np.array([float(mp.im(mp.zetazero(k))) for k in range(1, 400)])
g = g[(g > T-150) & (g < 2*T+150)]
print(f"T={T} d={d} zeros in window={len(g)}")

def Gmat(gams, betas):
    """rho = beta + i*gamma.  Weil summand uses h(gamma_rho) with gamma_rho = (rho-1/2)/i
       = gamma - i(beta-1/2)  -> complex argument when beta != 1/2.
       FE partner 1-beta+i*gamma is included for off-line ones."""
    G = np.zeros((d, d), dtype=complex)
    for gam, b in zip(gams, betas):
        for bb in ({b} if abs(b-0.5) < 1e-14 else {b, 1.0-b}):
            gr = gam - 1j*(bb - 0.5)
            v = phihat_c(gr - tau, L, w)
            G += np.outer(v, np.conj(v)) if abs(b-0.5) < 1e-14 else np.outer(v, np.conj(v))
    return (G + G.conj().T)/2

def report(tag, G):
    ev = np.linalg.eigvalsh(G)
    neg = ev[ev < -1e-9]
    nn = np.linalg.norm(G@G.conj().T - G.conj().T@G)/max(np.linalg.norm(G)**2, 1e-300)
    print(f"  {tag:34s} n_neg={len(neg):3d}  min_ev={ev.min():+.4e}  max_ev={ev.max():.4e}  nonnormality={nn:.1e}")

betas = np.full(len(g), 0.5)
report("ALL ON-LINE (beta=1/2)", Gmat(g, betas))
for delta in (0.02, 0.05, 0.10, 0.25):
    b = betas.copy(); b[len(b)//2] = 0.5 + delta
    report(f"one zero off-line, delta={delta:.2f}", Gmat(g, b))
