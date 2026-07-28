# locus-ledger/carrier-formalism session 2026-07-29 — depth-two harmonic
# spherical carrier experiment (correspondent's minimal object).
# Outer: log carrier, parent rotation g1(n,t) = rot(axis a1, t*log n).
# Inner: internal log carrier, child g2(m,t) = rot(axis a2, t*log m).
# Visible: G = g1*g2 acting on marked vector; scalar chart = x+iy readout.
# QUESTIONS: (1) does abelian-exact cell closure survive non-abelian
# nesting? (2) does the closure defect follow the BCH commutator-area law?
# (3) which invariants survive the 1D projection (trace vs frame)?
import numpy as np

def rot(axis, ang):
    axis = np.asarray(axis, float); axis /= np.linalg.norm(axis)
    K = np.array([[0,-axis[2],axis[1]],[axis[2],0,-axis[0]],[-axis[1],axis[0],0]])
    return np.eye(3) + np.sin(ang)*K + (1-np.cos(ang))*(K@K)

a1 = np.array([0,0,1.0])                  # parent axis
v0 = np.array([1.0,0,0])

# --- (1)+(2): closure defect vs commutator, mu6 cell ---
# abelian control: both rotations about a1 -> cell sum of 6th roots = 0 exactly.
# non-abelian: child about tilted axis a2(eps); measure |cell sum| vs eps.
print("eps    |cellsum_abelian|   |cellsum_nonabelian|   defect/eps^1  /eps^2")
H = np.pi/3
for eps in [0.4, 0.2, 0.1, 0.05, 0.025]:
    a2 = np.array([np.sin(eps), 0, np.cos(eps)])   # tilt by eps
    sA = np.zeros(3); sN = np.zeros(3)
    for k in range(6):                              # one complete mu6 cell
        gp = rot(a1, H*k)                           # parent placement phasor
        gcA = rot(a1, H*k)                          # abelian child (same axis)
        gcN = rot(a2, H*k)                          # non-abelian child
        sA += gp @ gcA @ v0                         # net angle 2Hk: still closes? 
        sN += gp @ gcN @ v0
    # abelian control with SINGLE rotation (true mu6 closure):
    sC = sum(rot(a1, H*k) @ v0 for k in range(6))
    dN = np.linalg.norm(sN); 
    print(f"{eps:5.3f}  {np.linalg.norm(sC):.2e} (control)  {dN:.6e}   {dN/eps:.4f}  {dN/eps**2:.4f}")

# --- (3): invariant survival in the scalar chart ---
# time series of the scalar readout for a small nested bank; test recovery
# of (a) total winding, (b) trace of holonomy (conjugacy class), (c) frame.
rng = np.random.default_rng(3)
ns = [2,3,5]; ms = [2,3]
a2 = np.array([np.sin(0.3),0,np.cos(0.3)])
T = np.linspace(0, 40, 20000)
Z = np.zeros(len(T), complex)
for n in ns:
    for m in ms:
        for i,t in enumerate(T):
            G = rot(a1, t*np.log(n)) @ rot(a2, t*np.log(m))
            w = G @ v0
            Z[i] += (w[0] + 1j*w[1])
# recover component frequencies from the scalar chart (winding survival):
F = np.fft.fft(Z - Z.mean()); freqs = np.fft.fftfreq(len(T), T[1]-T[0])*2*np.pi
mask = freqs > 0; F = F[mask]; freqs = freqs[mask]
peaks = freqs[np.argsort(np.abs(F))[-8:]]
expect = sorted(set(round(abs(s1*np.log(n)+s2*np.log(m)),3)
                for n in ns for m in ms for s1 in (1,-1) for s2 in (1,-1,0)))
print("\nscalar-chart spectral peaks (rad/s):", sorted(round(p,3) for p in peaks))
print("expected combination lines log n ± log m:", expect[:10])
# trace of holonomy at fixed t vs scalar readout information:
t0 = 7.3
tr = sum(np.trace(rot(a1,t0*np.log(n)) @ rot(a2,t0*np.log(m)))
         for n in ns for m in ms)
print(f"\nholonomy trace sum at t={t0}: {tr:.6f} (frame-independent)")
# frame loss: conjugate every child by fixed h -> same traces, different scalar chart?
h = rot(np.array([1,1,0.0]), 0.8)
Zc = 0
for n in ns:
    for m in ms:
        G = rot(a1, t0*np.log(n)) @ h @ rot(a2, t0*np.log(m)) @ h.T
        w = G @ v0; Zc += (w[0]+1j*w[1])
G0 = sum((rot(a1,t0*np.log(n)) @ rot(a2,t0*np.log(m)) @ v0)[0] +
     1j*(rot(a1,t0*np.log(n)) @ rot(a2,t0*np.log(m)) @ v0)[1]
     for n in ns for m in ms)
trc = sum(np.trace(rot(a1,t0*np.log(n)) @ h @ rot(a2,t0*np.log(m)) @ h.T)
          for n in ns for m in ms)
print(f"after frame conjugation: trace sum {trc:.6f} (unchanged={abs(trc-tr)<1e-9})"
      f", scalar readout changed by {abs(Zc-G0):.4f}")
