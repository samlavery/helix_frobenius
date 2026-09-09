#!/usr/bin/env python3
"""att681 — atom trajectories in the head Z. For the atom that becomes the k-th event, track s_k(Z) as Z decreases from 4γ_k
   to γ_k/6 (continuation by Newton). Candidate finite-object road: RH ⟸ [F_Z(½+it) ≠ 0 ∀ Z, t] + [atoms born left].
   PRE-REGISTERED: (i) for Z ≥ γ_k the atom stays left of the carrier (Re < ½) — predicted TRUE (sign + head laws);
   (ii) for Z in (γ_k/6, γ_k) some atom crosses to Re > ½ — predicted TRUE (crossings occur; the clean law fails)."""
import numpy as np, mpmath as mp
mp.mp.dps = 18
out = open("tmp/att681_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def fiber(Z):
    n = np.arange(1, int(np.ceil(Z))); n = n[n < Z]
    w = np.exp(1 - 1/(1 - (n/Z)**2)); c = (-1.0)**(n+1)*w; ln = np.log(n)
    F = lambda s: np.sum(c*np.exp(-s*ln)); dF = lambda s: np.sum(-ln*c*np.exp(-s*ln))
    return F, dF
def newton(F, dF, s0, tol=1e-13, maxit=50):
    s = s0
    for _ in range(maxit):
        f = F(s); d = dF(s)
        if d == 0: return None
        ds = f/d; s = s - ds
        if abs(ds) < tol: return s
    return None
zeros = [float(mp.zetazero(k).imag) for k in range(1, 13)]
say("k   γ_k     | Z≥γ: max Re, at Z | Z<γ: max Re, at Z | first crossing Z (Re>½) | Z where atom lost | Re at Z=γ/6")
for k, g in enumerate(zeros, 1):
    Z = 4*g; F, dF = fiber(Z); s = newton(F, dF, complex(0.5, g))
    traj = [(Z, s)]
    lost = None
    while Z > g/6:
        dZ = 0.02*Z if Z > 2*g else 0.01*Z
        Znew = Z - dZ; F, dF = fiber(Znew); snew = newton(F, dF, s)
        tries = 0
        while (snew is None or abs(snew - s) > 0.3) and tries < 6:   # refine the step
            dZ /= 2; Znew = Z - dZ; F, dF = fiber(Znew); snew = newton(F, dF, s); tries += 1
        if snew is None or abs(snew - s) > 0.3: lost = Z; break
        Z, s = Znew, snew; traj.append((Z, s))
    hi = [(Z, s) for Z, s in traj if Z >= g]; lo = [(Z, s) for Z, s in traj if Z < g]
    mhi = max(hi, key=lambda p: p[1].real); mlo = max(lo, key=lambda p: p[1].real) if lo else (0, complex(0,0))
    cross = next((Z for Z, s in reversed(traj) if s.real > 0.5), None)   # largest Z with Re>½ (first crossing coming down)
    say("%2d  %7.3f | %+.4f at Z=%6.1f | %+.4f at Z=%6.1f | %s | %s | Re=%+.3f (t=%.2f)"
        % (k, g, mhi[1].real - 0.5, mhi[0], mlo[1].real - 0.5, mlo[0],
           ("Z=%.1f (Z/γ=%.2f)" % (cross, cross/g)) if cross else "none",
           ("Z=%.1f (Z/γ=%.2f)" % (lost, lost/g)) if lost else "tracked to γ/6",
           traj[-1][1].real - 0.5, traj[-1][1].imag))
