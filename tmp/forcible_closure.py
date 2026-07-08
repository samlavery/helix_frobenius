#!/usr/bin/env python3
"""
forcible_closure.py -- test the per-crossing forcible-closure reframe of A1.

CLAIM under test: the readout-preserving chart-conversion warp omega(n)=beta^{Omega(n)}
(beta a unit-modulus scalar, Omega(n)=# prime factors with multiplicity -- a LEGITIMATE
completely-multiplicative unit-modulus warp, NOT arbitrary per-term phases) delivers what
A1's residual extinction needs, for CUSPIDAL fibers:
  (E) ENTIRENESS  = DC mode -> 0 : |A(X)|/X -> 0, A(X)=sum_{n<=X} a_n omega(n).
  (B) BOUNDEDNESS = warped primitive controlled : |A(X)| = O(X^{1/2+eps}).
and whether a PER-CELL adapted beta (1 param) or (beta, vertical-shift) (2 param) can
FORCE the per-cell residual D_C toward zero (controllability).

We test Delta (cuspidal, entireness CLASSICALLY known -> baseline/consistency) and the
OPEN cases Sym^5, Sym^13 (entireness of L(Sym^r Delta) not classical for r>=5).
The warp is readout-preserving: A(X) O(1)/o(X) is the warped-Abel primitive; the readout
folds omega back through the kernel. If (E)+(B) hold for the open Sym^r, the warp mechanism
gives residual extinction; per-cell forcing is the constructive strengthening.
Run: python3 tmp/forcible_closure.py
"""
import math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_closure_3d as S

def omega_sieve(spf, N):
    Om = np.zeros(N + 1, dtype=np.int64)
    for n in range(2, N + 1):
        Om[n] = Om[n // int(spf[n])] + 1
    return Om

def global_warp(a, Om, logn, N, theta):
    """A(X)=sum a_n beta^{Omega(n)}, beta=e^{i theta}; return DC=|A(N)|/N, growth exponent."""
    w = np.exp(1j * theta * Om[1:N + 1])
    A = np.cumsum(a[1:N + 1] * w)
    X = np.arange(1, N + 1)
    dc = abs(A[-1]) / N
    tail = slice(N // 5, N)
    expo = np.polyfit(np.log(X[tail]), np.log(np.maximum(np.abs(A[tail]), 1e-9)), 1)[0]
    return dc, abs(A[-1]), expo

def per_cell_force(a, Om, logn, N, ncells=40, npar=1):
    """partition [1,N] into ncells; per cell minimize |D_C| over the warp params.
    npar=1: theta (winding).  npar=2: (theta, phi) with extra factor e^{i phi log n}."""
    edges = np.linspace(1, N, ncells + 1).astype(int)
    grid = np.linspace(0, 2 * math.pi, 360, endpoint=False)
    rg, rf = [], []
    for c in range(ncells):
        lo, hi = edges[c], edges[c + 1]
        ac = a[lo:hi]; Oc = Om[lo:hi]; Lc = logn[lo:hi]
        Dglob = abs(np.sum(ac * np.exp(1j * (math.pi / 3) * Oc)))
        if npar == 1:
            Dv = np.array([abs(np.sum(ac * np.exp(1j * t * Oc))) for t in grid])
            Df = Dv.min()
        else:
            phis = np.linspace(-0.5, 0.5, 41)
            best = np.inf
            for t in grid[::3]:
                base = ac * np.exp(1j * t * Oc)
                for ph in phis:
                    v = abs(np.sum(base * np.exp(1j * ph * Lc)))
                    if v < best:
                        best = v
            Df = best
        rg.append(Dglob); rf.append(Df)
    return np.median(rg), np.median(rf), math.sqrt(N / ncells)

def omega_distinct_sieve(spf, N):
    om = np.zeros(N + 1, dtype=np.int64)
    for n in range(2, N + 1):
        p = int(spf[n]); m = n // p
        om[n] = om[m] + (0 if m % p == 0 else 1)
    return om

def theta_sieve(spf, th, N):
    """Completely additive Satake winding Theta(n) = sum_{p^k || n} k*theta_p -- the
    fiber's own local periods, a coherent (finitely-generated, low-complexity) warp
    generator, NOT an arbitrary per-term phase."""
    Th = np.zeros(N + 1)
    for n in range(2, N + 1):
        p = int(spf[n])
        Th[n] = Th[n // p] + th.get(p, 0.0)
    return Th

def per_cell_force_newton(a, gens, N, ncells=40, tol=5e-14, maxit=50):
    """k coherent generators: per cell, solve the exact nonlinear D_C(x)=0,
    warp exp(i * x.g(n)), x real, by Gauss-Newton (least-norm pseudo-inverse updates),
    seeded from the base point, a coarse grid over the two periodic (integer-generator)
    phases, and random draws. Also: apply cell c's solved weights to cell c+1
    (cross-cell independence check). Returns stats + indices of resistant cells."""
    rng = np.random.default_rng(0)
    k = len(gens)
    edges = np.linspace(1, N, ncells + 1).astype(int)
    finals, wmax, nextcell, fails, failidx = [], [], [], 0, []
    prev_x = None

    def newton(x, ac, g):
        for _ in range(maxit):
            w = np.exp(1j * (x @ g))
            D = np.sum(ac * w)
            if abs(D) < tol:
                return x, abs(D)
            Sj = 1j * (ac * w) @ g.T           # dD/dx_j, complex k-vector
            J = np.vstack([Sj.real, Sj.imag])  # real 2xk
            dx = -np.linalg.pinv(J) @ np.array([D.real, D.imag])
            step = 1.0
            for _ in range(15):                # backtracking line search
                w2 = np.exp(1j * ((x + step * dx) @ g))
                if abs(np.sum(ac * w2)) < abs(D):
                    break
                step *= 0.5
            x = x + step * dx
        return x, abs(np.sum(ac * np.exp(1j * (x @ g))))

    for c in range(ncells):
        lo, hi = edges[c], edges[c + 1]
        ac = a[lo:hi]
        g = np.vstack([gg[lo:hi] for gg in gens]).astype(float)
        if prev_x is not None:
            nextcell.append(abs(np.sum(ac * np.exp(1j * (prev_x @ g)))))
        seeds = [np.array([math.pi / 3] + [0.0] * (k - 1))]
        for t1 in np.linspace(0, 2 * math.pi, 6, endpoint=False):
            for t2 in np.linspace(0, 2 * math.pi, 4, endpoint=False):
                s = np.zeros(k); s[0], s[1] = t1, t2
                seeds.append(s)
        best_x, best_D = None, np.inf
        for s in seeds:
            xx, DD = newton(s, ac, g)
            if DD < best_D:
                best_x, best_D = xx, DD
            if best_D < tol:
                break
        tries = 0
        while best_D >= tol and tries < 15:
            s = rng.uniform(-math.pi, math.pi, size=k)
            xx, DD = newton(s, ac, g)
            if DD < best_D:
                best_x, best_D = xx, DD
            tries += 1
        if best_D >= tol:
            fails += 1; failidx.append(c)
        # integer generators (Om, om): phases only matter mod 2pi
        xw = best_x.copy()
        xw[0] = (xw[0] + math.pi) % (2 * math.pi) - math.pi
        xw[1] = (xw[1] + math.pi) % (2 * math.pi) - math.pi
        finals.append(best_D)
        wmax.append(np.max(np.abs(xw)))
        prev_x = best_x
    return (np.median(finals), np.max(finals), np.max(wmax),
            (np.median(nextcell) if nextcell else 0.0),
            math.sqrt(N / ncells), fails, failidx)

def per_cell_force_grown(a, gens, N, ncells=30, maxit=40):
    """NATIVE cells, no clip: the carrier grows from the origin, each phasor entering
    continuously at ZERO magnitude through the canonical C-infinity growth window
    w(n/Z) (focal_closure.growth_window, w(0)=1 complete, w(1)=0 point entry); a cell
    is the mass accrued between consecutive head heights Z_lo -> Z_hi, uniform in the
    native ordinate y = log Z.  D_C(x) = sum_n a_n e^{i x.g(n)} [w(n/Z_hi)-w(n/Z_lo)]:
    no phasor is ever introduced at an edge.  Gauss-Newton over the generator weights."""
    rng = np.random.default_rng(1)
    k = len(gens)
    ys = np.linspace(math.log(2000.0), math.log(N), ncells + 1)
    nn = np.arange(0, N + 1, dtype=float); nn[0] = 1.0
    G = np.vstack(gens).astype(float)
    finals, rels, wmax, fails, failidx, nextcell = [], [], [], 0, [], []
    prev_x = None

    def newton(x, ac, g, tol):
        for _ in range(maxit):
            w = np.exp(1j * (x @ g))
            D = np.sum(ac * w)
            if abs(D) < tol:
                return x, abs(D)
            Sj = 1j * (ac * w) @ g.T
            J = np.vstack([Sj.real, Sj.imag])
            dx = -np.linalg.pinv(J) @ np.array([D.real, D.imag])
            step = 1.0
            for _ in range(12):
                if abs(np.sum(ac * np.exp(1j * ((x + step * dx) @ g)))) < abs(D):
                    break
                step *= 0.5
            x = x + step * dx
        return x, abs(np.sum(ac * np.exp(1j * (x @ g))))

    for c in range(ncells):
        Zlo, Zhi = math.exp(ys[c]), math.exp(ys[c + 1])
        dw = FC.growth_window(nn / Zhi) - FC.growth_window(nn / Zlo)
        sup = np.abs(dw) > 1e-16
        sup[0] = False
        ac = (a[:N + 1] * dw)[sup]
        g = G[:, sup]
        mass = float(np.linalg.norm(ac))
        tol = 5e-14 * max(1.0, mass)
        if prev_x is not None:
            nextcell.append(abs(np.sum(ac * np.exp(1j * (prev_x @ g)))) / max(mass, 1e-30))
        seeds = [np.array([math.pi / 3] + [0.0] * (k - 1))]
        for t1 in np.linspace(0, 2 * math.pi, 6, endpoint=False):
            for t2 in np.linspace(0, 2 * math.pi, 4, endpoint=False):
                s = np.zeros(k); s[0], s[1] = t1, t2
                seeds.append(s)
        best_x, best_D = None, np.inf
        for s in seeds:
            xx, DD = newton(s, ac, g, tol)
            if DD < best_D:
                best_x, best_D = xx, DD
            if best_D < tol:
                break
        tries = 0
        while best_D >= tol and tries < 10:
            xx, DD = newton(rng.uniform(-math.pi, math.pi, size=k), ac, g, tol)
            if DD < best_D:
                best_x, best_D = xx, DD
            tries += 1
        if best_D >= tol:
            fails += 1; failidx.append(c)
        xw = best_x.copy()
        xw[0] = (xw[0] + math.pi) % (2 * math.pi) - math.pi
        xw[1] = (xw[1] + math.pi) % (2 * math.pi) - math.pi
        finals.append(best_D); rels.append(best_D / max(mass, 1e-30))
        wmax.append(np.max(np.abs(xw)))
        prev_x = best_x
    return (np.median(finals), np.max(rels), np.max(wmax),
            (np.median(nextcell) if nextcell else 0.0), fails, failidx)

def main():
    N = 200000
    spf = S.spf_sieve(N)
    Om = omega_sieve(spf, N)
    logn = np.log(np.arange(1, N + 1, dtype=float))
    logn = np.concatenate([[0.0], logn])[:N + 1]
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    th_d = {p: math.acos(max(-1, min(1, lam_d[p].real / 2))) for p in range(2, N + 1) if spf[p] == p}

    fibers = {
        "Delta (cuspidal, entire KNOWN)": np.array([lam_d[n].real for n in range(N + 1)]),
        "Sym^5 Delta (r>=5 OPEN)": S.sym_r_lambda(5, th_d, spf, N),
        "Sym^13 Delta (OPEN)": S.sym_r_lambda(13, th_d, spf, N),
    }
    print(f"N={N}, sqrt(N)={math.sqrt(N):.0f}; warp omega(n)=beta^Omega(n), beta=e^(i*pi/3)")
    print("=" * 84)
    print(f"{'fiber':<34} {'|A|/N unwarp':>12} {'|A|/N warp':>11} {'growth warp':>11}")
    for name, a in fibers.items():
        dc0, _, _ = global_warp(a, Om, logn, N, 0.0)
        dcw, Aw, ew = global_warp(a, Om, logn, N, math.pi / 3)
        print(f"{name:<34} {dc0:>12.2e} {dcw:>11.2e} {ew:>11.3f}")
    print("\n[read] entireness (E): |A|/N -> 0 (DC mode dies); boundedness (B): growth exp <~ 0.5-0.6.")
    print("       If warp gives (E)+(B) on the OPEN Sym^r, the readout-preserving warp delivers")
    print("       residual extinction where the raw projection did not.")

    print("\nper-cell forcing (adapt warp params per cell to close D_C):")
    print(f"{'fiber':<34} {'|D_C| glob':>11} {'1-param':>10} {'2-param':>10} {'sqrt(cell)':>11}")
    for name, a in fibers.items():
        g, f1, sc = per_cell_force(a, Om, logn, N, npar=1)
        _, f2, _ = per_cell_force(a, Om, logn, N, npar=2)
        print(f"{name:<34} {g:>11.2e} {f1:>10.2e} {f2:>10.2e} {sc:>11.0f}")
    print("\n[read] 1-param cannot zero a complex residual (2 real eqns, 1 unknown); 2-param should")
    print("       drive |D_C| far below the sqrt(cell) noise floor -> per-cell forcing is real.")

    om = omega_distinct_sieve(spf, N)
    Th = theta_sieve(spf, th_d, N)

    print("\nper-cell forcing, SHARP cells (clip control -- the method-law violation kept as contrast):")
    print(f"{'fiber':<34} {'med |D_C|':>10} {'max |D_C|':>10} {'max|x|':>8} {'next-cell':>10} {'fails':>6}  resistant cells")
    for name, a in fibers.items():
        med, mx, wm, nxt, sc, nf, fi = per_cell_force_newton(a, [Om, om, logn], N)
        print(f"{name:<34} {med:>10.2e} {mx:>10.2e} {wm:>8.2f} {nxt:>10.2e} {nf:>6d}  {fi}")

    print("\nper-cell forcing, NATIVE growth cells (start at the origin, every phasor enters at zero")
    print("magnitude through the canonical C-inf growth window, cells uniform in y=log Z -- no clip),")
    print("THREE coherent generators (Omega, omega, log n):")
    print(f"{'fiber':<34} {'med |D_C|':>10} {'max rel':>10} {'max|x|':>8} {'next/mass':>10} {'fails':>6}  resistant cells")
    for name, a in fibers.items():
        med, mxr, wm, nxt, nf, fi = per_cell_force_grown(a, [Om, om, logn], N)
        print(f"{name:<34} {med:>10.2e} {mxr:>10.2e} {wm:>8.2f} {nxt:>10.2e} {nf:>6d}  {fi}")

    print("\nNATIVE growth cells, FOUR generators (+ the fiber's own local periods Theta(n)):")
    print(f"{'fiber':<34} {'med |D_C|':>10} {'max rel':>10} {'max|x|':>8} {'next/mass':>10} {'fails':>6}  resistant cells")
    for name, a in fibers.items():
        med, mxr, wm, nxt, nf, fi = per_cell_force_grown(a, [Om, om, logn, Th], N)
        print(f"{name:<34} {med:>10.2e} {mxr:>10.2e} {wm:>8.2f} {nxt:>10.2e} {nf:>6d}  {fi}")

    print("\n[read] the sharp-cell run clips phasors in at full magnitude at a hard edge (the method-law")
    print("       violation); its resistant cells are the instrument's artifact hypothesis. The native")
    print("       run grows every phasor continuously from zero (focal_closure.growth_window) over")
    print("       cells uniform in the carrier ordinate y=log Z. max|x| reports weights after mod-2pi")
    print("       reduction of the integer-generator phases; next = cell c+1 residual under cell c's")
    print("       weights (cross-cell independence).")

if __name__ == "__main__":
    main()
