"""The make-or-break, part 2: the ADAPTED (nonlinear) center reading.

Wall four leaves exactly one candidate route to the primitive quadruple's
center: machinery that consumes the fiber's STRUCTURAL LAW (the four curves'
local data) rather than its coefficient stream.  The house protocol is
forcible closure: a unit-modulus warp exp(i sum_j x_j g_j(n)) over the coherent
generators -- log n, the distinct-prime count omega(n), and the fiber's own
local periods Theta_i(n) = sum_{p^k || n} k theta_p^{(i)}, one per constituent
curve (the structural law entering as data) -- with ONE weight vector x solved
by Gauss--Newton to close the pi/3-cells of the ordinate y = log n.

PRE-REGISTERED HONESTY: the corpus proves the continuation TRANSFERS (identity
theorem); a value recipe at the center via solved warps is NOT among the
proven statements -- un-twisting a warp termwise costs back its convergence.
So this instrument GATES the warp-value relation on certified truths first:

  GATE RS4:  L(11a1 x 37a1, 1/2) = 5.0227652   (certified, carrier_center.py)
  GATE S4:   L(Sym4 11a1, 1/2)   = 0.6058010   (certified, center_reading.py)

For each fiber: (1) solve x on a training window of cells; report closure
before/after (does degree-16 forcible closure even happen -- news either way);
(2) read the warped center F_w(1/2) = sum lam_n w_x(n) n^{-1/2} with a
cutoff-stability certificate; (3) compare with truth on the gates: equality /
lawful offset / gap -- all three are findings.  Then the primitive.

Run: python3 adapted_center.py     (~3-5 min)
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
import center_reading as CR
import farside_center as FC
import carrier_center as CC

NMAX = 100000
H = math.pi / 3

CURVES = [("11a1", 11, (0, -1, 1, -10, -20)),
          ("37a1", 37, (0, 0, 1, -1, 0)),
          ("53a1", 53, (1, -1, 1, 0, 0)),
          ("61a1", 61, (1, 0, 0, -2, 1))]


def spf_sieve(n):
    spf = np.arange(n + 1)
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            sl = spf[i * i::i]
            sl[sl == np.arange(i * i, n + 1, i)] = i
            spf[i * i::i] = sl
    return spf


def generators(nmax, legs):
    """g(n) matrix: [log n, omega(n), Theta_1..Theta_k] via factorization."""
    spf = spf_sieve(nmax)
    thetas = {}
    for lab, N, ainv in legs:
        th = np.zeros(nmax + 1)
        for p in SH.sieve_primes(nmax):
            if N % p == 0:
                continue
            th[p] = FC.theta_of(ainv, p)
        thetas[lab] = th
    ncols = 2 + len(legs)
    G = np.zeros((nmax + 1, ncols))
    G[1:, 0] = np.log(np.arange(1, nmax + 1))
    for n in range(2, nmax + 1):
        m = n
        while m > 1:
            p = int(spf[m])
            k = 0
            while m % p == 0:
                m //= p
                k += 1
            G[n, 1] += 1.0
            for j, (lab, _, _) in enumerate(legs):
                G[n, 2 + j] += k * thetas[lab][p]
    return G


def cell_index(nmax):
    y = np.log(np.arange(1, nmax + 1))
    return np.floor(y / H).astype(int)


def residuals(lam, G, cells, x, kmin, kmax):
    phase = np.exp(1j * (G[1:] @ x))
    n = np.arange(1, len(lam), dtype=float)
    terms = lam[1:] * n ** -0.5 * phase
    out = []
    for k in range(kmin, kmax + 1):
        out.append(terms[cells == k].sum())
    return np.array(out)


def gauss_newton(lam, G, cells, kmin, kmax, npar, iters=60):
    x = np.zeros(npar)
    for _ in range(iters):
        r = residuals(lam, G, cells, x, kmin, kmax)
        rv = np.concatenate([r.real, r.imag])
        J = np.zeros((len(rv), npar))
        eps = 1e-6
        for j in range(npar):
            xp = x.copy()
            xp[j] += eps
            rp = residuals(lam, G, cells, xp, kmin, kmax)
            J[:, j] = np.concatenate([(rp - r).real, (rp - r).imag]) / eps
        try:
            dx, *_ = np.linalg.lstsq(J, -rv, rcond=None)
        except np.linalg.LinAlgError:
            break
        x = x + 0.8 * dx
        if np.linalg.norm(dx) < 1e-12:
            break
    return x


def warped_center(lam, G, x, cuts):
    phase = np.exp(1j * (G[1:] @ x))
    n = np.arange(1, len(lam), dtype=float)
    terms = lam[1:] * n ** -0.5 * phase
    csum = np.cumsum(terms)
    return [complex(csum[c - 1]) for c in cuts]


def run_fiber(P, name, lam, legs, truth=None):
    P(f"  {name}:")
    G = generators(len(lam) - 1, legs)
    cells = cell_index(len(lam) - 1)
    kmin, kmax = 4, int(math.log(len(lam) - 1) / H) - 1
    npar = G.shape[1]
    r0 = residuals(lam, G, cells, np.zeros(npar), kmin, kmax)
    x = gauss_newton(lam, G, cells, kmin, kmax, npar)
    r1 = residuals(lam, G, cells, x, kmin, kmax)
    P(f"    cells {kmin}..{kmax}, generators {npar} "
      f"(log n, omega, {len(legs)} local-period legs)")
    P(f"    closure: median |D| {np.median(np.abs(r0)):.4f} -> "
      f"{np.median(np.abs(r1)):.4f}   max {np.abs(r0).max():.4f} -> "
      f"{np.abs(r1).max():.4f}   |x| max {np.abs(x).max():.3f}")
    cuts = [len(lam) // 8, len(lam) // 4, len(lam) // 2, len(lam) - 1]
    vals = warped_center(lam, G, x, cuts)
    for c, v in zip(cuts, vals):
        P(f"    F_w(1/2) at cutoff {c:7d}: {v.real:+.6f} {v.imag:+.6f}i")
    stab = abs(vals[-1] - vals[-2])
    P(f"    stability |d| = {stab:.4f}")
    if truth is not None:
        P(f"    truth L(1/2) = {truth:.6f};  F_w - L = "
          f"{vals[-1].real - truth:+.4f} {vals[-1].imag:+.4f}i;  "
          f"|F_w|/L = {abs(vals[-1]) / truth:.4f}")
    return np.median(np.abs(r1)), stab, vals[-1]


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# ADAPTED CENTER READING -- forcible closure vs the wall (pre-registered)")
    P("#" * 78)
    P()

    P("GATE RS4 (truth 5.0227652):")
    lam4 = CC.bank_rs(NMAX)
    m4, s4, v4 = run_fiber(P, "RS 11a1 x 37a1", lam4,
                           [CURVES[0], CURVES[1]], truth=5.0227652)
    P()
    P("GATE S4 (truth 0.6058010):")
    lam5 = CR.bank_sym_unitary(4, NMAX)
    m5, s5, v5 = run_fiber(P, "Sym4 11a1", lam5, [CURVES[0]], truth=0.6058010)
    P()
    P("THE PRIMITIVE (no classical value exists):")
    lam16 = FC.build_bank("primitive", NMAX)
    m16, s16, v16 = run_fiber(P, "primitive quadruple", lam16, CURVES)
    P()

    P("VERDICT (pre-registered outcomes):")
    P("  closure at degree 16: median residual "
      f"{m16:.4f} (news either way -- the first forcible-closure attempt")
    P("  above degree 14).")
    gates_equal = (abs(v4.real - 5.0227652) < 0.25 and abs(v4.imag) < 0.25
                   and abs(v5.real - 0.6058010) < 0.15 and abs(v5.imag) < 0.15)
    if gates_equal and s16 < 0.5:
        P(f"  GATES: the warped reading EQUALS the certified centers within")
        P(f"  tolerance -- the adapted route preserves values.  THE READING:")
        P(f"    L(primitive quadruple, 1/2) ~= {v16.real:+.4f} {v16.imag:+.4f}i")
        P(f"  Hostile checks mandatory before any claim.")
    else:
        P(f"  GATES: the warped reading does NOT equal the certified centers")
        P(f"  (RS4 offset {v4.real - 5.0227652:+.3f}{v4.imag:+.3f}i, "
          f"S4 offset {v5.real - 0.6058010:+.3f}{v5.imag:+.3f}i).")
        P(f"  MEASURED CONCLUSION: solved warps buy summability, not the value;")
        P(f"  the un-twisting compensation (the S(t)-analogue for VALUES -- the")
        P(f"  registration law connecting F_w(1/2) to L(1/2)) is the precise")
        P(f"  missing piece of the no-sqrt(Q) claim.  The wall stands until that")
        P(f"  law is proven; the framework's decisive experiment is now reduced")
        P(f"  to one named theorem-target, with all calibration data recorded.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "adapted_center_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to adapted_center_results.txt]")


if __name__ == "__main__":
    main()
