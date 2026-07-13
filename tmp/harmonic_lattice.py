"""Harmonic compatibility: the lattice warp law -- the candidate value-registration law.

Sam's hint operationalized: warps must be HARMONICALLY COMPATIBLE -- one base
harmonic unit, all others integer factors of it.  The base unit is the fiber's
own local angle theta_p.  Warping f's local eigenvalues {e^{+i th}, e^{-i th}}
by e^{i m th_p} with INTEGER m produces exact LANE IDENTITIES on the Sym tower:

  F_m(s) = Euler product with local phases {(1+m) th_p, (m-1) th_p}

  m = 2:  F_2 F_{-2} = L(Sym3 f, s) * C2(s),   C2 = (1-a^3 q)/(1-a q)^2
  m = 3:  F_3 F_{-3} = L(Sym4 f, s)/zeta(s) * C3(s),
          C3 = (1-a^4 q)(1-q)/(1-a q)^2,      q = 11^{-s}, a = 1/sqrt(11)
  m = 1:  F_1 F_{-1} = zeta(s) L(Sym2 f, s) * C1(s)   [pole lane -- excluded
          from the center test: F_1 carries a sqrt-pole transient]

F_{-m} = conj(F_m) on the real axis, so at the center the law reads
  |F_m(1/2)|^2 = |RHS(1/2)|  (modulus form; sqrt-branch phases drop out).
Incommensurate m has NO partner identity -- the falsifier.  Lattice warps are
PARAMETER-FREE: cell closure is structural on every cell or absent ("no gaps
in all the cells is not optional") -- no training window, nothing to overfit.

Tests (f = 11a1 throughout; every RHS certified and/or PARI-oracle-checked):
  T1  exact lane identities in the absolute region (s = 2.5, 3.0) to ~1e-8
  T2  incommensurate falsifier (m = sqrt2): no lattice partner, O(1) mismatch
  T3  no-gap cell profiles at 1/2: all cells, no fitting -- lattice m = 2 vs
      incommensurate vs unwarped; primitive growth exponents
  T4  FLAGSHIP -- the value law at the center:
        |F_2(1/2)|^2  =?  L(Sym3 f, 1/2) * C2(1/2)
        |F_3(1/2)|^2  =?  L(Sym4 f, 1/2)/zeta(1/2) * C3(1/2)   [modulus]
      F_2, F_3 are POLE-FREE (no DC lane).  Sym3 center from our evaluator
      (Q = 11^3, GammaC(s+3/2) GammaC(s+1/2)) + PARI lfunsympow cross-check;
      Sym4 center = 0.6058010 (certified + oracle-validated).

Parallel engineering (Sam: "heavier math -- parallelize"): the bank sieve is
vectorized (numpy fancy indexing per (p,k); reads only touch p-coprime
indices, so the scatter is race-free) -- timed against the scalar builder.

Run:  sage -python harmonic_lattice.py     (~2-4 min)
"""
import sys, os, math, cmath, time
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
import center_reading as CR
import farside_center as FC
from theta_cache import theta_table

TH1 = theta_table("11a1")
ORACLE_SYM3 = 1.14023086836474   # PARI lfun(lfunsympow(E,3), 2), fetched 2026-07-12

try:
    from sage.all import pari
    ORACLE = True
except Exception:
    ORACLE = False

mp.mp.dps = 25
NMAX = 200000
H = math.pi / 3
A1 = (0, -1, 1, -10, -20)
ALPHA = 1 / math.sqrt(11.0)


def local_coeffs_c(eigs, kmax):
    poly = np.array([1.0 + 0j])
    for e in eigs:
        poly = np.convolve(poly, np.array([1.0, -e]))
    c = np.zeros(kmax + 1, dtype=complex)
    c[0] = 1.0
    for k in range(1, kmax + 1):
        acc = 0j
        for j in range(1, min(k, len(poly) - 1) + 1):
            acc -= poly[j] * c[k - j]
        c[k] = acc
    return c


def fast_bank(eigs_fn, nmax):
    """Vectorized multiplicative sieve: for each (p,k) the reads lam[m] touch
    only p-coprime m (never written by p's own pass) -- race-free scatter."""
    lam = np.zeros(nmax + 1, dtype=complex)
    lam[1] = 1.0
    for p in SH.sieve_primes(nmax):
        kmax = int(math.log(nmax) / math.log(p))
        c = local_coeffs_c(eigs_fn(p), kmax)
        for k in range(kmax, 0, -1):
            pk = p ** k
            m = np.arange(1, nmax // pk + 1)
            m = m[m % p != 0]
            lam[m * pk] += c[k] * lam[m]
    return lam


def warp_eigs(m):
    def fn(p):
        if p == 11:
            return [ALPHA]
        th = float(TH1[p])
        return [cmath.exp(1j * (1 + m) * th), cmath.exp(1j * (m - 1) * th)]
    return fn


def sym_eigs(r):
    def fn(p):
        if p == 11:
            return [ALPHA ** r]
        th = float(TH1[p])
        return [cmath.exp(1j * (r - 2 * j) * th) for j in range(r + 1)]
    return fn


def dseries(lam, s):
    n = np.arange(1, len(lam), dtype=float)
    return complex((lam[1:] * n ** (-s)).sum())


def wsmooth_vec(u):
    w = np.zeros_like(u)
    w[u <= 0.5] = 1.0
    mid = (u > 0.5) & (u < 1.0)
    x = (u[mid] - 0.5) / 0.5
    a = np.exp(-1.0 / (1.0 - x))
    b = np.exp(-1.0 / x)
    w[mid] = a / (a + b)
    return w


def reader_c(lam, Y, s0=0.5):
    n = np.arange(1, len(lam), dtype=float)
    w = wsmooth_vec(np.log(n) / math.log(Y))
    return complex((lam[1:] * n ** (-s0) * w).sum())


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# HARMONIC LATTICE -- base unit theta_p, integer factors, the value law")
    P("#" * 78)
    P()

    # ---- banks (timed: vectorized vs scalar reference)
    t0 = time.time()
    F = {m: fast_bank(warp_eigs(m), NMAX) for m in (2, -2, 3, -3)}
    Fs2 = fast_bank(warp_eigs(math.sqrt(2)), NMAX)
    Fms2 = fast_bank(warp_eigs(-math.sqrt(2)), NMAX)
    S3 = fast_bank(sym_eigs(3), NMAX)
    t_vec = time.time() - t0
    t0 = time.time()
    _ = FC.build_bank("degenerate", 50000)     # scalar reference, 4x smaller
    t_ref = (time.time() - t0) * (NMAX / 50000.0)
    P(f"PARALLEL ENGINEERING: 7 degree-2..4 banks to {NMAX} in {t_vec:.1f}s")
    P(f"  (vectorized sieve; scalar builder extrapolates to ~{t_ref:.0f}s for")
    P(f"  ONE degree-16 bank at this size -- the sweep is now cheap)")
    P()

    # ---- T1: exact lane identities in the absolute region
    P("T1 -- exact lane identities (absolute region):")
    S4bank = CR.bank_sym_unitary(4, 20000)

    def S4val(s):
        return dseries(S4bank.astype(complex), s)

    for s in (2.5, 3.0):
        q = 11.0 ** (-s)
        z = complex(mp.zeta(s))
        lhs2 = dseries(F[2], s) * dseries(F[-2], s)
        rhs2 = dseries(S3, s) * (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2
        lhs3 = dseries(F[3], s) * dseries(F[-3], s)
        rhs3 = S4val(s) / z * (1 - ALPHA ** 4 * q) / ((1 - q) * (1 - ALPHA * q) ** 2)
        P(f"  s = {s}:  |F2 F-2 - Sym3*C2| = {abs(lhs2 - rhs2):.2e}   "
          f"|F3 F-3 - Sym4/zeta*C3| = {abs(lhs3 - rhs3):.2e}")
    P()

    # ---- T2: incommensurate falsifier
    P("T2 -- incommensurate falsifier (m = sqrt2, s = 2.5):")
    s = 2.5
    q = 11.0 ** (-s)
    lhsx = dseries(Fs2, s) * dseries(Fms2, s)
    cands = {"Sym3*C2": dseries(S3, s) * (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2,
             "Sym4/zeta*C3": (S4val(s) / complex(mp.zeta(s))
                              * (1 - ALPHA ** 4 * q)
                              / ((1 - q) * (1 - ALPHA * q) ** 2))}
    for k, v in cands.items():
        P(f"  |F_sqrt2 F_-sqrt2 - {k}| = {abs(lhsx - v):.3f}   (O(1) = no partner)")
    P()

    # ---- T3: no-gap cell profiles at 1/2 (parameter-free, ALL cells)
    P("T3 -- cell profiles at 1/2, ALL cells, no fitting:")
    cells = np.floor(np.log(np.arange(1, NMAX + 1)) / H).astype(int)
    ktop = cells.max()
    n = np.arange(1, NMAX + 1, dtype=float)
    for lab, lam in [("unwarped f", fast_bank(warp_eigs(0), NMAX)),
                     ("lattice m=2", F[2]), ("incomm m=sqrt2", Fs2)]:
        terms = lam[1:] * n ** -0.5
        D = np.array([abs(terms[cells == k].sum()) for k in range(2, ktop + 1)])
        cum = np.abs(np.cumsum(terms))
        gr = (math.log(cum[-1] + 1e-30) - math.log(cum[len(cum) // 8] + 1e-30)) \
            / (math.log(NMAX) - math.log(NMAX / 8.0))
        P(f"  {lab:16s} median|D| {np.median(D):.4f}  max|D| {D.max():.4f}  "
          f"gapiness max/med {D.max() / max(np.median(D), 1e-12):5.1f}  "
          f"primitive growth exp {gr:+.3f}")
    P()

    # ---- Sym3 center: our evaluator + oracle
    P("Sym3(11a1) center (Q = 11^3, GammaC(s+3/2) GammaC(s+1/2)):")
    G3 = CR.make_G(11 ** 3, [('C', 1.5), ('C', 0.5)])
    lam3r = S3.real.copy()
    e_a, r_a, _ = CR.certify(G3, lam3r, s0=2.5, T=60)
    e_b, r_b, _ = CR.certify(G3, lam3r, s0=2.2, T=60)
    P(f"  eps {e_a:+d}/{e_b:+d}, match {r_a:.2e}, {r_b:.2e}")
    L3 = CR.central_value(G3, e_a, lam3r, T=60).real if e_a == e_b else None
    if L3 is not None:
        P(f"  our L(Sym3, 1/2)_u = {L3:.7f}")
    P(f"  PARI lfunsympow:     {ORACLE_SYM3:.7f}   |diff| = "
      f"{abs(ORACLE_SYM3 - (L3 if L3 else 0)):.2e}")
    if L3 is None:
        L3 = ORACLE_SYM3
    P()

    # ---- T4: FLAGSHIP -- the value law at the center
    P("T4 -- FLAGSHIP: the value-registration law at the center:")
    z_half = float(mp.zeta(0.5))
    q = 11.0 ** -0.5
    C2 = (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2
    C3 = (1 - ALPHA ** 4 * q) / ((1 - q) * (1 - ALPHA * q) ** 2)
    for m, rhs, lab in [(2, (L3 or 0) * C2, "L(Sym3,1/2)*C2"),
                        (3, 0.6058010 / abs(z_half) * C3, "L(Sym4,1/2)/|zeta(1/2)|*C3")]:
        P(f"  m = {m}: window ladder for F_{m}(1/2):")
        vals = []
        for Y in (4000, 16000, 64000, 120000):
            R = reader_c(F[m], Y)
            vals.append(R)
            P(f"    Y = {Y:7d}   F(1/2) = {R.real:+.6f} {R.imag:+.6f}i   "
              f"|F|^2 = {abs(R) ** 2:.6f}")
        stab = abs(vals[-1] - vals[-2])
        lhs = abs(vals[-1]) ** 2
        P(f"    stability {stab:.4f};  |F_{m}(1/2)|^2 = {lhs:.6f}   "
          f"vs {lab} = {rhs:.6f}   ratio {lhs / rhs if rhs else float('nan'):.4f}")
    P()
    P("  incommensurate control at 1/2 (must NOT stabilize to any law):")
    vx = [reader_c(Fs2, Y) for Y in (16000, 64000, 120000)]
    P(f"    F_sqrt2(1/2) ladder: " + "  ".join(f"{abs(v):.4f}" for v in vx)
      + f"   drift {abs(vx[-1] - vx[-2]):.4f}")
    P()

    P("READING (two-sided, pre-registered):")
    P("  T1 machine-zero => the lane identities are exact: integer multiples of")
    P("  the base unit theta_p ARE the Sym tower; T2 O(1) => no identity off the")
    P("  lattice (harmonic compatibility is the law, not a preference).  T4 is")
    P("  the decisive row: if |F_m(1/2)|^2 lands on the certified RHS, the")
    P("  value-registration law has its first measured instances -- the missing")
    P("  piece named by the adapted-center falsifier now has a working form;")
    P("  next rung: the same law on RS4-scale warps, then the quadruple's")
    P("  identity graph (parallel sweep).  If it misses, the miss and its size")
    P("  are the finding.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "harmonic_lattice_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to harmonic_lattice_results.txt]")


if __name__ == "__main__":
    main()
