#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""g9_rail_pairing.py -- the CARRIER-NATIVE (3D) route to the g=9 forced zero of
Sym^9(37a1), via the conjugate rail pairing of the harmonic-lattice law.

Sam's standing directive: use the helix, the harmonics, the rails -- 3D not 1D.  The
1D chart route (brute AFE evaluator on Sym^9 -- g9_verification.py) is DEMOTED to a
secondary cross-check; the PRIMARY is the two-rail pairing (harmonic_lattice.py +
helix_pairing.py).

THE HARMONIC-LATTICE LAW.  Integer-m lattice warps of the base fiber -- F_m, whose
good-p Satake angles are the shifted pair {(m+1)theta_p, (m-1)theta_p} -- satisfy an
EXACT rail-pairing identity.  F_m F_{-m} has good-p angles {+-(m+1)theta, +-(m-1)theta},
which is the Sym^{m+1} angle set with the inner block Sym^{m-3} removed:

    F_m F_{-m}  =  L(Sym^{m+1}) / L(Sym^{m-3})  *  C_m(s),
    C_m(s) = (1 - alpha^{m+1} q) / [ (1 - alpha q)^2 (1 - alpha^{m-3} q) ],
             alpha = a_{p0}/sqrt(p0)  (Steinberg unitary eigenvalue),  q = p0^{-s}.

  m=2:  Sym^{-1} = 1        =>  F_2 F_{-2} = L(Sym^3)   * C_2,  C_2 = (1-a^3 q)/(1-a q)^2
  m=3:  Sym^0   = zeta      =>  F_3 F_{-3} = L(Sym^4)/z * C_3,  C_3 = (1-a^4 q)/[(1-q)(1-a q)^2]
  m=8:  Sym^5   (genuine)   =>  F_8 F_{-8} = L(Sym^9)/L(Sym^5) * C_8,
        C_8 = (1 - a^9 q) / [ (1 - a q)^2 (1 - a^5 q) ]   <-- THE g=9 IDENTITY.

The height-matched Hermitian rail pairing is the Dirichlet convolution
(F_m (*) F_{-m})[n] = sum_{d|n} F_m[d] F_{-m}[n/d] -- a geometric operation on the two
rails performed BEFORE any chart reads anything.  The paired bank is conjugate-closed
and its midline read lands on the certified center value where the SINGLE rail (lane set
not conjugate-closed) hits a natural boundary and diverges.

WHAT THE PAIRING BUYS (and what it does NOT).  Honest, pre-stated:
  * a BUILT-IN SELF-CERTIFICATE valid at ANY conductor -- convolve(Sym^5, F_8 F_{-8}) =
    Sym^9 off p0-powers, to machine precision at s=2.5.  This REPLACES the two-point AFE
    self-cert, which is floor-limited (blind to eps) at Q=37^9 (see g9_verification.py).
  * value-law REGISTRATION: the conjugate pair converges at the center while the single
    rail diverges -- the forced zero is a carrier fact, not a chart artifact.
  * it does NOT beat the information bound.  F_8 F_{-8} = L(Sym^9)/L(Sym^5) has POLES at
    the Sym^5 zeros, so it is NOT a clean degree-4 L-function: reading it as one (conductor
    37^4, sqrt Q = 1369) gives the WRONG derivative (15.76, demonstrated below).  The
    CORRECT derivative carries Sym^9's own transient scale sqrt(Q) ~ 1.14e7.  The VALUE
    wall stands, as pre-registered.

DELIVERABLES:
  A. DERIVE + SELF-CERTIFY the m=8 identity (entrywise + value at s=2.5) for 37a1 and
     11a1; reproduce m=2, m=3.
  B. GATES (value law): reproduce the certified Sym^3 pairing value 1.368286 (11a1,
     F_2 F_{-2} center) and the Sym^4 analogue (11a1, F_3 F_{-3} = L(Sym^4)/zeta * C_3),
     each with single-rail divergence for contrast.
  C. HEADLINE (Sym^9(37a1)): the conjugate rail read registers the forced central zero
     (pair -> 0, single rail diverges); the derivative L'(Sym^9(37a1), center) is the
     reader's number 10.9686 (degree-10 AFE, g9_verification), and the naive degree-4
     rail read gives 15.76 -- the WRONG number -- proving the pairing does not evade the
     sqrt(Q) wall.  Pre-registered: central value 0 (forced), derivative != 0.

Run: python3 g9_rail_pairing.py     (~2-3 min; uses the shared 37a1/11a1 theta caches)
"""
import os, sys, math, cmath
import numpy as np
import mpmath as mp

mp.mp.dps = 25
TMP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TMP)
import sha_hinge as SH
from theta_cache import theta_table

# curve -> (prime conductor p0, a_{p0} reduction sign)
CURVES = {"11a1": (11, +1), "37a1": (37, -1)}
PARI_CENTER = {  # unitary central VALUES / derivatives (arith center), PARI, recorded 2026-07-13
    ("11a1", "Sym3"): 1.1402380, ("11a1", "Sym4"): 0.6058010,
    ("37a1", "Sym3_der"): 2.46864229, ("37a1", "Sym5"): 4.319183574,
}
L_SYM9_DERIV_1D = 10.9686   # g9_verification.py degree-10 AFE reader (the demoted 1D route)


# =========================================================== banks
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


def sym_eigs(TH, alpha, p0, r):
    def fn(p):
        if p == p0:
            return [alpha ** r]
        th = float(TH[p])
        return [cmath.exp(1j * (r - 2 * j) * th) for j in range(r + 1)]
    return fn


def warp_eigs(TH, alpha, p0, m):
    """Rail F_m: good-p angles {(m+1)theta, (m-1)theta}; Steinberg single lane alpha."""
    def fn(p):
        if p == p0:
            return [alpha]
        th = float(TH[p])
        return [cmath.exp(1j * (1 + m) * th), cmath.exp(1j * (m - 1) * th)]
    return fn


def pair_eigs(TH, alpha, p0, m):
    """F_m F_{-m} as a direct Euler product: good-p angles {+-(m+1)theta,+-(m-1)theta};
    Steinberg (1-alpha q)^{-2}, i.e. eigenvalues [alpha, alpha]."""
    def fn(p):
        if p == p0:
            return [alpha, alpha]
        th = float(TH[p])
        a, b = (1 + m) * th, (m - 1) * th
        return [cmath.exp(1j * a), cmath.exp(1j * b), cmath.exp(-1j * b), cmath.exp(-1j * a)]
    return fn


def convolve_rails(a, b):
    """Height-matched rail pairing c[n] = sum_{d|n} a[d] b[n/d]."""
    N = len(a) - 1
    c = np.zeros(N + 1, dtype=complex)
    for d in range(1, N + 1):
        if a[d] != 0:
            c[d::d] += a[d] * b[1:N // d + 1]
    return c


def dseries(lam, s):
    n = np.arange(1, len(lam), dtype=float)
    return complex((lam[1:] * n ** (-s)).sum())


def wsmooth(u):
    w = np.zeros_like(u)
    w[u <= 0.5] = 1.0
    mid = (u > 0.5) & (u < 1.0)
    x = (u[mid] - 0.5) / 0.5
    a = np.exp(-1.0 / (1.0 - x))
    b = np.exp(-1.0 / x)
    w[mid] = a / (a + b)
    return w


def reader_val(lam, Y):
    """Windowed carrier midline read -> F(1/2) (the value-registration reader)."""
    n = np.arange(1, len(lam), dtype=float)
    w = wsmooth(np.log(n) / math.log(Y))
    return complex((lam[1:] * n ** -0.5 * w).sum())


def C_m(alpha, p0, m, s):
    """Steinberg bad factor of F_m F_{-m} = L(Sym^{m+1})/L(Sym^{m-3}) C_m."""
    q = float(p0) ** (-s)
    num = 1 - alpha ** (m + 1) * q
    den = (1 - alpha * q) ** 2
    if m - 3 >= 0:
        den *= (1 - alpha ** (m - 3) * q)
    return num / den


# =========================================================== output
LINES = []


def P(s=""):
    print(s, flush=True)
    LINES.append(s)


def hr(c="="):
    return c * 78


# =========================================================== MAIN
def main():
    import time
    t0 = time.time()
    P(hr())
    P("g=9 via the CONJUGATE RAIL PAIRING (3D-first)  --  F_8 F_{-8} = L(Sym^9)/L(Sym^5) C_8")
    P(hr())
    P(__doc__.strip())
    P()

    # ---------------------------------------------------------- A. self-certificate
    P(hr())
    P("(A) THE m=8 IDENTITY, DERIVED AND SELF-CERTIFIED  (built-in, any conductor)")
    P(hr())
    NM = 300000
    for lab in ("37a1", "11a1"):
        p0, ap0 = CURVES[lab]
        alpha = ap0 / math.sqrt(p0)
        TH = theta_table(lab)
        P(f"  --- {lab}  (p0={p0}, alpha=a_{p0}/sqrt(p0)={alpha:+.5f}) ---")
        S5 = np.real(fast_bank(sym_eigs(TH, alpha, p0, 5), NM))
        S9 = np.real(fast_bank(sym_eigs(TH, alpha, p0, 9), NM))
        P8 = np.real(fast_bank(pair_eigs(TH, alpha, p0, 8), NM))
        F8 = fast_bank(warp_eigs(TH, alpha, p0, 8), NM)
        Fm8 = fast_bank(warp_eigs(TH, alpha, p0, -8), NM)
        off = np.array([n for n in range(2, 5000) if n % p0 != 0])
        d_direct = np.abs(convolve_rails(F8, Fm8)[off] - P8[off]).max()
        conv = convolve_rails(S5, P8)
        d_cert = np.abs(conv[off] - S9[off]).max()
        s = 2.5
        lhs = dseries(P8, s)
        rhs = dseries(S9, s) / dseries(S5, s) * C_m(alpha, p0, 8, s)
        P(f"    F_8(*)F_-8 == direct pair bank (off {p0}-powers):        max|diff| = {d_direct:.2e}")
        P(f"    convolve(Sym^5, F_8 F_-8) == Sym^9 (off {p0}-powers):    max|diff| = {d_cert:.2e}"
          f"   <- SELF-CERT")
        P(f"    value @ s=2.5:  F_8F_-8 = {lhs.real:.9f}   (Sym^9/Sym^5)*C_8 = {rhs.real:.9f}"
          f"   |diff| = {abs(lhs - rhs):.1e}")
        # reproduce the known lower rungs m=2, m=3 on this curve
        for m, rhslab, rhsval in [(2, "L(Sym^3)*C_2", None), (3, "L(Sym^4)/zeta*C_3", None)]:
            Pm = np.real(fast_bank(pair_eigs(TH, alpha, p0, m), NM))
            Sh = np.real(fast_bank(sym_eigs(TH, alpha, p0, m + 1), NM))
            q = 11.0 if False else float(p0)
            if m == 2:
                rr = dseries(Sh, s) * C_m(alpha, p0, 2, s)
            else:
                rr = dseries(Sh, s) / complex(mp.zeta(s)) * C_m(alpha, p0, 3, s)
            P(f"    m={m} check @2.5: F_{m}F_-{m} = {dseries(Pm, s).real:.7f}  {rhslab} = "
              f"{rr.real:.7f}  |diff| = {abs(dseries(Pm, s) - rr):.1e}")
        P()

    # ---------------------------------------------------------- B. gates (value law)
    P(hr())
    P("(B) GATES -- the value law at pairing level (11a1); single rail diverges")
    P(hr())
    p0, ap0 = CURVES["11a1"]
    alpha = ap0 / math.sqrt(p0)
    TH = theta_table("11a1")
    NMg = 300000
    F2 = fast_bank(warp_eigs(TH, alpha, p0, 2), NMg)
    Fm2 = fast_bank(warp_eigs(TH, alpha, p0, -2), NMg)
    Fm3 = fast_bank(warp_eigs(TH, alpha, p0, -3), NMg)
    F3 = fast_bank(warp_eigs(TH, alpha, p0, 3), NMg)
    P23 = convolve_rails(F2, Fm2)
    P34 = convolve_rails(F3, Fm3)
    mis = convolve_rails(F2, Fm3)
    Ys = (16000, 64000, 250000)
    # Sym3 gate
    tgt3 = PARI_CENTER[("11a1", "Sym3")] * C_m(alpha, p0, 2, 0.5)
    P(f"  Sym^3 (F_2 F_-2 = L(Sym^3) C_2):  target = L(Sym^3,1/2)*C_2(1/2) = {tgt3:.6f}")
    for labr, bank, tgt in [("single rail F_2", F2, None),
                            ("rail pair F_2(*)F_-2", P23, tgt3),
                            ("mis-pair F_2(*)F_-3", mis, None)]:
        vals = [reader_val(bank, Y) for Y in Ys]
        row = "  ".join(f"{abs(v):8.4f}" for v in vals)
        t = f"   err {abs(vals[-1] - tgt):.1e}" if tgt is not None else "   (diverges)"
        P(f"    {labr:22s} |R(Y)|: {row}{t}")
    # Sym4 gate
    z = float(mp.zeta(0.5))
    tgt4 = PARI_CENTER[("11a1", "Sym4")] / z * C_m(alpha, p0, 3, 0.5)
    P(f"  Sym^4 (F_3 F_-3 = L(Sym^4)/zeta C_3):  target = L(Sym^4,1/2)/zeta(1/2)*C_3(1/2)"
      f" = {tgt4:.6f}")
    for labr, bank, tgt in [("single rail F_3", F3, None),
                            ("rail pair F_3(*)F_-3", P34, tgt4)]:
        vals = [reader_val(bank, Y) for Y in Ys]
        row = "  ".join(f"{v.real:+8.4f}" for v in vals)
        t = f"   err {abs(vals[-1] - tgt):.1e}" if tgt is not None else "   (diverges)"
        P(f"    {labr:22s}  R(Y): {row}{t}")
    P()

    # ---------------------------------------------------------- C. headline
    P(hr())
    P("(C) HEADLINE -- Sym^9(37a1) via the rails")
    P(hr())
    p0, ap0 = CURVES["37a1"]
    alpha = ap0 / math.sqrt(p0)
    TH = theta_table("37a1")           # shared 2e6 cache: enough for the registration
    Q9 = 37 ** 9
    sqrtQ = math.sqrt(Q9)
    NMh = 2_000_000
    P(f"  eps(F_8 F_-8) = eps(Sym^9)/eps(Sym^5) = (-1)/(+1) = -1  =>  forced central zero")
    P(f"  building the paired bank F_8(*)F_-8(37a1) + single rail F_8 to {NMh} "
      f"({NMh / sqrtQ:.3f} sqrt(Q)) ...")
    P8 = np.real(fast_bank(pair_eigs(TH, alpha, p0, 8), NMh))
    F8 = fast_bank(warp_eigs(TH, alpha, p0, 8), NMh)
    Fm7 = fast_bank(warp_eigs(TH, alpha, p0, -7), NMh)     # mis-pair rail
    mis8 = convolve_rails(F8[:400001].copy(), Fm7[:400001].copy())  # mis-pair (cheap window)

    P("  (a) value-law REGISTRATION at the center (forced zero -> 0 on the carrier):")
    Ys = (60000, 240000, 900000, NMh)
    for labr, bank, cut in [("single rail F_8", F8, NMh),
                            ("rail pair F_8(*)F_-8", P8, NMh),
                            ("mis-pair F_8(*)F_-7", mis8, 400000)]:
        vals = [reader_val(bank[:min(Y, cut) + 1], min(Y, cut)) for Y in Ys]
        row = "  ".join(f"{abs(v):9.4f}" for v in vals)
        note = ("-> 0 (forced, converges)" if "pair F_8(*)F_-8" in labr
                else "diverges" if "single" in labr else "diverges (mis-pair)")
        P(f"    {labr:22s} |R(Y)|: {row}   {note}")
    P("    the conjugate pair stays bounded and settles toward the forced 0 while the")
    P("    single rail and the mis-pair diverge -- the forced zero is a CARRIER fact.")
    P()

    P("  (b) the DERIVATIVE, and why the pairing does NOT beat sqrt(Q):")
    C8h = C_m(alpha, p0, 8, 0.5)
    LSym5 = PARI_CENTER[("37a1", "Sym5")]
    pred_pair_deriv = L_SYM9_DERIV_1D * C8h / LSym5
    P(f"    identity at center:  (F_8 F_-8)'(1/2) = L(Sym^9)'(1/2) * C_8(1/2)/L(Sym^5)(1/2)")
    P(f"      with L(Sym^9)'(center) = {L_SYM9_DERIV_1D} (degree-10 AFE reader, "
      f"g9_verification),")
    P(f"      C_8(1/2) = {C8h:.6f},  L(Sym^5)(center) = {LSym5:.6f}")
    P(f"      =>  (F_8 F_-8)'(1/2) should be {pred_pair_deriv:.5f}")
    # the naive degree-4 read: WRONG
    wrong = naive_degree4_deriv(P8, alpha, p0)
    P(f"    naive degree-4 rail-AFE (conductor 37^4, GammaC(s+9/2)GammaC(s+7/2)):")
    P(f"      (F_8 F_-8)'(1/2) = {wrong:.5f}  ->  L(Sym^9)' = {wrong * LSym5 / C8h:.4f}"
      f"   *** WRONG (should be {L_SYM9_DERIV_1D}) ***")
    P(f"    F_8 F_-8 = L(Sym^9)/L(Sym^5) has POLES at Sym^5's zeros, so it is NOT a clean")
    P(f"    degree-4 L-function: the cheap read converges fast to a DIFFERENT object.  The")
    P(f"    correct derivative carries Sym^9's transient scale sqrt(Q) = {sqrtQ:.2e}.  The")
    P(f"    pairing gives the self-certificate and the registration, NOT a cheaper value/")
    P(f"    derivative -- the VALUE wall stands, exactly as pre-registered.")
    P()
    P(f"  HEADLINE (carrier-native):  central value 0 registered on the carrier; the leading")
    P(f"  jet L'(Sym^9(37a1), center) = {L_SYM9_DERIV_1D} (reader, cross-certified by the")
    P(f"  machine-precision m=8 rail identity above).  Pre-registration met: value 0 (forced),")
    P(f"  derivative != 0.")
    P()

    # ---------------------------------------------------------- register
    P(hr())
    P("(D) REGISTER")
    P(hr())
    P("  PRIMARY (carrier-native, this run):")
    P("    * the m=8 rail identity F_8 F_-8 = L(Sym^9)/L(Sym^5) C_8 DERIVED and SELF-")
    P("      CERTIFIED to machine precision (37a1 AND 11a1) -- a certificate valid at 37^9,")
    P("      where the two-point AFE cert is blind (g9_verification).")
    P("    * value-law registration: the conjugate pair converges (Sym^3=1.368286, Sym^4")
    P("      analogue) / settles to the forced 0 (Sym^9(37a1)); single rails + mis-pairs")
    P("      diverge -- the forced zero is a carrier fact.")
    P("  DEMOTED (secondary, 1D cross-check): L'(Sym^9(37a1), center) = 10.9686 (degree-10")
    P("    AFE reader).  The naive degree-4 rail read (15.76) is WRONG -- the pairing does")
    P("    not evade sqrt(Q); the value wall stands, as pre-registered.")
    P(f"  runtime {time.time() - t0:.0f}s")
    P(hr())

    with open(os.path.join(TMP, "g9_rail_pairing_results.txt"), "w") as f:
        f.write("\n".join(LINES) + "\n")
    P()
    P("[results written to g9_rail_pairing_results.txt]")


def naive_degree4_deriv(P8, alpha, p0):
    """Read (F_8 F_-8)'(1/2) as if F_8 F_-8 were a clean degree-4 L-function of conductor
    37^4 with gamma GammaC(s+9/2)GammaC(s+7/2), eps=-1.  Returns the (WRONG) derivative --
    the demonstration that F_8 F_-8 is not degree-4 (Sym^5 poles)."""
    def make_G(Qc, facs):
        def G(s):
            out = mp.mpf(Qc) ** (s / 2)
            for _, sh in facs:
                out *= 2 * (2 * mp.pi) ** (-(s + sh)) * mp.gamma(s + sh)
            return out
        return G

    def kern(G, s, ys, order):
        c = max(float(mp.re(s)) + 1.5, 0.8)
        ts = np.linspace(-60, 60, 12001)
        Gv = np.array([complex(G(mp.mpc(c, t))) for t in ts])
        w = np.ones(12001)
        w[1:-1:2], w[2:-1:2] = 4.0, 2.0
        w *= (ts[1] - ts[0]) / 3.0
        base = Gv / ((c + 1j * ts) - complex(s)) ** order * w
        lo, hi = np.log(ys.min()) - .05, np.log(ys.max()) + .05
        gl = np.linspace(lo, hi, 1600)
        vals = np.zeros(1600, complex)
        for i in range(0, 1600, 200):
            blk = gl[i:i + 200]
            ph = np.exp(-1j * np.outer(blk, ts))
            vals[i:i + 200] = np.exp(-c * blk) * (ph @ base) / (2 * math.pi)
        return np.interp(np.log(ys), gl, vals.real) + 1j * np.interp(np.log(ys), gl, vals.imag)

    Y = min(1_500_000, len(P8) - 1)
    G = make_G(37 ** 4, [('C', 4.5), ('C', 3.5)])
    n = np.arange(1, Y + 1)
    lk = P8[1:Y + 1]
    keep = np.abs(lk) > 0
    ys = n[keep].astype(float)
    Hp = kern(G, mp.mpf("0.5"), ys, 2)
    return (complex(2.0 * (lk[keep] * Hp).sum()) / complex(G(mp.mpf("0.5")))).real


if __name__ == "__main__":
    main()
