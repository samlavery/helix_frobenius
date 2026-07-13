"""The harmonic Hodge structure, calibrated where the answer is known.

The companion paper's harmonic frame reads a weight-n Hodge structure as a clock
system: the Deligne torus acts on H^{p,q} by r^{-n} e^{i theta (q-p)}, so

  weight        = radial rate (ledger radius channel),
  H^{p,q}       = clock channel at frequency k = q - p,
  Hodge class   = RATIONAL DC MODE (k = 0 channel, rational amplitude),
  Hodge symmetry= chiral pairing k <-> -k (helix / anti-helix lanes).

This instrument calibrates that frame on weight-2 surfaces E1 x E2, where the
Hodge conjecture is a THEOREM (Lefschetz (1,1)): the DC occupancy of the (1,1)
channel -- the Picard number rho -- is read two independent ways and compared.

  CLOCK READING (periods; archimedean side).  Each curve's period lattice gives
  tau in the upper half-plane -- the curve's clock.  Extra DC modes of E1 x E2
  are CLOCK ALIGNMENTS: a degree-n Hecke correspondence (a tau1 + b)/d matching
  tau2 (isogeny = the two clocks phase-lock), certified against the EXACT
  algebraic j-invariant j = c4^3/Delta of the target curve -- so the period
  computation is self-validating, no table consulted.  CM = self-alignment
  (tau satisfies an integer quadratic; the clock has extra symmetry).

  COUNT READING (point counts; arithmetic side).  The DC occupancy is read as
  the carrier reads every DC mode -- as a residue/moment:
    m11 = mean over good p of b1(p) b2(p),  b = a_p / sqrt(p)
        -> the Rankin-Selberg pole order = # Q-rational alignments (0 or 1);
    m4  = mean of b^4 per curve -> 2 (generic) vs 3 (CM): the depth-2 channel
        that carries the CM alignment (rational only over the CM field K --
        the ledger's ANGLE channel records the field of definition, so the
        Q-moment sees it one tower level up, exactly the delayed signature).
    ss  = density of a_p = 0 -> 0 vs 1/2 (the CM inert lock), corroboration.

  VERDICT: rho_clock = rho_count = known rho on every case, or the harmonic
  frame dies here (it would be measuring the wrong thing).

Cases (all curve data certified in-instrument -- a_p agreement for the isogeny
pair, exact j for every period computation):
  A  11a1 x 37a1   no alignment                 rho = 2
  B  11a1 x 11a2   5-isogeny alignment          rho = 3
  C  11a1 x 11a1   self (generic)               rho = 3
  D  32a1 x 32a1   self, CM disc -4             rho = 4
  E  27a1 x 27a1   self, CM disc -3             rho = 4
  F  27a1 x 32a1   two special clocks, NOT      rho = 2
                   mutually aligned (different CM fields)

Run: python3 hodge_clock_demo.py [X]     (default X = 30000; ~2 min, oracle-free)
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH

CURVES = {
    "11a1": (11, (0, -1, 1, -10, -20)),
    "11a2": (11, (0, -1, 1, -7820, -263580)),
    "37a1": (37, (0, 0, 1, -1, 0)),
    "32a1": (32, (0, 0, 0, -1, 0)),
    "27a1": (27, (0, 0, 1, 0, 0)),
}

CASES = [
    ("A", "11a1", "37a1", 2, "no alignment"),
    ("B", "11a1", "11a2", 3, "5-isogeny alignment"),
    ("C", "11a1", "11a1", 3, "self, generic clock"),
    ("D", "32a1", "32a1", 4, "self, CM"),
    ("E", "27a1", "27a1", 4, "self, CM"),
    ("F", "27a1", "32a1", 2, "two CM clocks, different fields"),
]


# ---------------------------------------------------------------- periods ---
def cagm(a, b, tol=1e-15):
    """Complex AGM with the optimal (|a-b| <= |a+b|) branch at every step."""
    for _ in range(200):
        if abs(a - b) <= tol * max(abs(a), 1e-300):
            break
        m = 0.5 * (a + b)
        s = cmath.sqrt(a * b)
        if abs(m - s) > abs(m + s):
            s = -s
        a, b = m, s
    return a


def sl2_reduce(tau):
    """Reduce tau to the standard fundamental domain."""
    for _ in range(200):
        tau = complex(tau.real - round(tau.real), tau.imag)
        if abs(tau) < 1 - 1e-14:
            tau = -1 / tau
        else:
            break
    if tau.imag < 0:
        tau = complex(tau.real, -tau.imag)
    return tau


def jfun(tau):
    """j(tau) = E4^3 / Delta with Delta by the eta product q prod (1-q^n)^24 ---
    no E4^3 - E6^2 cancellation, so machine precision at every Im tau (large
    Im tau means huge j ~ 1/q, computed stably)."""
    q = cmath.exp(2j * math.pi * tau)
    if abs(q) < 1e-250:
        return complex(float("inf"), 0.0)
    E4 = 1.0 + 0j
    D = q
    qn = q
    for n in range(1, 6000):
        if abs(qn) < 1e-22:
            break
        E4 += 240.0 * (n ** 3) * qn / (1 - qn)
        D *= (1 - qn) ** 24
        qn *= q
    return E4 ** 3 / D


def j_exact(ainv):
    inv = SH.invariants(ainv)
    return inv["c4"] ** 3 / inv["disc"]


def curve_tau(ainv):
    """tau = omega2/omega1 of the period lattice, self-certified by the exact j.

    Roots of the completed-square cubic x^3 + (b2/4)x^2 + (b4/2)x + b6/4 and the
    two complex AGMs are computed in mpmath working precision (near-double root
    pairs occur whenever the minimal discriminant is tiny against the
    coefficients -- e.g. 11a2, disc -11 with coefficients ~2.6e5 -- and float
    eigenvalue roots lose exactly the digits the AGM needs).  The ordering /
    branch is ACCEPTED only if j(tau_reduced) matches the exact algebraic
    j = c4^3/Delta.
    """
    import mpmath as mp
    mp.mp.dps = 50
    inv = SH.invariants(ainv)
    b2, b4, b6 = inv["b2"], inv["b4"], inv["b6"]
    roots = mp.polyroots([mp.mpf(1), mp.mpf(b2) / 4, mp.mpf(b4) / 2,
                          mp.mpf(b6) / 4], maxsteps=200, extraprec=100)
    roots = [mp.mpc(r) for r in roots]

    def mp_cagm(a, b):
        for _ in range(300):
            if abs(a - b) <= mp.mpf("1e-45") * max(abs(a), mp.mpf("1e-300")):
                break
            m = (a + b) / 2
            s = mp.sqrt(a * b)
            if abs(m - s) > abs(m + s):
                s = -s
            a, b = m, s
        return a

    jex = j_exact(ainv)
    from itertools import permutations
    best = None
    for (r1, r2, r3) in permutations(roots):
        M1 = mp_cagm(mp.sqrt(r1 - r3), mp.sqrt(r1 - r2))
        M2 = mp_cagm(mp.sqrt(r1 - r3), mp.sqrt(r2 - r3))
        if abs(M1) < mp.mpf("1e-40") or abs(M2) < mp.mpf("1e-40"):
            continue
        tau_mp = (2j * mp.pi / M2) / (2 * mp.pi / M1)
        tau = complex(float(tau_mp.real), float(tau_mp.imag))
        if abs(tau.imag) < 1e-12:
            continue
        taur = sl2_reduce(tau if tau.imag > 0 else -tau)
        jv = jfun(taur)
        err = abs(jv - jex) / (1.0 + abs(jex))
        if best is None or err < best[0]:
            best = (err, taur)
    err, taur = best
    return taur, err


def hecke_alignments(tau1, jex2, nmax=36, tol=1e-6):
    """Degree-n clock alignments: primitive (a b; 0 d), ad = n, 0 <= b < d, with
    j((a tau1 + b)/d) = j_exact(E2).  Returns sorted list of (n, residual)."""
    hits = []
    for n in range(1, nmax + 1):
        for a in range(1, n + 1):
            if n % a:
                continue
            d = n // a
            for b in range(d):
                if math.gcd(math.gcd(a, b), d) != 1:
                    continue
                tp = (a * tau1 + b) / d
                jv = jfun(sl2_reduce(tp))
                if abs(jv - jex2) / (1.0 + abs(jex2)) < tol:
                    hits.append((n, abs(jv - jex2) / (1.0 + abs(jex2))))
    return sorted(set(h[0] for h in hits)), hits


def cm_disc(tau, amax=12, cmax=200, tol=1e-8):
    """Integer quadratic a tau^2 + b tau + c ~ 0 (gcd 1): the clock's extra
    symmetry.  Returns the discriminant b^2 - 4ac, or None."""
    best = None
    for a in range(1, amax + 1):
        # b, c from the real/imag parts: b = -a*2Re(tau)*? solve directly
        b_approx = -a * 2 * tau.real if abs(tau.real) > 1e-9 else 0.0
        for b in range(int(b_approx) - 2, int(b_approx) + 3):
            c_approx = -(a * (tau * tau) + b * tau).real
            for c in range(int(round(c_approx)) - 1, int(round(c_approx)) + 2):
                if abs(c) > cmax:
                    continue
                g = math.gcd(math.gcd(a, abs(b)), abs(c))
                if g != 1:
                    continue
                res = abs(a * tau * tau + b * tau + c)
                if res < tol * a * (1 + abs(tau)) ** 2:
                    D = b * b - 4 * a * c
                    if D < 0 and (best is None or res < best[1]):
                        best = (D, res)
    return None if best is None else best[0]


# ----------------------------------------------------------------- counts ---
def moment_data(labels, X):
    prs = SH.sieve_primes(X)
    banks = {}
    for lab in labels:
        N, ainv = CURVES[lab]
        bs = {}
        for p in prs:
            if N % p == 0:
                continue
            bs[p] = SH.ap_general(p, *ainv) / math.sqrt(p)
        banks[lab] = bs
    return banks


def main():
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# HODGE CLOCK DEMO -- the harmonic Hodge frame, calibrated on Lefschetz (1,1)")
    P(f"# weight-2 surfaces E1 x E2; DC occupancy rho read two ways; X = {X}")
    P("#" * 78)
    P()

    # ---- clock side: periods, self-certified by exact j
    P("CLOCK SIDE (periods; archimedean).  tau self-certified against exact j:")
    taus, jerrs = {}, {}
    for lab in CURVES:
        tau, err = curve_tau(CURVES[lab][1])
        taus[lab], jerrs[lab] = tau, err
        D = cm_disc(tau)
        cm = f"CM disc {D}" if D is not None else "generic"
        P(f"  {lab}: tau = {tau.real:+.6f} {tau.imag:+.6f}i   "
          f"|j(tau)-j_exact|/(1+|j|) = {err:.2e}   [{cm}]")
    cert_ok = all(e < 1e-6 for e in jerrs.values())
    P(f"  period certificate: {'PASS' if cert_ok else 'FAIL'} "
      f"(every tau reproduces its curve's exact algebraic j)")
    P()

    # in-house isogeny certificate for the 11a pair
    prs_c = [p for p in SH.sieve_primes(400) if 11 % p != 0 and p != 11]
    dev = max(abs(SH.ap_general(p, *CURVES["11a1"][1]) -
                  SH.ap_general(p, *CURVES["11a2"][1])) for p in prs_c)
    P(f"  [certificate] 11a1/11a2 a_p agreement (good p < 400): max dev = {dev}")
    P()

    # ---- count side: moments
    P(f"COUNT SIDE (point counts; arithmetic).  good p <= {X}:")
    banks = moment_data(list(CURVES), X)
    m4, ss = {}, {}
    for lab in CURVES:
        bs = np.array(list(banks[lab].values()))
        m4[lab] = float((bs ** 4).mean())
        ss[lab] = float((np.abs(bs) < 1e-12).mean())
        P(f"  {lab}: m4 = {m4[lab]:.3f} (2 generic / 3 CM)   "
          f"ss-density = {ss[lab]:.3f} (0 / 0.5)")
    P()

    # ---- cases
    P("CASES -- DC occupancy of the (1,1) channel, two readings vs known truth:")
    P(f"  {'case':4s} {'pair':14s} {'align(deg)':>11s} {'CM':>6s} "
      f"{'m11':>7s} {'rho_clock':>9s} {'rho_count':>9s} {'known':>5s} {'OK':>3s}")
    all_ok = True
    for cid, l1, l2, rho_known, desc in CASES:
        # clock reading
        degs, _ = hecke_alignments(taus[l1], j_exact(CURVES[l2][1]))
        self_pair = (l1 == l2)
        if self_pair:
            degs_nontriv = [n for n in degs if n > 1]
            aligned = True
            D = cm_disc(taus[l1])
            rho_clock = 2 + 1 + (1 if D is not None else 0)
            align_str = "self" + (f"+{degs_nontriv[0]}" if degs_nontriv else "")
            cm_str = str(D) if D is not None else "-"
        else:
            aligned = len(degs) > 0
            rho_clock = 2 + (1 if aligned else 0)
            align_str = ",".join(str(n) for n in degs[:3]) if aligned else "none"
            cm_str = "-"
        # count reading
        ps = sorted(set(banks[l1]) & set(banks[l2]))
        b1 = np.array([banks[l1][p] for p in ps])
        b2 = np.array([banks[l2][p] for p in ps])
        m11 = float((b1 * b2).mean())
        rho_count = 2 + int(round(m11))
        if self_pair and m4[l1] > 2.5:
            rho_count += 1  # the depth-2 CM channel (K-rational class)
        ok = (rho_clock == rho_count == rho_known)
        all_ok = all_ok and ok
        P(f"  {cid:4s} {l1+'x'+l2:14s} {align_str:>11s} {cm_str:>6s} "
          f"{m11:7.3f} {rho_clock:9d} {rho_count:9d} {rho_known:5d} "
          f"{'YES' if ok else 'NO':>3s}")
    P()
    P("VERDICT:")
    if cert_ok and dev == 0 and all_ok:
        P("  rho_clock = rho_count = rho_known on every case: the harmonic Hodge")
        P("  frame (Hodge class = rational DC mode; alignment = clock phase-lock;")
        P("  CM class carried one tower level up, on the angle channel) reproduces")
        P("  Lefschetz (1,1) truth from both sides, oracle-free.  CALIBRATED.")
    else:
        P("  DISAGREEMENT -- the harmonic frame or an instrument is wrong here.")
        P("  Publish per the falsifiability register and investigate.")
    P()
    P("  Scope: weight 2, product surfaces, Q-isogenies read at depth 1 and the")
    P("  CM (K-rational) class at depth 2.  Not tested here: non-product K3s")
    P("  (the v2 ledger hunt) and any case where Lefschetz (1,1) is unavailable.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "hodge_clock_demo_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to hodge_clock_demo_results.txt]")


if __name__ == "__main__":
    main()
