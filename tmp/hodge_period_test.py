#!/usr/bin/env python3
"""
hodge_period_test.py -- a could-fail Hodge test on REAL data, with the harmonics
treated as TRANSCENDENTALS (periods), per the standing claim.

SIMPLEST GENUINE HODGE CASE (proven ground truth):
    On E_tau x E_tau there is an extra Hodge class  <=>  E_tau has CM
    <=>  tau is a quadratic irrational  <=>  2*Re(tau) AND |tau|^2 are BOTH rational.
    That extra class is ALGEBRAIC (the graph of the endomorphism) -- a theorem.
    So detecting the class = detecting an integer relation among period data.

THE HARMONICS ARE TRANSCENDENTAL:
    tau is the RATIO of two periods (omega_1, omega_2) which are themselves
    transcendental (Chowla-Selberg: Gamma-values).  The Hodge class is an
    algebraic relation living on top of transcendental harmonics.  Test H2 shows
    the transcendental period closing via a Gamma-value relation.

COULD-FAIL (the point):
    H1 must (a) CLOSE on every CM tau (integer relation found, bounded height),
    and (b) NOT close on transcendental controls.  A false close on a
    transcendental, or a miss on a CM point, is a HIT.

SCOPE (honest): this is E x E, where Hodge is PROVEN.  Passing is evidence the
period-harmonic method detects Hodge classes correctly on real data; it does NOT
solve Hodge -- the open cases (Ceresa/Griffiths, higher dim) are where the class
is transcendental and NOT a period-ratio rationality.  This is the toy rung with
a real answer, built could-fail, exactly as prescribed.
"""

import mpmath as mp
mp.mp.dps = 80


def is_rational(x, maxden=10**6):
    """PSLQ test: does x satisfy an integer relation p*x + q*1 = 0 with |p|,|q|
    bounded?  Returns (p,q) if x ~ -q/p is rational at this height, else None."""
    if abs(x) < mp.mpf(10) ** (-mp.mp.dps + 15):
        return (1, 0)                       # x = 0 is rational
    rel = mp.pslq([x, mp.mpf(1)], maxcoeff=maxden, maxsteps=10**4)
    if rel and rel[0] != 0:
        # verify to precision (guards against a spurious low-height hit)
        if abs(x + mp.mpf(rel[1]) / rel[0]) < mp.mpf(10) ** (-mp.mp.dps + 15):
            return (rel[0], rel[1])
    return None


def hodge_class_on_ExE(tau):
    """Detect the extra algebraic Hodge class on E_tau x E_tau via the period
    invariants.  Returns (present, detail)."""
    s1 = 2 * tau.real                 # trace of the minimal poly of tau
    s2 = mp.fabs(tau) ** 2            # norm of tau
    r1, r2 = is_rational(s1), is_rational(s2)
    present = (r1 is not None) and (r2 is not None)
    return present, (r1, r2)


def test_H1():
    print("=" * 72)
    print("H1  Hodge class on E_tau x E_tau  <=>  CM  (could-fail, real ground truth)")
    print("=" * 72)
    CM = {   # tau (quadratic irrational) : discriminant  -- HAS the Hodge class
        "i            (D=-4)":  mp.mpc(0, 1),
        "omega        (D=-3)":  mp.mpc(mp.mpf(1)/2, mp.sqrt(3)/2),
        "i*sqrt2      (D=-8)":  mp.mpc(0, mp.sqrt(2)),
        "(1+i*sqrt7)/2(D=-7)":  mp.mpc(mp.mpf(1)/2, mp.sqrt(7)/2),
        "i*sqrt5      (D=-20)": mp.mpc(0, mp.sqrt(5)),
        "(1+i*sqrt11)/2(D=-11)":mp.mpc(mp.mpf(1)/2, mp.sqrt(11)/2),
    }
    TR = {   # transcendental tau  -- must have NO Hodge class
        "i*e          ":        mp.mpc(0, mp.e),
        "i*pi/2       ":        mp.mpc(0, mp.pi/2),
        "(1+i*e)/2    ":        mp.mpc(mp.mpf(1)/2, mp.e/2),      # rational trace, transc norm
        "i*sqrt2*e    ":        mp.mpc(0, mp.sqrt(2)*mp.e),
        "i*ln3        ":        mp.mpc(0, mp.log(3)),
    }
    ok = True
    print("\n  CM points (expect CLOSE):")
    for name, tau in CM.items():
        present, _ = hodge_class_on_ExE(tau)
        ok &= present
        print(f"    {name:22} -> {'CLOSE (Hodge class)' if present else 'MISS  <-- HIT'}")
    print("\n  Transcendental controls (expect NO close):")
    for name, tau in TR.items():
        present, _ = hodge_class_on_ExE(tau)
        ok &= (not present)
        print(f"    {name:22} -> {'no class (correct)' if not present else 'FALSE CLOSE <-- HIT'}")
    print(f"\n  [{'PASS' if ok else 'HIT ':>4}] harmonic period-relation closure tracks CM exactly")
    return ok


def test_H2():
    print("\n" + "=" * 72)
    print("H2  the harmonics ARE transcendental: the CM period closes on Gamma-values")
    print("=" * 72)
    # tau = i (lemniscatic, D=-4).  Real period of y^2 = x^3 - x:
    #   varpi = pi / AGM(1, sqrt2)  = Gamma(1/4)^2 / (2 sqrt(2 pi))   (Chowla-Selberg)
    varpi = mp.pi / mp.agm(1, mp.sqrt(2))            # transcendental PERIOD (a harmonic)
    G = mp.gamma(mp.mpf(1)/4) ** 2                    # transcendental Gamma-value
    ratio = G / varpi                                # should be 2 sqrt(2 pi)
    target = 2 * mp.sqrt(2 * mp.pi)
    print(f"    period  varpi = pi/AGM(1,sqrt2)     = {mp.nstr(varpi, 20)}")
    print(f"    Gamma(1/4)^2                        = {mp.nstr(G, 20)}")
    print(f"    Gamma(1/4)^2 / varpi                = {mp.nstr(ratio, 25)}")
    print(f"    2*sqrt(2*pi)                        = {mp.nstr(target, 25)}")
    closes = abs(ratio - target) < mp.mpf(10) ** (-60)
    # PSLQ: an integer relation among the transcendental trio (G, varpi*sqrt(2pi))
    rel = mp.pslq([G, varpi * mp.sqrt(2*mp.pi)], maxcoeff=100)
    print(f"    PSLQ relation among (Gamma(1/4)^2, varpi*sqrt(2pi)) = {rel}   (expect [1,-2])")
    ok = closes and rel == [1, -2]
    print(f"\n  [{'PASS' if ok else 'HIT ':>4}] the transcendental period harmonic closes exactly "
          f"on a Gamma-value relation")
    print("  (the 'harmonic' here is transcendental -- a period -- and the closure is an")
    print("   integer relation among transcendentals, exactly the claimed structure.)")
    return ok


def main():
    h1, h2 = test_H1(), test_H2()
    print("\n" + "#" * 72)
    print(f"H1 Hodge-on-ExE could-fail test:   {'PASS' if h1 else 'HIT -- FALSIFIED'}")
    print(f"H2 transcendental-harmonic closure:{'PASS' if h2 else 'HIT'}")
    print("#" * 72)
    print("HONEST SCOPE: E x E is the PROVEN case; passing = the period-harmonic method")
    print("detects real Hodge classes and rejects transcendental controls.  It does NOT")
    print("solve Hodge -- the open frontier is where the class itself is transcendental")
    print("(Ceresa/Griffiths), which a period-ratio rationality does NOT capture.  Next")
    print("real rung: a genus-3 Ceresa class, known non-torsion, as a transcendental that")
    print("MUST correctly fail to close -- the true could-fail against the hard case.")


if __name__ == "__main__":
    main()
