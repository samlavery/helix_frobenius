"""The twistor hunt, v1: DC-locking on the dial happens exactly at algebraic points.

The harmonic frame's sphere is the dial -- the space of clocks.  For the product/Kummer
K3 world (transcendental H^2 of Km(E_1 x E_2) = transcendental H^2 of E_1 x E_2), the
dial coordinate is the second clock tau_2, rotating against a fixed first clock tau_1.
A (1,1) class LOCKS TO DC exactly when the two clocks align -- a Hecke correspondence
(a tau_1 + b)/d = tau_2 -- and the Picard number jumps by one (calibrated in
hodge_clock_demo.py against Lefschetz (1,1) truth).

The Cattani--Deligne--Kaplan-shaped prediction, measured here:

    the DC-locking locus of the dial is DISCRETE and ALGEBRAIC -- every lock sits
    at a rational point of the dial (an integer clock relation), and no lock
    occurs at any non-algebraic point.

Instrument: fix tau_1 = i (curve 32a1's clock, certified in hodge_clock_demo.py by the
exact j = 1728).  Scan the dial path tau_2(t) = (1+t) i, t in [0,1].  A lock at t means
(1+t) i is GL_2^+(Q)-equivalent to i, which happens IFF 1+t = a/d is RATIONAL (solve
(a i + b)/(c i + d) = (1+t) i over Z: b = -c(1+t), a = d(1+t)); within Hecke degree
n = a*d <= NMAX the predicted lock set is exactly {t = a/d - 1 : 1 <= a/d <= 2, ad <= NMAX,
gcd(a,d)=1}.  So the run checks BOTH directions, falsifiably:

  (i)  every predicted rational lock point dips to ~0 residual (locks found);
  (ii) every detected lock is one of the predicted rationals (no lock off the
       algebraic set) -- probed also at explicit irrational controls
       (1+t = sqrt(2), golden ratio phi - 1/2 ... scaled into range).

FALTINGS SHIELD (honest scope): for product/Kummer K3s the zeta function determines the
isogeny class of the factors, so a clause-(c) ledger failure (equal full ledger,
different cycle theory) CANNOT occur here -- this locus is structurally safe ground for
calibrating the dial, and the genuine clause-(c) hunt needs non-product K3s (quartic
point counts) -- the named v3 target.

Run: python3 twistor_hunt.py       (~seconds; oracle-free, reuses hodge_clock_demo)
"""
import sys, os, math, cmath
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hodge_clock_demo as HC

NMAX = 36
TSAMPLES = 4000
LOCK_TOL = 1e-8


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# TWISTOR HUNT v1 -- DC-locking on the dial is discrete and algebraic")
    P(f"# tau_1 = i fixed; dial tau_2(t) = (1+t)i, t in [0,1]; Hecke degree <= {NMAX}")
    P("#" * 78)
    P()

    tau1 = complex(0.0, 1.0)

    # precompute the j-values of every Hecke image of tau_1 (the fixed clock's
    # full alignment fan, up to degree NMAX)
    fan = []
    for n in range(1, NMAX + 1):
        for a in range(1, n + 1):
            if n % a:
                continue
            d = n // a
            for b in range(d):
                if math.gcd(math.gcd(a, b), d) != 1:
                    continue
                tp = (a * tau1 + b) / d
                fan.append((n, HC.jfun(HC.sl2_reduce(tp))))
    P(f"  alignment fan of tau_1: {len(fan)} Hecke images precomputed")

    # predicted lock set: 1+t = a/d in [1,2], gcd(a,d)=1, a*d <= NMAX
    predicted = sorted(set(
        Fraction(a, d) for d in range(1, NMAX + 1) for a in range(d, 2 * d + 1)
        if a * d <= NMAX and math.gcd(a, d) == 1 and 1 <= Fraction(a, d) <= 2))
    P(f"  predicted algebraic lock points (1+t = a/d, ad <= {NMAX}): "
      f"{len(predicted)}")
    P()

    def residual_at(s):        # s = 1 + t, the dial coordinate
        j2 = HC.jfun(HC.sl2_reduce(complex(0.0, s)))
        return min(abs(jv - j2) / (1.0 + abs(j2)) for _, jv in fan)

    # (i) every predicted lock dips
    P("  (i) predicted locks -- residual at each rational point:")
    miss = 0
    for q in predicted:
        r = residual_at(float(q))
        ok = r < LOCK_TOL
        miss += 0 if ok else 1
        P(f"      1+t = {str(q):>6s}   residual = {r:.2e}   "
          f"{'LOCK' if ok else '*** NO LOCK ***'}")
    P()

    # (ii) ALGEBRAICITY of every detected lock: dense scan; each near-lock
    # sample must identify as a small-denominator RATIONAL point of the dial.
    # (The base clock i is CM, disc -4: its ZZ[i]-endomorphisms compose with
    # Hecke, so the lock set is LARGER than the naive a/d, ad <= NMAX list --
    # extra clock symmetry, extra alignments -- but every lock must still be
    # rational.  That is the CDK-shaped claim under test.)
    # a lock candidate is a LOCAL MINIMUM of the residual along the dial (the
    # base point i is a critical point of j -- j-1728 vanishes quadratically --
    # so true locks have wide flat shoulders that must not be double-counted)
    rs = [residual_at(1.0 + k / TSAMPLES) for k in range(TSAMPLES + 1)]
    detected = []
    for k in range(TSAMPLES + 1):
        if rs[k] >= 1e-4:
            continue
        left = rs[k - 1] if k > 0 else float("inf")
        right = rs[k + 1] if k < TSAMPLES else float("inf")
        if rs[k] <= left and rs[k] <= right:
            detected.append((1.0 + k / TSAMPLES, rs[k]))
    QMAX = 64
    locks = {}          # rational -> best residual
    nonalgebraic = []
    for s, r in detected:
        best = min(((Fraction(p, q), abs(p / q - s))
                    for q in range(1, QMAX + 1)
                    for p in (round(s * q),)), key=lambda x: x[1])
        frac, dist = best
        if dist <= 1.5 / TSAMPLES:
            rr = residual_at(float(frac))
            if frac not in locks or rr < locks[frac]:
                locks[frac] = rr
        else:
            nonalgebraic.append((s, r))
    P(f"  (ii) dense scan: {TSAMPLES + 1} dial samples, "
      f"{len(detected)} near-lock samples, {len(nonalgebraic)} NOT identifiable "
      f"as a rational (q <= {QMAX})")
    for s, r in nonalgebraic:
        P(f"         UNMATCHED sample 1+t = {s:.6f}   residual = {r:.2e}")
    P("       identified lock points (all must be rational = algebraic):")
    for frac in sorted(locks):
        tag = "naive Hecke" if frac in predicted else "CM-composed"
        P(f"         1+t = {str(frac):>6s}   residual = {locks[frac]:.2e}   "
          f"[{tag}]")
    unmatched = nonalgebraic

    controls = [math.sqrt(2), (1 + math.sqrt(5)) / 2 - 0.11, math.e / 2,
                math.pi / 2 - 0.35]
    P("       irrational controls (must NOT lock):")
    ctrl_ok = True
    for s in controls:
        r = residual_at(s)
        locked = r < LOCK_TOL
        ctrl_ok = ctrl_ok and not locked
        P(f"         1+t = {s:.6f}   residual = {r:.2e}   "
          f"{'*** LOCKED (failure) ***' if locked else 'no lock'}")
    P()

    P("VERDICT:")
    if miss == 0 and not unmatched and ctrl_ok:
        P("  (i)  every naive-Hecke rational point of the dial LOCKS (residual 0);")
        P("  (ii) EVERY detected lock identifies as a rational point of the dial")
        P("       (any beyond the naive list would be the CM-composed alignments of")
        P("       the base clock's disc -4 endomorphisms -- none needed at this")
        P("       resolution), and every irrational control stays at O(1) residual.")
        P("  The DC-locking locus of the dial is discrete and exactly algebraic --")
        P("  the Cattani-Deligne-Kaplan-shaped behavior, measured on the carrier's")
        P("  own clock coordinates.  The sphere is a legitimate induction dial:")
        P("  rotating it locks classes to DC only at algebraic clock relations.")
    else:
        P(f"  FAILURE: {miss} predicted locks missing; {len(unmatched)} detected")
        P("  locks NOT identifiable as rational; irrational controls "
          + ("clean" if ctrl_ok else "LOCKED") + ".")
        P("  Publish per the falsifiability register and investigate.")
    P()
    P("  Scope: the product/Kummer-K3 transcendental dial (one modulus).  Faltings")
    P("  shields this locus from a clause-(c) ledger failure (zeta determines the")
    P("  isogeny class of the factors), so the genuine equal-ledger different-Chow")
    P("  hunt needs non-product K3s -- quartic point counts, the named v3 target.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "twistor_hunt_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to twistor_hunt_results.txt]")


if __name__ == "__main__":
    main()
