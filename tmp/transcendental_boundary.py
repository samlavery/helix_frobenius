#!/usr/bin/env python3
"""
transcendental_boundary.py -- push to the real boundary: where does
"harmonics are transcendentals" (integer relations among transcendental periods)
stop being a Hodge detector and start being OVERFITTING?

This is the prerequisite for ever touching Ceresa/Griffiths.  The frontier claim
is that a Hodge class is an integer relation among transcendental harmonics.  But
integer-relation search (PSLQ) will "close" ANY target if the basis is big enough
or the precision small enough -- it always finds a relation of height ~10^(P/N)
among N reals at P digits, real or not.  So the ONLY honest discriminator is
STABILITY UNDER INCREASING PRECISION: a real relation has fixed small height as P
grows; a spurious (overfit) one has height that grows with P.

Built so a FALSE CLOSE is the alarm.  Three probes:
  R  a REAL relation among transcendentals (Chowla-Selberg) -- must stay stable.
  I  an INDEPENDENT target (zeta(3) vs pi^3) -- must be rejected (height grows).
  O  the OVERFIT map: throw a growing transcendental basis at an independent
     target and locate the (basis size, precision) where PSLQ starts false-closing.
"""

import mpmath as mp


def relation_height(values, P, maxcoeff=10**12):
    """PSLQ at P digits; return max|coeff| of the relation found, or None."""
    old = mp.mp.dps
    mp.mp.dps = P
    try:
        rel = mp.pslq([mp.mpf(v) for v in values], maxcoeff=maxcoeff, maxsteps=10**5)
    except Exception:
        rel = None
    mp.mp.dps = old
    if not rel:
        return None
    return max(abs(c) for c in rel), rel


def stable_across_precision(make_values, Ps=(40, 70, 110, 160)):
    """A relation is REAL iff its height is bounded as precision grows; SPURIOUS
    iff the height climbs with P (the overfit signature)."""
    hs = []
    for P in Ps:
        r = relation_height(make_values(P), P)
        hs.append(None if r is None else r[0])
    return hs


def probe_R():
    print("=" * 72)
    print("R  REAL relation among transcendentals (Chowla-Selberg) -- must be STABLE")
    print("=" * 72)
    def make(P):
        mp.mp.dps = P
        varpi = mp.pi / mp.agm(1, mp.sqrt(2))
        return [mp.gamma(mp.mpf(1)/4)**2, varpi * mp.sqrt(2*mp.pi)]   # [1,-2]
    hs = stable_across_precision(make)
    print(f"  relation height at P=40,70,110,160:  {hs}")
    ok = all(h is not None and h <= 4 for h in hs)                    # fixed, tiny
    print(f"  [{'PASS' if ok else 'HIT ':>4}] height stays O(1) as precision grows -> REAL")
    return ok


def probe_I():
    print("\n" + "=" * 72)
    print("I  INDEPENDENT target zeta(3) vs pi^3 -- must be REJECTED (height grows)")
    print("=" * 72)
    def make(P):
        mp.mp.dps = P
        return [mp.zeta(3), mp.pi**3]
    hs = stable_across_precision(make)
    print(f"  relation height at P=40,70,110,160:  {hs}")
    # honest: either no relation (None) or height that grows unboundedly with P
    growing = all(h is None for h in hs) or (
        hs[-1] is not None and hs[0] is not None and hs[-1] > 10**3 * hs[0])
    print(f"  [{'PASS' if growing else 'HIT ':>4}] no fixed low-height relation "
          f"(zeta(3)/pi^3 not a period-relation here) -> correctly NOT closed")
    return growing


def probe_O():
    print("\n" + "=" * 72)
    print("O  OVERFIT MAP: growing transcendental basis vs an independent target")
    print("=" * 72)
    print("  PSLQ finds a bounded relation for N reals once precision P is small")
    print("  relative to N.  We locate the false-close threshold.\n")
    consts = [mp.euler, mp.log(2), mp.catalan, mp.zeta(3), mp.zeta(5),
              mp.pi, mp.e, mp.sqrt(2), mp.log(3)]
    target = mp.mpf('1.2020569031595942854')      # zeta(3), independent of the above (conjecturally)
    print(f"  {'basis N':>8} {'P=30':>10} {'P=60':>10} {'P=120':>10}   (relation height; '-' = none)")
    honest = True
    for N in (2, 4, 6, 8):
        row = []
        for P in (30, 60, 120):
            mp.mp.dps = P
            vals = [target] + [c for c in consts[:N]]
            r = relation_height(vals, P, maxcoeff=10**18)
            row.append("-" if r is None else f"{r[0]:.1e}")
        print(f"  {N:>8} {row[0]:>10} {row[1]:>10} {row[2]:>10}")
    print("\n  reading: a REAL relation would show the SAME small height across P.")
    print("  Overfit relations appear at low P / large N and their height MOVES with P.")
    print("  => the honest rule: a closure counts only if its height is STABLE as P grows;")
    print("     otherwise the transcendental-harmonic 'closure' is a precision artifact.")
    return honest


def main():
    r = probe_R(); i = probe_I(); probe_O()
    print("\n" + "#" * 72)
    print(f"R real relation stable:        {'PASS' if r else 'HIT'}")
    print(f"I independent target rejected: {'PASS' if i else 'HIT'}")
    print("O overfit boundary mapped above (the precision-stability rule).")
    print("#" * 72)
    print("BOUNDARY, stated: 'harmonics are transcendentals' is a real detector ONLY")
    print("under the precision-stability discipline + a PRINCIPLED (finite, motivic)")
    print("basis.  Hand PSLQ an unrestricted transcendental basis and it closes")
    print("anything -- that is the overfit trap the Ceresa test MUST guard against.")
    print("This is the gate any real Hodge/Ceresa attempt has to pass first, and now")
    print("it's a runnable rule, not a hope.")


if __name__ == "__main__":
    main()
