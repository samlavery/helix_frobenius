"""GGK drift-singularity probe, slice 1: the purity-mass dimension census.

MECHANISM UNDER TEST (sec:terminus, staked 2026-07-14): recognition = the harmonic-1 transport
of a frozen class breaking over a family (Green-Griffiths-Kerr singularity), located exactly at
the discriminant points, with the break size = the algebraic support materializing.

OBSERVABLE: for C_s : y^3 = f(x) g_s(x)^2 over F_p (p = 1 mod 3), the chi3 Weil sum
W_p(s) = sum_x chi3(f g_s^2(x)).  Deligne equidistribution: M(s) := avg_p |W_p(s)|^2 / p
converges to the INTEGER dim of the chi3-eigenspace of H^1(C_s) — quantized on the smooth locus.

PRE-REGISTERED PREDICTIONS:
  Family A: f = x^4+1, g_s = x^4+s.  Discriminant points: s=0 (disc g = -256 s^3: quadruple
  root) and s=1 (g = f: total collision, curve degenerates maximally).  Prediction: M(s) sits on
  ONE integer plateau for s not in {0,1}, and DROPS at s=0 and s=1 (integer drop = vanishing
  cycles = the singularity firing exactly at the discriminant, nowhere else).
  Family B (control): f = x^4+1, g_s = x^4 + s*x + 2.  No integer-s degenerations expected
  (checked via resultant/disc at each s): M(s) constant integer plateau THROUGHOUT.
FALSIFIER: a drop off the discriminant, or no drop at it, kills the probe (not the frame) —
discussion gate before any verdict (Sam's protocol).
"""

import cmath
import math

PRIMES = [p for p in range(7, 420) if all(p % q for q in range(2, int(p**0.5) + 1)) and p % 3 == 1]
W3 = cmath.exp(2j * math.pi / 3)

def chi3_table(p):
    # cubic residue character via a^((p-1)/3); map to {1, w, w^2}, 0 -> 0
    e = (p - 1) // 3
    # find the two nontrivial cube roots of unity mod p, fix chi(gen^1) = w consistently
    tab = [0] * p
    # determine value of a^e in {1, r, r^2}: r = some primitive cube root mod p
    r = None
    for a in range(2, p):
        v = pow(a, e, p)
        if v != 1:
            r = v
            break
    r2 = (r * r) % p
    for a in range(1, p):
        v = pow(a, e, p)
        tab[a] = 1 if v == 1 else (W3 if v == r else W3**2)
    return tab

def weil_sum(p, tab, fco, gco):
    # W = sum_x chi3( f(x) * g(x)^2 mod p )
    s = 0j
    for x in range(p):
        fx = 0
        for c in fco:
            fx = (fx * x + c) % p
        gx = 0
        for c in gco:
            gx = (gx * x + c) % p
        s += tab[(fx * gx * gx) % p]
    return s

def mass(fco, gco_of_s, s):
    gco = gco_of_s(s)
    tot, n = 0.0, 0
    for p in PRIMES:
        tab = chi3_table(p)
        W = weil_sum(p, tab, fco, [c % p for c in gco])
        tot += abs(W) ** 2 / p
        n += 1
    return tot / n

F = [1, 0, 0, 0, 1]                      # x^4 + 1
famA = lambda s: [1, 0, 0, 0, s]         # x^4 + s
famB = lambda s: [1, 0, 0, s, 2]         # x^4 + s x + 2

lines = ["== GGK drift probe: purity-mass census (primes %d..%d, n=%d) ==" %
         (PRIMES[0], PRIMES[-1], len(PRIMES))]
for name, fam, svals in [("A (discriminant at s=0, s=1)", famA, range(-6, 8)),
                          ("B (control, smooth)", famB, range(-6, 8))]:
    lines.append("-- family %s --" % name)
    for s in svals:
        M = mass(F, fam, s)
        lines.append("  s=%3d  M=%7.3f" % (s, M))
out = "\n".join(lines)
print(out)
open("/Users/samuellavery/work/helix_frobenius/tmp/ggk_drift_probe_results.txt", "w").write(out + "\n")
