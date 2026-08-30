"""att542 -- C3 batch 4.  FOUR-PRECISION adjudication of the apparent second sign
change of T(r,x) near r = 1.58 (x=60) / r = 1.70 (x=88).

The att541 hostile sweep printed T(r,60) frozen at -1.7731014905e-65 for EVERY
r in [1.60, 2.00] to 11 printed digits.  A genuine T(r) = int_r^inf (u-r)C(u,x)du
decays double-exponentially in r; a value independent of r is the signature of an
r-INDEPENDENT additive error, i.e. a resolution floor, not a crossing.

Decision rule, PRE-REGISTERED before running:
  * if the value at a fixed r MOVES when (dps, cutoff, panel) change -> it is FLOOR,
    the apparent second crossing is an artifact, and T's sign is UNDETERMINED below
    that magnitude;
  * if it AGREES to >= 8 digits across all four settings -> it is a REAL second sign
    change and single-crossing is REFUTED at that x.
PREDICTION: floor.  Reason: r-independence over a range where the true object varies
by many orders, plus the cancellation budget (integrand scale 1e-36, answer 1e-65).

Also reports the same ladder for U(R,x), whose positivity is the surviving hypothesis.
"""
import sys
import mpmath as mp

sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
import att541_c3b4_ramp2 as A

SETTINGS = [
    # (dps, cutoff, deg, panel)
    (40, 150, 5, '0.5'),
    (60, 200, 5, '0.25'),
    (80, 250, 6, '0.25'),
    (110, 300, 6, '0.125'),
]


def ladder(x, rlist):
    print('# att542 four-precision ladder, x = %s' % x)
    print('#   settings: ' + ' | '.join('dps=%d T=%d deg=%d panel=%s' % s for s in SETTINGS))
    for r in rlist:
        vals, uvals = [], []
        for (dps, T, deg, panel) in SETTINGS:
            mp.mp.dps = dps
            xv = mp.mpf(x)
            tv, tb = A.T_of(xv, r, T, deg, mp.mpf(panel))
            L1 = A.L1_of(xv)
            m, mb = A.M_of(xv, r, T, deg, mp.mpf(panel))
            vals.append(tv)
            uvals.append(L1 / 16 - m)
        print('  r = %s' % r)
        for (s, v, u) in zip(SETTINGS, vals, uvals):
            print('     dps=%-4d T=%-4d panel=%-6s  T = %-26s  U = %s'
                  % (s[0], s[1], s[3], mp.nstr(v, 16), mp.nstr(u, 16)))
        # agreement of the last three against the first
        mp.mp.dps = 60
        spread = max(abs(v - vals[0]) for v in vals[1:])
        scale = max(abs(v) for v in vals)
        print('     -> T spread = %-16s  scale = %-16s  rel = %s   %s'
              % (mp.nstr(spread, 6), mp.nstr(scale, 6),
                 mp.nstr(spread / scale, 6) if scale > 0 else 'n/a',
                 'FLOOR (artifact)' if scale > 0 and spread / scale > mp.mpf('1e-8')
                 else 'STABLE (real)'))
        uspread = max(abs(v - uvals[0]) for v in uvals[1:])
        uscale = max(abs(v) for v in uvals)
        print('     -> U spread = %-16s  scale = %-16s  rel = %s   %s'
              % (mp.nstr(uspread, 6), mp.nstr(uscale, 6),
                 mp.nstr(uspread / uscale, 6) if uscale > 0 else 'n/a',
                 'FLOOR (artifact)' if uscale > 0 and uspread / uscale > mp.mpf('1e-8')
                 else 'STABLE (real)'))
        sys.stdout.flush()


if __name__ == '__main__':
    x = sys.argv[1]
    rlist = sys.argv[2].split(',')
    ladder(x, rlist)
