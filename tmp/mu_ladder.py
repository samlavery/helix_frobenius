"""The mu-ladder: scaling the harmonic battery up the roots of unity.

Sam's scaling design (2026-07-12): climb a REGULAR ladder of increasing roots of
unity and falsify every rung by reading it with the wrong root.  The rung-m
object is the superelliptic curve  y^m = x(1-x)  (genus (m-1)(m-2)/2-ish; leaves
the elliptic world at m = 5), whose count over F_p (p = 1 mod m) decomposes into
mu_m channels -- Jacobi sums J_j = sum_x chi^j(x) chi^j(1-x), chi of order m:

  T0 SPHERE LOCK (odd m; inert primes gcd(m, p-1) = 1): y -> y^m is a bijection,
     so the affine count is EXACTLY p -- the silent channel counts like the
     sphere; deviation = broken counter.
  T1 COUNT RECONSTRUCTION (exact integer landing): #affine = 2 + (p-2) +
     sum_{j>=1} J_j exactly -- the right root of unity rebuilds the point count.
  T2 PURITY + PLACEMENT: every live channel has |J_j|^2 = p exactly (the radius
     channel is sqrt(p) -- purity at rung m); the degenerate (DC) slots are
     exactly the predicted set {j != 0 : 2j = 0 mod m} with |J| = 1 there.
  W1 WRONG ROOT (the falsifier): decompose the SAME counts against mu_m' with
     m' != m: the reconstruction = the count of the WRONG object y^{m'} = x(1-x)
     and must MISS the true count (integer miss, typically O(m sqrt p)).

All in-house: primitive root, index table, exact integer channel coefficients;
no L-library, no lookup.  Run: python3 mu_ladder.py   (~1 min)
"""
import sys, os, math, cmath

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

RUNGS = [3, 4, 5, 6, 7, 8, 9, 12]
WRONG = {3: 4, 4: 3, 5: 3, 6: 5, 7: 3, 8: 3, 9: 4, 12: 5}
NPRIMES = 10
PMIN, PMAX = 500, 60000


def sieve(n):
    s = bytearray([1]) * 0 or bytearray([1] * (n + 1))
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]

PRIMES = sieve(PMAX)


def primitive_root(p):
    fac = []
    n = p - 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fac.append(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError


def index_table(p, g):
    ind = [0] * p
    v = 1
    for k in range(p - 1):
        ind[v] = k
        v = (v * g) % p
    return ind


def brute_count(p, m):
    """#affine{(x,y): y^m = x(1-x)} by direct frequency count -- the oracle-free
    ground truth."""
    freq = [0] * p
    for y in range(p):
        freq[pow(y, m, p)] += 1
    return sum(freq[(x * (1 - x)) % p] for x in range(p))


def channel_sums_correct(p, ind, m):
    """J_j exactly: chi(t) = zeta_m^{ind(t) mod m} (valid since m | p-1), so the
    slot-j term at t is zeta_m^{j*(ind t + ind(1-t)) mod m}; accumulate integer
    coefficients n_r and assemble J_j = sum_r n_r zeta_m^r."""
    zeta = [cmath.exp(2j * math.pi * r / m) for r in range(m)]
    coeffs = [[0] * m for _ in range(m)]        # coeffs[j][r]
    for t in range(2, p):
        st = (ind[t] + ind[(1 - t) % p]) % m
        for j in range(1, m):
            coeffs[j][(j * st) % m] += 1
    return [sum(coeffs[j][r] * zeta[r] for r in range(m)) for j in range(1, m)]


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# THE MU-LADDER -- increasing roots of unity, falsified by the wrong root")
    P("# rung m: y^m = x(1-x); channels = Jacobi sums; all counts in-house")
    P("#" * 78)
    P()
    P(f"  {'rung':>4s} {'#p':>3s} {'T0 sphere':>9s} {'T1 count':>9s} "
      f"{'T2 purity (max dev)':>19s} {'DC slots':>9s} {'W1 wrong-root miss':>19s}")

    all_ok = True
    for m in RUNGS:
        mw = WRONG[m]
        L = m * mw // math.gcd(m, mw)
        ps = [p for p in PRIMES if p > PMIN and (p - 1) % L == 0][:NPRIMES]
        t0_ok, t1_ok, t2_ok, dc_ok, w1_ok = True, True, True, True, True
        maxdev = 0.0
        minmiss = None
        # T0: sphere-lock primes (odd m only)
        if m % 2 == 1:
            inert = [p for p in PRIMES if p > PMIN and math.gcd(m, p - 1) == 1][:3]
            for p in inert:
                t0_ok = t0_ok and (brute_count(p, m) == p)
            t0s = "PASS" if t0_ok else "FAIL"
        else:
            t0s = "n/a"
        for p in ps:
            g = primitive_root(p)
            ind = index_table(p, g)
            bc = brute_count(p, m)
            Js = channel_sums_correct(p, ind, m)
            recon = 2 + (p - 2) + sum(Js).real
            t1_ok = t1_ok and abs(recon - bc) < 1e-6
            # T2: purity on live slots, |J| = 1 on predicted degenerate slots
            for idx, J in enumerate(Js):
                j = idx + 1
                degenerate = (2 * j) % m == 0
                if degenerate:
                    dc_ok = dc_ok and abs(abs(J) - 1.0) < 1e-9
                else:
                    dev = abs(abs(J) ** 2 / p - 1.0)
                    maxdev = max(maxdev, dev)
                    t2_ok = t2_ok and dev < 1e-9
            # W1: wrong-root reconstruction must miss the true count
            Jw = channel_sums_correct(p, ind, mw)
            reconw = 2 + (p - 2) + sum(Jw).real
            miss = abs(reconw - bc)
            minmiss = miss if minmiss is None else min(minmiss, miss)
            w1_ok = w1_ok and miss > 0.5
        ok = t0_ok and t1_ok and t2_ok and dc_ok and w1_ok
        all_ok = all_ok and ok
        P(f"  {m:>4d} {len(ps):>3d} {t0s:>9s} "
          f"{'EXACT' if t1_ok else 'FAIL':>9s} "
          f"{maxdev:>19.1e} {'PASS' if dc_ok else 'FAIL':>9s} "
          f"{('>= %.0f' % minmiss) if minmiss is not None else '-':>19s}")
    P()
    P("VERDICT:")
    if all_ok:
        P("  Every rung of the ladder lands with its own root of unity -- the count")
        P("  reconstructed EXACTLY, every live channel at radius sqrt(p) to 1e-9,")
        P("  the DC slots exactly where the harmonic structure predicts, inert")
        P("  primes counting like the sphere -- and every rung MISSES with the")
        P("  wrong root (integer-level reconstruction failure at every prime).")
        P("  Purity, placement, and the falsifier scale together up the ladder.")
    else:
        P("  A RUNG FAILED -- instrument defect or a reading landing with the")
        P("  wrong root.  Publish per the falsifiability register and investigate.")
    P()
    P("  Scaling: rungs mu_3..mu_12 here (genus 1 through 55); the mu_7 GL(3)")
    P("  Artin rung (F21, exact zeta_7 focal closure) and the GL(2) drift census")
    P("  are the neighbors; the same three falsifier columns apply at every")
    P("  further rung -- the ladder extends by adding one line to RUNGS.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "mu_ladder_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to mu_ladder_results.txt]")


if __name__ == "__main__":
    main()
