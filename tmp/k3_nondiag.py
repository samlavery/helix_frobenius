"""Clause-(c) falsifier hunt on NON-DIAGONAL quartic K3s (escalation of k3_ledger).

Clause (c) of the house Hodge falsifiability register: two K3s with matched
Satake / partial-zeta data (identical Frobenius trace sequence, hence identical
point counts at every good prime) but structurally distinct cycle theory
(different Picard/Chow structure) would break the ledger's retention.

The diagonal family cannot produce this -- twist characters separate everything
(measured in k3_ledger).  Product / Kummer K3s are shielded by Faltings (zeta
determines the isogeny class of the factors).  The genuine hunt needs
non-product, non-diagonal quartics.  This instrument scans:

  * the Dwork / Fermat pencil   X_c :  x^4 + y^4 + z^4 + w^4 - 4c * xyzw = 0
    (singular exactly at c^4 = 1; the canonical non-diagonal deformation with
    known extra symmetries -> structured zeta -> a stringent accidental-match
    test), for several rational c;
  * block-separable "generic" perturbations  Phi(x,y) + Psi(z,w) = 0 with genuine
    cross-monomials (x y^3 etc.) and, in some members, asymmetric blocks so the
    block-swap symmetry is broken.

Everything is EXACT integer point counting -- no character-sum formula is
trusted.  Two independent counting cores are used and both are validated at
small primes against a brute projective enumerator (the real calibration of the
new instrument), then the diagonal readings of k3_ledger are reproduced:

  * count_separable  : F = Phi(x,y) + Psi(z,w); additive value-histogram
                       convolution, O(p^2) per prime.
  * count_dwork      : the non-separable Dwork form; pair-histogram A[a][v] over
                       (y,z) with a = y z, then a sheared O(p^3) gather over
                       (x, w, a).  Raw counting, just vectorized.

Readout (as in k3_ledger):
    #X(F_p)  exact ;  t_p := (#X(F_p) - (1 + p + p^2)) / p   (normalized trace on
    the 21-dim primitive H^2).  DC occupancy = mean t_p ; angle channel = means
    over p mod 8.

THE HUNT: over all surfaces in the scan, the pairwise separation
    sep(S,S') := max_p |#X_S(F_p) - #X_S'(F_p)|          (exact integer)
is measured on the common good primes.  A pair with sep = 0 (identical zeta data
at every computed prime) that is NOT forced-isomorphic and is structurally
distinct = a clause-(c) EVENT (report loudly).  Forced-isomorphic pairs
(Dwork c and -c, via w -> -w over Q) must be identical -- an internal control.
Expected outcome: a clean null (every non-iso pair separates); the separation
statistic min over pairs of sep is the strengthening.

Run:  python3 k3_nondiag.py [COMMON_PMAX=400]      (a few min)
"""
import sys, os, time
from fractions import Fraction
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH


# --------------------------------------------------------------------------- #
#  monomial machinery (for the brute self-test and the smoothness screen)      #
# --------------------------------------------------------------------------- #
# a surface polynomial is a list of (coeff, (ex, ey, ez, ew)) monomials.

def poly_val(mons, x, y, z, w, p):
    v = 0
    coord = (x, y, z, w)
    for c, e in mons:
        t = c % p
        for var, k in zip(coord, e):
            for _ in range(k):
                t = t * var % p
        v = (v + t) % p
    return v


def poly_partial(mons, var_index):
    """symbolic d/d(var_index) of a monomial list -> new monomial list."""
    out = []
    for c, e in mons:
        k = e[var_index]
        if k == 0:
            continue
        ne = list(e)
        ne[var_index] -= 1
        out.append((c * k, tuple(ne)))
    return out


def dwork_mons(cval):
    return [(1, (4, 0, 0, 0)), (1, (0, 4, 0, 0)), (1, (0, 0, 4, 0)),
            (1, (0, 0, 0, 4)), ((-4 * cval), (1, 1, 1, 1))]


def sep_mons(phi, psi):
    """phi over (x,y), psi over (z,w); return the full 4-var monomial list."""
    out = []
    for c, (ex, ey) in phi:
        out.append((c, (ex, ey, 0, 0)))
    for c, (ez, ew) in psi:
        out.append((c, (0, 0, ez, ew)))
    return out


def binary_quartic_disc(mons2):
    """discriminant of the leading-monic binary quartic
       a x^4 + b x^3 y + c x^2 y^2 + d x y^3 + e y^4 (here a = 1, no root at
       infinity), an exact integer; its prime divisors are the reduction primes
       where the quartic acquires a repeated root (surface bad reduction)."""
    m = {e: c for c, e in mons2}
    a = m.get((4, 0), 0); b = m.get((3, 1), 0); c = m.get((2, 2), 0)
    d = m.get((1, 3), 0); e = m.get((0, 4), 0)
    return (256 * a**3 * e**3 - 192 * a**2 * b * d * e**2
            - 128 * a**2 * c**2 * e**2 + 144 * a**2 * c * d**2 * e
            - 27 * a**2 * d**4 + 144 * a * b**2 * c * e**2
            - 6 * a * b**2 * d**2 * e - 80 * a * b * c**2 * d * e
            + 18 * a * b * c * d**3 + 16 * a * c**4 * e - 4 * a * c**3 * d**2
            - 27 * b**4 * e**2 + 18 * b**3 * c * d * e - 4 * b**3 * d**3
            - 4 * b**2 * c**3 * e + b**2 * c**2 * d**2)


def prime_factors(n):
    n = abs(n)
    out = set()
    dd = 2
    while dd * dd <= n:
        while n % dd == 0:
            out.add(dd)
            n //= dd
        dd += 1
    if n > 1:
        out.add(n)
    return out


# --------------------------------------------------------------------------- #
#  brute projective enumerator (small p only) -- ground truth                  #
# --------------------------------------------------------------------------- #

def proj_points(p):
    """canonical representatives of P^3(F_p): first nonzero coord = 1."""
    for lead in range(4):
        # coords before lead are 0, lead coord is 1, rest free
        rngs = [[0]] * lead + [[1]] + [range(p)] * (3 - lead)
        for a in rngs[0]:
            for b in rngs[1]:
                for cc in rngs[2]:
                    for d in rngs[3]:
                        yield (a, b, cc, d)


def brute_proj_count(p, mons):
    return sum(1 for pt in proj_points(p) if poly_val(mons, *pt, p) == 0)


def brute_singular(p, mons):
    """does the surface have a projective singular point over F_p?"""
    parts = [poly_partial(mons, i) for i in range(4)]
    for pt in proj_points(p):
        if poly_val(mons, *pt, p) != 0:
            continue
        if all(poly_val(pr, *pt, p) == 0 for pr in parts):
            return True
    return False


# --------------------------------------------------------------------------- #
#  fast exact counting cores                                                   #
# --------------------------------------------------------------------------- #

def _powmod(arr, e, p):
    r = np.ones_like(arr)
    b = arr % p
    while e:
        if e & 1:
            r = r * b % p
        e >>= 1
        if e:
            b = b * b % p
    return r


def _grid_hist(p, mons2):
    """histogram over F_p of a bivariate form given as [(coeff,(ea,eb)),...]."""
    idx = np.arange(p, dtype=np.int64)
    A = idx[:, None]                       # first var, p x 1
    B = idx[None, :]                       # second var, 1 x p
    val = np.zeros((p, p), dtype=np.int64)
    for c, (ea, eb) in mons2:
        term = (c % p) * _powmod(A, ea, p) % p * _powmod(B, eb, p) % p
        val = (val + term) % p
    return np.bincount(val.ravel(), minlength=p).astype(np.int64)


def count_separable(p, phi, psi):
    """#X(F_p) for F = phi(x,y) + psi(z,w) = 0, exact, O(p^2)."""
    hphi = _grid_hist(p, phi)
    hpsi = _grid_hist(p, psi)
    idx = np.arange(p, dtype=np.int64)
    cone = int((hphi * hpsi[(-idx) % p]).sum())     # #{phi + psi = 0} affine
    assert (cone - 1) % (p - 1) == 0
    return (cone - 1) // (p - 1)


def count_dwork(p, cval):
    """#X(F_p) for x^4+y^4+z^4+w^4 - 4c xyzw = 0, exact, O(p^3).

    Pair histogram A[a][v] = #{(y,z): y z = a, y^4+z^4 = v}; then for each x the
    equation becomes y^4+z^4 = -(x^4+w^4) + 4c (x w)(y z), summed over (x,w,a)."""
    idx = np.arange(p, dtype=np.int64)
    sq = idx * idx % p
    x4 = sq * sq % p                                    # r^4 for residue r
    a = (idx[:, None] * idx[None, :]) % p               # y z
    v = (x4[:, None] + x4[None, :]) % p                 # y^4 + z^4
    A = np.bincount((a.ravel() * p + v.ravel()),
                    minlength=p * p).reshape(p, p).astype(np.int64)
    fourc = (4 * cval) % p
    wa = (idx[:, None] * idx[None, :]) % p              # w * a  (w axis0, a axis1)
    arow = idx[None, :]                                 # a indices along axis1
    total = 0
    for xv in range(p):
        base = (-x4[xv] - x4) % p                       # over w, length p
        coef = (fourc * xv) % p
        M = (base[:, None] + coef * wa) % p             # M[w,a]
        total += int(A[arow, M].sum())
    assert (total - 1) % (p - 1) == 0
    return (total - 1) // (p - 1)


# --------------------------------------------------------------------------- #
#  surfaces                                                                    #
# --------------------------------------------------------------------------- #

class Surface:
    def __init__(self, name, kind, data, mons, iso_key, note=""):
        self.name = name
        self.kind = kind            # 'sep' or 'dwork'
        self.data = data            # (phi,psi) or cval-fraction
        self.mons_fn = mons         # callable p -> monomial list (for brute/screen)
        self.iso_key = iso_key      # forced-isomorphism class label
        self.note = note
        self.counts = {}            # p -> #X(F_p)

    def bad(self, p):
        return p in self.bad_primes

    def count(self, p):
        if self.kind == 'sep':
            phi, psi = self.data
            return count_separable(p, phi, psi)
        else:
            n, d = self.data
            cval = (n % p) * pow(d % p, -1, p) % p
            return count_dwork(p, cval)


def dwork_surface(c):
    fr = Fraction(c)
    n, d = fr.numerator, fr.denominator
    s = Surface(f"Dwork c={fr}", 'dwork', (n, d),
                lambda p, n=n, d=d: dwork_mons((n % p) * pow(d % p, -1, p) % p),
                iso_key=("dwork", frozenset({fr, -fr})),
                note="singular at c^4=1")
    # bad primes: 2, primes dividing denominator, primes where c^4 == 1 (mod p)
    bad = {2}
    for p in SH.sieve_primes(2000):
        p = int(p)
        if p == 2:
            continue
        if d % p == 0:
            bad.add(p)
            continue
        cv = (n % p) * pow(d % p, -1, p) % p
        if (cv * cv % p) * (cv * cv % p) % p == 1 % p:
            bad.add(p)
    s.bad_primes = bad
    s.smooth = (fr**4 != 1)                        # smooth K3 over Q iff c^4 != 1
    s.discs = None
    return s


def sep_surface(name, phi, psi, iso_key, note=""):
    s = Surface(name, 'sep', (phi, psi),
                lambda p, phi=phi, psi=psi: sep_mons(phi, psi),
                iso_key=iso_key, note=note)
    dphi, dpsi = binary_quartic_disc(phi), binary_quartic_disc(psi)
    s.discs = (dphi, dpsi)
    s.smooth = (dphi != 0 and dpsi != 0)          # smooth K3 over Q
    s.bad_primes = {2} | prime_factors(dphi) | prime_factors(dpsi)
    return s


def build_surfaces():
    S = []
    # -- diagonal calibration family (reproduce k3_ledger) --
    S.append(sep_surface("diag c=1", [(1, (4, 0)), (1, (0, 4))],
                         [(1, (4, 0)), (1, (0, 4))], iso_key=("diag", 1),
                         note="Fermat quartic, rho=20"))
    S.append(sep_surface("diag c=2", [(1, (4, 0)), (1, (0, 4))],
                         [(1, (4, 0)), (2, (0, 4))], iso_key=("diag", 2)))
    # -- Dwork pencil --
    for c in [2, -2, 3, 5, Fraction(1, 2)]:
        S.append(dwork_surface(c))
    # -- block-separable non-diagonal generics --
    #    gen_A: asymmetric blocks (no block-swap symmetry), cross monomials x y^3 / 2 z w^3
    S.append(sep_surface("gen_A xy^3|2zw^3",
                         [(1, (4, 0)), (1, (0, 4)), (1, (1, 3))],
                         [(1, (4, 0)), (1, (0, 4)), (2, (1, 3))],
                         iso_key=("gen", "A")))
    #    gen_B: different cross monomial x^3 y (block-swap symmetric but non-diagonal)
    S.append(sep_surface("gen_B x^3y|z^3w",
                         [(1, (4, 0)), (1, (0, 4)), (1, (3, 1))],
                         [(1, (4, 0)), (1, (0, 4)), (1, (3, 1))],
                         iso_key=("gen", "B")))
    #    gen_C: asymmetric x^2 y^2 / 3 z^2 w^2
    S.append(sep_surface("gen_C x2y2|3z2w2",
                         [(1, (4, 0)), (1, (0, 4)), (1, (2, 2))],
                         [(1, (4, 0)), (1, (0, 4)), (3, (2, 2))],
                         iso_key=("gen", "C")))
    return S


# --------------------------------------------------------------------------- #
#  main                                                                        #
# --------------------------------------------------------------------------- #

def main():
    COMMON_PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# CLAUSE-(c) HUNT ON NON-DIAGONAL QUARTIC K3s")
    P(f"# exact counts; common good primes p <= {COMMON_PMAX}")
    P("#" * 78)
    P()

    # ---- 0. new-core validation against brute enumerator (small p) ----
    P(">> CORE VALIDATION (new counters vs brute projective enumerator)")
    ok_core = True
    test_surfaces = build_surfaces()
    for sp in [5, 7, 11, 13]:
        for s in test_surfaces:
            if s.bad(sp):
                continue
            fast = s.count(sp)
            slow = brute_proj_count(sp, s.mons_fn(sp))
            if fast != slow:
                ok_core = False
                P(f"   MISMATCH p={sp} {s.name}: fast={fast} brute={slow}")
    if ok_core:
        P("   all cores match brute counts at p in {5,7,11,13}  OK")
    else:
        P("   *** CORE MISMATCH -- aborting ***")
        _write(lines)
        return
    P()

    # ---- 1. calibration gate: reproduce k3_ledger diagonal readings ----
    P(">> CALIBRATION GATE (reproduce k3_ledger diagonal t_p, p <= 800)")
    prs800 = [int(p) for p in SH.sieve_primes(800) if p > 2]
    ref = {  # from k3_ledger_results.txt (PMAX=800)
        "diag c=1": (3.233, 18.826, -5.124, 1.000),
        "diag c=2": (2.298, 4.304, 5.163, -0.042),
    }
    gate_ok = True
    for s in test_surfaces:
        if s.name not in ref:
            continue
        ts = {}
        for p in prs800:
            if s.bad(p) or (s.name == "diag c=2" and p == 2):
                continue
            # diagonal bad prime p|c handled: skip p dividing the twist coeff
            if s.name == "diag c=2" and p == 2:
                continue
            N = s.count(p)
            ts[p] = (N - (1 + p + p * p)) / p
        arr = np.array(list(ts.values()))
        p1 = np.array([v for q, v in ts.items() if q % 8 == 1])
        p5 = np.array([v for q, v in ts.items() if q % 8 == 5])
        p37 = np.array([v for q, v in ts.items() if q % 8 in (3, 7)])
        got = (arr.mean(), p1.mean(), p5.mean(), p37.mean())
        exp = ref[s.name]
        match = all(abs(g - e) < 0.02 for g, e in zip(got, exp))
        gate_ok = gate_ok and match
        P(f"   {s.name}: mean={got[0]:7.3f} (ref {exp[0]:.3f})  "
          f"mod8 1:{got[1]:7.3f} 5:{got[2]:7.3f} 3,7:{got[3]:7.3f}   "
          f"{'MATCH' if match else '*** DIFF ***'}")
    if not gate_ok:
        P("   *** GATE FAILED ***")
        _write(lines)
        return
    P("   gate passed: new core reproduces k3_ledger diagonal readings")
    P()

    # ---- 2. smoothness / bad-reduction classification (exact discriminants) ----
    P(">> SMOOTHNESS + BAD-REDUCTION (exact binary-quartic discriminants;")
    P("   cross-validated vs brute singular-point search at small primes)")
    # cross-validate the bad-prime sets against brute singularity, small p
    val_ok = True
    for s in test_surfaces:
        for p in [3, 5, 7, 11, 13, 17, 19, 23]:
            bruted = brute_singular(p, s.mons_fn(p))
            claimed = s.bad(p)
            if bruted != claimed:
                val_ok = False
                P(f"   BAD-PRIME MISMATCH {s.name} p={p}: "
                  f"brute_singular={bruted} claimed_bad={claimed}")
    P(f"   bad-prime validation vs brute (p<=23): "
      f"{'consistent OK' if val_ok else '*** MISMATCH ***'}")
    for s in test_surfaces:
        bp = sorted(x for x in s.bad_primes if x <= 1000)
        dtag = ("" if s.discs is None
                else f"disc(Phi,Psi)=({s.discs[0]},{s.discs[1]})  ")
        smt = "smooth K3/Q" if s.smooth else "SINGULAR over Q (not K3)"
        P(f"   {s.name:22s} {smt:22s} {dtag}bad primes<=1000: {bp}  {s.note}")
    P()

    # ---- 3. main scan: exact #X over common good primes ----
    P(f">> SCAN: exact #X(F_p), t_p profile, p <= {COMMON_PMAX}")
    prs = [int(p) for p in SH.sieve_primes(COMMON_PMAX) if p > 2]
    t0 = time.time()
    for s in test_surfaces:
        for p in prs:
            if s.bad(p):
                continue
            s.counts[p] = s.count(p)
    P(f"   (scan wall time {time.time() - t0:.1f}s)")
    P()
    P("   per-surface fingerprint (DC occupancy + angle channel):")
    for s in test_surfaces:
        ts = {p: (N - (1 + p + p * p)) / p for p, N in s.counts.items()}
        arr = np.array(list(ts.values()))
        p1 = np.array([v for q, v in ts.items() if q % 8 == 1])
        p5 = np.array([v for q, v in ts.items() if q % 8 == 5])
        p37 = np.array([v for q, v in ts.items() if q % 8 in (3, 7)])
        sm = "smooth" if getattr(s, "smooth", True) else "SINGULAR"
        P(f"   {s.name:22s} [{sm:8s}] DC={arr.mean():7.3f}  "
          f"mod8 1:{_m(p1):7.3f} 5:{_m(p5):7.3f} 3,7:{_m(p37):7.3f}  "
          f"(n={len(arr)})")
    P()

    # ---- 4. pairwise separation ----
    P("   PAIRWISE SEPARATION  sep(S,S') = max_p |#X_S(F_p) - #X_S'(F_p)|")
    P("   over common good primes (exact integer); forced-iso pairs are a control")
    event = False
    iso_pairs, noniso = [], []
    n = len(test_surfaces)
    for i in range(n):
        for j in range(i + 1, n):
            s1, s2 = test_surfaces[i], test_surfaces[j]
            common = sorted(set(s1.counts) & set(s2.counts))
            if not common:
                continue
            sep = max(abs(s1.counts[p] - s2.counts[p]) for p in common)
            tgap = max(abs(s1.counts[p] - s2.counts[p]) / p for p in common)
            firstp = min(p for p in common
                         if abs(s1.counts[p] - s2.counts[p]) == sep)
            iso = (s1.iso_key == s2.iso_key)
            rec = (sep, tgap, len(common), s1, s2)
            if iso:
                iso_pairs.append(rec)
            else:
                noniso.append(rec)
    # forced-iso controls
    P("   forced-isomorphic controls (Dwork c ~ -c, must be identical):")
    for sep, tgap, nc, s1, s2 in iso_pairs:
        ok = (sep == 0)
        event = event or (not ok)
        P(f"     {s1.name:20s} == {s2.name:20s} sep={sep:5d}  "
          f"(n={nc})  {'OK identical' if ok else '*** SEPARATED: DEFECT ***'}")
    # non-iso separation distribution
    seps = sorted(r[0] for r in noniso)
    collisions = [r for r in noniso if r[0] == 0]
    for sep, tgap, nc, s1, s2 in collisions:
        struct = (s1.iso_key[0] != s2.iso_key[0]) or (s1.smooth != s2.smooth)
        event = True
        P(f"     *** COLLISION {s1.name} == {s2.name} sep=0 (n={nc}) "
          f"{'STRUCTURALLY DISTINCT -> CLAUSE-(c) EVENT' if struct else 'same family, inspect'} ***")
    if seps:
        mn, md, mx = seps[0], seps[len(seps) // 2], seps[-1]
        P(f"   non-iso pairs: {len(noniso)}   sep distribution  "
          f"min={mn}  median={md}  max={mx}")
        P("   closest (smallest-sep) non-iso pairs:")
        for sep, tgap, nc, s1, s2 in sorted(noniso, key=lambda r: (r[0], r[1]))[:6]:
            P(f"     {s1.name:20s} vs {s2.name:20s} sep={sep:6d}  "
              f"min t-gap>={_gapmin(s1, s2):.3f}  (n={nc})")
    P()

    # ---- verdict ----
    P("VERDICT:")
    if event:
        P("  *** clause-(c) EVENT or instrument defect flagged above --")
        P("      investigate with priority before any claim ***")
    else:
        P(f"  Clean null: all {len(noniso)} non-isomorphic pairs separate "
          f"(min sep = {seps[0]} > 0 in exact point counts), every")
        P("  forced-isomorphic control (Dwork c ~ -c) is identical as required,")
        P("  and the new counting cores are validated against brute enumeration")
        P("  and reproduce the k3_ledger diagonal readings.  No clause-(c) event")
        P("  on the Dwork pencil or the block-separable non-diagonal generics at")
        P("  the tested primes -- a clean strengthening of the retention register")
        P("  past the diagonal family, where no Faltings shield and no twist")
        P("  structure protects the ledger.")
    P()
    _write(lines)
    P("[results written to k3_nondiag_results.txt]")


def _gapmin(s1, s2):
    common = set(s1.counts) & set(s2.counts)
    return min(abs(s1.counts[p] - s2.counts[p]) / p for p in common)


def _m(a):
    return a.mean() if len(a) else float("nan")


def _write(lines):
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "k3_nondiag_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
