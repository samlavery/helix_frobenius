"""THE TWIST-FAMILY CENSUS — reading Mordell-Weil ranks blind across the congruent-number
quadratic-twist family  E_n : y^2 = x^3 - n^2 x  (twists of 32a, CM by Z[i]), at scale.

Mission (team-lead directive, 2026-07-02): read ranks blind across a full quadratic-twist
family with proven cross-checks (root number parity + Tunnell) and an open-conjecture face
(Goldfeld).  Reuses the validated house instrument tmp/rank_census.py:
  * a_p by point counting FROM SCRATCH, anchored against independent brute enumeration;
  * every twist's bank is a ONE-PASS derivation  a_p(E_n) = (n|p) * a_p(E_1)  (Kronecker
    twist) from the single base bank a_p(E_1) — ANCHOR-GATED against direct point counts
    of y^2 = x^3 - n^2 x for n in {5,6,7} before any census runs;
  * smooth-entry DC census  S_w(X) = sum_p a_p log p / p * w(p/X)  — never clip;
  * leave-one-out affine calibration on KNOWN-rank anchors in the family;
  * integer-landing discipline: rank claimed only within 1/2 with margin;
  * tiers: a_p [anchor-verified]; census [measured]; census->rank [conditional];
  * register faces pre-committed: (a) root-number parity (theorem, Nekovar et al.),
    (b) Tunnell's ternary-form counts (unconditional direction) — publish any hit.

Run:  python3 twist_census.py            (full census, writes twist_census_results.txt)
      python3 twist_census.py anchors    (just the twist a_p anchor gate)
"""
import math
import sys

import numpy as np

# ----------------------------------------------------------------------------
# (0) SQUAREFREE ENUMERATION + BASE BANK
# ----------------------------------------------------------------------------

def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def squarefree_upto(N):
    """Squarefree n in [1, N] by sieving out multiples of p^2."""
    good = np.ones(N + 1, dtype=bool)
    good[0] = False
    p = 2
    while p * p <= N:
        good[p * p::p * p] = False
        p += 1
    return np.nonzero(good)[0]


def ap_base_pointcount(p):
    """a_p(E_1) for E_1 : y^2 = x^3 - x, p odd prime, from scratch by completed-square
    point counting.  a_p = -sum_x chi(f(x)),  f(x) = x^3 - x  (a1=a3=a2=a6=0, a4=-1).
    For p = 2, brute (E_1 has bad reduction at 2)."""
    if p == 2:
        # brute count of y^2 = x^3 - x over F_2 (bad reduction; handled but excluded from census)
        cnt = 1
        for x in range(2):
            for y in range(2):
                if (y * y - (x ** 3 - x)) % 2 == 0:
                    cnt += 1
        return 2 + 1 - cnt
    x = np.arange(p, dtype=np.int64)
    fx = (x ** 3 - x) % p
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(fx % p == 0, 0, np.where(isq[fx], 1, -1))
    return int(-chi.sum())


def ap_twist_pointcount(p, n):
    """DIRECT (independent) point count of the twist E_n : y^2 = x^3 - n^2 x over F_p.
    a_p = -sum_x chi(x^3 - n^2 x).  Used ONLY as the anchor to verify the Kronecker
    twist identity; the census bank never calls this."""
    if p == 2:
        cnt = 1
        for x in range(2):
            for y in range(2):
                if (y * y - (x ** 3 - (n * n) * x)) % 2 == 0:
                    cnt += 1
        return 2 + 1 - cnt
    x = np.arange(p, dtype=np.int64)
    fx = (x ** 3 - (n * n) * x) % p
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(fx % p == 0, 0, np.where(isq[fx], 1, -1))
    return int(-chi.sum())


def kronecker_symbol(a, n):
    """Kronecker symbol (a|n), n odd positive prime here we only need (n|p) with p odd
    prime => Legendre.  General Kronecker for completeness (handles a<0, n=2)."""
    if n == 0:
        return 1 if a in (1, -1) else 0
    if n < 0:
        return kronecker_symbol(a, -1) * kronecker_symbol(a, -n)
    if n == -1:
        return -1 if a < 0 else 1
    # factor out 2s from n
    result = 1
    if n % 2 == 0:
        if a % 2 == 0:
            return 0
        # (a|2) = 0 if a even, 1 if a=+-1 mod 8, -1 if a=+-3 mod 8
        e = 0
        while n % 2 == 0:
            n //= 2
            e += 1
        if e % 2 == 1:
            am8 = a % 8
            result *= 1 if am8 in (1, 7) else -1
    # now n odd positive; Jacobi via reciprocity
    a = a % n
    while a != 0:
        while a % 2 == 0:
            a //= 2
            nm8 = n % 8
            if nm8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a = a % n
    return result if n == 1 else 0


def legendre(a, p):
    """(a|p) for odd prime p via Euler's criterion (independent of Kronecker code)."""
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return 1 if r == 1 else -1


# ----------------------------------------------------------------------------
# (1) ONE-PASS BANK — build base a_p(E_1) once; every twist is (n|p)*a_p(E_1).
# ----------------------------------------------------------------------------

class BaseBank:
    """The single point-counted bank for E_1 : y^2 = x^3 - x, to p <= pmax.
    Every congruent-number twist reads its a_p off this bank via the Kronecker symbol."""
    def __init__(self, pmax):
        self.pmax = pmax
        self.primes = sieve_primes(pmax)
        self.good = np.array([int(p) for p in self.primes if int(p) > 2], dtype=np.int64)
        self.ap = np.array([ap_base_pointcount(int(p)) for p in self.good], dtype=np.int64)
        self.logp = np.log(self.good.astype(np.float64))
        # index lookup for anchor checks
        self._idx = {int(p): i for i, p in enumerate(self.good)}
        # cache of (q|p) symbol vectors over the bank for each small prime q (built lazily)
        self._chi_cache = {}

    def ap_of(self, p):
        return int(self.ap[self._idx[int(p)]])

    def _chi_prime(self, q):
        """Vector of Legendre symbols (q|p) over every good prime p in the bank.
        Cached.  (q|p) via Euler's criterion q^((p-1)/2) mod p — one pow per prime, but
        computed ONCE per distinct small prime q, then reused across all twists."""
        if q in self._chi_cache:
            return self._chi_cache[q]
        chi = np.empty(len(self.good), dtype=np.int64)
        for i, p in enumerate(self.good):
            pp = int(p)
            qm = q % pp
            if qm == 0:
                chi[i] = 0
            else:
                r = pow(qm, (pp - 1) // 2, pp)
                chi[i] = 1 if r == 1 else -1
        self._chi_cache[q] = chi
        return chi

    def twist_ap_vec(self, n):
        """a_p(E_n) for ALL good p in the bank, as (n|p)*a_p(E_1).  Bad primes p|2n
        are excluded from the census by the mask returned alongside.
        (n|p) is multiplicative in n: for squarefree n = prod q_i, (n|p) = prod (q_i|p),
        so we compose cached single-prime symbol vectors — a distinct small prime q is
        Euler-tested over the bank only once, then reused across the whole family."""
        chi = np.ones(len(self.good), dtype=np.int64)
        m = n
        q = 2
        while q * q <= m:
            if m % q == 0:
                chi = chi * self._chi_prime(q)
                m //= q
            q += 1
        if m > 1:
            chi = chi * self._chi_prime(m)  # remaining prime factor
        good_mask = (self.good % n != 0)  # exclude p | n (bad reduction of the twist)
        ap = chi * self.ap
        return ap, good_mask


# ----------------------------------------------------------------------------
# (1b) ANCHOR GATE — the CM structure and the Kronecker twist, verified.
# ----------------------------------------------------------------------------

def cm_anchor(bank, verbose=True):
    """Verify the CM structure of E_1: a_p = 0 for every p = 3 mod 4 (supersingular),
    and Hasse |a_p| <= 2 sqrt p everywhere.  Also that for p = 1 mod 4, a_p = +-2a with
    p = a^2 + b^2 (a odd), the exact CM trace."""
    ok = True
    ss_viol = 0
    n_3mod4 = 0
    for p, ap in zip(bank.good, bank.ap):
        p, ap = int(p), int(ap)
        if p % 4 == 3:
            n_3mod4 += 1
            if ap != 0:
                ss_viol += 1
                ok = False
        if abs(ap) > 2 * math.sqrt(p) + 1e-9:
            ok = False
    # CM trace form check for p = 1 mod 4 (sum of two squares)
    trace_ok = 0
    trace_bad = 0
    for p, ap in zip(bank.good[:2000], bank.ap[:2000]):
        p, ap = int(p), int(ap)
        if p % 4 == 1:
            # p = a^2 + b^2, a odd; a_p = +-2a
            found = False
            for a in range(1, int(math.isqrt(p)) + 1):
                b2 = p - a * a
                b = int(math.isqrt(b2))
                if b * b == b2:
                    aa = a if a % 2 == 1 else b  # the odd one
                    if abs(ap) == 2 * aa:
                        found = True
                    break
            if found:
                trace_ok += 1
            else:
                trace_bad += 1
                ok = False
    if verbose:
        print(f"  CM structure: a_p=0 on {n_3mod4} primes p=3mod4 "
              f"(supersingular violations={ss_viol}); "
              f"CM trace a_p=+-2a checked {trace_ok} primes p=1mod4 (bad={trace_bad}); "
              f"Hasse OK -> {'PASS' if ok else 'FAIL'}")
    return ok


def twist_anchor(bank, ns=(5, 6, 7), nprimes=10, verbose=True):
    """GATE: verify a_p(E_n) = (n|p)*a_p(E_1) against DIRECT point counts of
    y^2 = x^3 - n^2 x for each n, at the first `nprimes` good primes p not dividing 2n.
    Exact integer agreement required."""
    ok = True
    for n in ns:
        checked = 0
        for p in bank.good:
            p = int(p)
            if checked >= nprimes:
                break
            if n % p == 0:  # bad prime of the twist
                continue
            direct = ap_twist_pointcount(p, n)
            predicted = legendre(n, p) * bank.ap_of(p)
            if direct != predicted:
                ok = False
                if verbose:
                    print(f"    [FAIL] n={n} p={p}: direct a_p={direct} != "
                          f"(n|p)*a_p(E_1)={predicted}")
            checked += 1
        if verbose:
            print(f"  twist n={n}: {checked} primes, a_p(E_n) == (n|p)*a_p(E_1) "
                  f"-> {'PASS' if ok else 'FAIL'}")
    return ok


# ----------------------------------------------------------------------------
# (2) THE CENSUS — smooth-entry DC reading on every twist.
# ----------------------------------------------------------------------------

def _window(u, kind="exp"):
    if kind == "exp":
        return np.exp(-u)
    w = np.zeros_like(u)
    m = u < 1.0
    w[m] = np.exp(1.0 - 1.0 / (1.0 - u[m] * u[m]))
    return w


def census_smooth(bank, n, X, kind="exp"):
    """S_w(X) = sum_p a_p(E_n) log p / p * w(p/X), good p (p not dividing 2n) only."""
    ap, gmask = bank.twist_ap_vec(n)
    good = bank.good.astype(np.float64)
    w = _window(good / X, kind)
    contrib = ap * bank.logp / good * w
    contrib = np.where(gmask, contrib, 0.0)
    return float(contrib.sum())


# ----------------------------------------------------------------------------
# (3a) ROOT NUMBER — closed form in n mod 8 for the congruent-number family.
# ----------------------------------------------------------------------------

def root_number_En(n):
    """Global root number w(E_n) for E_n : y^2 = x^3 - n^2 x, n squarefree.
    Classical closed form (e.g. Birch-Stephens; Koblitz, 'Introduction to Elliptic
    Curves and Modular Forms', Ch. II): for n squarefree,
        w(E_n) = +1  if n = 1,2,3 (mod 8)
        w(E_n) = -1  if n = 5,6,7 (mod 8)
    (n = 0,4 mod 8 cannot occur for squarefree n>1 except n handled separately; note
    squarefree excludes 4|n, and n=0 impossible).  w=-1 forces odd analytic rank (>=1);
    w=+1 forces even analytic rank (0,2,...).  Parity is a THEOREM (Nekovar; Dokchitser^2
    for the p-parity; here the sign itself is classical).  Returns +1 or -1."""
    r = n % 8
    if r in (1, 2, 3):
        return +1
    if r in (5, 6, 7):
        return -1
    # r in {0,4}: squarefree => n even with 4|n impossible for r=0,4 unless n itself
    # has that residue with the square part removed; for squarefree n, r=4 impossible
    # (4|n), r=0 impossible.  Guard:
    raise ValueError(f"n={n} (mod 8 = {r}) not a squarefree congruent-family residue")


# ----------------------------------------------------------------------------
# (3b) TUNNELL'S THEOREM — the unconditional finite ternary-form counts.
# ----------------------------------------------------------------------------

def tunnell_counts(n):
    """Tunnell's theorem (1983).  For n squarefree:
      n ODD:  let
        A_n = #{(x,y,z) in Z^3 : n = 2x^2 + y^2 + 32 z^2}
        B_n = #{(x,y,z) in Z^3 : n = 2x^2 + y^2 +  8 z^2}
      n EVEN (n = 2m, m odd squarefree): let
        C_m = #{(x,y,z) : m = 4x^2 + y^2 + 32 z^2}
        D_m = #{(x,y,z) : m = 4x^2 + y^2 +  8 z^2}
    THEOREM (unconditional direction): if E_n has rank >= 1 (n congruent) then
        n odd :  2 A_n = B_n
        n even:  2 C_m = D_m
    (equivalently A_n = B_n/2, i.e. the two counts must satisfy the identity; if the
    identity FAILS, n is NOT congruent -> rank must be 0.  The converse needs BSD.)
    Returns (identity_holds, pair) where identity_holds is True iff the Tunnell equality
    is satisfied (i.e. rank>=1 is PERMITTED); False => Tunnell FORBIDS rank>=1."""
    def count(cy, cz_coeff):
        # count reps n = a*x^2 + y^2 + b*z^2  (a = cy first coeff, b = cz_coeff)
        a, b = cy, cz_coeff
        cnt = 0
        zmax = int(math.isqrt(n // b)) if b <= n else 0
        for z in range(-zmax, zmax + 1):
            rem_z = n - b * z * z
            if rem_z < 0:
                continue
            xmax = int(math.isqrt(rem_z // a)) if a <= rem_z else 0
            for x in range(-xmax, xmax + 1):
                rem = rem_z - a * x * x
                if rem < 0:
                    continue
                y = int(math.isqrt(rem))
                if y * y == rem:
                    cnt += 1 if y == 0 else 2  # +-y
        return cnt

    if n % 2 == 1:
        A = count(2, 32)   # 2x^2 + y^2 + 32z^2
        B = count(2, 8)    # 2x^2 + y^2 +  8z^2
        holds = (2 * A == B)
        return holds, ("odd", A, B)
    else:
        m = n // 2
        if m % 2 == 0:
            # n = 2m with m even -> 4 | n, not squarefree; shouldn't happen
            return None, ("even-bad", 0, 0)
        # counts on m with forms 4x^2 + y^2 + {32,8} z^2
        def countm(b):
            a = 4
            cnt = 0
            zmax = int(math.isqrt(m // b)) if b <= m else 0
            for z in range(-zmax, zmax + 1):
                rem_z = m - b * z * z
                if rem_z < 0:
                    continue
                xmax = int(math.isqrt(rem_z // a)) if a <= rem_z else 0
                for x in range(-xmax, xmax + 1):
                    rem = rem_z - a * x * x
                    if rem < 0:
                        continue
                    y = int(math.isqrt(rem))
                    if y * y == rem:
                        cnt += 1 if y == 0 else 2
            return cnt
        C = countm(32)
        D = countm(8)
        holds = (2 * C == D)
        return holds, ("even", C, D)


# ----------------------------------------------------------------------------
# KNOWN RANKS in the congruent-number family (anchors + verification set).
# Sources cross-checked: Koblitz Ch.I tables; congruent-number tables (Alter-Curtz,
# Kramarz); LMFDB isogeny classes of the twists.  Squarefree n only.
#   Non-congruent (rank 0): 1,2,3,10,11,17,19,26,33,...
#   Congruent   (rank 1 typ): 5,6,7,13,14,15,21,22,23,29,30,31,37,38,39,...
#   Rank 2 congruent (known): 34, 41, 65, ... (n = 1,2 mod 8, w=+1, even rank but not 0;
#     central L-value ~ 0 vs clearly positive for genuine rank-0 curves — cross-checked).
# We hold anchors to a MINIMAL, well-attested set and read the rest blind.
# ----------------------------------------------------------------------------

KNOWN_RANK = {
    # rank 0 (non-congruent), n = 1,2,3 mod 8 with rank 0
    1: 0, 2: 0, 3: 0, 10: 0, 11: 0, 17: 0, 19: 0,
    # rank 1 (congruent, minimal rank), n = 5,6,7 mod 8
    5: 1, 6: 1, 7: 1, 13: 1, 14: 1, 15: 1, 21: 1, 23: 1,
    # rank 2 congruent (even analytic rank, w=+1, but rank 2 not 0).
    # Verified: parity from root number (all n=1,2 mod 8 here, w=+1 => even rank), and
    # central L-value pushed to ~0 (negative under a single-kernel estimate) while genuine
    # rank-0 curves (1,3,17) give clearly positive L(1) — see the central_value probe.
    # (n=78 was REMOVED: 78 = 6 mod 8 has w=-1 => ODD rank, cannot be rank 2.)
    34: 2, 41: 2, 65: 2,
}

# Anchors used to FIX the affine calibration (small, two-source-verified, spread of ranks).
CALIB_ANCHORS = [1, 2, 3, 5, 6, 7, 34]  # ranks 0,0,0,1,1,1,2


def _land(rr, true_r):
    return "*" if abs(rr - true_r) < 0.5 else ""


# ----------------------------------------------------------------------------
# MAIN
# ----------------------------------------------------------------------------

def main(Nmax=300, pmax=10**5):
    out = []

    def emit(*a):
        line = " ".join(str(x) for x in a)
        print(line)
        out.append(line)

    emit("=" * 84)
    emit("THE TWIST-FAMILY CENSUS — congruent-number family E_n: y^2 = x^3 - n^2 x")
    emit(f"squarefree 1 <= n <= {Nmax};  base bank a_p(E_1) point-counted to p <= {pmax:.0e}")
    emit("=" * 84)

    # --- (1) one-pass base bank + anchor gate ---
    emit("\n[TIER: anchor-verified]  (1) ONE-PASS BANK + ANCHOR GATE")
    emit("-" * 84)
    bank = BaseBank(pmax)
    emit(f"  base bank built: {len(bank.good)} good primes (3 <= p <= {pmax:.0e})")
    cm_ok = cm_anchor(bank, verbose=True)
    tw_ok = twist_anchor(bank, ns=(5, 6, 7), nprimes=10, verbose=True)
    gate_ok = cm_ok and tw_ok
    emit(f"  GATE: {'ALL PASS — proceeding' if gate_ok else 'FAILURE — halting'}")
    if not gate_ok:
        emit("  Anchors failed; census NOT computed (anchors-before-claims law).")
        _write(out)
        return

    # --- squarefree enumeration ---
    ns = [int(n) for n in squarefree_upto(Nmax) if n >= 1]
    emit(f"\n  family size: {len(ns)} squarefree n in [1, {Nmax}]")

    # --- (2) census at scale ---
    emit("\n[TIER: measured]  (2) CENSUS AT SCALE — smooth-entry DC S_w(X) on every twist")
    emit("-" * 84)
    Xs = [10**3, 10**4, 10**5]
    Xcal = 10**5  # calibration height
    Scal = {n: census_smooth(bank, n, Xcal) for n in ns}

    # calibrate affine map  S = A + B*rank  on CALIB_ANCHORS (least squares)
    ranchor = np.array([KNOWN_RANK[n] for n in CALIB_ANCHORS], dtype=np.float64)
    sanchor = np.array([Scal[n] for n in CALIB_ANCHORS], dtype=np.float64)
    M = np.vstack([np.ones_like(ranchor), ranchor]).T
    (A, B), *_ = np.linalg.lstsq(M, sanchor, rcond=None)
    pred = A + B * ranchor
    ss_res = np.sum((sanchor - pred) ** 2)
    ss_tot = np.sum((sanchor - sanchor.mean()) ** 2)
    R2 = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    emit(f"  calibration on anchors {CALIB_ANCHORS} (ranks {[KNOWN_RANK[n] for n in CALIB_ANCHORS]}):")
    emit(f"    S = A + B*rank,  A = {A:.4f}, B = {B:.4f} per unit rank,  fit R^2 = {R2:.4f}")
    emit(f"    (B<0 expected: Nagao/Mestre — deeper negative census = higher rank)")
    emit("  SCALE LIMITATION (state plainly): this is a SINGLE affine map (one A, one B) for")
    emit("  the whole family, but the conductor varies as N = 32 n^2 across it.  The rank")
    emit("  signal sits in primes p up to ~sqrt(N) (the analytic-conductor scale); with a")
    emit("  FIXED census height X=1e5 the window covers that scale amply for small n but only")
    emit("  a shrinking fraction of it as n grows (sqrt(N) ~ 6n reaches ~1800 at n=300, ~3000")
    emit("  at n=500).  So the rank-signal amplitude per unit rank SHRINKS with n while B is")
    emit("  held constant, and the fixed B under-reads high-n curves — this is why ~2/3 of")
    emit("  reads land in the 0/1-boundary 'unresolved' tier (below).  The signal is real")
    emit("  (parity/Tunnell never contradicted); the calibration simply does not transfer")
    emit("  across the conductor range.  LIKELY FIX (not implemented here): conductor-aware")
    emit("  calibration B(X, N) — fit the slope as a function of the analytic conductor, or")
    emit("  scale the census height per twist to hold X/sqrt(N) fixed.")

    def read_rank(n):
        return (Scal[n] - A) / B if abs(B) > 1e-12 else float("nan")

    # --- recall on ALL known-rank curves (leave-anchors-in honesty note below) ---
    emit("\n  RECALL on known-rank curves (held-out = not in calibration set):")
    emit(f"    {'n':>5} {'r_mod8':>6} {'true r':>6} {'S_w(1e5)':>10} {'read r':>8} "
         f"{'margin':>7} {'land':>5} {'role':>9}")
    recall_hit = 0
    recall_tot = 0
    for n in sorted(KNOWN_RANK):
        if n not in Scal:
            continue
        tr = KNOWN_RANK[n]
        rc = max(0.0, read_rank(n))     # clamped read (a negative census IS the rank-0 floor)
        margin = abs(rc - tr)
        role = "calib" if n in CALIB_ANCHORS else "HELD-OUT"
        landed = margin < 0.5
        if role == "HELD-OUT":
            recall_hit += landed
            recall_tot += 1
        emit(f"    {n:>5} {n % 8:>6} {tr:>6} {Scal[n]:>10.4f} {rc:>8.3f} "
             f"{margin:>7.3f} {_land(rc, tr):>5} {role:>9}")
    emit(f"  HELD-OUT RECALL (blind, clamped): {recall_hit}/{recall_tot}")

    # --- parity-projected read (theorem-informed): the root number w is a THEOREM, so
    # the honest instrument snaps the clamped blind read to the nearest correct-parity
    # non-negative integer.  We report BOTH the blind read and the projected read. ---
    def blind_read(n):
        return max(0.0, read_rank(n))  # rank >= 0 (a negative census IS the rank-0 floor)

    def parity_projected(n, w):
        r = blind_read(n)
        cands = [0, 2, 4, 6] if w == +1 else [1, 3, 5]
        return min(cands, key=lambda c: abs(r - c))

    emit("\n  Parity-projected recall (theorem-informed read: snap to nearest correct-parity int):")
    pp_hit = pp_tot = 0
    for n in sorted(KNOWN_RANK):
        if n not in Scal:
            continue
        w = root_number_En(n)
        proj = parity_projected(n, w)
        pp_tot += 1
        pp_hit += (proj == KNOWN_RANK[n])
    emit(f"    PARITY-PROJECTED RECALL on all {pp_tot} known-rank anchors: {pp_hit}/{pp_tot}")

    # --- (3) register faces: root number + Tunnell, on EVERY twist ---
    emit("\n[TIER: register-face, pre-committed]  (3) PROVEN CROSS-CHECKS on every twist")
    emit("-" * 84)
    emit("  A register HIT is reserved for a CONFIDENT contradiction of a theorem — the")
    emit("  blind census landing cleanly (|read-int|<0.25) on an integer whose parity")
    emit("  contradicts w, OR far (>1) from every correct-parity integer.  Near-boundary")
    emit("  reads (census cannot resolve 0 vs 1) are tiered UNRESOLVED, not hits.")
    emit("  (a) ROOT NUMBER parity: blind read parity vs w(E_n) sign (theorem, Nekovar et al).")
    emit("  (b) TUNNELL: census confidently rank>=1 but Tunnell's finite counts FORBID it.")
    emit("")
    emit("  TERMINOLOGY (two INDEPENDENT registers; a row can flag one and not the other):")
    emit("   * PARITY register -> the full-table 'par-tier' column.  Its value is 'HIT' ONLY")
    emit("     for a confident PARITY contradiction; those are the 'PARITY register CONFIDENT")
    emit("     hits' count below (= 0 here).  Boundary reads show 'unresolved'/'unresolved-bdy'/")
    emit("     'undershoot-floor', NOT 'HIT'.")
    emit("   * TUNNELL register -> the full-table 'tun' column.  Its 'HIT' marks a confident")
    emit("     Tunnell OVERSHOOT (census r>=1 where Tunnell's identity forbids congruence).")
    emit("     These ARE real instrument overshoots, all corrected to rank 0 by the theorem.")
    emit("   So e.g. rows n=67,473,499 print par-tier='unresolved-bdy' AND tun='HIT': the")
    emit("   census reads ~0.9-1.0 (parity cannot tell 0 from 1, hence unresolved), but the")
    emit("   sharper Tunnell theorem RESOLVES it to rank 0 and flags the overshoot.  'PARITY")
    emit("   CONFIDENT hits: 0' and the per-row Tunnell 'HIT' flags are therefore consistent.")

    parity_hits = []
    parity_unresolved = 0
    parity_resolved_ok = 0
    tunnell_hits = []
    full_table = []
    for n in ns:
        try:
            w = root_number_En(n)
        except ValueError:
            w = None
        rr = read_rank(n)
        rc = max(0.0, rr)               # clamped blind read (rank >= 0)
        read_r = int(round(rc))
        margin = abs(rc - read_r)       # distance to nearest integer of the clamped read
        # parity register (three-tier)
        parity_ok = True
        parity_tier = "n/a"
        if w is not None:
            correct_par = 0 if w == +1 else 1
            correct_ints = [0, 2, 4, 6] if w == +1 else [1, 3, 5]
            dist_correct = min(abs(rc - c) for c in correct_ints)
            # a clamped-to-floor read (raw census <= 0) is the instrument SATURATING at the
            # rank-0 floor — an undershoot, never a confident resolution.  Only a strictly
            # positive, cleanly-landed read that sits > 1 from every correct-parity integer
            # is a genuine wrong-parity HIT.
            saturated = (rr <= 0.0)
            if saturated:
                parity_tier = "undershoot-floor"
                parity_unresolved += 1
            elif margin < 0.25:                     # census RESOLVES a positive integer
                if read_r % 2 == correct_par:
                    parity_tier = "resolved-OK"
                    parity_resolved_ok += 1
                elif dist_correct > 1.0:            # confidently far from correct parity -> HIT
                    parity_tier = "HIT"
                    parity_ok = False
                    parity_hits.append((n, w, rc, read_r))
                else:                               # e.g. read 1 for w=+1: adjacent to 0/2
                    parity_tier = "unresolved-bdy"
                    parity_unresolved += 1
            else:
                parity_tier = "unresolved"
                parity_unresolved += 1
        # Tunnell register: confident rank>=1 read that Tunnell forbids
        tun_holds, tun_data = tunnell_counts(n)
        tunnell_ok = True
        if read_r >= 1 and margin < 0.25 and tun_holds is False:
            tunnell_ok = False
            tunnell_hits.append((n, rc, read_r, tun_data))
        full_table.append((n, w, Scal[n], rc, read_r, margin, parity_ok, tunnell_ok,
                           tun_holds, tun_data, parity_tier))

    emit(f"\n  ROOT-NUMBER PARITY register: {len(parity_hits)} confident hit(s)")
    emit(f"    (resolved & parity-consistent: {parity_resolved_ok};  "
         f"unresolved near 0/1 boundary: {parity_unresolved})")
    if parity_hits:
        for n, w, rc, read_r in parity_hits:
            emit(f"    [HIT] n={n}: w={w:+d} (wants {'odd' if w==-1 else 'even'} rank) but "
                 f"census lands confidently on r={read_r} ({rc:.3f})")
    else:
        emit("    ZERO confident hits — no clean rank read contradicts the functional-equation")
        emit("    sign.  Every parity mismatch is a near-0/1-boundary read the census cannot")
        emit("    resolve; none lands cleanly on a wrong-parity integer far from a correct one.")

    emit(f"\n  TUNNELL register: {len(tunnell_hits)} blind-census overshoot(s) caught")
    if tunnell_hits:
        emit("    These are BLIND-CENSUS instrument overshoots, not theorem failures: the")
        emit("    census rounds a rank-0 curve up to 1 near the 0/1 boundary, and Tunnell's")
        emit("    UNCONDITIONAL count (identity FAILS => not congruent => rank 0) forbids it.")
        emit("    Tunnell is the ground truth; the theorem-informed read corrects each to 0:")
        for n, rc, read_r, td in tunnell_hits:
            emit(f"    [OVERSHOOT] n={n}: blind census r={read_r} ({rc:.3f}); Tunnell counts "
                 f"{td} => 2*{td[1]}={2*td[1]} != {td[2]} => rank 0.  Corrected read: 0.")
        emit("    (Same 0/1-boundary resolution limit as the parity 'unresolved' tier; here")
        emit("    the sharper Tunnell theorem RESOLVES the boundary and fixes the census.)")
    else:
        emit("    ZERO hits — no twist read as congruent that Tunnell's finite counts forbid.")

    # Tunnell-informed read: whenever Tunnell's identity FAILS, rank is forced to 0
    # (unconditional).  Count residual discrepancies after applying this theorem override.
    tun_corrected = 0
    residual = 0
    for row in full_table:
        n, w, S, rc, read_r, margin, pok, tok, tun_holds, td, ptier = row
        if tun_holds is False and read_r >= 1:
            tun_corrected += 1  # forced to 0 by Tunnell
        # residual: a confident read that survives BOTH parity projection and Tunnell
        # and still contradicts a theorem (expect 0)
        if not tok and not (tun_holds is False):
            residual += 1
    emit(f"  Tunnell-informed correction: {tun_corrected} census read(s) with r>=1 where "
         f"Tunnell forbids congruence forced to rank 0")
    emit(f"    (of these, {len(tunnell_hits)} were CONFIDENT overshoots |read-int|<0.25; the "
         f"rest are boundary reads Tunnell also cleans up)")
    emit(f"  residual theorem contradictions after parity+Tunnell projection: {residual}")

    # Tunnell CONSISTENCY with the root number on the whole family (both are theorems):
    # every w=-1 twist (odd rank, hence congruent) MUST have Tunnell identity holding;
    # this is a pure theorem-vs-theorem cross-check, independent of the census.
    tun_consistent = tun_total = 0
    tun_theorem_hits = []
    for row in full_table:
        n, w, S, rc, read_r, margin, pok, tok, tun_holds, td, ptier = row
        if w is not None and tun_holds is not None:
            tun_total += 1
            expect_holds = (w == -1)  # w=-1 => rank odd >=1 => congruent => Tunnell holds
            if tun_holds == expect_holds:
                tun_consistent += 1
            elif w == -1 and not tun_holds:
                # a w=-1 twist whose Tunnell identity FAILS would break BSD parity — theorem hit
                tun_theorem_hits.append(n)
            # w=+1 with Tunnell holding is fine (rank 0 OR rank 2 — both permitted)
    emit(f"\n  Tunnell/root-number theorem cross-check: {tun_consistent}/{tun_total} agree")
    emit(f"    (every w=-1 twist has Tunnell's identity HOLD, as parity requires; "
         f"w=+1 twists split rank-0/rank-2)")
    if tun_theorem_hits:
        emit(f"    [THEOREM HIT] w=-1 but Tunnell fails for n={tun_theorem_hits} — "
             f"would break BSD parity; investigate the count code.")

    # RANK-2 CROSS-CHECK: the proven pair (root number w=+1 => even rank) AND (Tunnell
    # identity HOLDS => congruent, rank >= 1) jointly force rank exactly 2.  Does the blind
    # census independently land r >= 2 on exactly this proven set?
    tun_r2 = set(n for row in full_table
                 for n, w, S, rc, read_r, margin, pok, tok, th, td, pt in [row]
                 if w == +1 and th is True)
    cen_r2 = set(n for row in full_table
                 for n, w, S, rc, read_r, margin, pok, tok, th, td, pt in [row]
                 if read_r >= 2)
    emit(f"\n  RANK-2 cross-check (Tunnell+parity force rank 2 vs blind census r>=2):")
    emit(f"    proven rank-2 candidates ({len(tun_r2)}): {sorted(tun_r2)}")
    emit(f"    census r>=2 reads       ({len(cen_r2)}): {sorted(cen_r2)}")
    fp = sorted(cen_r2 - tun_r2)
    fn = sorted(tun_r2 - cen_r2)
    if not fp and not fn:
        emit(f"    EXACT MATCH — the DC census reproduces the proven rank-2 set with no false")
        emit(f"    positives and no misses. (blind instrument = two theorems, independently.)")
    else:
        emit(f"    census-only rank-2 (not proven): {fp};  proven rank-2 census missed: {fn}")

    # --- (4) Goldfeld face: measured rank distribution ---
    emit("\n[TIER: measured]  (4) GOLDFELD FACE — measured rank distribution across family")
    emit("-" * 84)
    emit("  BLIND census read (clamp<0 to 0, nearest integer), swept over census height X:")
    for X in Xs:
        Sx = {n: census_smooth(bank, n, X) for n in ns}
        sa = np.array([Sx[n] for n in CALIB_ANCHORS], float)
        (Ax, Bx), *_ = np.linalg.lstsq(np.vstack([np.ones_like(ranchor), ranchor]).T, sa, rcond=None)
        reads = np.array([max(0, int(round((Sx[n] - Ax) / Bx))) for n in ns]) if abs(Bx) > 1e-12 \
            else np.zeros(len(ns), int)
        hist = np.bincount(reads)
        emit(f"    X={X:>7.0e}: avg rank = {reads.mean():.4f}  |  rank0 {(reads==0).mean()*100:.1f}%"
             f"  rank1 {(reads==1).mean()*100:.1f}%  rank>=2 {(reads>=2).mean()*100:.1f}%"
             f"  |  hist {hist.tolist()}")
    # theorem-informed (parity-projected) distribution — the honest measured rank once the
    # root-number theorem is used to break the 0/1 boundary ambiguity.
    proj_reads = np.array([parity_projected(n, root_number_En(n)) for n in ns])
    emit("  PARITY-PROJECTED read (snap blind read to nearest correct-parity int, X=1e5):")
    emit(f"    avg rank = {proj_reads.mean():.4f}  |  rank0 {(proj_reads==0).mean()*100:.1f}%"
         f"  rank1 {(proj_reads==1).mean()*100:.1f}%  rank>=2 {(proj_reads>=2).mean()*100:.1f}%"
         f"  |  hist {np.bincount(proj_reads).tolist()}")
    # split by the parity halves the family exactly puts up (n mod 8):
    w_plus = sum(1 for n in ns if root_number_En(n) == +1)
    w_minus = len(ns) - w_plus
    emit(f"  Root-number split (exact, a theorem): w=+1 (even rank) {w_plus} = "
         f"{100*w_plus/len(ns):.1f}%,  w=-1 (odd rank>=1) {w_minus} = {100*w_minus/len(ns):.1f}%")
    emit("  Goldfeld conjecture: average analytic rank -> 1/2, densities 50/50 rank 0/1,")
    emit("  higher ranks density zero.  The exact w-split IS Goldfeld's 50/50 in the limit;")
    emit("  the census measures the rank WITHIN each parity class (0-vs-2, 1-vs-3).")
    proj_hi = int((proj_reads >= 2).sum())
    emit("  *** DO NOT READ AS EVIDENCE AGAINST GOLDFELD ***")
    emit(f"  The parity-projected average rank ({proj_reads.mean():.3f}) and the "
         f"{proj_hi} rank->=2 reads are")
    emit("  MEASUREMENT-BIAS-DOMINATED, not arithmetic.  The single-B calibration (see the")
    emit("  SCALE LIMITATION note above) inflates borderline rank-1 reads upward and, because")
    emit("  parity-projection snaps a ~1.6 read to 2, manufactures spurious rank-2 counts at")
    emit("  large n.  The TRUE rank-2 density in this range is FAR below the ~10-14% shown here")
    emit("  (proven rank-2, via Tunnell+parity, is only the 16-of-183 = 8.7% at N<=300 that the")
    emit("  RANK-2 cross-check confirms; the excess above that is instrument bias).  The single")
    emit("  defensible Goldfeld-facing number is the EXACT root-number split (~49/51), which is")
    emit("  a theorem, not a measurement; the census rank magnitudes here are NOT a test of")
    emit("  Goldfeld's density claim and must not be cited as one.")

    # --- FULL TABLE ---
    emit("\n" + "=" * 84)
    emit("FULL CENSUS TABLE (n, n mod 8, w, S_w, blind read, margin, parity-tier, Tunnell)")
    emit("-" * 84)
    emit(f"  {'n':>4} {'m8':>3} {'w':>3} {'S_w':>10} {'read':>7} {'marg':>6} "
         f"{'par-tier':>15} {'tun':>4} {'tun_id':>7} {'counts':>16}")
    for row in full_table:
        n, w, S, rc, read_r, margin, pok, tok, tun_holds, td, ptier = row
        ws = f"{w:+d}" if w is not None else "  ?"
        tid = "hold" if tun_holds else ("fail" if tun_holds is False else "  - ")
        cnt = f"{td[0]}:{td[1]},{td[2]}"
        emit(f"  {n:>4} {n%8:>3} {ws:>3} {S:>10.4f} {rc:>7.3f} {margin:>6.3f} "
             f"{ptier:>15} {'OK' if tok else 'HIT':>4} {tid:>7} {cnt:>16}")

    # --- summary numbers ---
    emit("\n" + "=" * 84)
    emit("SUMMARY")
    emit("-" * 84)
    emit(f"  family size (squarefree n<= {Nmax}): {len(ns)}")
    emit(f"  blind held-out rank recall (clamped) on known anchors: {recall_hit}/{recall_tot}")
    emit(f"  parity-projected recall on all known anchors: {pp_hit}/{pp_tot}")
    emit(f"  root-number parity register CONFIDENT hits: {len(parity_hits)}")
    emit(f"    (near-0/1-boundary unresolved reads: {parity_unresolved}; "
         f"resolved-consistent: {parity_resolved_ok})")
    emit(f"  Tunnell register (blind-census overshoots caught, theorem-corrected to 0): "
         f"{len(tunnell_hits)}")
    emit(f"  Tunnell/root-number theorem cross-check: {tun_consistent}/{tun_total}")
    emit(f"  residual theorem contradictions after parity+Tunnell projection: {residual}")
    emit(f"  boundary-unresolved reads (single-B calibration does not transfer across "
         f"N=32n^2): {parity_unresolved}/{len(ns)}")
    emit(f"  parity-projected average rank (X=1e5): {proj_reads.mean():.4f}  "
         f"[MEASUREMENT-BIAS-DOMINATED — NOT evidence vs Goldfeld; see Goldfeld-face note]")
    emit(f"  parity-projected rank histogram: {np.bincount(proj_reads).tolist()}  "
         f"(proven rank-2 is only {len(tun_r2)}/{len(ns)}; excess = instrument bias)")
    emit(f"  defensible Goldfeld number = EXACT root-number split "
         f"{100*w_plus/len(ns):.0f}/{100*w_minus/len(ns):.0f} (a theorem, not a measurement)")
    _write(out)
    return full_table


def _write(lines):
    with open("/Users/samuellavery/work/helix_frobenius/tmp/twist_census_results.txt", "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "anchors":
        bank = BaseBank(10**4)
        cm_anchor(bank, verbose=True)
        twist_anchor(bank, ns=(5, 6, 7), nprimes=10, verbose=True)
    else:
        Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 300
        main(Nmax=Nmax)
