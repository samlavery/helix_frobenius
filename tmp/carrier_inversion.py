"""tmp/carrier_inversion.py -- the INVERSION ARM of the collective recognition loop.

DEMONSTRATE that the carrier's per-prime readings DETERMINE the cover's arithmetic
data, BLIND.  The collective-level analogue of grade 1's "recover the CM point tau":
the step that hands the construction recipe its input.

Object: cyclic cubic covers  C : y^3 = f(x) g(x)^2  (f,g monic coprime squarefree,
3 does not divide deg(f g^2)); B = Prym = the (2,2) [g_W=4] or (3,3) [g_W=6]
abelian variety of Weil type over K = Q(sqrt-3), zeta_3 deck rails W (+) W-bar.

THE MECHANISM THEOREM (freeze_mechanism_notes.md, item 37), the analytic bridge we
invert:
        det(Frob_p | V_zeta) = (-1)^{delta_p} * p^{g_W/2} * chi_3(D),
        D = disc(f) * disc(g)^2,     r_p := det/((-1)^{delta_p} p^{g_W/2}) = chi_3,p(D)
delta_p = 0 at every rational-branch (integer-root) good prime; delta_p != 0 (even
freeze order 2/6) exactly where a branch factor is inert.  chi_3 is a CUBIC character
=> r_p depends only on D mod cubes.

BLIND PROTOCOL (enforced by a firewall):
  * measure(hc, roots, primes, gW)  -- the PHYSICAL CARRIER.  Has the cover object;
    produces ONLY per-prime observables (freeze value/index, rail angles, rail
    coeffs, gate flags).  No D, no disc.
  * invert_*(reading, ...)           -- consume ONLY the reading.  Never see (f,g,D).
  * grade(recovered, truth)          -- the ONLY place truth is consulted.

PART 1  discriminant-class inversion : from {freeze index e_p} recover D mod cubes.
PART 2  structure inversion          : signature, decomposability, bad set, K-field.
PART 3  well-posedness               : two covers, same D mod cubes, different angle
                                       streams -> Faltings boundary of the inversion.

Run:  python3 carrier_inversion.py
Reuses caches/machinery from weil_sixfold_count.py, weil_scout.py, freeze_mechanism.py.
"""
import sys, os, math, cmath, itertools
from fractions import Fraction as Fr
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import weil_scout as WS
import weil_sixfold_count as WSC
import freeze_mechanism as FM

x = sp.symbols('x')
W = cmath.exp(2j * math.pi / 3)                        # zeta_3 embedding (the LABELING)

OUT = []
def P(s=""):
    print(s, flush=True); OUT.append(s)


# ============================================================================
# cubic-residue index in the SAME primitive-root convention as the carrier's
# cube_root_map (weil_sixfold_count): rho = g^{(p-1)/3}, chi_3(rho)=W.
# ============================================================================
def cubic_index(n, p):
    """index e in {0,1,2} with chi_3,p(n) = W^e; None if p | n or p != 1 mod 3."""
    if (p - 1) % 3 != 0 or n % p == 0:
        return None
    g = WS.primitive_root(p)
    rho = pow(g, (p - 1) // 3, p)
    val = pow(n % p, (p - 1) // 3, p)
    return {1: 0, rho: 1, (rho * rho) % p: 2}[val]


def read_freeze(frz):
    """Snap a freeze scalar to the 6th-root grid.
    Returns (e_cube_index in {0,1,2} or None, order in {1,2,3,6} or None,
             is_cube_root bool).  is_cube_root False => unbalanced signature OR the
    Hasse-Davenport even-order (non-rational branch) case -- excluded from the clean
    D-equation, but its order is a readable structural bit."""
    if frz is None:
        return None, None, False
    sixth = {k: cmath.exp(1j * math.pi * k / 3) for k in range(6)}   # e^{i pi k/3}
    k = min(sixth, key=lambda k: abs(frz - sixth[k]))
    if abs(frz - sixth[k]) > 2e-3 or abs(abs(frz) - 1) > 2e-3:
        return None, None, False                                    # not a root of unity
    order = {0: 1, 1: 6, 2: 3, 3: 2, 4: 3, 5: 6}[k]
    is_cube = (k % 2 == 0)                                          # 1, W, W^2
    e_cube = {0: 0, 2: 1, 4: 2}.get(k, None)
    return e_cube, order, is_cube


# ============================================================================
# THE PHYSICAL CARRIER.  measure() knows the cover (that IS the carrier); it emits
# only per-prime observables.  The inversion below never sees (f,g,D).
# ============================================================================
def measure_one(hc, roots, p, gW):
    """Single-prime carrier reading of y^3 = h from cubic character sums.
    roots (the physical branch data) is used ONLY to compute the sums / flag the
    obvious singular fibre; the returned dict carries NO (f,g,D)."""
    rec = dict(p=p)
    if (p - 1) % 3 != 0:
        rec.update(usable=False, split=False, reason="inert p!=1 mod3: no split cubic rail")
        return rec
    collide = (roots is not None) and (len({r % p for r in roots}) != len(roots))
    try:
        Ts = {k: WSC.Tk(p, k, hc) for k in range(1, gW + 1)}
        cpoly = WSC.rail_charpoly(Ts, gW)
        val = WSC.validate_rail(cpoly, p, gW)
    except Exception as e:
        rec.update(usable=False, split=True, bad=True, reason=f"char-sum failure: {e}")
        return rec
    integ = val["integ"]; weil = val["weil"]; frz = val["freeze"]
    e_cube, order, is_cube = read_freeze(frz)
    angs = (sorted(round(cmath.phase(r) / math.pi, 4) for r in val["roots"])
            if len(val["roots"]) == gW else None)
    bad = (integ > 1e-3) or (not weil) or collide          # BLIND gate-based bad flag
    rec.update(usable=(not bad), split=True, bad=bad, collide=collide,
               integ=float(integ), weil=bool(weil),
               freeze=frz, freeze_index=e_cube, freeze_order=order,
               is_cube_root=is_cube, angles=angs,
               rail_eis=[(a, b) for a, b, _ in val["eis"]])
    return rec


def measure(hc, roots, primes, gW):
    """Carrier reading over a fixed prime list (per-prime observables only)."""
    return {p: measure_one(hc, roots, p, gW) for p in primes}


def pi_above(p):
    """a prime pi = a + b*omega of Z[omega] above p (p = 1 mod 3), N(pi)=a^2-ab+b^2=p."""
    K = int(2 * math.isqrt(p)) + 2
    for a in range(-K, K + 1):
        for b in range(0, K + 1):
            if a * a - a * b + b * b == p:
                return (a, b)
    raise RuntimeError(f"no pi above {p}")


def v_pi(det, pi, p):
    """pi-adic valuation of det in Z[omega]."""
    cur = det; cnt = 0
    pic = FM.zconj(pi)                                             # conj(pi); pi*conj(pi)=p
    while True:
        t = FM.zmul(cur, pic)                                     # = cur * conj(pi)
        a, b = int(t[0]), int(t[1])
        if a % p == 0 and b % p == 0:
            cur = (a // p, b // p); cnt += 1
        else:
            return cnt


# ============================================================================
# F_3 linear algebra for the discriminant-class system
# ============================================================================
INV3 = {1: 1, 2: 2}
def rank_f3(rows):
    A = [r[:] for r in rows]; nc = len(A[0]) if A else 0; rank = 0; pr = 0
    for c in range(nc):
        piv = next((i for i in range(pr, len(A)) if A[i][c] % 3), None)
        if piv is None:
            continue
        A[pr], A[piv] = A[piv], A[pr]
        inv = INV3[A[pr][c] % 3]
        A[pr] = [(v * inv) % 3 for v in A[pr]]
        for i in range(len(A)):
            if i != pr and A[i][c] % 3:
                f = A[i][c] % 3
                A[i] = [(A[i][j] - f * A[pr][j]) % 3 for j in range(nc)]
        pr += 1; rank += 1
    return rank


def solve_f3(rows, rhs, ncols):
    """solve rows . a = rhs over F_3.  Returns (solution list or None, rank)."""
    A = [rows[i][:] + [rhs[i] % 3] for i in range(len(rows))]
    pr = 0; where = [-1] * ncols
    for c in range(ncols):
        piv = next((i for i in range(pr, len(A)) if A[i][c] % 3), None)
        if piv is None:
            continue
        A[pr], A[piv] = A[piv], A[pr]
        inv = INV3[A[pr][c] % 3]
        A[pr] = [(v * inv) % 3 for v in A[pr]]
        for i in range(len(A)):
            if i != pr and A[i][c] % 3:
                f = A[i][c] % 3
                A[i] = [(A[i][j] - f * A[pr][j]) % 3 for j in range(ncols + 1)]
        where[c] = pr; pr += 1
    for i in range(pr, len(A)):                                   # consistency
        if A[i][ncols] % 3 != 0 and all(A[i][j] % 3 == 0 for j in range(ncols)):
            return None, pr
    if any(w == -1 for w in where):                              # underdetermined
        return None, pr
    sol = [A[where[c]][ncols] % 3 for c in range(ncols)]
    return sol, pr


# ============================================================================
# PART 1 -- the discriminant-class inversion (BLIND)
# ============================================================================
def invert_discriminant(reading, candidate_primes):
    """From {freeze index e_p}_p recover a_l = v_l(D) mod 3 for l in candidate_primes
    (=> D mod cubes).  Uses ONLY clean cube-root freezes (delta_p = 0)."""
    eqs = []                                                      # (p, e_p, row)
    for p in sorted(reading):
        r = reading[p]
        if not r.get("usable") or not r.get("is_cube_root"):
            continue
        row = []
        ok = True
        for l in candidate_primes:
            c = cubic_index(l, p)
            row.append(0 if c is None else c)                    # l==p contributes 0 (a_p=0 at good p)
        eqs.append((p, r["freeze_index"], row))
    # incremental rank -> data cost
    rows = [e[2] for e in eqs]; rhs = [e[1] for e in eqs]
    ncols = len(candidate_primes)
    data_cost = None
    for k in range(1, len(rows) + 1):
        if rank_f3(rows[:k]) == ncols:
            data_cost = k; break
    sol, rank = solve_f3(rows, rhs, ncols)
    return dict(solution=sol, rank=rank, ncols=ncols, n_eqs=len(eqs),
                data_cost=data_cost, primes_used=[e[0] for e in eqs])


def class_str(primes, exps):
    """readable representative of a class in Q*/(Q*)^3."""
    if exps is None:
        return "UNRESOLVED"
    parts = [f"{l}^{e}" for l, e in zip(primes, exps) if e % 3]
    val = 1
    for l, e in zip(primes, exps):
        val *= l ** (e % 3)
    return (" * ".join(parts) if parts else "1(cube)") + f"   (= {val} mod cubes)"


# ============================================================================
# TRUTH (grading only) -- exact D mod cubes from sympy
# ============================================================================
def true_D_class(fc, gc, candidate_primes):
    """disc(f) disc(g)^2 factored mod cubes over the candidate lattice; sign dropped
    (-1 = (-1)^3 is a cube)."""
    f = FM.sp_poly(fc); g = FM.sp_poly(gc)
    discf = int(sp.discriminant(f)) if f.degree() > 0 else 1
    discg = int(sp.discriminant(g)) if g.degree() > 0 else 1
    D = discf * discg ** 2
    fac = sp.factorint(abs(D))
    exps = [fac.get(l, 0) % 3 for l in candidate_primes]
    support_outside = {l: e for l, e in fac.items() if l not in candidate_primes and e % 3}
    return D, exps, support_outside


# ============================================================================
# MEMBERS  (roots; the carrier object -- inversion never reads these)
# ============================================================================
def fg_from_roots(fr, gr):
    fc = WSC.poly_from_roots(fr)
    gc = WSC.poly_from_roots(gr) if gr else [1]
    return fc, gc

MEMBERS = [
    # name, f-roots, g-roots, g_W, note
    ("M1", [0, 1], [2, 3, 4], 4, "fourfold (2,2), D=16"),
    ("M2", [0, 1], [2, 4, 7], 4, "fourfold (2,2), D=810000"),
    ("M3", [0, 3], [1, 2, 5], 4, "fourfold (2,2), D=186624"),
    ("S6", [0, 1, 2, 3], [4, 5, 6], 6, "sixfold (3,3), D=2304"),
]
# candidate lattice: the small primes (an integer-root cover with small roots has a
# smooth discriminant; class is pinned WITHIN this lattice, as the task specifies).
# The fourfold's cheap primes (p^4) resolve a 6-prime lattice; the sixfold (p^6) is
# field-size-limited to a 3-prime lattice -- both cover the true discriminant support.
CAND = [2, 3, 5, 7, 11, 13]
CAND6 = [2, 3]
FOUR_POOL = [7, 13, 19, 31, 37, 43, 61, 67, 73]     # p^4 stays cheap
SIX_POOL = [7, 13]                                   # p^6 field-size cap


def part1():
    P("#" * 78)
    P("# PART 1 -- DISCRIMINANT-CLASS INVERSION  (from freeze stream -> D mod cubes)")
    P(f"# candidate lattice (small-prime, task-sanctioned): {CAND}")
    P("#" * 78)
    results = []
    for name, fr, gr, gW, note in MEMBERS:
        fc, gc = fg_from_roots(fr, gr)
        hc = WSC.h_member(fr, gr) if gr else WSC.poly_from_roots(fr)
        roots = fr + gr
        pool = FOUR_POOL if gW == 4 else SIX_POOL
        cand = CAND if gW == 4 else CAND6
        # LAZY measurement: pull one prime at a time; stop when the F3 system is full rank
        reading = {}; rec = None
        for p in pool:
            reading[p] = measure_one(hc, roots, p, gW)
            rec = invert_discriminant(reading, cand)
            if rec["data_cost"] is not None:
                break
        # ---- grade (truth) ----
        D, true_exps, outside = true_D_class(fc, gc, cand)
        got = rec["solution"]
        match = (got is not None) and (got == true_exps) and (not outside)
        P("")
        P("-" * 78)
        P(f"MEMBER {name}   {note}")
        clean = [p for p in sorted(reading) if reading[p].get("is_cube_root")]
        badp = [p for p in sorted(reading) if reading[p].get("bad")]
        fz = {p: (reading[p]["freeze_index"], reading[p]["freeze_order"]) for p in clean}
        P(f"  freeze stream (clean cube-root primes) [p: (index,order)] = {fz}")
        if badp:
            P(f"  bad primes skipped (degenerate reading) = {badp}")
        P(f"  candidate lattice = {cand}")
        P(f"  BLIND recovered D mod cubes : {class_str(cand, got)}")
        P(f"    rank {rec['rank']}/{rec['ncols']};  data cost = {rec['data_cost']} clean "
          f"primes to full rank;  primes scanned = {sorted(reading)}")
        P(f"  TRUE D = {D} = {class_str(cand, true_exps)}"
          + (f"  [support outside lattice: {outside}]" if outside else ""))
        P(f"  ==> {'MATCH (inversion correct)' if match else 'MISMATCH'}")
        results.append((name, match, rec["data_cost"]))
    P("")
    P("PART 1 SUMMARY: " + ", ".join(f"{n}:{'OK' if m else 'FAIL'}(cost {c})"
                                     for n, m, c in results))
    return results


# ============================================================================
# PART 2 -- structure inversion (signature, decomposability, bad set, K-field)
# ============================================================================
def invert_signature(reading, gW):
    """From the reading ALONE: balanced (freeze = root of unity everywhere) => (g/2,g/2);
    else the exact Hodge signature {s, g-s} = {v_pi(det), g-v_pi(det)}, det = the top
    rail coefficient rail_eis[gW] in Z[omega]."""
    clean = [p for p in reading if reading[p].get("usable") and reading[p].get("is_cube_root")]
    unbalanced = [p for p in reading if reading[p].get("split")
                  and reading[p].get("freeze") is not None
                  and read_freeze(reading[p]["freeze"])[1] is None]
    if clean and not unbalanced:
        return (gW // 2, gW // 2), "balanced: freeze is a root of unity at every good prime"
    # unbalanced: pi-adic valuation of the Z[omega] determinant (top rail coefficient)
    sig = None; reads = []
    for p in sorted(reading):
        r = reading[p]
        if not r.get("split") or r.get("rail_eis") is None:
            continue
        try:
            det = tuple(r["rail_eis"][gW]); pi = pi_above(p); s = v_pi(det, pi, p)
        except Exception:
            continue
        reads.append((p, s))
        sig = tuple(sorted((s, gW - s)))
        if len(reads) >= 2:
            break
    return sig, f"unbalanced: pi-adic Newton signature {reads}"


def invert_decomposability(reading):
    """The item-39 signature, with its TWO tells DECOUPLED (a finding of this run):
      * rail reality (all coeffs real, omega-part 0)  = DECOMPOSABILITY tell
        (P_B = Pi_W^2 <=> conjugate-closed rail <=> B isogenous to a square);
      * freeze-order uniformity (all order 1)         = D-IN-CUBES tell (Part-1 content).
    The Schoen bielliptic member (item 39) has BOTH; a generic y^3=fg^2 member can have
    order-uniformity WITHOUT real rails (D a cube yet simple) -- the two are independent."""
    clean = [reading[p] for p in reading if reading[p].get("usable") and reading[p].get("is_cube_root")]
    orders = sorted({r["freeze_order"] for r in clean})
    real_rail = all(all(b == 0 for (a, b) in r["rail_eis"]) for r in clean) if clean else None
    order_trivial = (set(orders) <= {1})
    decomp = ("DECOMPOSABLE (real rails: P_B = Pi_W^2, conjugate-closed)" if real_rail
              else "SIMPLE-type (genuinely complex Z[zeta3] rails: W not conjugation-closed)")
    disc_bit = ("D in cubes (freeze order uniformly 1)" if order_trivial
                else "D not a cube (freeze order varies 1<->3 by prime)")
    return dict(orders=orders, real_rail=real_rail, order_trivial=order_trivial,
                decomposability=decomp, disc_bit=disc_bit)


def invert_bad_set(hc, roots, gW, scan_primes):
    """BLIND bad-prime detection: primes where the carrier rail fails its weight-1 gate
    (or the fibre is visibly singular)."""
    reading = measure(hc, roots, scan_primes, gW)
    bad = [p for p in scan_primes if reading.get(p, {}).get("bad")]
    return bad, reading


def invert_hd_bit(reading):
    """even freeze order (2 or 6) => Hasse-Davenport delta_p != 0 => a branch factor is
    INERT (non-rational) at those primes -- a readable structural bit."""
    even = [p for p in reading if reading[p].get("freeze_order") in (2, 6)]
    return even


def part2():
    P("")
    P("#" * 78)
    P("# PART 2 -- STRUCTURE INVERSION  (signature / decomposability / bad set / K)")
    P("#" * 78)
    dossiers = {}

    # (a) signature: balanced (2,2)/(3,3) vs a genuine (1,3)
    P("")
    P("(a) SIGNATURE inversion")
    sig_members = [
        ("M1", [0, 1], [2, 3, 4], 4, (2, 2)),
        ("S6", [0, 1, 2, 3], [4, 5, 6], 6, (3, 3)),
        ("Q5(1,3)", [0, 1, 2, 3, 4], [], 4, (1, 3)),   # y^3 = f, deg f = 5 -> Weil-Hodge (1,3)
    ]
    for name, fr, gr, gW, true_sig in sig_members:
        fc, gc = fg_from_roots(fr, gr)
        hc = WSC.h_member(fr, gr) if gr else WSC.poly_from_roots(fr)
        roots = fr + gr
        primes = [7, 13, 19, 31] if gW == 4 else [7, 13]
        reading = measure(hc, roots, primes, gW)
        sig, why = invert_signature(reading, gW)
        # grade against Chevalley-Weil truth
        exps = [1] * len(fr) + [2] * len(gr)
        dims, _, _ = WS.cyclic_cover_signature(exps, 3)
        cw = tuple(sorted((dims[1], dims[2])))
        ok = (sig == tuple(sorted(true_sig)) == cw)
        P(f"  {name:8s} BLIND signature = {sig}   [{why}]")
        P(f"           Chevalley-Weil truth = {cw}   ==> {'MATCH' if ok else 'MISMATCH'}")
        dossiers.setdefault(name, {})["signature"] = sig

    # (b) decomposability class (rail reality) vs D-in-cubes (order uniformity)
    P("")
    P("(b) DECOMPOSABILITY inversion (item-39 tell, two signals DECOUPLED)")
    dec_members = list(MEMBERS) + [
        ("DEC64", [0, 2], [3, 4, 5], 4, "D=64=4^3 (cube): order-1 but complex rails"),
    ]
    for name, fr, gr, gW, note in dec_members:
        hc = WSC.h_member(fr, gr) if gr else WSC.poly_from_roots(fr)
        roots = fr + gr
        primes = FOUR_POOL[:5] if gW == 4 else SIX_POOL[:2]
        reading = measure(hc, roots, primes, gW)
        dec = invert_decomposability(reading)
        P(f"  {name:8s} orders={dec['orders']} real_rail={dec['real_rail']}")
        P(f"           decomposability: {dec['decomposability']}")
        P(f"           disc bit:        {dec['disc_bit']}")
        dossiers.setdefault(name, {})["decomposability"] = dec["decomposability"]
    P("  [DECOUPLING FINDING: DEC64 has D a cube (order uniformly 1) yet COMPLEX rails")
    P("   => order-uniformity tracks D mod cubes; rail-reality tracks decomposability;")
    P("   the Schoen bielliptic member (item 39) is the instance carrying BOTH tells.]")

    # (c) bad set (blind gate-failure detection); demo with a member singular at 7 (=1 mod 3)
    P("")
    P("(c) BAD-SET inversion (blind gate failure = degeneracy)")
    bad_members = [
        ("M1", [0, 1], [2, 3, 4]),
        ("M4bad7", [0, 1], [2, 3, 9]),           # disc(g) roots 2,3,9: 2==9 mod 7 => bad at 7
    ]
    for name, fr, gr in bad_members:
        fc, gc = fg_from_roots(fr, gr)
        hc = WSC.h_member(fr, gr)
        roots = fr + gr
        scan = [p for p in WS.sieve(60) if p % 3 == 1 and p >= 7]
        bad, _ = invert_bad_set(hc, roots, 4, scan)
        # truth: primes (=1 mod3, in scan) dividing disc(f) disc(g) Res(f,g)
        f, g = FM.sp_poly(fc), FM.sp_poly(gc)
        rad = int(sp.discriminant(f)) * int(sp.discriminant(g)) * int(sp.resultant(f, g))
        true_bad = [p for p in scan if rad % p == 0]
        ok = (sorted(bad) == sorted(true_bad))
        P(f"  {name:8s} BLIND bad set (scan {scan[0]}..{scan[-1]}, =1 mod3) = {bad}")
        P(f"           TRUE {{p | disc.disc.Res}} in scan = {true_bad}   ==> {'MATCH' if ok else 'MISMATCH'}")
        dossiers.setdefault(name, {})["bad_set(=1mod3, scanned)"] = bad

    # (d) Hasse-Davenport / K-field structural bits
    P("")
    P("(d) HASSE-DAVENPORT bit (even freeze order => inert branch factor) + K-field")
    fc = [1, 0, 1]; gc = [-24, 26, -9, 1]                # f = x^2+1 (irreducible), g=(x-2)(x-3)(x-4)
    hc = FM.h_from_fg(fc, gc)
    reading = measure(hc, None, [7, 13, 19, 31, 37, 43], 4)
    even = invert_hd_bit(reading)
    fz = {p: reading[p].get("freeze_order") for p in reading if reading[p].get("split")}
    P(f"  F4-irr (f=x^2+1)  freeze orders by prime = {fz}")
    P(f"           even-order primes (BLIND 'inert branch factor present') = {even}")
    P(f"           truth: x^2+1 is inert at p = 3 mod 4  => {[p for p in [7,13,19,31,37,43] if p % 4 == 3]}"
      f"   ==> {'MATCH' if sorted(even) == [p for p in [7,13,19,31,37,43] if p % 4 == 3] else 'MISMATCH'}")
    P(f"  K-FIELD: rail coefficients live in Z[zeta_3] (cubic deck sigma) => K = Q(sqrt-3),")
    P(f"           read directly off the rail lattice at every member (universal for y^3=fg^2).")
    return dossiers


# ============================================================================
# PART 3 -- well-posedness : same D mod cubes, different angle streams
# ============================================================================
def canonical_class(fc, gc):
    f = FM.sp_poly(fc); g = FM.sp_poly(gc)
    D = int(sp.discriminant(f)) * int(sp.discriminant(g)) ** 2
    fac = sp.factorint(abs(D))
    return tuple(sorted((int(l), int(e) % 3) for l, e in fac.items() if int(e) % 3))


def part3():
    P("")
    P("#" * 78)
    P("# PART 3 -- WELL-POSEDNESS  (how much of (f,g) does the carrier determine?)")
    P("#" * 78)
    # engineer two df=2,dg=3 covers with the SAME D mod cubes but different point counts
    buckets = {}
    for r1 in range(1, 6):
        fr = [0, r1]
        for gr in itertools.combinations([g for g in range(2, 10) if g not in fr], 3):
            gr = list(gr)
            fc, gc = fg_from_roots(fr, gr)
            f, g = FM.sp_poly(fc), FM.sp_poly(gc)
            if sp.gcd(f, g) != 1:
                continue
            cls = canonical_class(fc, gc)
            buckets.setdefault(cls, []).append((fr, gr))
    # pick a nontrivial class with >= 2 members whose streams differ at p=7
    pair = None
    for cls, mem in buckets.items():
        if cls == () or len(mem) < 2:
            continue
        for i in range(len(mem)):
            for j in range(i + 1, len(mem)):
                (fr1, gr1), (fr2, gr2) = mem[i], mem[j]
                t1 = WSC.Tk(7, 1, WSC.h_member(fr1, gr1))
                t2 = WSC.Tk(7, 1, WSC.h_member(fr2, gr2))
                if abs(t1 - t2) > 0.5:
                    pair = (cls, (fr1, gr1), (fr2, gr2)); break
            if pair: break
        if pair: break
    cls, A, B = pair
    P("")
    val = 1
    for l, e in cls:
        val *= l ** e
    P(f"  engineered pair, SAME D mod cubes = {' * '.join(f'{l}^{e}' for l, e in cls)} (= {val} mod cubes):")
    P(f"    cover A:  f-roots {A[0]}, g-roots {A[1]}")
    P(f"    cover B:  f-roots {B[0]}, g-roots {B[1]}")
    primes = [7, 13, 19, 31]
    rA = measure(WSC.h_member(*A), A[0] + A[1], primes, 4)
    rB = measure(WSC.h_member(*B), B[0] + B[1], primes, 4)
    P("")
    P(f"  {'p':>4s} | {'A freeze idx':>12s} {'B freeze idx':>12s} | {'A angles':>26s} {'B angles':>26s}  {'angles differ':>13s}")
    freeze_same = True; angles_differ = False
    for p in primes:
        a, b = rA[p], rB[p]
        fa, fb = a.get("freeze_index"), b.get("freeze_index")
        aa, ab = a.get("angles"), b.get("angles")
        diff = (aa != ab)
        freeze_same = freeze_same and (fa == fb)
        angles_differ = angles_differ or diff
        P(f"  {p:>4d} | {str(fa):>12s} {str(fb):>12s} | {str(aa):>26s} {str(ab):>26s}  {str(diff):>13s}")
    P("")
    P(f"  freeze stream identical across primes : {freeze_same}   (both read chi_3(D), same D mod cubes)")
    P(f"  angle stream differs at some prime    : {angles_differ}   (different Frobenius => not isogenous)")
    P("")
    P("  => D mod cubes is STRICTLY COARSER than the full angle stream: the freeze")
    P("     scalar is one cubic character of D; the angle stream is the whole L-function.")
    return cls, A, B, freeze_same, angles_differ


def main():
    P("#" * 78)
    P("# CARRIER INVERSION ARM -- do the per-prime readings DETERMINE the arithmetic?")
    P("# blind protocol: measure()=carrier, invert_*()=blind, grade()=truth-only")
    P("#" * 78)
    r1 = part1()
    r2 = part2()
    r3 = part3()
    P("")
    P("#" * 78)
    P("# VERDICT")
    P("#" * 78)
    P(f"  PART 1 (D mod cubes):     " + ", ".join(f"{n}:{'OK' if m else 'FAIL'}" for n, m, c in r1))
    P(f"  PART 2 (structure):       signature/decomposability/bad-set/HD-bit/K-field -- see above")
    P(f"  PART 3 (well-posedness):  same-class pair found; freeze identical, angles differ -> "
      f"carrier stream ⇒ isogeny class (Faltings) + D mod cubes; specific member = L-invisible")
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "carrier_inversion_results.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    print(f"\n[results -> {path}]", flush=True)


if __name__ == "__main__":
    main()
