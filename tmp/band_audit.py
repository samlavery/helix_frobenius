"""INDEPENDENT AUDIT of the Part II "register hit" band claim.

Fully independent re-implementation (different code path, own conventions).
NOTHING is imported from tmp/coherence_margins.py.

Chart under audit:   s = 1/2 + i*z   (so Re s = 1/2 - Im z).
Claim under audit:   E  := 2*sum_n chi(n)*S2_n   (the (1-s)/2 strand)
                     E* := conj(E(conj z)) = 2*sum_n chi(n)*S1_n  (the s/2 strand)
                     ratio r(z) = ||E*(z)|| / ||E(z)||  EXCEEDS 1 in alternating
                     x-bands for every y=Im z>0 (q=5: worst -0.0128 at z=9.831+1i).

Strands (upper incomplete gamma  Gamma(a,x)=gammainc(a,x,inf)):
    S1_n(s) = (q/(pi n^2))^{s/2}      * Gamma(s/2,     pi n^2/q)
    S2_n(s) = (q/(pi n^2))^{(1-s)/2}  * Gamma((1-s)/2, pi n^2/q)

We derive conventions from first principles, verify against mpmath's genuine
Dirichlet L-function, then run the decisive argument-principle zero census.
"""
import math
import cmath
import mpmath as mp

mp.mp.dps = 40  # error budget: incomplete-gamma + Ldirichlet good to ~1e-35 here


# --------------------------------------------------------------------------
# 0. Character: real primitive even quadratic character mod prime q (Legendre)
# --------------------------------------------------------------------------
def legendre(q):
    qr = set((k * k) % q for k in range(1, q))

    def chi(n):
        r = n % q
        if r == 0:
            return 0
        return 1 if r in qr else -1
    return chi


# --------------------------------------------------------------------------
# 1. The two strands, defined EXACTLY as the audited claim states.
#    Independent of the other agent's helper names.
# --------------------------------------------------------------------------
def strands(n, q, s):
    """Return (S1_n, S2_n) at complex s.  Upper incomplete gamma."""
    a1 = s / 2
    a2 = (1 - s) / 2
    x = mp.pi * (n * n) / q
    base = mp.mpf(q) / (mp.pi * (n * n))     # q/(pi n^2)
    S1 = base ** a1 * mp.gammainc(a1, x, mp.inf)
    S2 = base ** a2 * mp.gammainc(a2, x, mp.inf)
    return S1, S2


def bank(q, cutoff=45.0):
    nmax = int(math.sqrt(cutoff * q / math.pi)) + 1
    chi = legendre(q)
    return [(n, chi(n)) for n in range(1, nmax + 1) if chi(n) != 0]


def Lambda_terms(q, s, terms):
    """Completed-L candidate  Lam = sum chi(n)(S1+S2),  and the two summed strands."""
    S1sum = mp.mpc(0)
    S2sum = mp.mpc(0)
    for (n, c) in terms:
        s1, s2 = strands(n, q, s)
        S1sum += c * s1
        S2sum += c * s2
    return S1sum, S2sum


def E_and_star(q, z, terms):
    """E(z)=2 sum chi S2  and  E*(z)=conj(E(conj z))=2 sum chi S1  at chart z.

    We compute E* the HONEST way (conj of E at conj z) to catch any identity error,
    AND separately as 2 sum chi S1, and check they agree.
    """
    s = mp.mpf("0.5") + 1j * mp.mpc(z)
    S1sum, S2sum = Lambda_terms(q, s, terms)
    E = 2 * S2sum
    Estar_from_S1 = 2 * S1sum

    # honest star:  E*(z) = conj( E(conj z) )
    zc = mp.conj(mp.mpc(z))
    sc = mp.mpf("0.5") + 1j * zc
    _, S2sum_c = Lambda_terms(q, sc, terms)
    Estar_honest = mp.conj(2 * S2sum_c)
    return E, Estar_from_S1, Estar_honest, S1sum, S2sum


# --------------------------------------------------------------------------
# 2. Ground-truth completed L-function from mpmath (fully independent path)
# --------------------------------------------------------------------------
def true_completed_L(q, s):
    """Genuine completed Dirichlet L for even primitive real chi mod q:
        Lambda(s) = (q/pi)^{s/2} Gamma(s/2) L(s,chi).
    Uses mpmath.mp.zeta? No -- use the character L via Hurwitz zeta sum.
    """
    chi = legendre(q)
    # L(s,chi) = q^{-s} sum_{a=1}^{q} chi(a) zeta(s, a/q)   (Hurwitz), Re s>1 then analytic
    L = mp.mpc(0)
    for a in range(1, q + 1):
        ca = chi(a)
        if ca != 0:
            L += ca * mp.zeta(s, mp.mpf(a) / q)
    L *= mp.power(q, -s)
    Lam = mp.power(mp.mpf(q) / mp.pi, s / 2) * mp.gamma(s / 2) * L
    return Lam, L


# --------------------------------------------------------------------------
# 3. Argument principle: count zeros of a callable f(complex)->complex in a
#    rectangle by numerically integrating f'/f around its boundary (Cauchy).
#    Fully self-contained; uses central finite differences for f'.
# --------------------------------------------------------------------------
def _num_deriv(f, w, h=None):
    if h is None:
        h = mp.mpf(10) ** (-15)
    return (f(w + h) - f(w - h)) / (2 * h)


def winding_count(f, x0, x1, y0, y1, npts=240):
    """(1/2pi i) oint f'/f dz around rectangle [x0,x1]x[y0,y1] in the z-plane.

    Returns the (complex, should be ~integer) count of zeros minus poles inside.
    f has no poles here (entire in z), so this counts zeros with multiplicity.
    Uses trapezoidal integration of f'/f along the 4 edges.
    """
    def integrand(z):
        return _num_deriv(f, z) / f(z)

    total = mp.mpc(0)

    def edge(za, zb, m):
        s = mp.mpc(0)
        for k in range(m):
            t0 = mp.mpf(k) / m
            t1 = mp.mpf(k + 1) / m
            wa = za + (zb - za) * t0
            wb = za + (zb - za) * t1
            s += (integrand(wa) + integrand(wb)) / 2 * (wb - wa)
        return s

    c00 = mp.mpc(x0, y0)
    c10 = mp.mpc(x1, y0)
    c11 = mp.mpc(x1, y1)
    c01 = mp.mpc(x0, y1)
    total += edge(c00, c10, npts)
    total += edge(c10, c11, npts)
    total += edge(c11, c01, npts)
    total += edge(c01, c00, npts)
    return total / (2 * mp.pi * 1j)


def argprinc_phase(f, x0, x1, y0, y1, npts=400):
    """Robust winding via total change of arg(f) along the contour (no derivative).

    Sums the wrapped phase increments of f around the rectangle; divides by 2pi.
    Independent of the f'/f path -- a cross-check on winding_count.
    """
    def boundary_points():
        pts = []
        for k in range(npts):
            pts.append(mp.mpc(x0 + (x1 - x0) * k / npts, y0))
        for k in range(npts):
            pts.append(mp.mpc(x1, y0 + (y1 - y0) * k / npts))
        for k in range(npts):
            pts.append(mp.mpc(x1 - (x1 - x0) * k / npts, y1))
        for k in range(npts):
            pts.append(mp.mpc(x0, y1 - (y1 - y0) * k / npts))
        pts.append(pts[0])
        return pts

    pts = boundary_points()
    total = mp.mpf(0)
    prev = f(pts[0])
    for p in pts[1:]:
        cur = f(p)
        # wrapped phase increment of cur/prev
        d = mp.arg(cur / prev)
        total += d
        prev = cur
    return total / (2 * mp.pi)


# --------------------------------------------------------------------------
# main audit
# --------------------------------------------------------------------------
def make_E(q, terms):
    """Return E(z) as a plain callable complex->complex (for zero census)."""
    def E(z):
        s = mp.mpf("0.5") + 1j * mp.mpc(z)
        _, S2sum = Lambda_terms(q, s, terms)
        return 2 * S2sum
    return E


def make_Estar(q, terms):
    def Es(z):
        s = mp.mpf("0.5") + 1j * mp.mpc(z)
        S1sum, _ = Lambda_terms(q, s, terms)
        return 2 * S1sum
    return Es


def make_Lambda(q, terms):
    def L(z):
        s = mp.mpf("0.5") + 1j * mp.mpc(z)
        S1sum, S2sum = Lambda_terms(q, s, terms)
        return S1sum + S2sum
    return L


OUT = []
def emit(*a):
    line = " ".join(str(x) for x in a)
    print(line)
    OUT.append(line)


def task1_reproduce(q=5, cutoff=45.0):
    emit("=" * 78)
    emit(f"TASK 1  REPRODUCE from scratch  (q={q}, cutoff={cutoff}, dps={mp.mp.dps})")
    emit("=" * 78)
    terms = bank(q, cutoff)
    emit(f"  bank: {len(terms)} terms, n in {[t[0] for t in terms]}")

    # 1a. star identity: 2 sum chi S1  ==  conj(E(conj z))  ?
    emit("\n  (1a) STAR IDENTITY  2*sumChiS1 == conj(E(conj z)) :")
    for z in [mp.mpc(3.0, 0.7), mp.mpc(9.831, 1.0), mp.mpc(0.0, 1.2)]:
        E, Es_S1, Es_honest, S1, S2 = E_and_star(q, z, terms)
        d = abs(Es_S1 - Es_honest)
        emit(f"     z={complex(z)}:  |2SumS1 - conj(E(conj z))| = {mp.nstr(d,3)}")

    # 1b. on-axis |E|==|E*|  (boundary)
    emit("\n  (1b) ON-AXIS (z real) boundary |E|==|E*|:")
    for zr in [0.0, 3.0, 6.6485]:
        E, Es_S1, _, S1, S2 = E_and_star(q, mp.mpc(zr, 0.0), terms)
        emit(f"     z={zr}:  |E|={mp.nstr(abs(E),8)}  |E*|={mp.nstr(abs(Es_S1),8)}  "
             f"ratio={mp.nstr(abs(Es_S1)/abs(E),10)}")

    # 1c. A=(E+E*)/2 recovers Lambda?  compare to genuine mpmath completed L.
    emit("\n  (1c) A=(E+E*)/2  vs  genuine completed L  Lambda(1/2+iz):")
    for z in [mp.mpc(0.0, 0.0), mp.mpc(3.0, 0.0), mp.mpc(2.0, 0.9), mp.mpc(9.831, 1.0)]:
        s = mp.mpf("0.5") + 1j * mp.mpc(z)
        E, Es_S1, _, S1, S2 = E_and_star(q, z, terms)
        A = (E + Es_S1) / 2
        Lam_true, Lval = true_completed_L(q, s)
        emit(f"     z={complex(z)}: A={mp.nstr(A,6)}  Lam_true={mp.nstr(Lam_true,6)}  "
             f"|A-Lam_true|={mp.nstr(abs(A-Lam_true),3)}")

    # 1d. first zero of A (=Lambda) on axis near 6.6485
    emit("\n  (1d) first zero of A=(E+E*)/2 on the axis (bisect Re):")
    Lam = make_Lambda(q, terms)
    def Are(zr):
        return mp.re(Lam(mp.mpc(zr, 0.0)))
    lo, hi = 6.0, 7.0
    a, b = mp.mpf(lo), mp.mpf(hi)
    fa, fb = Are(a), Are(b)
    if fa * fb < 0:
        for _ in range(80):
            m = (a + b) / 2
            if Are(a) * Are(m) <= 0:
                b = m
            else:
                a = m
        emit(f"     zero at z = {mp.nstr((a+b)/2, 8)}   (LMFDB gamma_1(chi_5) ~ 6.6485)")
    else:
        emit(f"     no sign change in [{lo},{hi}]  (fa={mp.nstr(fa,4)} fb={mp.nstr(fb,4)})")

    # 1e. reproduce the claimed band ratios at the claimed points
    emit("\n  (1e) CLAIMED BAND POINTS  ratio=|E*|/|E|:")
    claim_pts = [(9.831, 1.0), (9.831, 0.05), (9.831, 2.0),
                 (0.0, 1.0), (6.6485, 1.0), (11.959, 1.0), (25.0, 1.0)]
    for (x, y) in claim_pts:
        E, Es_S1, _, S1, S2 = E_and_star(q, mp.mpc(x, y), terms)
        r = abs(Es_S1) / abs(E)
        flag = "  <-- ratio>1 (claimed band)" if r > 1 else ""
        emit(f"     z={x}+{y}i:  ratio={mp.nstr(r,8)}  margin={mp.nstr(1-r,6)}{flag}")
    return terms


def task1b_bandscan(q, terms):
    emit("\n  (1f) FINE x-BAND SCAN at y=1.0 (locate ratio>1 bands):")
    E = make_E(q, terms)
    Es = make_Estar(q, terms)
    y = 1.0
    xs = [i * 0.25 for i in range(0, 100)]  # 0..24.75
    inband = []
    prev = None
    for x in xs:
        z = mp.mpc(x, y)
        r = abs(Es(z)) / abs(E(z))
        gt = r > 1
        if prev is not None and gt != prev[1]:
            inband.append((prev[0], x, prev[1]))
        prev = (x, gt)
    # summarize crossing structure
    emit(f"     sign-change x-locations (ratio crossing 1) at y=1.0:")
    for (xa, xb, was_gt) in inband:
        emit(f"        crossing near x in [{xa:.2f},{xb:.2f}]  (leaving ratio>1={was_gt})")


def task2_zero_census(q, terms):
    emit("\n" + "=" * 78)
    emit("TASK 2  ARGUMENT-PRINCIPLE ZERO CENSUS of E over z-UPPER-HALF-PLANE")
    emit("=" * 78)
    E = make_E(q, terms)
    Lam = make_Lambda(q, terms)
    Es = make_Estar(q, terms)

    # Tile [0,25] x [0.05,4].  Count zeros of E per tile via two independent methods.
    emit("  Method A: winding of E'/E (Cauchy).  Method B: total-arg(E) change.")
    emit("  (both should agree and be a nonneg integer = #zeros of E in the tile)")

    xedges = [0, 5, 10, 15, 20, 25]
    yedges = [0.05, 1.0, 2.0, 3.0, 4.0]
    emit(f"\n  E zeros per tile [x0,x1]x[y0,y1]:")
    emit(f"    {'tile':>26} | {'windA':>10} {'argB':>10}")
    total_E = 0.0
    for i in range(len(xedges) - 1):
        for j in range(len(yedges) - 1):
            x0, x1 = xedges[i], xedges[i + 1]
            y0, y1 = yedges[j], yedges[j + 1]
            wa = winding_count(E, x0, x1, y0, y1, npts=200)
            wb = argprinc_phase(E, x0, x1, y0, y1, npts=600)
            emit(f"    [{x0:>4},{x1:>4}]x[{y0:>4},{y1:>4}] | "
                 f"{mp.nstr(mp.re(wa),5):>10} {mp.nstr(wb,5):>10}")
            total_E += float(mp.re(wb))
    emit(f"    ---> approx total E-zeros in [0,25]x[0.05,4]: {total_E:.2f}")

    # Far field
    emit(f"\n  FAR FIELD  E zeros in [25,60]x[0.05,4]:")
    for (x0, x1) in [(25, 40), (40, 60)]:
        wb = argprinc_phase(E, x0, x1, 0.05, 4.0, npts=800)
        emit(f"    [{x0},{x1}]x[0.05,4]:  argB={mp.nstr(wb,5)}")

    # Compare: zeros of Lambda (=A) in UHP should be ZERO if RH holds for chi_5
    emit(f"\n  CONTROL  Lambda(=A) zeros in [0,25]x[0.05,4] (RH => 0 in open UHP):")
    total_L = 0.0
    for i in range(len(xedges) - 1):
        x0, x1 = xedges[i], xedges[i + 1]
        wb = argprinc_phase(Lam, x0, x1, 0.05, 4.0, npts=600)
        total_L += float(wb)
        emit(f"    [{x0},{x1}]x[0.05,4]:  Lambda argB={mp.nstr(wb,5)}")
    emit(f"    ---> total Lambda-zeros in UHP: {total_L:.2f}  (expect ~0)")

    return E, Es, Lam


def task2b_localize_E_zeros(q, terms):
    """If E has UHP zeros, localize the low-x ones with a Newton/root scan and
    check whether they sit at/near the ratio>1 band centers."""
    emit("\n  (2b) LOCALIZE low-x E zeros (grid-min of |E| + polish):")
    E = make_E(q, terms)
    # scan grid for local minima of |E|
    cand = []
    xs = [i * 0.2 for i in range(0, 90)]   # 0..17.8
    ys = [0.1 * k for k in range(1, 40)]   # 0.1..3.9
    grid = {}
    for x in xs:
        for y in ys:
            grid[(x, y)] = float(abs(E(mp.mpc(x, y))))
    for x in xs:
        for y in ys:
            v = grid[(x, y)]
            nb = []
            for dx in (-0.2, 0, 0.2):
                for dy in (-0.1, 0, 0.1):
                    key = (round(x + dx, 4), round(y + dy, 4))
                    key2 = (x + dx, y + dy)
                    if (x + dx, y + dy) in grid and (dx, dy) != (0, 0):
                        nb.append(grid[(x + dx, y + dy)])
            if nb and v <= min(nb) and v < 0.05:
                cand.append((x, y, v))
    # polish candidates with 2D Newton on (Re E, Im E)
    def polish(x0, y0):
        z = mp.mpc(x0, y0)
        for _ in range(40):
            f = E(z)
            h = mp.mpf(10) ** (-18)
            fp = (E(z + h) - E(z - h)) / (2 * h)   # dE/dz
            if abs(fp) < mp.mpf(10) ** (-30):
                break
            dz = f / fp
            z = z - dz
            if abs(dz) < mp.mpf(10) ** (-25):
                break
        return z, abs(E(z))
    emit(f"     grid-min candidates (|E|<0.05): {len(cand)}")
    seen = []
    for (x, y, v) in sorted(cand, key=lambda t: t[2]):
        zr, res = polish(x, y)
        if mp.im(zr) > 0.02 and float(res) < 1e-12:
            dup = any(abs(zr - s) < 1e-6 for s in seen)
            if not dup:
                seen.append(zr)
                emit(f"        E zero at z = {mp.nstr(zr, 10)}   |E|={mp.nstr(res,3)}")
    if not seen:
        emit("        no polished E zeros with Im z>0.02 found on this grid")
    return seen


def task3_asymptotics(q, terms):
    emit("\n" + "=" * 78)
    emit("TASK 3  ASYMPTOTIC BOOKKEEPING  (y->+inf, Re s = 1/2 - y -> -inf)")
    emit("=" * 78)
    emit("  Strand growth of |S1_n| (a=s/2, Re a-> -inf) vs |S2_n| (a=(1-s)/2, Re a->+inf).")
    emit("  n=1, q=5:  x=pi/q. Track |S1|,|S2|, ratio |S1|/|S2| as y grows.")
    n = 1
    for y in [0.1, 0.5, 1.0, 2.0, 3.0, 5.0, 8.0]:
        s = mp.mpf("0.5") + 1j * mp.mpc(mp.mpc(0.0, y))  # x=0
        s = mp.mpf("0.5") + 1j * mp.mpc(0.0, y)
        S1, S2 = strands(n, q, s)
        emit(f"     y={y:>4}: |S1|={mp.nstr(abs(S1),5)}  |S2|={mp.nstr(abs(S2),5)}  "
             f"|S1|/|S2|={mp.nstr(abs(S1)/abs(S2),6)}")
    emit("  Full-bank summed ratio |E*|/|E| = |2SumChiS1|/|2SumChiS2| at x=0 vs y:")
    E = make_E(q, terms); Es = make_Estar(q, terms)
    for y in [0.1, 0.5, 1.0, 2.0, 3.0, 5.0]:
        z = mp.mpc(0.0, y)
        emit(f"     y={y:>4}: |E*|/|E| = {mp.nstr(abs(Es(z))/abs(E(z)),6)}")


def task4_convention(q, terms):
    emit("\n" + "=" * 78)
    emit("TASK 4  CONVENTION CHECK  (de Branges: E has zeros in closed LOWER half;")
    emit("        |E*|<|E| in open UPPER half).  Which strand is the natural E?")
    emit("=" * 78)
    E = make_E(q, terms)      # E  = 2 sum chi S2  (audited choice)
    Es = make_Estar(q, terms) # E* = 2 sum chi S1
    # role-swap: call F = 2 sum chi S1 the structure fn, F* = 2 sum chi S2.
    # side-swap: measure ratio in the LOWER half-plane too.
    emit("  ratio r=|E*|/|E| and swapped rF=|F*|/|F|=|E|/|E*| at a few UHP points:")
    for (x, y) in [(9.831, 1.0), (0.0, 1.0), (6.6485, 1.0), (2.0, 0.5), (15.0, 1.0)]:
        z = mp.mpc(x, y)
        r = abs(Es(z)) / abs(E(z))
        emit(f"     z={x}+{y}i:  |E*|/|E|={mp.nstr(r,7)}   |E|/|E*|={mp.nstr(1/r,7)}")
    emit("  Same audited E but evaluated in LOWER half (y<0):")
    for (x, y) in [(9.831, -1.0), (0.0, -1.0), (6.6485, -1.0)]:
        z = mp.mpc(x, y)
        r = abs(Es(z)) / abs(E(z))
        emit(f"     z={x}+{y}i:  |E*|/|E|={mp.nstr(r,7)}")


def main():
    q = 5
    terms = task1_reproduce(q)
    task1b_bandscan(q, terms)
    task2_zero_census(q, terms)
    task2b_localize_E_zeros(q, terms)
    task3_asymptotics(q, terms)
    task4_convention(q, terms)
    with open("tmp/band_audit_results.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")
    print("\n[written] tmp/band_audit_results.txt")


if __name__ == "__main__":
    main()
