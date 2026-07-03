"""Fast, independent argument-principle zero census of E over the z-UHP.

Uses ONLY total-argument-change (phase winding) around rectangles -- no
finite-difference derivatives.  Cross-checked by refining npts and by the
sum-of-tiles vs single-big-contour consistency.  dps=25 (ample for counting).

E(z) = 2 sum_n chi(n) (q/(pi n^2))^{(1-s)/2} Gamma((1-s)/2, pi n^2/q),  s=1/2+iz.
"""
import math
import mpmath as mp

mp.mp.dps = 25


def legendre(q):
    qr = set((k * k) % q for k in range(1, q))
    def chi(n):
        r = n % q
        return 0 if r == 0 else (1 if r in qr else -1)
    return chi


def bank(q, cutoff=45.0):
    nmax = int(math.sqrt(cutoff * q / math.pi)) + 1
    chi = legendre(q)
    terms = [(n, chi(n)) for n in range(1, nmax + 1) if chi(n) != 0]
    # precompute per-term constants
    pre = []
    for (n, c) in terms:
        x = mp.pi * (n * n) / q
        base = mp.mpf(q) / (mp.pi * (n * n))
        pre.append((c, x, base))
    return pre


def make_E(pre):
    def E(z):
        s = mp.mpf("0.5") + 1j * mp.mpc(z)
        a = (1 - s) / 2
        tot = mp.mpc(0)
        for (c, x, base) in pre:
            tot += c * base ** a * mp.gammainc(a, x, mp.inf)
        return 2 * tot
    return E


def make_star(pre):
    def Es(z):
        s = mp.mpf("0.5") + 1j * mp.mpc(z)
        a = s / 2
        tot = mp.mpc(0)
        for (c, x, base) in pre:
            tot += c * base ** a * mp.gammainc(a, x, mp.inf)
        return 2 * tot
    return Es


def make_Lambda(pre):
    def L(z):
        s = mp.mpf("0.5") + 1j * mp.mpc(z)
        a1 = s / 2
        a2 = (1 - s) / 2
        tot = mp.mpc(0)
        for (c, x, base) in pre:
            tot += c * (base ** a1 * mp.gammainc(a1, x, mp.inf)
                        + base ** a2 * mp.gammainc(a2, x, mp.inf))
        return tot
    return L


def arg_winding(f, x0, x1, y0, y1, npts):
    """Total change of arg(f) / 2pi around rectangle [x0,x1]x[y0,y1]."""
    def edge_pts(za, zb):
        return [za + (zb - za) * mp.mpf(k) / npts for k in range(npts)]
    corners = [mp.mpc(x0, y0), mp.mpc(x1, y0), mp.mpc(x1, y1), mp.mpc(x0, y1)]
    pts = []
    for i in range(4):
        pts += edge_pts(corners[i], corners[(i + 1) % 4])
    pts.append(pts[0])
    total = mp.mpf(0)
    prev = f(pts[0])
    for p in pts[1:]:
        cur = f(p)
        total += mp.arg(cur / prev)
        prev = cur
    return total / (2 * mp.pi)


OUT = []
def emit(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    OUT.append(s)


def main():
    q = 5
    pre = bank(q)
    E = make_E(pre); Es = make_star(pre); Lam = make_Lambda(pre)
    emit(f"CENSUS q={q}, dps={mp.mp.dps}, bank={len(pre)} terms")

    # --- E zeros: big contour [0,25]x[0.05,4], then tiled, then refine npts ---
    emit("\n[A] E zero count in [0,25]x[0.05,4]:")
    for npts in (300, 600):
        w = arg_winding(E, 0.0, 25.0, 0.05, 4.0, npts)
        emit(f"    single contour, npts={npts}: winding={mp.nstr(w,6)}")

    emit("\n[B] E zeros tiled (npts=400 per tile):")
    xedges = [0, 5, 8, 10, 12, 15, 20, 25]
    yedges = [0.05, 1.0, 2.0, 4.0]
    tot = mp.mpf(0)
    for i in range(len(xedges) - 1):
        for j in range(len(yedges) - 1):
            x0, x1, y0, y1 = xedges[i], xedges[i+1], yedges[j], yedges[j+1]
            w = arg_winding(E, x0, x1, y0, y1, 400)
            tot += w
            mark = "  <== nonzero" if abs(float(w)) > 0.3 else ""
            emit(f"    [{x0:>3},{x1:>3}]x[{y0:>4},{y1:>4}]: {mp.nstr(w,5):>10}{mark}")
    emit(f"    SUM over tiles = {mp.nstr(tot,6)}")

    # --- Far field ---
    emit("\n[C] E far-field zeros:")
    for (x0, x1) in [(25, 40), (40, 60)]:
        w = arg_winding(E, x0, x1, 0.05, 4.0, 600)
        emit(f"    [{x0},{x1}]x[0.05,4]: winding={mp.nstr(w,5)}")

    # --- Control: Lambda (=A) zeros in UHP (RH => 0) ---
    emit("\n[D] CONTROL Lambda(=A) zeros in [0,25]x[0.05,4]:")
    w = arg_winding(Lam, 0.0, 25.0, 0.05, 4.0, 600)
    emit(f"    winding = {mp.nstr(w,6)}   (expect ~0 under RH for chi_5)")

    # --- Localize E zeros in the low-x region if any ---
    emit("\n[E] E zero localization (Newton from grid minima of |E|), Im z>0.02:")
    def Enewton(x0, y0):
        z = mp.mpc(x0, y0)
        h = mp.mpf(10) ** (-15)
        for _ in range(60):
            f = E(z)
            fp = (E(z + h) - E(z - h)) / (2 * h)
            if abs(fp) == 0:
                break
            dz = f / fp
            z -= dz
            if abs(dz) < mp.mpf(10) ** (-20):
                break
        return z, abs(E(z))
    seen = []
    for xi in range(0, 130):
        x = xi * 0.2
        for yj in range(1, 40):
            y = yj * 0.1
            zr, res = Enewton(x, y)
            if mp.im(zr) > mp.mpf("0.02") and float(res) < 1e-14:
                if not any(abs(zr - t) < mp.mpf("1e-6") for t in seen):
                    if 0 <= float(mp.re(zr)) < 30 and float(mp.im(zr)) < 5:
                        seen.append(zr)
    seen.sort(key=lambda t: (float(mp.re(t)), float(mp.im(t))))
    if seen:
        for z in seen:
            r = abs(Es(z)) / abs(E(z))
            emit(f"    E zero z={mp.nstr(z,10)}   |E|={mp.nstr(abs(E(z)),2)}   "
                 f"(|E*|/|E| here={mp.nstr(r,4)})")
    else:
        emit("    NONE found with Im z>0.02, |E|<1e-14 on 0.2x0.1 grid over [0,26]x[0.1,3.9]")
    emit(f"    total distinct E zeros localized: {len(seen)}")

    with open("tmp/band_census_results.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")
    emit("\n[written] tmp/band_census_results.txt")


if __name__ == "__main__":
    main()
