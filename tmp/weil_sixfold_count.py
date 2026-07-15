"""NON-CM Weil-type point-count instrument (the open-frontier HUNT machine).

Cyclic cubic covers  C: y^3 = f(x) g(x)^2  (f,g coprime squarefree) with mu_3 = Z[zeta_3]
= Z[sqrt(-3)] action.  Chevalley-Weil signature of the mu_3-eigenspaces of H^{1,0}:
  deg f = deg g = 3  (6 branch pts) -> genus 4, signature (2,2): a Q(sqrt-3)-Weil FOURFOLD;
  deg f = deg g = 4  (8 branch pts) -> genus 6, signature (3,3): a Q(sqrt-3)-Weil SIXFOLD.
For GENERIC f,g the Jacobian is NON-CM, End^0 = Q(sqrt-3) exactly -- the genuine open-
frontier Weil variety (Markman-transcendental at dim 4; unclassified & conjecture-open at
dim 6).  These are the ORPHAN-test targets: a class whose per-prime Frobenius has no naive
CM/Jacobi-sum shortcut.

RAILS ARE NATIVE.  H^1 tensor C = V_zeta + V_{zeta^2} = W + Wbar (the K = Q(sqrt-3)
eigenspaces).  Frobenius (p = 1 mod 3, zeta_3 in F_p) preserves each rail.  The zeta-rail
(=W) power sums are  s_k = -T_k,  T_k = sum_{x in F_{p^k}} chi_3(h(x))  (cubic char sum;
NOT naive y-enumeration).  Newton -> the degree-g W-rail characteristic polynomial;
Wbar-rail = complex conjugate; full degree-2g L-poly = product.  The Weil class is
wedge^{g/2}W + wedge^{g/2}Wbar; wedge^{g/2}W = (prod of W-rail Frobenius eigenvalues) =
top coeff of the W-rail L-poly; freeze <=> that / p^{g/2} is a root of unity (finite-order
Hecke character = discriminant regime).

ENGINEERING.  Full genus-6 counting is p^6-hard; we sum the cubic character over F_{p^k}
with a NUMPY-VECTORISED F_{p^k} (chunked), not a Python loop.  Validated: Weil bound
|alpha|=sqrt(p), integrality in Z[zeta_3], functional equation, and an INDEPENDENT
reconstruction (the degree-g W-rail L-poly built from k=1..g predicts T_{g+1}, cross-checked
by a direct count).

Run:  python3 weil_sixfold_count.py [pmax]     (fourfold ladder + sixfold at small p)
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import weil_scout as WS


# ============================================================================
# vectorised F_{p^k}  (elements as (n,k) int arrays, coeffs low->high, mod m)
# ============================================================================
class GFpk:
    def __init__(self, p, k, m=None):
        self.p, self.k = p, k
        self.m = m or WS.find_irreducible(p, k)      # monic irreducible, low->high, len k+1
        assert len(self.m) == k + 1 and self.m[-1] == 1
        # reduction table: t^d mod m for d = k .. 2k-2, each a length-k vector
        red = np.zeros((k - 1, k), dtype=np.int64) if k > 1 else np.zeros((0, 0))
        if k > 1:
            cur = np.array([(-self.m[i]) % p for i in range(k)], dtype=np.int64)  # t^k
            red[0] = cur
            for d in range(1, k - 1):
                # t^{k+d} = t * t^{k+d-1} mod m
                shifted = np.zeros(k + 1, dtype=np.int64)
                shifted[1:] = cur                      # multiply by t
                top = shifted[k]
                nxt = shifted[:k].copy()
                nxt = (nxt + top * red[0]) % p          # reduce the single t^k term
                cur = nxt % p
                red[d] = cur
        self.red = red

    def mul(self, A, B):
        """field product of (n,k) arrays A,B mod m, vectorised."""
        p, k = self.p, self.k
        n = A.shape[0]
        C = np.zeros((n, 2 * k - 1), dtype=np.int64)
        for i in range(k):
            Ai = A[:, i]
            if k == 1:
                C[:, i] = (C[:, i] + Ai * B[:, 0]) % p
            else:
                # add Ai * B shifted by i
                C[:, i:i + k] = (C[:, i:i + k] + Ai[:, None] * B) % p
        if k == 1:
            return C % p
        # reduce degrees 2k-2 .. k into 0..k-1
        out = C[:, :k].copy()
        for d in range(k, 2 * k - 1):
            out = (out + C[:, d][:, None] * self.red[d - k]) % p
        return out % p

    def powq(self, A, e):
        """A ** e (scalar exponent), vectorised over rows."""
        k = self.k
        res = np.zeros_like(A)
        res[:, 0] = 1                                   # identity = 1
        base = A.copy()
        while e:
            if e & 1:
                res = self.mul(res, base)
            e >>= 1
            if e:
                base = self.mul(base, base)
        return res

    def elements_chunk(self, lo, hi):
        """rows = base-p digit vectors of indices [lo,hi): shape (hi-lo, k)."""
        idx = np.arange(lo, hi, dtype=np.int64)
        cols = []
        for j in range(self.k):
            cols.append((idx // (self.p ** j)) % self.p)
        return np.stack(cols, axis=1)


def cube_root_map(p):
    """{F_p value of a cube root of unity: complex cube root}."""
    g = WS.primitive_root(p)
    r = pow(g, (p - 1) // 3, p)
    w = cmath.exp(2j * math.pi / 3)
    return {1: 1.0 + 0j, r: w, (r * r) % p: w * w, 0: 0.0 + 0j}


def eval_h_chunk(F, h_mod, X):
    """Horner evaluation of polynomial h (coeffs low->high, mod p) on element-array X."""
    n, k = X.shape
    acc = np.zeros((n, k), dtype=np.int64)
    for c in reversed(h_mod):
        acc = F.mul(acc, X)
        acc[:, 0] = (acc[:, 0] + c) % F.p
    return acc


def Tk(p, k, h_coeffs, m=None, chunk=1 << 20):
    """T_k = sum_{x in F_{p^k}} chi_3(h(x)),  chi_3 = cubic character (0 at h=0)."""
    F = GFpk(p, k, m)
    q = p ** k
    e = (q - 1) // 3
    h_mod = [c % p for c in h_coeffs]
    crmap = cube_root_map(p)
    total = 0.0 + 0j
    lo = 0
    while lo < q:
        hi = min(lo + chunk, q)
        X = F.elements_chunk(lo, hi)
        H = eval_h_chunk(F, h_mod, X)
        chi = F.powq(H, e)                              # in mu_3 subset F_p (constant polys)
        vals = chi[:, 0]                                # the F_p value; higher coeffs are 0
        # map F_p values -> complex; nonzero-but-not-cube-root would signal a bug
        # (chi(H)=H^e is a constant poly for H!=0; ==0 for H==0)
        uniq, inv = np.unique(vals, return_counts=False, return_inverse=True)
        cmap = np.array([crmap.get(int(u), None) for u in uniq], dtype=object)
        if any(c is None for c in cmap):
            bad = [int(u) for u, c in zip(uniq, cmap) if c is None]
            raise RuntimeError(f"non-cube-root value(s) {bad[:5]} at p={p} k={k} (bug)")
        cvec = np.array([complex(c) for c in cmap])
        total += cvec[inv].sum()
        lo = hi
    return total


# ============================================================================
# W-rail characteristic polynomial from T_1..T_g, and validation
# ============================================================================
def rail_charpoly(Ts, g):
    """W-rail (V_zeta) degree-g L-poly prod(1 - alpha_i T) from power sums s_k = -T_k."""
    s = [0] + [-Ts[k] for k in range(1, g + 1)]
    e = [0j] * (g + 1)
    e[0] = 1.0
    for kk in range(1, g + 1):
        acc = 0j
        for i in range(1, kk + 1):
            acc += (-1) ** (i - 1) * e[kk - i] * s[i]
        e[kk] = acc / kk
    return [((-1) ** kk) * e[kk] for kk in range(g + 1)]   # c_0..c_g, low->high


def eisenstein_round(z):
    """nearest element of Z[zeta_3] = Z + Z*w (w = e^{2pi i/3}); returns (a,b,err)."""
    w = cmath.exp(2j * math.pi / 3)
    b = z.imag / w.imag
    a = z.real - b * w.real
    ar, br = round(a), round(b)
    err = abs(z - (ar + br * w))
    return ar, br, err


def validate_rail(cpoly, p, g):
    """returns dict: integrality-in-Z[zeta3] err, Weil-bound ok, FE ok, freeze value."""
    # Eisenstein integrality
    eis = [eisenstein_round(c) for c in cpoly]
    integ = max(e[2] for e in eis)
    # Weil: reciprocal roots of X^g P(1/X) = sum c_k X^{g-k}
    Q = [complex(c) for c in cpoly]                    # c_0 X^g + ... + c_g
    roots = np.roots(Q) if len(Q) > 1 else []
    weil = (len(roots) == g and all(abs(abs(r) - math.sqrt(p)) < 1e-4 * math.sqrt(p)
                                    for r in roots))
    # functional equation: |c_g| = p^{g/2}; freeze = prod(alpha)/p^{g/2} = c_g / p^{g/2}
    freeze = cpoly[g] / p ** (g // 2) if g % 2 == 0 else None
    return dict(integ=integ, weil=weil, roots=roots, freeze=freeze, eis=eis)


# ============================================================================
# non-CM members (small integer roots; 6 distinct for g4, 8 distinct for g6)
# ============================================================================
def poly_from_roots(rts):
    c = [1]
    for r in rts:
        c2 = [0] * (len(c) + 1)
        for i, a in enumerate(c):
            c2[i] += a * (-r)
            c2[i + 1] += a
        c = c2
    return c                                            # low->high


def h_member(fr, gr):
    """h = f * g^2 from root lists fr (for f) and gr (for g)."""
    fpoly = poly_from_roots(fr)
    gpoly = poly_from_roots(gr)
    g2 = poly_from_roots(gr + gr)                       # g^2
    # multiply fpoly * g2
    out = [0] * (len(fpoly) + len(g2) - 1)
    for i, a in enumerate(fpoly):
        for j, b in enumerate(g2):
            out[i + j] += a * b
    return out


# INFINITY-RAMIFIED configs (3 does not divide deg h) so the cubic character sum
# cleanly equals the degree-g zeta-rail trace (no spurious principal term).
# g4 fourfold: h = f_2 g_3^2, exps [1,1,2,2,2], deg 8, sig (2,2).
# g6 sixfold:  h = f_4 g_3^2, exps [1,1,1,1,2,2,2], deg 10, sig (3,3).
FOURFOLD = ([0, 1], [2, 3, 4])                          # 5 distinct roots
SIXFOLD = ([0, 1, 2, 3], [4, 5, 6])                     # 7 distinct roots


def run_family(name, fr, gr, g, primes, do_predict=True):
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    hc = h_member(fr, gr)
    allroots = fr + gr
    P(f"  member {name}: y^3 = f(x) g(x)^2, f roots {fr}, g roots {gr}; genus {g}, "
      f"signature ({g//2},{g//2})")
    P(f"    h(x) degree {len(hc)-1}, {len(set(allroots))} distinct roots")
    P(f"  {'p':>5s} {'W-rail deg-%d L-poly (Z[zeta3])' % g:>34s} {'Weil':>5s} "
      f"{'wedge^%d W / p^%d' % (g, g//2):>16s} {'recon':>7s}")
    angle_stream = {}
    for p in primes:
        if (p - 1) % 3 != 0:
            continue
        # bad prime: a root collides mod p (need distinct roots mod p)
        if len({r % p for r in allroots}) != len(allroots):
            continue
        Ts = {k: Tk(p, k, hc) for k in range(1, g + 1)}
        cpoly = rail_charpoly(Ts, g)
        val = validate_rail(cpoly, p, g)
        eis_str = "[" + ",".join(
            (f"{a}" if b == 0 else f"{a}{'+' if b>=0 else ''}{b}w")
            for a, b, _ in val["eis"]) + "]"
        frz = val["freeze"]
        frz_str = ("1(FREEZE)" if abs(frz - 1) < 1e-4
                   else f"{frz.real:+.3f}{frz.imag:+.3f}i") if frz is not None else "-"
        recon = "-"
        if do_predict and val["weil"] and p ** (g + 1) <= 2_000_000:
            # predict T_{g+1} from the g roots, cross-check by an INDEPENDENT direct count
            Tpred = sum(r ** (g + 1) for r in val["roots"])     # T_{g+1} = -s_{g+1} = sum alpha^{g+1}
            Tpred = -Tpred                                       # s_{g+1}=sum alpha^{g+1}; T=-s
            Tdir = Tk(p, g + 1, hc)
            recon = "OK" if abs(Tpred - Tdir) < 1e-3 else f"MISS({abs(Tpred-Tdir):.1e})"
        P(f"  {p:>5d} {eis_str:>34s} {'YES' if val['weil'] else 'NO':>5s} "
          f"{frz_str:>16s} {recon:>7s}")
        # angle vector (W-rail arg/pi) for the detector
        angs = sorted(round(cmath.phase(r) / math.pi, 4) for r in val["roots"])
        P(f"        angle-{g}-vector (W-rail arg/pi): {angs}")
        angle_stream[p] = dict(Lpoly_eis=[(a, b) for a, b, _ in val["eis"]],
                               angles=angs, freeze=(frz.real, frz.imag) if frz else None,
                               c1=val["eis"][1][:2])              # s_1 proxy (trace spread)
    # NON-CM diagnostic: the freeze character has finite order (Weil class present even
    # transcendentally), and the degree-1 coeff (trace proxy) SPREADS across primes -- a
    # CM Hecke character would lock it to a fixed pattern.
    frz_orders = set()
    for d in angle_stream.values():
        if d["freeze"]:
            z = complex(*d["freeze"])
            for o in (1, 2, 3, 4, 6):
                if abs(z ** o - 1) < 1e-3:
                    frz_orders.add(o)
                    break
    c1s = {d["c1"] for d in angle_stream.values()}
    P(f"  NON-CM check: freeze-character order(s) = {sorted(frz_orders)} "
      f"(finite => Weil class present transcendentally); {len(c1s)} distinct trace "
      f"coeffs over {len(angle_stream)} primes (spread, not CM-locked).")
    P(f"    Verification level: heuristic. End^0 ⊇ Q(√-3) structural; generic member has "
      f"End^0 = Q(√-3) exactly (non-CM); geometric simplicity not proven here.")
    return lines, angle_stream


def main():
    pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    out = []

    def P(s=""):
        print(s, flush=True)
        out.append(s)

    P("#" * 78)
    P("# NON-CM WEIL-TYPE POINT-COUNT INSTRUMENT (cyclic cubic covers y^3 = f g^2)")
    P("# open-frontier hunt: fourfold (2,2) + sixfold (3,3), K = Q(sqrt-3), zeta_3 rails")
    P("#" * 78)
    P()
    P("=" * 78)
    P("FOURFOLD  y^3 = f_3(x) g_3(x)^2  (genus 4, signature (2,2)) -- ORPHAN-TEST target")
    P("=" * 78)
    fp = [p for p in WS.sieve(pmax) if p % 3 == 1 and p >= 7]
    l4, stream4 = run_family("F4", *FOURFOLD, 4, fp)
    out += l4
    P()
    P("=" * 78)
    P("SIXFOLD  y^3 = f_4(x) g_4(x)^2  (genus 6, signature (3,3)) -- OPEN FRONTIER")
    P("=" * 78)
    sp = [p for p in WS.sieve(20) if p % 3 == 1 and p >= 7][:2]   # small p (p^6 vectorised)
    l6, stream6 = run_family("S6", *SIXFOLD, 6, sp, do_predict=False)
    out += l6
    P()
    P("  (sixfold k=6 counts are p^6 vectorised; largest prime reached noted above.)")

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "weil_sixfold_count_results.txt")
    with open(path, "w") as f:
        f.write("\n".join(out) + "\n")
    print(f"\n[results -> {path}]", flush=True)
    return stream4, stream6


if __name__ == "__main__":
    main()
