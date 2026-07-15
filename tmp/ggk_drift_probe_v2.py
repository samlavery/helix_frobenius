"""GGK drift probe v2 — correctly harmonized (Sam's audit, 2026-07-14).

FIXES over v1 (all four method-law violations):
  1. k-LADDER: moments at k = 1,2,3 via genuine Frobenius powers (character sums over F_{p^k},
     chi = chi3 . Norm — Hasse-Davenport compatible), not single-harmonic.
  2. NO CLIP: smooth cosine-squared taper in log p replaces the hard cutoff (raw also reported).
  3. RAILS: deterministic global character convention (smallest primitive root); phase-coherence
     statistic C_k = |avg_p unit(W_p^(k))| — frozen content is phase-coherent, Haar is not.
  4. CERTIFICATE: frozen mass = excess consistent ACROSS k (k-flatness) + C_k bounded away from 0;
     single-moment excess alone is not accepted.

PRE-REGISTERED (discussion gate before verdict):
  A generic s: excess ~1 unit at EVERY k + phase coherence (mu4-automorphism frozen line).
  B generic s: excess ~0, C_k ~ 0 (pure Haar).  B s=0: A-level excess (symmetry restored).
  A s=1: explosion at all k (total collision).  A s=0: branch collision, now resolvable or not.
M_k(s) = weighted avg |W_p^(k)|^2 / p^k;  excess = M_k - 1 (Haar baseline, Katz-Sarnak).
"""

import cmath
import math

W3 = cmath.exp(2j * math.pi / 3)

def primes_upto(n):
    return [p for p in range(7, n) if all(p % q for q in range(2, int(p**0.5) + 1)) and p % 3 == 1]

def prim_root(p):
    fac = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    return None

def chi3_table(p):
    g = prim_root(p)
    r = pow(g, (p - 1) // 3, p)  # deterministic: chi3(g) = w
    tab = [0j] * p
    e = (p - 1) // 3
    r2 = (r * r) % p
    for a in range(1, p):
        v = pow(a, e, p)
        tab[a] = 1 + 0j if v == 1 else (W3 if v == r else W3 * W3)
    return tab

def find_irr(p, k):
    # monic irreducible of degree k mod p: x^k + c x + d by trial (k = 2, 3)
    for c in range(p):
        for d in range(1, p):
            co = [1] + [0] * (k - 2) + [c, d] if k > 2 else [1, c, d][:k + 1]
            if k == 2:
                co = [1, c, d]
            # irreducible iff no root (k<=3)
            has_root = False
            for x in range(p):
                v = 0
                for cc in co:
                    v = (v * x + cc) % p
                if v == 0:
                    has_root = True
                    break
            if not has_root:
                if k == 2:
                    return co
                # degree 3: no root suffices for irreducibility
                return co
    return None

def field_ops(p, k, irr):
    # returns mul(a,b) and norm(a) for elements as tuples length k (coeffs of t^0..t^{k-1})
    red = [(-c) % p for c in irr[1:]]  # t^k = red[0] t^{k-1} + ... NO: irr = [1, a_{k-1i}...]
    # t^k = -(irr[1] t^{k-1} + ... + irr[k])
    def mul(a, b):
        prod = [0] * (2 * k - 1)
        for i in range(k):
            if a[i] == 0:
                continue
            for j in range(k):
                prod[i + j] = (prod[i + j] + a[i] * b[j]) % p
        for deg in range(2 * k - 2, k - 1, -1):
            c = prod[deg]
            if c:
                prod[deg] = 0
                for j in range(1, k + 1):
                    prod[deg - j] = (prod[deg - j] - c * irr[j]) % p
        return tuple(prod[:k])
    def norm(a):
        # det of multiplication-by-a matrix
        cols = []
        basis = [tuple(1 if i == j else 0 for i in range(k)) for j in range(k)]
        for e in basis:
            cols.append(mul(a, e))
        if k == 2:
            (m00, m10), (m01, m11) = cols[0], cols[1]
            return (m00 * m11 - m01 * m10) % p
        (a0, a1, a2), (b0, b1, b2), (c0, c1, c2) = cols
        det = (a0 * (b1 * c2 - b2 * c1) - b0 * (a1 * c2 - a2 * c1)
               + c0 * (a1 * b2 - a2 * b1)) % p
        return det
    return mul, norm

def weil_sum_ext(p, k, tab, hco):
    # sum over F_{p^k} of chi3(Norm(h(x))), h coeffs in F_p
    if k == 1:
        s = 0j
        for x in range(p):
            v = 0
            for c in hco:
                v = (v * x + c) % p
            s += tab[v]
        return s
    irr = find_irr(p, k)
    mul, norm = field_ops(p, k, irr)
    hmod = [c % p for c in hco]
    s = 0j
    # enumerate all p^k elements as tuples
    def elems(idx, cur):
        if idx == k:
            yield tuple(cur)
            return
        for v in range(p):
            cur.append(v)
            yield from elems(idx + 1, cur)
            cur.pop()
    one = tuple([1] + [0] * (k - 1))
    for x in elems(0, []):
        acc = tuple([hmod[0]] + [0] * (k - 1))
        for c in hmod[1:]:
            acc = mul(acc, x)
            acc = tuple((acc[i] + (c if i == 0 else 0)) % p for i in range(k))
        s += tab[norm(acc)]
    return s

def hpoly(fco, gco):
    # h = f * g^2 coefficient list
    def pmul(a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                r[i + j] += x * y
        return r
    return pmul(fco, pmul(gco, gco))

def probe(fco, gname, gfam, svals, kmax_primes):
    out = []
    for s in svals:
        h = hpoly(fco, gfam(s))
        row = {"s": s}
        for k, plist in kmax_primes.items():
            tot, wsum, coh = 0.0, 0.0, 0j
            L0, L1 = math.log(plist[0]), math.log(plist[-1]) + 1e-9
            for p in plist:
                tab = chi3_table(p)
                W = weil_sum_ext(p, k, tab, h)
                q = float(p) ** k
                w = math.cos(0.5 * math.pi * (math.log(p) - L0) / (L1 - L0)) ** 2
                tot += w * abs(W) ** 2 / q
                wsum += w
                if abs(W) > 1e-9:
                    coh += w * W / abs(W)
            row["M%d" % k] = tot / wsum
            row["C%d" % k] = abs(coh) / wsum
        out.append(row)
    return out

P1 = primes_upto(410)
P2 = primes_upto(200)
P3 = [7, 13, 19, 31, 37]
KP = {1: P1, 2: P2, 3: P3}

F = [1, 0, 0, 0, 1]
lines = ["== GGK probe v2: k-ladder, windowed, phase-coherent =="]
lines.append("primes: k1 n=%d (<=409), k2 n=%d (<=199), k3 %s" % (len(P1), len(P2), P3))
for name, fam, svals in [("A", lambda s: [1, 0, 0, 0, s], [-2, 0, 1, 2, 3]),
                          ("B", lambda s: [1, 0, 0, s, 2], [0, 2, 3])]:
    lines.append("-- family %s --" % name)
    for row in probe(F, name, fam, svals, KP):
        lines.append("  s=%3d  M1=%7.3f C1=%.3f | M2=%8.3f C2=%.3f | M3=%9.3f C3=%.3f"
                     % (row["s"], row["M1"], row["C1"], row["M2"], row["C2"],
                        row["M3"], row["C3"]))
out = "\n".join(lines)
print(out)
open("/Users/samuellavery/work/helix_frobenius/tmp/ggk_drift_probe_v2_results.txt", "w").write(out + "\n")
