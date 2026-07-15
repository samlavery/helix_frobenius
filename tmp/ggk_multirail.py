"""
ggk_multirail.py -- the CORRECT multi-rail reading of the freeze mass (no k-ladder).

The block/freeze structure is a MULTI-RAIL decomposition, not a single-rail higher harmonic:
you decompose the fiber into components (rails) and count them with multiplicity, Sum mi^2.
That count IS the k=1 freeze mass  M1 = avg_p |W_p|^2 / p  (the second moment of the
chi3-eigenspace Frobenius trace) -- read at the FIRST level, sharpened with many primes.
No Frobenius powers, no cubic root change, none of the failure modes that wreck k>=2.

Rails, named by the fiber's own structure:
  family A  h=(x^4+1)(x^4+s)^2 : has the mu4 automorphism x -> i x  (h(ix)=h(x))
            => chi3-part splits into TWO mu4 rail-groups  => freeze mass 2
  family B  h=(x^4+1)(x^4+s x+2)^2 : generically no mu4 => ONE rail => freeze mass 1
W_p = sum_{x in F_p} chi3(h(x))  = -tr(Frob | H^1_chi3).  M1 = avg |W_p|^2 / p.
Primes p == 1 mod 12 (chi3 needs 3|p-1; the mu4 rail lives over i in F_p, 4|p-1).
"""
import cmath, math

W3 = cmath.exp(2j * cmath.pi / 3)

def primes_1mod12(n):
    out = []
    for p in range(13, n):
        if p % 12 != 1:
            continue
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            out.append(p)
    return out

def prim_root(p):
    fac, m, d = [], p - 1, 2
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
    return 2

def chi3_table(p):
    g = prim_root(p)
    r = pow(g, (p - 1) // 3, p)
    e = (p - 1) // 3
    tab = [0j] * p
    for a in range(1, p):
        v = pow(a, e, p)
        tab[a] = 1 + 0j if v == 1 else (W3 if v == r else W3 * W3)
    return tab

def hval(fco, gco, x, p):
    def ev(co):
        v = 0
        for c in co:
            v = (v * x + c) % p
        return v
    f = ev(fco); g = ev(gco)
    return (f * g % p) * g % p        # f * g^2

def freeze_mass(fco, gfam, s, primes):
    tot = wsum = 0.0
    for p in primes:
        tab = chi3_table(p)
        W = sum(tab[hval(fco, gfam(s), x, p)] for x in range(p))
        tot += abs(W) ** 2 / p
        wsum += 1.0
    return tot / wsum

P = primes_1mod12(9000)     # k=1 is cheap: use many primes for a sharp count
F = [1, 0, 0, 0, 1]         # f = x^4 + 1
famA = lambda s: [1, 0, 0, 0, s]        # g = x^4 + s
famB = lambda s: [1, 0, 0, s, 2]        # g = x^4 + s x + 2
A_GEN = [-2, 2, 3]          # generic (mu4-symmetric) members, 3 rails on p=1 mod 12
B_GEN = [2, 3]              # generic members, 1 rail

lines = ["== multi-rail freeze mass (k=1 only, Sum mi^2 = rail count) =="]
lines.append("primes: %d  (p == 1 mod 12)" % len(P))
Avals = {s: freeze_mass(F, famA, s, P) for s in A_GEN}
Bvals = {s: freeze_mass(F, famB, s, P) for s in B_GEN}
for s in A_GEN:
    lines.append("  A s=%3d  freeze mass = %.4f" % (s, Avals[s]))
for s in B_GEN:
    lines.append("  B s=%3d  freeze mass = %.4f" % (s, Bvals[s]))
a = sum(Avals.values()) / len(Avals)
b = sum(Bvals.values()) / len(Bvals)
lines.append("-- rail count --")
lines.append("  A generic mean = %.4f  (mu4 splits: expect 3 rails)" % a)
lines.append("  B generic mean = %.4f  (simple: expect 1 rail)" % b)
lines.append("  ratio A/B      = %.4f  (expect 3.00)" % (a / b))
out = "\n".join(lines)
print(out)
open("/Users/samuellavery/work/helix_frobenius/tmp/ggk_multirail_results.txt", "w").write(out + "\n")
