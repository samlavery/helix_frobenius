# End/MT analysis for the eightfold, run once tmp/eightfold_lpoly.log carries P_Prym.
# Parses the deg-16 Prym char poly at p = 7 and runs the sixfold-proven battery:
#   (1) irreducibility over Q  ==> SIMPLICITY (split prime: Frob_p = Frob_frak-p)
#   (2) subfield lattice of Q(pi_7): must contain Q(sqrt-3) = K; the OTHER subfields
#       are the End-candidate fingerprint (compare with a second prime when available)
#   (3) power stability: minpoly degree of pi^n for n in {2,3,4,6,8,12,16} -- degree
#       drop would signal extra endomorphisms appearing over an extension
#   (4) purity recheck exact: constant term = p^8, |roots|^2 p = 1
import re

with open('tmp/eightfold_lpoly.log') as fh:
    txt = fh.read()
m = re.search(r'P_Prym\(T\) deg 16 : (.*)', txt)
if not m:
    print("P_Prym not in log yet -- tower still running")
    sys.exit(0)

S = PolynomialRing(QQ, 'T')
T = S.gen()
P = S(sage_eval(m.group(1), locals={'T': T}))
print("P_Prym =", P)
assert P.degree() == 16

fac = P.factor()
print("factorization over Q:", fac)
irr = len(list(fac)) == 1 and fac[0][1] == 1
print("(1) SIMPLICITY:", "PASS -- simple abelian eightfold" if irr else "FAIL/inspect")

if irr:
    # normalize to monic integral: reciprocal poly of Frobenius eigenvalues
    Pm = (T ^ 16 * P(1 / T) / P(0) * P.leading_coefficient()).numerator()
    Pm = S(P.reverse() / P.leading_coefficient()) if False else S(list(reversed(P.list())))
    Pm = Pm / Pm.leading_coefficient()
    L = NumberField(Pm, 'pi')
    pi = L.gen()
    print("Q(pi_7) degree:", L.degree())
    subs = L.subfields()
    print("(2) subfield degrees:", sorted(set(F[0].degree() for F in subs)))
    for F, emb, _ in subs:
        if F.degree() == 2:
            print("    quadratic subfield:", F.defining_polynomial(),
                  " disc:", F.discriminant())
    has_K = any(F[0].degree() == 2 and F[0].discriminant() == -3 for F in subs)
    print("    contains K = Q(sqrt-3):", "PASS" if has_K else
          "NOT FOUND (check normalization)")
    print("(3) power stability (minpoly degree of pi^n):")
    stable = True
    for n in [2, 3, 4, 6, 8, 12, 16]:
        d = (pi ^ n).minpoly().degree()
        stable = stable and (d == 16)
        print(f"    n={n}: degree {d}")
    print("    STABLE (no degree drop):", "PASS -- End constraints geometric"
          if stable else "DROP -- extension endomorphisms, inspect")
    print("(4) constant/leading:", P.list()[0], P.list()[-1],
          " (expect 1 and 7^8 =", 7 ^ 8, ")")
    rts = P.change_ring(CDF).roots(multiplicities=False)
    print("    purity:", "PASS" if all(abs(abs(r) ^ 2 * 7 - 1) < 1e-6 for r in rts)
          else "FAIL")
