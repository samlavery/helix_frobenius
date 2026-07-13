"""The K3 ledger reader: retention past the Faltings shield, v1 (diagonal quartics).

The clause-(c) falsifier hunt (equal full ledger, different cycle theory) is
structurally impossible on product/Kummer K3s (Faltings: zeta determines the
isogeny class of the factors).  Genuine non-product K3s are the mandatory
hunting ground.  This instrument builds the reader on the diagonal quartic
family -- Weil's original test bed --

    X_c :  x^4 + y^4 + z^4 + c w^4 = 0  in  P^3,   (rho(X_c/Qbar) = 20)

with EXACT point counts to large p via quartic-power frequency tables
(O(p^2) per prime, vectorized; no character-sum formula trusted, the counts
are raw).  Readings:

  t_p := (#X_c(F_p) - (1 + p + p^2)) / p     -- the normalized trace on the
         21-dimensional primitive H^2 (hyperplane class removed);

  DC occupancy (Q-rational primitive algebraic classes)   = mean of t_p;
  the angle channel (field of definition of the classes)  = means over
         progressions p mod 8 (the lines of X_c live over cyclotomic fields;
         classes rational only over K show up in the progression split --
         the delayed/base-change signature, as with CM);
  ledger separation (the clause-(c) probe, in-family)     = pairwise: twists
         with c'/c a fourth power are isomorphic (identical t_p forced);
         non-fourth-power twists must SEPARATE at primes with
         chi_4(c'/c) != 1.  A non-isomorphic pair with identical readings
         would be the falsifier.

Scope stated exactly: v1 reads the diagonal family (singular K3s, rho = 20,
maximal -- the CM-most corner); the escalation is non-diagonal quartics with
matched partial zeta data.  Run: python3 k3_ledger.py [PMAX=1500]  (~2 min)
"""
import sys, os, math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH

CS = [1, 2, 3, 4, 16]      # c-values; c=16 = 2^4 * 1 ~ isomorphic to c=1


def count_projective(p, c):
    """#X_c(F_p) exactly: affine cone count via quartic frequency tables,
    then (cone - 1)/(p - 1)."""
    x = np.arange(p, dtype=np.int64)
    q4 = np.zeros(p, dtype=np.int64)
    np.add.at(q4, (x * x % p) * (x * x % p) % p, 1)      # r4[v] = #{x^4 = v}
    # pair table: P2[s] = #{(x,y): x^4 + y^4 = s}
    P2 = np.zeros(p, dtype=np.int64)
    for v in range(p):
        if q4[v]:
            P2[(np.arange(p) + v) % p] += q4[v] * q4[np.arange(p)]
    # cone count: sum over (z,w) of P2[-(z^4 + c w^4)]
    zw = np.add.outer(x * x % p * (x * x % p) % p,
                      (c % p) * ((x * x % p) * (x * x % p) % p) % p) % p
    cone = int(P2[(-zw) % p].sum())
    return (cone - 1) // (p - 1)


def main():
    PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# K3 LEDGER READER v1 -- diagonal quartics, retention past the Faltings")
    P(f"# shield; exact counts, good odd p <= {PMAX}")
    P("#" * 78)
    P()
    prs = [p for p in SH.sieve_primes(PMAX) if p > 2]
    traces = {}
    for c in CS:
        ts = {}
        for p in prs:
            if c % p == 0:
                continue
            N = count_projective(p, c)
            ts[p] = (N - (1 + p + p * p)) / p
        traces[c] = ts
        arr = np.array(list(ts.values()))
        p1 = np.array([v for q, v in ts.items() if q % 8 == 1])
        p5 = np.array([v for q, v in ts.items() if q % 8 == 5])
        p37 = np.array([v for q, v in ts.items() if q % 8 in (3, 7)])
        P(f"  c = {c:3d}: DC occupancy (mean t_p) = {arr.mean():7.3f}   "
          f"by p mod 8:  1: {p1.mean():7.3f}   5: {p5.mean():7.3f}   "
          f"3,7: {p37.mean():7.3f}")
    P()
    P("  (the mod-8 split is the angle channel: classes rational only over")
    P("   cyclotomic fields appear in the progression means -- the base-change")
    P("   / delayed signature, as with CM; the Qbar total is rho - 1 = 19 over")
    P("   the splitting field.)")
    P()

    P("  LEDGER SEPARATION (the in-family clause-(c) probe):")
    ok = True
    for i in range(len(CS)):
        for j in range(i + 1, len(CS)):
            c1, c2 = CS[i], CS[j]
            common = sorted(set(traces[c1]) & set(traces[c2]))
            d = max(abs(traces[c1][p] - traces[c2][p]) for p in common)
            # c'/c a rational fourth power => isomorphic => identical forced
            ratio_is_4th = round((c2 / c1) ** 0.25) ** 4 * c1 == c2 or \
                round((c1 / c2) ** 0.25 if c2 > 0 else 0) ** 4 * c2 == c1
            iso = ratio_is_4th
            sep = d > 1e-12
            verdict = ("identical (isomorphic: ratio is a 4th power) OK"
                       if (iso and not sep) else
                       "separated OK" if (not iso and sep) else
                       "*** IDENTICAL BUT NOT ISOMORPHIC: clause-(c) EVENT ***"
                       if (not iso and not sep) else
                       "*** SEPARATED BUT ISOMORPHIC: instrument defect ***")
            if (not iso and not sep) or (iso and sep):
                ok = False
            P(f"    c = {c1:3d} vs c = {c2:3d}:  max |dt_p| = {d:8.4f}   "
              f"{verdict}")
    P()
    P("VERDICT:")
    if ok:
        P("  The K3 reader is live: exact counts, DC occupancies read with the")
        P("  angle channel resolving fields of definition, isomorphic twists")
        P("  identical as forced, and every non-isomorphic pair separated by the")
        P("  ledger -- no clause-(c) event in the diagonal family (as expected:")
        P("  twist characters separate).  The genuine hunt now escalates to")
        P("  non-diagonal quartics with matched partial zeta data, where no")
        P("  Faltings-type shield and no twist structure protects retention.")
    else:
        P("  An anomaly -- either a clause-(c) event (publish with priority) or")
        P("  an instrument defect; investigate before any claim.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "k3_ledger_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to k3_ledger_results.txt]")


if __name__ == "__main__":
    main()
