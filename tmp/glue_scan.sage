# THE GLUE SCAN (2026-07-28): hunt for a design whose Pfaffian lands ODD at an
# inert prime => non-split Weil type => the beyond-Markman specimen class.
# Generic over finite groups via libgap: for each group G, each Galois-orbit
# packet of irreps of dim >= 2 NOT factoring through an abelian quotient
# (= outside Patel-Zhang), each subgroup H with <chi|_H, 1> = 1 (multiplicity-
# one slice), compute the isotypic/slice lattice of the cut-glue model
# H1 = Z[G]^{2(g-1)} (+) Z^2, its polarization type, Pfaffian, and prime
# valuations. Model TRIPLE-GATED earlier (Lange-Ortega x2, house mu6).
from sage.all import (matrix, identity_matrix, ZZ, QQ, block_matrix, libgap)
import json

def scan_group(gap_id_desc, gname, g_base, out):
    G = libgap.eval(gap_id_desc)
    els = list(G.Elements())
    n = len(els)
    idx = {str(e): i for i, e in enumerate(els)}
    tbl = G.CharacterTable()
    irr = tbl.Irr()
    classes = tbl.ConjugacyClasses()
    # class index of each element
    elcls = []
    for e in els:
        for ci, c in enumerate(classes):
            if e in c.AsList():
                elcls.append(ci); break
    # abelianization: irreps factoring through it are P-Z-covered; skip them
    der = G.DerivedSubgroup()
    packets = {}   # rational packet key -> integer char values per element
    for chi in irr:
        d = int(chi[0])
        if d < 2:
            continue
        # does chi factor through G/der? dim>=2 never does for the quotient
        # abelian; still check kernel contains der
        ker = tbl.KernelOfCharacter(chi)
        if bool(libgap.IsSubgroup(ker, der)):
            continue
        vals = [chi[elcls[i]] for i in range(n)]
        # rational packet = sum over Galois orbit: use GaloisOrbitSum via trace
        ratvals = tuple(int(libgap.Trace(v)) if not v.IsRat() else
                        int(v) * 1 for v in vals)
        # Trace = sum of conjugates when v cyclotomic; for rational v in a
        # nontrivial field the orbit size multiplies -- normalize by grouping
        packets.setdefault(ratvals, []).append(chi)
    H = g_base - 1
    N = 2 * H * n + 2
    E = matrix(ZZ, N, N)
    for h in range(H):
        base = 2 * n * h
        for i in range(n):
            E[base + i, base + n + i] = 1
            E[base + n + i, base + i] = -1
    E[N-2, N-1] = 1; E[N-1, N-2] = -1
    mulidx = {}
    def act(kk):
        M = matrix(ZZ, N, N)
        for h in range(H):
            base = 2 * n * h
            for gi, ge in enumerate(els):
                t = idx[str(kk * ge)]
                M[base + t, base + gi] = 1
                M[base + n + t, base + n + gi] = 1
        M[N-2, N-2] = 1; M[N-1, N-1] = 1
        return M
    acts = [act(e) for e in els]
    subs = [S.Representative() for S in G.ConjugacyClassesSubgroups()]
    for ratvals, chis in packets.items():
        chi0 = chis[0]
        d = int(chi0[0])
        fld = str(libgap.Field(libgap.Rationals, list(chi0)))
        # packet projector numerator: sum_e ratchar(e^{-1}) act(e); ratchar
        # symmetric under inverse for these (real or conj-closed packets)
        Pnum = sum(int(ratvals[i]) * acts[i] for i in range(n))
        scale = n // d
        M_iso = scale * identity_matrix(ZZ, N) - d * 0  # placeholder
        M_iso = scale * identity_matrix(ZZ, N) - Pnum
        Lam = M_iso.right_kernel().basis_matrix()
        rows = [("iso", Lam)]
        # multiplicity-one slices: subgroups H0 with <chi|_H0, 1> = 1
        for S in subs:
            so = int(S.Order())
            if so == 1 or so == int(G.Order()):
                continue
            selems = list(S.Elements())
            fix = sum(int(libgap.Trace(chi0[elcls[idx[str(e)]]]))
                      if not chi0[elcls[idx[str(e)]]].IsRat()
                      else int(chi0[elcls[idx[str(e)]]]) for e in selems)
            # <chi|_S, 1> for ONE chi (use exact char not packet): recompute
            inner = sum(chi0[elcls[idx[str(e)]]] for e in selems)
            try:
                innerq = int(inner) if inner.IsRat() else None
            except Exception:
                innerq = None
            if innerq is None or innerq != so:   # want dim chi^S = 1
                continue
            Msub = block_matrix(ZZ, [[M_iso]] +
                [[acts[idx[str(e)]] - identity_matrix(ZZ, N)] for e in selems])
            Bs = Msub.right_kernel().basis_matrix()
            if Bs.nrows() > 0:
                rows.append((f"slice|H|={so}", Bs))
        for tag, B in rows:
            if B.nrows() == 0:
                continue
            Gram = B * E * B.T
            eds = [x for x in Gram.elementary_divisors() if x != 0]
            pairs = eds[::2]
            if eds[1::2] != pairs:
                continue
            pf = ZZ(1)
            for x in pairs:
                pf *= x
            vals = {p: int(pf.valuation(p)) for p in (2, 3, 5, 7, 11, 13)
                    if pf % p == 0}
            odd = {p: v for p, v in vals.items() if v % 2 == 1}
            rec = {"group": gname, "g": g_base, "packet_dim": d,
                   "char_field": fld, "kind": tag, "rank": int(B.nrows()),
                   "type": [int(x) for x in pairs], "Pf": int(pf),
                   "valuations": vals, "ODD_VALUATIONS": odd}
            out.append(rec)
            flag = "  <<< ODD HIT" if odd else ""
            print(f"{gname} g={g_base} dim{d} {fld} {tag}: type={rec['type']}"
                  f" Pf={pf} vals={vals}{flag}", flush=True)

out = []
DESIGNS = [
    ("SmallGroup(12,1)", "Dic3=Z3:Z4"),
    ("SmallGroup(8,4)",  "Q8"),
    ("SmallGroup(24,3)", "SL(2,3)"),
    ("SmallGroup(24,11)","Q8xZ3"),
    ("SmallGroup(24,10)","D4xZ3"),
    ("SmallGroup(16,9)", "Q16"),
    ("SmallGroup(18,3)", "S3xZ3"),
    ("SmallGroup(21,1)", "F21=Z7:Z3"),
    ("SmallGroup(24,1)", "Z3:Z8"),
]
for gid, gname in DESIGNS:
    for g_base in (2,):
        try:
            scan_group(gid, gname, g_base, out)
        except Exception as ex:
            print(f"{gname}: ERROR {ex}", flush=True)
with open("glue_scan.json", "w") as fh:
    json.dump(out, fh, default=int)
print("GLUE SCAN DONE", flush=True)
