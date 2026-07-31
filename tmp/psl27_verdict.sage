# THE PSL(2,7) VERDICT (2026-07-28): etale PSL(2,7)-cover of a genus-2 curve;
# the 3-dim irrep packet (char field EXACTLY Q(sqrt-7)) gives a Weil-type
# SIXFOLD B, signature (3,3)/Q(sqrt-7) (Chevalley-Weil balance, etale), from a
# SIMPLE group -- outside Patel-Zhang entirely. K = Q(sqrt-7): 2 SPLITS,
# 3 and 5 are INERT. Verdict: Pfaffian of the multiplicity-one slice lattice
# (H = Z/3: dim chi^H = 1); ODD v_3 or v_5 => disc not a norm => NON-SPLIT
# Weil sixfold class = the beyond-everything frontier object.
# Model: triple-gated cut-glue (Lange-Ortega x2 + house mu6).
from sage.all import matrix, identity_matrix, ZZ, block_matrix, libgap
import json

G = libgap.PSL(2, 7)
els = list(G.Elements())
n = len(els)
assert n == 168
idx = {str(e): i for i, e in enumerate(els)}
tbl = G.CharacterTable()
irr = tbl.Irr()
classes = tbl.ConjugacyClasses()
elcls = []
for e in els:
    for ci, c in enumerate(classes):
        if e in c.AsList():
            elcls.append(ci)
            break
# the 3-dim packet: the two conjugate degree-3 characters
chi3s = [chi for chi in irr if int(chi[0]) == 3]
assert len(chi3s) == 2
psi = []   # rational packet char values per element
for i in range(n):
    v = chi3s[0][elcls[i]] + chi3s[1][elcls[i]]
    psi.append(int(v))
print("packet char values (distinct):", sorted(set(psi)), flush=True)

gbase = 2
H = gbase - 1
N = 2 * H * n + 2
E = matrix(ZZ, N, N)
for i in range(n):
    E[i, n + i] = 1
    E[n + i, i] = -1
E[N-2, N-1] = 1; E[N-1, N-2] = -1

def act(kk):
    M = matrix(ZZ, N, N)
    for gi, ge in enumerate(els):
        t = idx[str(kk * ge)]
        M[t, gi] = 1
        M[n + t, n + gi] = 1
    M[N-2, N-2] = 1; M[N-1, N-1] = 1
    return M

print("building projector...", flush=True)
Pnum = matrix(ZZ, N, N)
for gi, ge in enumerate(els):
    if psi[gi] != 0:
        Pnum += psi[gi] * act(ge)
scale = n // 3          # e_packet = (3/168) sum psi(g^{-1}) g ; psi symmetric
M_iso = scale * identity_matrix(ZZ, N) - Pnum
print("isotypic kernel...", flush=True)
Lam = M_iso.right_kernel().basis_matrix()
print("iso rank:", Lam.nrows(), "(expect 36 = H1(B^3))", flush=True)

# multiplicity-one slice: H0 = Z/3 (chi3 restricted = 1 + omega + omegabar)
z3gen = None
for e in els:
    if int(libgap.Order(e)) == 3:
        z3gen = e
        break
Mz = act(z3gen) - identity_matrix(ZZ, N)
stack = block_matrix(ZZ, [[M_iso], [Mz]])
B = stack.right_kernel().basis_matrix()
print("slice rank:", B.nrows(), "(expect 12 = H1 of the sixfold)", flush=True)
Gram = B * E * B.T
eds = [x for x in Gram.elementary_divisors() if x != 0]
pairs = eds[::2]
assert eds[1::2] == pairs, f"SNF pairing anomaly {eds}"
pf = ZZ(1)
for x in pairs:
    pf *= x
vals = {str(p): int(pf.valuation(p)) for p in (2, 3, 5, 7, 11, 13) if pf % p == 0}
odd_inert = {p: v for p, v in [("3", pf.valuation(3)), ("5", pf.valuation(5))]
             if v % 2 == 1}
rec = {"group": "PSL(2,7)", "g": 2, "packet": "3+3bar (field Q(sqrt-7))",
       "slice": "Z/3-invariants", "rank": int(B.nrows()),
       "type": [int(x) for x in pairs], "Pf": int(pf), "valuations": vals,
       "odd_at_K_inert(3,5)": {k: int(v) for k, v in odd_inert.items()}}
print(rec, flush=True)
verdict = "NON-SPLIT CLASS FOUND" if odd_inert else "split again (null)"
print("VERDICT:", verdict, flush=True)
with open("psl27_verdict.json", "w") as fh:
    json.dump(rec, fh)
print("PSL27 DONE", flush=True)
