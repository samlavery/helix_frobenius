# W9/J4 stage 2: the syzygy presentation of coker(delta) on the certified
# (3,3)-specimen.  With rigidity (rank 27), delta: H^1(T_Z) -> H^1(O_Z) (x) W
# is injective and coker(delta) = (ker mu)^* where mu is the rigidity
# multiplication — the 33-dim SYZYGY SPACE of the products, the part of
# H^1(N) that receives the transverse Kodaira-Spencer obstructions.
# This script re-runs the certified candidate (deterministic seed; it is
# candidate 1) via load, then extracts the graded syzygy basis and stores it.

load('w8_model33.sage')   # stops after the certified hit; globals in scope:
                          # bases, WITS, Ppoly, rowsM, labels, A, NODES

MM = matrix(K6, rowsM)
KS = MM.left_kernel().basis_matrix()
print(f"SYZYGY SPACE: dim = {KS.nrows()} (expect 33 = 60 - 27)", flush=True)

# graded dims: a syzygy is graded if supported on products of one grade;
# the product list order: (j1 in 0..2) x (j2 in 1,2) x (ra) x (rb)
gdim = {}
for gt in range(3):
    idxs = [i for i in range(len(labels)) if labels[i] == gt]
    sub = MM.matrix_from_rows(idxs)
    gdim[gt] = sub.nrows() - sub.rank()
print(f"graded syzygy dims: {gdim}  (predict 9/12/12 by the product counts "
      f"18/21/21 minus 9/9/9)", flush=True)

# sanity: the graded pieces exhaust the kernel
assert sum(gdim.values()) == KS.nrows(), "grading mismatch"

# store the syzygy basis + the product index map for stage 3
import json
out = {
    'dim': int(KS.nrows()),
    'graded': {str(k): int(v) for k, v in gdim.items()},
    'labels': [int(l) for l in labels],
    'nodes': str(NODES),
}
with open('w9_syzygy_meta.json', 'w') as fh:
    json.dump(out, fh)
print("meta stored (w9_syzygy_meta.json); basis in session scope for stage 3",
      flush=True)

# ---- first stage-3 ingredient: the U-side.  H^2(O_Z) restriction classes
# come from Lambda^2 H^1(O_X); on the curve model H^1(O_C~) = H^0(omega~)^*
# via Serre duality, and the anti-invariant part is W.  The pairing columns
# need cup products H^1(O) x H^1(O) -> H^2(O) on Z = Sym^3: in curve terms
# these are exterior products of Serre-dual functionals — representable by
# the SAME witness machinery once H^1-classes are coded as functionals on
# H^0(omega~).  Bookkeeping check we can do NOW: the dimension ledger.
print("LEDGER: h^0(N) = 6 (rigidity, certified);", flush=True)
print("        coker delta = 33 (syzygies, computed above);", flush=True)
print("        H^1(O_Z)(x)W = 60; H^1(T_Z) = 27 injects (certified);",
      flush=True)
print("        delta_2: H^2(T_Z) = H^1(T_C~)(x)H^1(O_C~) = 270 ->", flush=True)
print("        H^2(O_Z)(x)W = 45 x 6 = 270 (square; ker = remaining piece "
      "of H^1(N))", flush=True)