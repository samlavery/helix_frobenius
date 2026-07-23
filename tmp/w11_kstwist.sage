# W11: the KS-twist resolution.  Geometry demands: the eps-equivariant
# (Weil-family) KS-rows lie IN im(delta) — the AP-cycle deforms along the
# Prym family, so ob(v) = 0 there, i.e. v|_Z in ker(q) = im(delta).  The
# naive rows are NOT in im(delta) (B is full-rank on them yet kills
# im(delta)) => the U-side restriction carries its own AP scalar twist.
# Scan the relative twist r: rows v_mn(r) = theta_m (x) w_n + r * theta_n
# (x) w_m over mixed (grade-1, grade-2) pairs; find r with all 9 rows in
# im(delta).  Then re-measure B on the corrected transverse complement.
load('w10_pairing.sage')   # B, IMD (27x60), POS, CM, zeta, K6

cands = []
for k in range(6):
    for base in [K6(1), CM[0]/CM[3], CM[3]/CM[0], CM[0]*CM[3],
                 1/(CM[0]*CM[3]), CM[0]^2, CM[3]^2]:
        cands.append((zeta^k) * base)
        cands.append(-(zeta^k) * base)
cands = list(set(cands))
print(f"scanning {len(cands)} twist candidates", flush=True)

IMDrank = IMD.rank()
hits = []
for r in cands:
    rows = matrix(K6, 9, 60)
    ridx = 0
    for m in range(3):
        for n in range(3, 6):
            rows[ridx, POS[(4+m, n)]] += 1
            rows[ridx, POS[(4+n, m)]] += r
            ridx += 1
    stacked = IMD.stack(rows)
    if stacked.rank() == IMDrank:
        hits.append(r)
print(f"twists with ALL 9 equivariant rows in im(delta): {hits}", flush=True)

if len(hits) == 1:
    r = hits[0]
    print(f"GEOMETRY SELECTS r = {r}", flush=True)
    # corrected blocks:
    # equivariant (in im delta, obstruction-free): v_mn(r)  [verified above]
    # transverse candidates: the complementary mixed twist v_mn(-r or 1/r?)
    # = the other eigenline: v'_mn = theta_m (x) w_n - r * theta_n (x) w_m,
    # plus the pure blocks Sym^2 W1, Sym^2 W2 (12 dims).
    T1 = matrix(K6, 9, 60)
    ridx = 0
    for m in range(3):
        for n in range(3, 6):
            T1[ridx, POS[(4+m, n)]] += 1
            T1[ridx, POS[(4+n, m)]] += -r
            ridx += 1
    P11 = matrix(K6, 6, 60)
    ridx = 0
    for m in range(3):
        for n in range(m, 3):
            P11[ridx, POS[(4+m, n)]] += 1
            P11[ridx, POS[(4+n, m)]] += 1
            ridx += 1
    P22 = matrix(K6, 6, 60)
    ridx = 0
    for m in range(3, 6):
        for n in range(m, 6):
            P22[ridx, POS[(4+m, n)]] += 1
            P22[ridx, POS[(4+n, m)]] += 1
            ridx += 1
    print(f"CORRECTED BLOCK RANKS of the Bloch pairing:", flush=True)
    print(f"  anti-twisted mixed (9):  rank {(T1*B).rank()}", flush=True)
    print(f"  Sym^2 W1 (6):            rank {(P11*B).rank()}", flush=True)
    print(f"  Sym^2 W2 (6):            rank {(P22*B).rank()}", flush=True)
    TR = T1.stack(P11).stack(P22)
    print(f"  FULL TRANSVERSE (21-9=12... 21-dim candidate space): "
          f"rank {(TR*B).rank()} of {TR.nrows()}", flush=True)
    # also check: are the pure blocks in im delta too? (they'd be flat by
    # deformation, not just undetected)
    for nm, MM_ in (('Sym^2 W1', P11), ('Sym^2 W2', P22), ('anti-mixed', T1)):
        st = IMD.stack(MM_)
        extra = st.rank() - IMDrank
        print(f"  {nm}: dims OUTSIDE im(delta) = {extra} of {MM_.nrows()}",
              flush=True)
else:
    print("no unique twist — report all block memberships:", flush=True)
    for r in cands[:8]:
        rows = matrix(K6, 9, 60)
        ridx = 0
        for m in range(3):
            for n in range(3, 6):
                rows[ridx, POS[(4+m, n)]] += 1
                rows[ridx, POS[(4+n, m)]] += r
                ridx += 1
        extra = IMD.stack(rows).rank() - IMDrank
        print(f"  r = {r}: rows outside im(delta): {extra}/9", flush=True)
