# W13: the lambda*Theta^3 closure test.  The universal rigidity law says
# [Z] = lambda Theta^3; Theta stays (1,1) on every POLARIZED deformation,
# so the class-variation pi(ob(v)) must vanish on the ENTIRE true-polarized
# KS-image (twisted-mixed r=3 (+) pure-sym, 21-dim) and be nonzero exactly
# where Theta moves (polarization-breaking Lambda^2 directions).
load('w10_pairing.sage')
r = 3
# true-polarized image: twisted-sym mixed (9) + pure-sym (12)
TP = matrix(K6, 21, 60)
ridx = 0
for m in range(3):
    for n in range(3, 6):
        TP[ridx, POS[(4+m, n)]] += 1
        TP[ridx, POS[(4+n, m)]] += r
        ridx += 1
for blk in (range(3), range(3, 6)):
    for m in blk:
        for n in blk:
            if n < m: continue
            TP[ridx, POS[(4+m, n)]] += 1
            TP[ridx, POS[(4+n, m)]] += 1
            ridx += 1
print(f"PREDICTION 1: rank(B on true-polarized 21) = {(TP*B).rank()}  (lambda-Theta^3 law demands 0)")
# polarization-breaking image: twisted-anti mixed (9) + pure-anti (6)
NP = matrix(K6, 15, 60)
ridx = 0
for m in range(3):
    for n in range(3, 6):
        NP[ridx, POS[(4+m, n)]] += 1
        NP[ridx, POS[(4+n, m)]] += -r
        ridx += 1
for blk in (range(3), range(3, 6)):
    for m in blk:
        for n in blk:
            if n <= m: continue
            NP[ridx, POS[(4+m, n)]] += 1
            NP[ridx, POS[(4+n, m)]] += -1
            ridx += 1
print(f"PREDICTION 2: rank(B on pol-breaking 15) = {(NP*B).rank()}  (Theta moves everywhere: 15)")
# and obstructedness of pol-breaking pure-anti block (outside im delta?)
PA = NP[9:, :]
print(f"pure-anti dims outside im(delta): {PA.stack(IMD).rank() - IMD.rank()} of 6")
