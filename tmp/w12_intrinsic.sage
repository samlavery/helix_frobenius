# W12: upgrade the r=3 scan hit to an intrinsic law:
#   im(delta) ∩ (mixed KS-span, 18-dim)  =?  the r=3 twisted space (9-dim)
# If dim = 9 exactly, the Weil tangent = im(delta) ∩ mixed — no convention.
load('w10_pairing.sage')
M18 = matrix(K6, 18, 60)
ridx = 0
for m in range(3):
    for n in range(3, 6):
        M18[ridx, POS[(4+m, n)]] = 1; ridx += 1
        M18[ridx + 8, POS[(4+n, m)]] = 1
for m in range(3):          # fix indexing: build cleanly instead
    pass
M18 = matrix(K6, 18, 60)
ridx = 0
for m in range(3):
    for n in range(3, 6):
        M18[ridx, POS[(4+m, n)]] = 1; ridx += 1
for m in range(3):
    for n in range(3, 6):
        M18[ridx, POS[(4+n, m)]] = 1; ridx += 1
rM, rI = M18.rank(), IMD.rank()
rU = M18.stack(IMD).rank()
inter = rM + rI - rU
print(f"dim(mixed span) = {rM}, dim(im delta) = {rI}, dim(union) = {rU}")
print(f"dim(im delta ∩ mixed) = {inter}   (intrinsic Weil tangent; scan said 9)")
# and the full 21-dim polarized-KS space for completeness:
S21 = matrix(K6, 21, 60)
ridx = 0
for m in range(6):
    for n in range(m, 6):
        S21[ridx, POS[(4+m, n)]] += 1
        S21[ridx, POS[(4+n, m)]] += 1
        ridx += 1
print(f"dim(im delta ∩ naive-Sym21) = {S21.rank() + rI - S21.stack(IMD).rank()}")
