# REGISTER-FREE cell floor: anchors defined by the READOUT'S OWN zeros.
# Between consecutive vanishings the carrier phase advances by pi; the pi/3 cells are
# the thirds.  (At those thirds a pure clock has |cos| = sqrt(3)/2 EXACTLY -- the sharp
# constant of the compiled floor.  No theta, no Gram, no RS truncation: anchors come
# from the object itself.  siegelz is used only as a NUMERICAL evaluator.)
# PRE-REGISTERED: report min over gaps of |Z| at third-points, and A_eff = that/(sqrt(3)/2).
# Compare to the theta-anchored numbers (att561): 1.01, 0.75, 1.00, 0.74.
# Rule: register-free >= theta-anchored at every height => harmonization helps (Sam);
#       otherwise report the shortfall honestly.
from mpmath import mp, mpf, siegelz, zetazero, sqrt
mp.dps = 15
print(f"{'height':>9} {'n gaps':>7} {'min |Z| at thirds':>19} {'A_eff':>8} {'theta-anchored':>15}")
prev = {1000: 1.0145, 10000: 0.7497, 100000: 1.0008, 1000000: 0.7358}
idx = {1000: 649, 10000: 10142, 100000: 138069, 1000000: 1747146}
for T0, n0 in idx.items():
    gs = [zetazero(n0 + i).imag for i in range(0, 26)]
    vals = []
    for k in range(len(gs)-1):
        a, b = gs[k], gs[k+1]
        for j in [1, 2]:
            vals.append(abs(siegelz(a + (b-a)*mpf(j)/3)))
    m = min(vals)
    print(f"{T0:>9} {len(gs)-1:>7} {float(m):>19.4f} {float(m/(sqrt(3)/2)):>8.3f} {prev[T0]:>15.4f}")
