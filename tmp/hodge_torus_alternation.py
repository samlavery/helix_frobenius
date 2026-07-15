"""
Sam: "the Hodge structure switches between elliptical and circular torus, it alternates as
grades increase" + "gets cleaner as more roots of unity and more harmonics scale out".

(A) Tabulate the alternation: weight k=m+1, the polarization symmetry (-1)^k (symmetric=orthogonal
    =CIRCULAR torus; alternating=symplectic=ELLIPTICAL torus), the archimedean phase i^{m+1}
    (real mu2 <-> circular ; imaginary mu4 <-> elliptical), and the measured sign.  Show the
    torus shape alternates with grade parity, and mu4 (the quarter-turn i = quadratic Gauss sum
    i*sqrt7) lives exactly on the elliptical (odd-weight, even-m) grades.

(B) Does m=2 dissolve as more roots of unity scale out?  Scan clean formulas over mu4, mu6, mu12,
    mu24 and report the best match to the 17 measured signs.  Honest test of "cleaner".
    Key falsifier: any clean mu_d-PERIODIC fix for m=2 also fires at m=2+d; e.g. a mu12 fix
    would flip m=14 -- but m=14 is measured CLEAN (+1).  So watch whether finer roots actually
    reach 17/17 or whether m=2 stays irreducible.
"""
import mpmath as mp
mp.mp.dps = 30
I = mp.mpc(0, 1)
MEAS = {1:+1,2:-1,3:-1,4:-1,5:+1,6:+1,7:-1,8:-1,9:+1,10:+1,11:-1,12:-1,13:+1,14:+1,15:-1,16:-1,17:+1}

print("== (A) torus / polarization alternation ==")
print(" m  wt=k  pol.symmetry   torus       arch i^{m+1}   mu     meas eps")
for m in range(1, 15):
    k = m + 1
    sym = "symmetric " if k % 2 == 0 else "alternating"
    torus = "CIRCULAR " if k % 2 == 0 else "ELLIPTICAL"
    ph = I ** (m + 1)
    isreal = abs(ph.imag) < 1e-9
    mu = "mu2 (+/-1)" if isreal else "mu4 (+/-i)"
    print("  %2d   %2d   %s   %s   %-7s  %s   %+d"
          % (m, k, sym, torus, mp.nstr(ph, 3), mu, MEAS[m]))
print("  -> circular (even wt, odd m): real mu2 sign.  elliptical (odd wt, even m): mu4 quarter-turn")
print("     (the i is exactly tau(eta_7)/sqrt7, the quadratic Gauss sum).  Alternates every grade.")

print("\n== (B) does m=2 dissolve as roots of unity get finer? ==")
z7 = mp.e ** (2 * mp.pi * I / 7)
QR = {1, 2, 4}
tau_eta = sum(((1 if a in QR else -1) * z7 ** a for a in range(1, 7)), mp.mpc(0))
quad = tau_eta / mp.sqrt(7)   # = i
def sgn(w): return +1 if w.real > 0 else -1

def best_over(dord):
    """best match over W_m = kappa * w^(alpha*m+beta) * quad^e, w=zeta_dord, real W only."""
    w = mp.e ** (2 * mp.pi * I / dord)
    best = (0, None)
    kappas = [w ** t for t in range(dord)]
    for e in (0, 1):
        for alpha in range(dord):
            for beta in range(dord):
                for kap in kappas:
                    ok, matches, miss = True, 0, []
                    for m in range(1, 18):
                        fac = (quad if (m % 2 == 0 and e == 1) else mp.mpc(1))
                        val = kap * w ** (alpha * m + beta) * fac
                        if abs(val.imag) > 1e-9:
                            ok = False; break
                        if sgn(val) == MEAS[m]: matches += 1
                        else: miss.append(m)
                    if ok and matches > best[0]:
                        best = (matches, (alpha, beta, e, miss))
    return best

for dord in (4, 6, 12, 24):
    matches, info = best_over(dord)
    miss = info[3] if info else None
    print("  roots of unity mu_%-2d :  best %d/17   misses=%s" % (dord, matches, miss))
print("  (17/17 would mean finer roots DISSOLVE m=2; 16/17 miss={2} means m=2 is irreducible)")

# recurrence falsifier: is the m=2 anomaly mu_d-periodic for any d dividing into measured range?
print("\n  recurrence check: measured sign at m=2 and m=2+d for small d (anomaly would repeat):")
for d in (4, 6, 12):
    if 2 + d in MEAS:
        print("   d=%2d : eps(2)=%+d  eps(%d)=%+d   %s"
              % (d, MEAS[2], 2 + d, MEAS[2 + d],
                 "same (could be periodic)" if MEAS[2] == MEAS[2 + d] else "DIFFERENT -> not mu_%d-periodic" % d))
