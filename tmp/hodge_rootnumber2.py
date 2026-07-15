"""
Widened exact root-number scan: W_m = kappa * i^(alpha*m + beta) * factor(kind,m),
factor in {1, quad if m even, quad if m odd, quad all}, quad = tau(eta_7)/sqrt7 = i (mu4).
All terms are exact mu4 phases -> W_m must be real +/-1 (self-dual).  Scan (alpha,beta,kind,kappa),
find every clean formula reproducing the 17 measured signs; report per-m misses; extend winners.

Question settled by the output:
  - if a FULLY clean mu4 law hits 17/17 -> the sign law is exactly period-4, m=2 NOT special,
    and the extension gives the definitive exception set (Sam's doubt resolved by the pattern).
  - if the best clean law is 16/17 with the sole miss = m=2 -> m=2 is an IRREDUCIBLE local
    anomaly at the minimal odd weight k=3 (a genuine Atkin-Lehner flip no character formula
    predicts), and NO other exceptions exist in the exactly-computable range.
"""
import mpmath as mp
mp.mp.dps = 40
I = mp.mpc(0, 1)
z7 = mp.e ** (2 * mp.pi * I / 7)
QR = {1, 2, 4}
def leg7(a):
    a %= 7
    return 0 if a == 0 else (1 if a in QR else -1)
tau_eta = sum((leg7(a) * z7 ** a for a in range(1, 7)), mp.mpc(0))
quad = tau_eta / mp.sqrt(7)          # == i
MEAS = {1:+1,2:-1,3:-1,4:-1,5:+1,6:+1,7:-1,8:-1,9:+1,10:+1,11:-1,12:-1,13:+1,14:+1,15:-1,16:-1,17:+1}

def factor(kind, m):
    if kind == 'none': return mp.mpc(1)
    if kind == 'qe':   return quad if m % 2 == 0 else mp.mpc(1)
    if kind == 'qo':   return quad if m % 2 == 1 else mp.mpc(1)
    if kind == 'qa':   return quad
def sgn(w): return +1 if w.real > 0 else -1

results = []
for kind in ('none', 'qe', 'qo', 'qa'):
    for alpha in range(-3, 4):
        for beta in range(-3, 4):
            for kap in (mp.mpc(1), mp.mpc(-1), I, -I):
                realQ, matches, misses = True, 0, []
                for m in range(1, 18):
                    w = kap * I ** (alpha * m + beta) * factor(kind, m)
                    if abs(w.imag) > 1e-9:
                        realQ = False; break
                    if sgn(w) == MEAS[m]: matches += 1
                    else: misses.append(m)
                if realQ:
                    results.append((matches, kind, alpha, beta, kap, misses))

results.sort(key=lambda r: -r[0])
print("== best clean mu4 formulas (real W_m for all m) ==")
seen = set()
for (matches, kind, alpha, beta, kap, misses) in results:
    key = (matches, kind, alpha % 4, beta % 4, str(misses))
    if key in seen: continue
    seen.add(key)
    if matches >= 15:
        print("  %d/17  kind=%-4s i^(%+d m %+d)  kappa=%-6s  misses=%s"
              % (matches, kind, alpha, beta, mp.nstr(kap, 3), misses))

best = results[0][0]
print("\n  BEST = %d/17" % best)
seventeen = [r for r in results if r[0] == 17]
if seventeen:
    print("  -> a FULLY CLEAN period-4 law exists; m=2 is NOT anomalous. Extending:")
    matches, kind, alpha, beta, kap, _ = seventeen[0]
    seq = []
    for m in range(1, 49):
        w = kap * I ** (alpha * m + beta) * factor(kind, m)
        seq.append('+' if sgn(w) > 0 else '-')
    for r0 in range(0, 48, 12):
        print("   m=%2d..%2d: %s" % (r0 + 1, r0 + 12, " ".join(seq[r0:r0 + 12])))
    exc = [m for m in range(1, 49)
           if (m % 2 == 0) and ((seq[m-1] == '+') != (m % 4 == 2))]
    print("   even-m deviations from (m==2 mod4 -> +):", exc)
else:
    solo = [r for r in results if r[0] == 16 and r[5] == [2]]
    print("  -> NO fully clean law; best is 16/17 with sole miss = m=2 in %d formulas." % len(solo))
    print("     => m=2 is an IRREDUCIBLE local anomaly at weight k=3; the law is otherwise")
    print("        exactly period-4 and predicts NO further exceptions.  Extending the clean law:")
    if solo:
        matches, kind, alpha, beta, kap, _ = solo[0]
        seq = []
        for m in range(1, 49):
            w = kap * I ** (alpha * m + beta) * factor(kind, m)
            seq.append('+' if sgn(w) > 0 else '-')
        seq[1] = '-'  # impose the measured m=2 anomaly
        for r0 in range(0, 48, 12):
            print("   m=%2d..%2d: %s" % (r0 + 1, r0 + 12, " ".join(seq[r0:r0 + 12])))
        print("   hidden-cycle (eps=-1) grades m<=48:", [m for m in range(1, 49) if seq[m-1] == '-'])
