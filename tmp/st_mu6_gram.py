"""S(t) registration statistics: Gram's law (unit-1 chart ticks) vs the mu6/pi-3 carrier cells.

PRE-REGISTERED (2026-07-14, Sam's protocol):
  Single confirmatory statistic for THIS run: the mod-6 alignment signal (sum sq dev of the 6
  bin nonzero-defect rates beyond what mod-2 explains) tested against the CIRCULAR-SHIFT null
  (which preserves the Rosser-block autocorrelation of the defect sequence exactly; the IID
  permutation null of run 1 overstates significance for autocorrelated sequences and is kept
  only for comparison).
  Run-1 findings at N=1200 (tmp/st_mu6_gram_results_run1.txt): wall-parity prediction NULL
  (0.0449 vs 0.0483, reversed in upper half); mod-6 IID-permutation p=0.0355 (suspect).
  DISCUSSION GATE: any verdict (either direction) goes to discussion before being recorded.

Facts used: theta(g_n) = n*pi, so S(g_n) = N(g_n) - 1 - n exactly; Gram's law (weak) =
  sign Z(g_n) = (-1)^n; defect D_n := N(g_n) - (n+1).
"""

import os
import sys
import bisect
import random
from mpmath import mp, zetazero, grampoint, siegelz

mp.dps = 15
N = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
NZ = N + 100

ZCACHE = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"
GCACHE = "/Users/samuellavery/work/helix_frobenius/tmp/gram_cache.txt"

def load_cache(path):
    if os.path.exists(path):
        with open(path) as f:
            return [float(x) for x in f.read().split()]
    return []

def save_cache(path, vals):
    with open(path, "w") as f:
        f.write("\n".join("%.10f" % v for v in vals))

gam = load_cache(ZCACHE)
print("cached zeros: %d" % len(gam))
for n in range(len(gam) + 1, NZ + 1):
    gam.append(float(zetazero(n).imag))
    if n % 250 == 0:
        print("  zero %d: %.4f" % (n, gam[-1]))
        save_cache(ZCACHE, gam)
save_cache(ZCACHE, gam)

gz = load_cache(GCACHE)  # interleaved: gram point, Z-sign
g = gz[0::2]
zs = gz[1::2]
print("cached gram points: %d" % len(g))
for n in range(len(g), N + 1):
    gp = float(grampoint(n))
    g.append(gp)
    zs.append(1.0 if siegelz(gp) > 0 else -1.0)
    if n % 250 == 0:
        print("  gram %d: %.4f" % (n, g[-1]))
        inter = []
        for a, b in zip(g, zs):
            inter.extend([a, b])
        save_cache(GCACHE, inter)
inter = []
for a, b in zip(g, zs):
    inter.extend([a, b])
save_cache(GCACHE, inter)

g = g[:N + 1]
zs = zs[:N + 1]
Ncount = [bisect.bisect_right(gam, gp) for gp in g]
D = [Ncount[n] - (n + 1) for n in range(N + 1)]
viol = [n for n in range(N + 1) if (zs[n] > 0) != (n % 2 == 0)]
Dnz = [1 if D[n] != 0 else 0 for n in range(N + 1)]

def sig6_of(seq):
    m6 = []
    for kk in range(6):
        sel = [seq[n] for n in range(len(seq)) if n % 6 == kk]
        m6.append(sum(sel) / max(1, len(sel)))
    me = (m6[0] + m6[2] + m6[4]) / 3
    mo = (m6[1] + m6[3] + m6[5]) / 3
    return sum((m6[k] - (me if k % 2 == 0 else mo)) ** 2 for k in range(6)), m6

sig, m6 = sig6_of(Dnz)

# circular-shift null: preserves autocorrelation exactly, tests mod-6 ALIGNMENT only
shift_sigs = []
L = len(Dnz)
for s in range(1, L):
    shifted = Dnz[s:] + Dnz[:s]
    shift_sigs.append(sig6_of(shifted)[0])
p_shift = (1 + sum(1 for x in shift_sigs if x >= sig)) / (1 + len(shift_sigs))

# IID permutation null (kept for comparison; known to overstate)
random.seed(12345)
perm = Dnz[:]
perm_sigs = []
for _ in range(2000):
    random.shuffle(perm)
    perm_sigs.append(sig6_of(perm)[0])
p_iid = (1 + sum(1 for x in perm_sigs if x >= sig)) / (1 + len(perm_sigs))

lines = []
lines.append("== run 2: N=%d gram ticks (heights %.2f .. %.2f) ==" % (N, g[0], g[-1]))
lines.append("gram violations (weak law): %d / %d  rate %.4f" % (len(viol), N + 1, len(viol) / (N + 1)))
ve = sum(1 for n in viol if n % 2 == 0)
vo = len(viol) - ve
lines.append("  wall parity (even n): %d/%d rate %.4f   DC parity (odd n): %d/%d rate %.4f"
             % (ve, (N + 2) // 2, ve / ((N + 2) // 2), vo, (N + 1) // 2, vo / ((N + 1) // 2)))
lines.append("nonzero defect rate: %.4f" % (sum(Dnz) / (N + 1)))
lines.append("mod-6 bin rates: " + "  ".join("%.4f" % r for r in m6))
lines.append("mod-6 signal: %.6f" % sig)
lines.append("CIRCULAR-SHIFT p (correct null): %.4f   [IID permutation p: %.4f]" % (p_shift, p_iid))
half = N // 2
sig_hi, m6_hi = sig6_of(Dnz[half:])
shift_hi = []
Lh = len(Dnz[half:])
for s in range(1, Lh):
    sh = Dnz[half:][s:] + Dnz[half:][:s]
    shift_hi.append(sig6_of(sh)[0])
p_hi = (1 + sum(1 for x in shift_hi if x >= sig_hi)) / (1 + len(shift_hi))
lines.append("upper half only: mod-6 signal %.6f, circular-shift p %.4f" % (sig_hi, p_hi))
lines.append("")
lines.append("VERDICT INPUTS (discussion gate before any recorded verdict):")
lines.append("  pre-registered statistic = mod-6 alignment vs circular-shift null: p=%.4f (full), p=%.4f (upper half)" % (p_shift, p_hi))

out = "\n".join(lines)
print(out)
with open("/Users/samuellavery/work/helix_frobenius/tmp/st_mu6_gram_results.txt", "w") as f:
    f.write(out + "\n")
print("\nwritten to tmp/st_mu6_gram_results.txt")
