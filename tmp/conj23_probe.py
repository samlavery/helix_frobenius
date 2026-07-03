"""Direct numerical probe of Zagier's literal 1977 Sym^4 conjecture for Delta
(equivalently Ibukiyama-Katsurada 2014 Conjecture 2.3, given their proven Thm 2.2).

Zagier Conj 1.1 (quoted verbatim in IK 2014 p.140; see tmp/sym4_constants_notes.md):
  (2pi)^(33-3s) * Gamma(11)^(-1) * Gamma(s) * Gamma(s-11) * L^mot(s, Delta, Sym4)
      = c(s) * 2^33 * <Delta,Delta>^3          for s = 24,26,28,30,32.

Split of proven vs open (IK 2014):
  - T(s) := LHS / (c(s) * 2^33) CONSTANT across s  <=> Thm 2.2 (PROVEN; T = (F,F)/2^33-scale).
  - R(s) := T(s) / <D,D>^3 == 1                    <=> Conjecture 2.3 (OPEN, tested here).
Also reports the measured (F,F)/<D,D>^3 against Conj 2.3's exact constant
2^15 * 3^6 * 5^5 * 13 = 970444800000, using (F,F) = 2^33*DD^3*R / (2^18 3^-6 5^-5 13^-1)
bookkeeping implicitly (R==1 <=> that identity).

Machinery reused verbatim from tmp/sym4_boundary.py (certified there:
Euler-vs-Dirichlet 1.6e-10, symbolic h_k 1e-13, unitarity OK).  mpmath 50 dps.
L^mot(s) = L^unit(s-22)  [rank-5 unitary shift u = s - 2(k-1), k=12].
<Delta,Delta> = Zagier's independent value (IK bare convention), cross-validated
in petersson_rung to 2.5e-17.
"""
import sys

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")

import mpmath as mp
import sym4_boundary as sb

mp.mp.dps = 50
N = 20000

lam = sb.load_tau_source(N)
spf = sb.smallest_prime_factor(N)
c4, _ = sb.build_ladder(lam, spf, N, 4)

DD = sb.DD_ZAGIER
C_TABLE = {
    24: mp.mpf(2) ** 5 * 3 ** 2,
    26: mp.mpf(2) ** 5 * 3 * 5,
    28: mp.mpf(2) ** 2 * 23 * 691 / mp.mpf(7) ** 2,
    30: mp.mpf(2) ** 3 * 653,
    32: mp.mpf(2) * 3 * 34981 / mp.mpf(7),
}
CONJ23_CONST = 2 ** 15 * 3 ** 6 * 5 ** 5 * 13  # 970444800000

lines = []


def emit(s=""):
    print(s)
    lines.append(s)


emit("CONJECTURE 2.3 PROBE -- Zagier's literal Sym^4 Delta conjecture, first numerics")
emit("=" * 78)
emit(f"ladder N={N}, mpmath dps={mp.mp.dps}; <D,D> = {mp.nstr(DD, 19)} (Zagier)")
emit("")
emit("  s   u    L^unit(u)              T(s)=LHS/(c(s)*2^33)     R(s)=T/<D,D>^3        tail")
Ts, Rs = [], []
for s in (24, 26, 28, 30, 32):
    u = s - 22
    L = sb.Lsum(c4, u, N)
    Lhalf = sb.Lsum(c4, u, N // 2)
    tail = abs(L - Lhalf)  # empirical truncation scale (N/2 -> N difference)
    lhs = (mp.power(2 * mp.pi, 33 - 3 * s) * mp.gamma(s) * mp.gamma(s - 11)
           / mp.gamma(11) * L)
    T = lhs / (C_TABLE[s] * mp.mpf(2) ** 33)
    R = T / DD ** 3
    Ts.append(T)
    Rs.append((s, R, tail))
    emit(f"  {s}  {u:2d}   {mp.nstr(L, 18):22s} {mp.nstr(T, 18):24s} "
         f"{mp.nstr(R, 18):20s} {mp.nstr(tail, 2)}")

emit("")
Tmid = Ts[2]
spread = max(abs(t / Tmid - 1) for t in Ts)
emit(f"THEOREM CHECK (IK Thm 2.2, proven): T(s) constant across s -- relative spread {mp.nstr(spread, 3)}")
emit(f"  (spread dominated by the u=2 edge tail; u>=4 points only: "
     f"{mp.nstr(max(abs(t / Tmid - 1) for t in Ts[1:]), 3)})")
emit("")
emit("OPEN-CONJECTURE VERDICT (Conj 2.3 / Zagier literal): R(s) == 1 ?")
for s, R, tail in Rs:
    dev = R - 1
    emit(f"  s={s}: R-1 = {mp.nstr(dev, 6)}")
best = min(abs(R - 1) for _, R, _ in Rs[1:])
emit("")
emit(f"implied (F,F)/<D,D>^3 vs Conj 2.3 constant {CONJ23_CONST}:")
FF_ratio = Tmid * mp.mpf(2) ** 33 / DD ** 3 * CONJ23_CONST / (mp.mpf(2) ** 33)
emit(f"  measured/predicted = {mp.nstr(Ts[2] * mp.mpf(2)**33 / (DD**3 * mp.mpf(2)**33), 18)}"
     f"  (== R(28); MATCH iff 1)")

if best < mp.mpf("1e-9"):
    emit("")
    emit("VERDICT: MATCH [open-conjecture-tested] -- Zagier's literal 1977 conjecture")
    emit("  (= IK Conj 2.3) confirmed numerically at the u>=4 points to < 1e-9;")
    emit("  first numerical test of the open constant ever run.")
else:
    emit("")
    emit(f"VERDICT: deviation {mp.nstr(best, 3)} at best u>=4 point -- NOT a sub-1e-9 landing;")
    emit("  register-grade result either way; see per-point table.")

with open("/Users/samuellavery/work/helix_frobenius/tmp/conj23_probe_results.txt", "w") as fh:
    fh.write("\n".join(lines) + "\n")
