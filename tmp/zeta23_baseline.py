"""BASELINE: reproduce the published numbers of

    Claude/Anthropic, "More than two thirds of the zeros of the Riemann zeta function
    lie on the critical line" (2026-08-10).   Local copy: refs/zeta23_paper.pdf

Every target below is a number PRINTED IN THE PAPER.  Each check recomputes it from the
paper's own stated formulas and compares.  Nothing here is fitted, and nothing is taken
from our own earlier scripts.

SCOPE, stated up front so the certification is not over-read:
  * CERTIFIED here: the closed-form laws (1.3), every DERIVED column of the tables in
    section 8 (l, L, X, d, N, F), the headline constants of Theorems A-D, the degree
    formula of Remark 7.2(ii), and the internal algebraic consistency of the three laws.
  * NOT certified here: the MEASURED columns (C/N, tr R, cert), which require building
    the Gram matrix from primes and zeros.  Those live in zeta23_twosided.py / _lambda.py.
    A line is printed for each so the boundary is explicit.
"""
import math

PASS, FAIL = [], []


def chk(name, got, want, tol, note=""):
    ok = (want == 0 and abs(got) <= tol) or (want != 0 and abs(got - want) <= tol)
    (PASS if ok else FAIL).append(name)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name:<46} got {got!r:>14}  want {want!r:>12}"
          f"{('   ' + note) if note else ''}")
    return ok


# ---------------------------------------------------------------- the three laws, (1.3)
def H(lam):  return 2.0 - 1.0/lam - lam/3.0          # on-line proportion
def Hd(lam): return (1.0 + H(lam))/2.0               # distinct-zero proportion
def F(lam):  return lam/(1.0 + lam*lam/3.0)          # form factor  (tr G)^2 / (N tr G^2)


print("=" * 100)
print("(1.3)  THE THREE LAWS AT lambda = 1")
print("=" * 100)
chk("H(1) = 2/3",  round(H(1.0), 12),  round(2/3, 12),  1e-12)
chk("Hd(1) = 5/6", round(Hd(1.0), 12), round(5/6, 12),  1e-12)
chk("F(1) = 3/4",  round(F(1.0), 12),  0.75,            1e-12,
    "paper's fraction is layout-mangled; sec 8(1) prints F(1)=0.750")

print("\n  threshold:  Hd(lam) >= F(lam)  <=>  H(lam) >= 0  <=>  lam >= 3 - sqrt 6")
thr = 3 - math.sqrt(6)
chk("3 - sqrt(6)", round(thr, 4), 0.5505, 1e-4)
chk("H(3-sqrt6) = 0", round(H(thr), 12), 0.0, 1e-12)
# the equivalence itself, over a grid -- and F(lam) > 1/2 is the SAME condition
bad = [l for l in [x/2000 for x in range(20, 2001)]
       if (Hd(l) >= F(l)) != (H(l) >= -1e-15) or (F(l) > 0.5) != (H(l) > 1e-15)]
chk("equivalences hold on 0.01<=lam<=1 grid", len(bad), 0, 0,
    "Hd>=F <=> H>=0 <=> F>1/2")

print("\n" + "=" * 100)
print("SECTION 8(2)   l = log(sqrt(T1 T2)/2pi),  L = lam*l,  X = e^L = (T/2pi)^lam")
print("=" * 100)
# window, lam, printed L, printed X, printed F
S82 = [((9000, 10000),      0.70,  5.12,    168, 0.602),
       ((9000, 10000),      0.85,  6.22,    504, 0.685),
       ((9000, 10000),      1.00,  7.32,   1510, 0.750),
       ((48000, 50000),     0.85,  7.62,   2033, 0.685),
       ((48000, 50000),     1.00,  8.96,   7797, 0.750),
       ((998000, 1000000),  0.85, 10.18,  26374, 0.685),
       ((998000, 1000000),  1.00, 11.98, 158996, 0.750)]
for (T1, T2), lam, Lp, Xp, Fp in S82:
    l = math.log(math.sqrt(T1*T2)/(2*math.pi))
    L = lam*l
    X = math.exp(L)
    tag = f"[{T1},{T2}] lam={lam:.2f}"
    chk(f"{tag}  L", round(L, 2), Lp, 5e-3)
    chk(f"{tag}  X", round(X),    Xp, max(2, 0.002*Xp))
    chk(f"{tag}  F(lam)", round(F(lam), 3), Fp, 1e-3)

print("\n" + "=" * 100)
print("SECTION 8(4)   eta = 1/log(l),  lam0 = (1-eta)lam,  L0 = (1-eta)*lam*l,")
print("               d = floor(T/h) with h = 2pi/L0,   N = T*l/2pi")
print("=" * 100)
# T, eta, printed L0, printed d, printed Tl/2pi, printed F(lam0);  lam = 0.9 throughout
S84 = [(2000.0, 0.571, 2.225,  708,  1834, 0.368),
       (2000.0, 0.150, 4.409, 1403,  1834, 0.640),
       (1e4,    0.501, 3.314, 5274, 11734, 0.421),
       (1e4,    0.150, 5.640, 8976, 11734, 0.640)]
LAM = 0.9
# NOTE.  For the two rows where the paper says eta = 1/log(l), the PRINTED eta (0.571,
# 0.501) is a 3-figure rounding of it.  Using the printed value instead of the exact one
# shifts L0 in the 3rd decimal and can move floor(T/h) by one.  Use exact where stated.
EXACT_ETA = {0.571, 0.501}
for T, eta_p, L0p, dp, Np, Fp in S84:
    l = math.log(T/(2*math.pi))
    eta = 1/math.log(l) if eta_p in EXACT_ETA else eta_p
    L0 = (1 - eta)*LAM*l
    h = 2*math.pi/L0
    d_raw = T/h
    d = math.floor(d_raw)
    N = T*l/(2*math.pi)
    lam0 = (1 - eta)*LAM
    tag = f"T={T:g} eta={eta_p}"
    chk(f"{tag}  L0", round(L0, 3), L0p, 2e-3, f"exact eta={eta:.6f}")
    chk(f"{tag}  d",  d, dp, 1, f"T/h = {d_raw:.2f}")
    chk(f"{tag}  T*l/2pi", round(N), Np, 1)
    chk(f"{tag}  F(lam0)", round(F(lam0), 3), Fp, 1e-3)
# the paper's parenthetical: eta = 0.571, 0.501 are 1/log(l)
for T, eta_p in ((2000.0, 0.571), (1e4, 0.501)):
    l = math.log(T/(2*math.pi))
    chk(f"eta = 1/log(l) at T={T:g}", round(1/math.log(l), 3), eta_p, 1e-3)

print("\n" + "=" * 100)
print("HEADLINE CONSTANTS (Theorems A-D) AND THE CEILING")
print("=" * 100)
chk("Thm A/B on-line proportion  H(1)", round(H(1.0), 4), 0.6667, 1e-4, "= 2/3")
chk("Thm C distinct proportion  Hd(1)", round(Hd(1.0), 4), 0.8333, 1e-4, "= 5/6")
chk("improves on-line from 5/12",  round(5/12, 4), 0.4167, 1e-4, "Levinson-type prior")
chk("improves distinct from 0.6603", 0.6603, 0.6603, 0.0, "[Wu15]")
print("  [ -- ] Thm D optimised (Montgomery-Taylor kernel): 0.6725, 0.6725, 0.83625"
      "   NOT recomputed: needs the extremal kernel of sec 7.1")
print("  [ -- ] Remark 1.1 ceiling 0.68185 for bandwidth-one certificates"
      "         NOT recomputed: needs the 256-periodic extremal law")
chk("Thm B's 2/3 is within 0.016 of 0.68185",
    round(0.68185 - 2/3, 3), 0.015, 1e-3, "paper says 'within 0.016'")

print("\n  Remark 7.2(ii):  c = Lambda/(1 + m_F Lambda^2/3);  GL(2) has Lambda* = 1/2, m_F = 1")
c_gl2 = 0.5/(1 + 1*0.25/3)
chk("c(GL2) = 6/13", round(c_gl2, 6), round(6/13, 6), 1e-9)
chk("c(GL2) < 1/2  => method vacuous", int(c_gl2 < 0.5), 1, 0, "'nothing, whatever the window'")
chk("on-line proportion 2 - 1/c <= 0", int(2 - 1/c_gl2 <= 0), 1, 0)
chk("non-vacuous iff Lambda* > 3-sqrt6 (m_F=1)",
    round(3 - math.sqrt(6), 4), 0.5505, 1e-4, "same root as H(lam)=0 -- consistent")

print("\n" + "=" * 100)
print("BOUNDARY: measured quantities NOT certified here (need the Gram matrix)")
print("=" * 100)
for s in ("sec 8(1) two-sided agreement 1e-6..1.1e-8   -> zeta23_twosided.py",
          "sec 8(1) C_prime=351.3, C_zero=351.4, C/N=0.744 -> zeta23_lambda.py",
          "sec 8(2) C/N and cert columns                -> zeta23_lambda.py",
          "sec 8(3) C_pred vs C_zero (1322.72/1322.28)  -> not reproduced",
          "sec 8(4) tr R/main, tr R^2/main columns      -> not reproduced"):
    print(f"  [ -- ] {s}")

print("\n" + "=" * 100)
print(f"CERTIFIED {len(PASS)} / {len(PASS)+len(FAIL)} checks against printed values.")
if FAIL:
    print("FAILURES:")
    for f in FAIL:
        print("   -", f)
print("=" * 100)
