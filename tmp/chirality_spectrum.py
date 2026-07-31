# ATTEMPT: chirality spectrum of W-rail strands (carrier-native pairing readout).
# FIBER: W-rail Frobenius traces s_k = tr(Frob^k | V_omega), exact in Z[w], w = zeta_3.
# CARRIER: mu6 cells. HELIX: the odd (sine) channel of the strand: c_k = Im(s_k)/p^{k/2}.
# Self-paired rail (rational coeffs) => c_k = 0 EXACTLY (integer-level).  Cross-paired
# => a chirality SPECTRUM.  Pre-registered readouts:
#   C0 gate: self-paired specimens give b-part == 0 exactly at every k.
#   G0 gate: exact Newton power sums match numeric roots (1e-8).
#   C1: harmonic concentration of |c_k| (report by k, and k mod 6 / k mod 3 classes).
#   C2: cross-prime stability for B_{a=1} (p=7 vs 13): sign pattern + spectrum corr
#       (2 primes => indicative only, registered as such).
#   C3: same-degree cross-specimen comparison at p=7 (three cross-paired sixfold rails
#       + the SAME-DEGREE self-paired B2 rail control).
# GUARD: no number-field factorization, no gcd, no polynomial algebra beyond integer
# Newton identities on Z[w] pairs (the mu6 lattice's own integers).  Numeric roots are
# used ONLY for the G0 gate and the mu6-cell histogram display.
import numpy as np

SQRT3_2 = np.sqrt(3.0) / 2.0
W = np.exp(2j * np.pi / 3)

# ---- exact Z[w] arithmetic: pair (a, b) = a + b*w,  w^2 = -1 - w ----
def zw_add(x, y): return (x[0] + y[0], x[1] + y[1])
def zw_mul(x, y):
    a, b = x; c, d = y
    return (a * c - b * d, a * d + b * c - b * d)
def zw_neg(x): return (-x[0], -x[1])
def zw_scale(n, x): return (n * x[0], n * x[1])
def zw_complex(x): return x[0] + x[1] * W

def newton_power_sums(coeffs, kmax):
    """coeffs = [c1..cn] of monic T^n + c1 T^{n-1} + ... + cn, entries Z[w] pairs.
    Returns exact power sums s_1..s_kmax (Z[w] pairs)."""
    n = len(coeffs)
    s = []
    for k in range(1, kmax + 1):
        acc = (0, 0)
        for i in range(1, min(k, n) + 1):
            prev = s[k - i - 1] if k - i >= 1 else None
            if k - i == 0:
                continue
            acc = zw_add(acc, zw_mul(coeffs[i - 1], prev))
        if k <= n:
            acc = zw_add(acc, zw_scale(k, coeffs[k - 1]))
        s.append(zw_neg(acc))
    return s

# ---- specimens: monic Frobenius-eigenvalue char polys (roots |alpha| = sqrt p) ----
# coefficients c1..cn as Z[w] pairs (a, b)
SPECIMENS = [
    # fourfold W-rail at p=7, monic reciprocal of 49T^4-7T^3+2T^2-T+1
    ("fourfold  self  p=7 ", 7, [(-1, 0), (2, 0), (-7, 0), (49, 0)]),
    # B2 rail (Z/2-Prym piece, mu6 tower) at p=7 -- SAME-DEGREE self-paired control
    ("B2-rail   self  p=7 ", 7, [(-1, 0), (0, 0), (31, 0), (0, 0), (-49, 0), (343, 0)]),
    # sixfold B_{a=1} f_omega at p=7
    ("B_a=1     cross p=7 ", 7, [(0, -2), (3, -2), (9, 0), (35, 14), (98, 98), (343, 0)]),
    # sixfold B_{a=1} f_omega at p=13
    ("B_a=1     cross p=13", 13, [(3, -1), (22, -1), (63, 0), (299, 13), (676, 169), (2197, 0)]),
    # mu6 tower B6 (chi-primitive) rail at p=7
    ("B6-mu6    cross p=7 ", 7, [(1, 4), (-12, -12), (43, 0), (0, 84), (-147, -196), (343, 0)]),
    # mu6 tower B3 (mu3 control) rail at p=7
    ("B3-mu6    cross p=7 ", 7, [(-3, -2), (-2, 0), (3, 0), (-14, 0), (-49, 98), (343, 0)]),
]

KMAX = 12
results = {}
gate_fail = False

for name, p, coeffs in SPECIMENS:
    n = len(coeffs)
    s = newton_power_sums(coeffs, KMAX)

    # G0 gate: numeric cross-check via roots
    poly = [1.0 + 0j] + [zw_complex(c) for c in coeffs]
    roots = np.roots(poly)
    g0_ok = True
    for k in range(1, KMAX + 1):
        num = np.sum(roots ** k)
        exact = zw_complex(s[k - 1])
        if abs(num - exact) / max(1.0, abs(exact)) > 1e-8:
            g0_ok = False
    # purity display + mu6-cell histogram (numeric, display only)
    purity = np.max(np.abs(np.abs(roots) - np.sqrt(p)))
    ph = np.angle(roots / np.abs(roots))
    cells = np.floor(((ph + np.pi) / (np.pi / 3))).astype(int)  # 6 cells of pi/3... 12 half-cells
    hist = np.bincount(cells % 12, minlength=12)

    # chirality spectrum
    b_parts = [s[k - 1][1] for k in range(1, KMAX + 1)]
    c = [SQRT3_2 * b_parts[k - 1] / p ** (k / 2.0) for k in range(1, KMAX + 1)]
    r = [(s[k - 1][0] - s[k - 1][1] / 2.0) / p ** (k / 2.0) for k in range(1, KMAX + 1)]

    self_paired = all(cc[1] == 0 for cc in coeffs)
    c0 = "n/a"
    if self_paired:
        c0 = "PASS" if all(b == 0 for b in b_parts) else "FAIL"
        if c0 == "FAIL":
            gate_fail = True
    if not g0_ok:
        gate_fail = True

    results[name] = dict(p=p, c=c, r=r, b=b_parts, self_paired=self_paired)
    print(f"{name} deg={n}  G0={'PASS' if g0_ok else 'FAIL'}  purity_dev={purity:.2e}  "
          f"C0(self=>b==0)={c0}")
    print(f"   b-parts (exact): {b_parts}")
    print(f"   c_k = Im s_k/p^(k/2): {[f'{x:+.4f}' for x in c]}")
    print(f"   mu6 half-cell hist: {hist.tolist()}", flush=True)

print()
print("== C1: harmonic concentration (cross-paired, p=7) ==")
for name in results:
    if results[name]["self_paired"] or "13" in name:
        continue
    c = np.array(results[name]["c"])
    e = c ** 2
    tot = e.sum()
    by3 = [e[[k - 1 for k in range(1, KMAX + 1) if k % 3 == rr]].sum() / tot for rr in (0, 1, 2)]
    by6 = [e[[k - 1 for k in range(1, KMAX + 1) if k % 6 == rr]].sum() / tot for rr in range(6)]
    top = np.argsort(-e)[:3] + 1
    print(f"{name}: energy by k mod 3 (0,1,2) = {[f'{x:.3f}' for x in by3]}  "
          f"top-k = {top.tolist()}")
    print(f"   energy by k mod 6 = {[f'{x:.3f}' for x in by6]}")

print()
print("== C2: cross-prime stability, B_a=1 p=7 vs p=13 (2 primes: indicative only) ==")
c7 = np.array(results["B_a=1     cross p=7 "]["c"])
c13 = np.array(results["B_a=1     cross p=13"]["c"])
signs7 = np.sign(c7).astype(int)
signs13 = np.sign(c13).astype(int)
match = int(np.sum(signs7 == signs13))
corr = float(np.corrcoef(c7, c13)[0, 1])
print(f"sign(c_k) p=7 : {signs7.tolist()}")
print(f"sign(c_k) p=13: {signs13.tolist()}")
print(f"sign matches: {match}/{KMAX}   spectrum corr: {corr:+.3f}")

print()
print("== C3: same-degree comparison at p=7 (three cross rails + self control) ==")
for name in ["B_a=1     cross p=7 ", "B6-mu6    cross p=7 ", "B3-mu6    cross p=7 ",
             "B2-rail   self  p=7 "]:
    c = np.array(results[name]["c"])
    print(f"{name}: |c| L2 = {np.linalg.norm(c):.4f}  Linf = {np.max(np.abs(c)):.4f}  "
          f"first-fire k = {next((k for k in range(1, KMAX + 1) if abs(c[k - 1]) > 1e-12), None)}")

print()
print("GATES:", "FAIL -- verdicts void" if gate_fail else "ALL PASS")
print("CHIRALITY DONE", flush=True)
