#!/usr/bin/env python3
"""
C3 batch 14 -- numerical block 3.  SELF-AUDIT of a batch-13 citation.

Batch 13's FAILED item F4 killed the Schoenberg / Gaussian-scale-mixture route with this
argument:  a Gaussian scale mixture has a transform that is itself a Gaussian scale mixture,
hence completely monotone in x^2, hence MONOTONE DECREASING in |x|; and (F4 asserted)
"|L1| is not monotone", citing section P11.

P11's number came from tmp/c3b13_num2.py -- a script that NEVER FINISHED and produced ZERO
output.  The batch-13 ledger itself says "no result from it is used anywhere".  So F4's
evidence does not exist.  This block settles the question directly, cancellation-free, using
L1(x) = Xi(x)^2 * (xi'/xi)'(1/2 + i x).

Batch 14's S5 measured Rhat monotone on xi in [0,40] (i.e. x in [0,20]) in float64, which
CONTRADICTS F4 as stated.  Adjudicated here at 40 digits over a much wider range.
"""
from mpmath import mp, mpf, mpc, pi, log, fabs, psi, zeta, gamma, nstr

mp.dps = 40

def xi(s): return pi ** (-s / 2) * gamma(1 + s / 2) * (s - 1) * zeta(s)
def ldp(s):
    z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
    return -1/s**2 - 1/(s-1)**2 + psi(1, s/2)/4 + (z2*z0 - z1**2)/z0**2
def XI(x): return xi(mpc(mpf(1)/2, x)).real
def L1(x):
    X = XI(x); return X**2 * ldp(mpc(mpf(1)/2, x)).real

print("=" * 78)
print("A1 -- is |L1| monotone decreasing in |x| ?   (settles batch 13 F4 / P11)")
print("=" * 78)
print("  L1 computed cancellation-free from zeta, zeta', zeta'' and psi_1 at 40 digits.")
print()
for (lo, hi, step, label) in [(0, 20, '0.25', 'x in [0,20] step 0.25'),
                              (0, 60, '0.25', 'x in [0,60] step 0.25'),
                              (0, 120, '0.5', 'x in [0,120] step 0.5'),
                              (0, 300, '1.0', 'x in [0,300] step 1.0')]:
    st = mpf(step)
    n = int((hi - lo) / float(st))
    prev = None; ups = 0; first = None
    for k in range(n + 1):
        x = mpf(lo) + k * st
        v = fabs(L1(x))
        if prev is not None and v > prev:
            ups += 1
            if first is None: first = x
        prev = v
    print(f"  {label:<26} increases at {ups}/{n} steps"
          + (f", first at x = {nstr(first, 8)}" if first is not None else ""))

print()
print("  Fine scan near the first zero ordinate, where a dip would be most likely:")
print(f"{'x':>12} {'L1(x)':>26} {'increase?':>12}")
prev = None
for k in range(0, 41):
    x = mpf(13) + mpf(k) / 20     # 13.00 .. 15.00
    v = L1(x)
    inc = (prev is not None and v > prev)
    if k % 5 == 0 or inc:
        print(f"{nstr(x,8):>12} {nstr(v,16):>26} {('YES' if inc else ''):>12}")
    prev = v

print()
print("=" * 78)
print("A2 -- VERDICT")
print("=" * 78)
print("  Whatever the scan shows above is the answer; batch 13's F4 is corrected to match.")
print("  Note that the Schoenberg route is killed INDEPENDENTLY by batch 14's S2")
print("  (complete monotonicity of g(tau) = R(sqrt tau) fails at the THIRD derivative:")
print("  min (-1)^3 g''' = -3.81), so the CONCLUSION of F4 stands either way; only its")
print("  stated EVIDENCE was unsupported.")
print("=" * 78)
