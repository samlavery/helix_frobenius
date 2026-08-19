#!/usr/bin/env python3
"""
att246 — Suzuki §7.7 / [14] Clark-defect coordinates: the mechanism checks and
the low-strip census.

Frame (source-read 2606.09096 §7.7 + 2301.00421):
  E_xi(z) = xi(1/2−iz) + xi'(1/2−iz);  Theta = E^#/E;  identity ⟺ RH ([14] Thm 1.2).
  Defect support = C+ zeros of E_xi ⟺ solutions of xi'/xi(s) = −1 in Re s > 1/2
  (or off-line xi zeros) — a level set of the ledger-218 seat field
  S(s) = 2Re[xi'/xi]/(2σ−1).  Ledger-221 band positivity ⟹ no defect on the
  verified band.  Remaining unconditional pieces measured here:

  (1) CLARK MECHANISM CHECK: Theta(γ) = −1 exactly at on-line zeros
      (⟺ Re xi'(ρ) = 0 on the line — the derivation conj xi'(ρ) = −xi'(ρ)).
  (2) LOW-STRIP CENSUS: argument-principle count of E_xi zeros in the C+ box
      Re z ∈ [−60, 60], Im z ∈ [0.05, 3]  (⟺ σ ∈ [0.55, 3.5], |τ| ≤ 60):
      expected 0.  POSITIVE CONTROL: a C− box must count > 0 (E's zeros live
      in C− under RH — the control fails by MISSING structure if the
      instrument is blind).
  (3) LARGE-σ MARGIN: Re xi'/xi on σ = 3.5 samples (elementary-positivity
      support for the σ ≥ 3.5 piece).
"""
import mpmath as mp

mp.mp.dps = 30

def xi(s):
    return 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def L(s):
    """xi'/xi = 1/s + 1/(s-1) - (1/2)log(pi) + (1/2)psi(s/2) + zeta'/zeta."""
    return (1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2
            + mp.zeta(s, derivative=1) / mp.zeta(s))

def Lp(s):
    zp = mp.zeta(s, derivative=1) / mp.zeta(s)
    zpp = mp.zeta(s, derivative=2) / mp.zeta(s)
    return (-1 / s ** 2 - 1 / (s - 1) ** 2 + mp.polygamma(1, s / 2) / 4
            + (zpp - zp ** 2))

def E(z):
    s = mp.mpf(0.5) - 1j * z
    x = xi(s)
    return x + x * L(s)          # xi + xi'

def Elog(z):
    """E'(z)/E(z) = -i * (xi' + xi'')/(xi + xi') at s = 1/2 - iz."""
    s = mp.mpf(0.5) - 1j * z
    l, lp = L(s), Lp(s)
    # xi'' / xi = l^2 + lp ; (xi' + xi'')/(xi + xi') = (l + l^2 + lp)/(1 + l)
    return -1j * (l + l ** 2 + lp) / (1 + l)

def clark_check():
    print("== (1) CLARK MECHANISM: Theta(gamma) = -1 at on-line zeros ==")
    for n in [1, 2, 3, 5, 10]:
        g = mp.im(mp.zetazero(n))
        s = mp.mpf(0.5) - 1j * g
        xp = xi(s) * L(s)        # xi'(rho); xi(rho) ~ 0 so E ~ xi'
        Ev = E(g)
        theta = mp.conj(Ev) / Ev
        print(f"  gamma_{n} = {mp.nstr(g, 12)}: Re xi'(rho) = {mp.nstr(mp.re(xp), 3)}"
              f"   Theta = {mp.nstr(theta, 10)}   |Theta+1| = {mp.nstr(abs(theta+1), 3)}")

def winding(box, npts=240, label=""):
    (x0, x1, y0, y1) = box
    corners = [mp.mpc(x0, y0), mp.mpc(x1, y0), mp.mpc(x1, y1), mp.mpc(x0, y1)]
    total = mp.mpc(0)
    for k in range(4):
        a, b = corners[k], corners[(k + 1) % 4]
        f = lambda t: Elog(a + (b - a) * t) * (b - a)
        total += mp.quad(f, [0, 1], maxdegree=8)
    N = total / (2j * mp.pi)
    print(f"  box {label} Re[{x0},{x1}] x Im[{y0},{y1}]: winding = {mp.nstr(N, 6)}"
          f"  -> count = {int(mp.nint(mp.re(N)))}")
    return int(mp.nint(mp.re(N)))

def census():
    print("== (2) E_xi ZERO CENSUS (argument principle) ==")
    n_plus = 0
    for x0 in range(-60, 60, 20):
        n_plus += winding((x0, x0 + 20, 0.05, 3.0), label="C+")
    print(f"  TOTAL C+ count on [-60,60] x [0.05, 3]: {n_plus}   (defect support: expected 0)")
    print("  positive control (C-):")
    n_minus = winding((0, 30, -1.5, -0.05), label="C-")
    print(f"  control count = {n_minus}  (must be > 0 or the instrument is blind)")

def large_sigma():
    print("== (3) LARGE-SIGMA MARGIN: Re xi'/xi at sigma = 3.5 ==")
    for tau in [0, 10, 30, 60, 100]:
        v = L(mp.mpc(3.5, tau))
        print(f"  s = 3.5 + {tau}i: Re xi'/xi = {mp.nstr(mp.re(v), 8)}")

if __name__ == "__main__":
    clark_check()
    census()
    large_sigma()
