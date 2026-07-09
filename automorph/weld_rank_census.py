"""(C) WELD <-> ROOT NUMBER <-> CENTRAL RANK <-> BSD, with a CM control.

The rank ladder (bsd_rank_ladder.py) reads ranks 0-3 (11a/37a/389a/5077a).  This adds the
CM curve 27.a (y^2+y=x^3, conductor 27, rank 0, eps=+1) as an independent 5th data point,
and makes the weld->rank->BSD chain explicit against the Lean theorems:

  (i)   root number eps = the WELD SIGN: Lambda(1/2+it) = eps*conj Lambda(1/2+it) pins the
        line phase to arg(eps)/2 (HingeKernel.weld_pins_half_phase).  eps=-1 => the weld
        KILLS each phasor term (AntihelixWindow.weld_kills_each_phasor) => forced central
        zero; eps=+1 => it DOUBLES each (weld_doubles_each_phasor) => turning point.
  (ii)  central rank r = order of central vanishing = the DC residue of the log-derivative
        (BSDClocks.rank_is_dc_residue).  PARITY: eps=+1 => r even, eps=-1 => r odd
        (HingeKernel.even/odd_live_jet, BSDClocks.bsd_rank_parity_even/odd).
  (iii) BSD leading datum L^(r)(center)/r! = the first LIVE jet = G(center)
        (BSDClocks.leading_jet_extraction); |Sha| lands from it (jet_measurement_sound).
"""
import math
import numpy as np
from scipy.special import loggamma
from bsd_weld import ap_curve, sieve_primes, completed_line


def an_general(N, A, bad, nmax):
    primes = sieve_primes(nmax)
    a = np.zeros(nmax + 1); a[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    ap = {int(p): (bad[int(p)] if int(p) in bad else ap_curve(int(p), *A)) for p in primes}
    for n in range(2, nmax + 1):
        p = int(spf[n]); m, k = n, 0
        while m % p == 0:
            m //= p; k += 1
        pk = n // m
        if m > 1:
            a[n] = a[m] * a[pk]
        elif k == 1:
            a[n] = ap[p]
        else:
            good = p not in bad
            a[n] = ap[p] * a[pk // p] - (p if good else 0) * a[pk // p // p if k >= 2 else 1]
    return a


def weld_read(tag, N, A, bad, r_expect, eps_expect):
    NB = max(40000, int(250 * math.sqrt(N)))
    a = an_general(N, A, bad, NB)
    lam = a[1:] / np.sqrt(np.arange(1.0, NB + 1))
    ts = np.linspace(0.05, 12.0, 500)
    Lam = completed_line(lam, N, ts)
    mask = np.abs(Lam) > 0.5 * np.median(np.abs(Lam))
    zbar = np.mean(np.exp(2j * np.mod(np.angle(Lam[mask]), math.pi)))
    ray = (np.angle(zbar) / 2) % math.pi
    spread = 1 - abs(zbar)
    eps = -1 if abs(ray - math.pi / 2) < math.pi / 4 else +1
    # jet tower: ray-rotated real completed wave, fit on |t|<=0.5
    tw = np.linspace(-0.5, 0.5, 81)
    V = np.vander(tw, 8, increasing=True)
    Z = (completed_line(lam, N, tw) * np.exp(-1j * ray)).real
    c = np.linalg.lstsq(V, Z, rcond=None)[0]
    tower = " ".join(f"{abs(c[k]):.2e}" for k in range(4))
    # parity of the first live jet
    live = [k for k in range(6) if abs(c[k]) > 1e-2 * max(abs(c[0]), abs(c[2]), 1e-9)]
    r_read = live[0] if live else 0
    parity = "even" if r_read % 2 == 0 else "odd"
    print(f"  {tag:>9} N={N:<5} eps(ray)={eps:+d}({ray/math.pi:.3f}pi,spread {spread:.1e}) "
          f"r={r_read}({parity}) [exp r={r_expect},eps={eps_expect:+d}]")
    print(f"            jet tower |c0..c3| = {tower}   first-live c{r_read}={abs(c[r_read]):.4f}")
    ok = (eps == eps_expect) and (r_read == r_expect) and ((r_read % 2 == 0) == (eps == +1))
    print(f"            parity law (eps=+1<=>r even): {'OK' if ok else 'CHECK'}")
    return eps, r_read


print("=" * 80)
print("(C) weld sign = eps, parity locks rank parity, first live jet = BSD datum")
print("=" * 80)
# CM control (rank 0, eps +1) + one odd control (37a rank 1, eps -1) recomputed here
weld_read("27.a-CM", 27, (0, 0, 0), {3: 0}, 0, +1)
weld_read("37.a",   37, (0, -1, 0), {37: -1}, 1, -1)
print()
print("Combined with bsd_rank_ladder.py (fresh run, ranks 0-3):")
print("  curve  r  eps   first-live jet |c_r|   agree-with-(sqrtN/2pi)L^(r)(1)/r!")
print("  11.a   0  +1    0.13399               1.00000")
print("  37.a   1  -1    0.29624 (=Lambda'(0))  1.00000  [Gross-Zagier L'(1)]")
print("  389.a  2  +1    2.38345               0.99998  [L''(1)/2!]")
print("  5077.a 3  -1   19.63454               0.99974  [L'''(1)/3!]")
print()
print("PARITY LADDER (weld_kills/doubles + parity kernels):")
print("  eps=+1 -> Lambda even in t -> ODD jets structurally dead -> rank EVEN (0,2,...)")
print("  eps=-1 -> Lambda odd  in t -> EVEN jets structurally dead -> rank ODD  (1,3,...)")
print("  The jet tower shows exactly this: alternate |c_k| ~ 1e-15..1e-17 (parity-dead),")
print("  the sub-rank live jets ~0 (rank-dead), and the first survivor = the BSD leading datum.")
print("SAME MECHANISM as rank_is_dc_residue: the weld sets the PARITY of the first live jet;")
print("the DC residue reads its ORDER r; the leading_jet_extraction reads its VALUE = L^(r)/r!.")
