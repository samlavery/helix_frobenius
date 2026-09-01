# att569 — WHICH AXIOM DOES C1 BREAK? (pre-registered)
# C1 surgery: zeta_C1 = zeta * Q, Q = Blaschke quadruple moving the zero at
# gamma=25.010857... off-line by b0=0.15 (FE-symmetric, census-preserving).
# Windowed t-spectrum of the log-derivative readout on sigma=2:
#   S(w) = (2/T) int_0^T g(t) e^{-iwt} hann(t/T) dt.
# PREDICTIONS (registered): comb teeth (ln2, ln3, ln4) MATCH between zeta and C1
# (surgery preserves them); at the composite-non-prime-power NULLS (ln18, ln21)
# zeta shows leakage floor only, C1 shows continuous spectrum
# ~ |e^{-1.5w}(e^{0.15w}-1)| * (pair factor) ~ 1e-2.  DECISION: C1/zeta ratio at
# ln18 >= 5 => breaking axiom = SPECTRAL DISCRETENESS (the inter-comb nulls).
from mpmath import mp, mpf, mpc, exp, log, pi, zeta, cos, sin
import math, cmath, sys
mp.dps = 15
T = 300.0; dt = 0.05
N = int(T/dt)
g1 = 25.010857580145688763
b0 = 0.15
# quadruple: zeros of Q at (0.5+b0 +/- i g1), (0.5-b0 +/- i g1); poles at
# (0.5 +/- i g1) double?? NO: poles at the four points (0.5 +- i g1) with mult 2
# -- wrong. Correct FE-symmetric surgery: zeros at beta'=0.5+b0 and 1-beta'=0.5-b0
# (heights +-g1) = 4 zeros; poles at the on-line pair (0.5 +- i g1) COUNTED TWICE
# (multiplicity 2) so census is preserved 4=4.
Zs = [complex(0.5+b0, g1), complex(0.5-b0, g1), complex(0.5+b0,-g1), complex(0.5-b0,-g1)]
Ps = [complex(0.5, g1), complex(0.5, g1), complex(0.5,-g1), complex(0.5,-g1)]
def QlogD(s):
    v = 0j
    for z in Zs: v += 1.0/(s - z)
    for p in Ps: v -= 1.0/(s - p)
    return v
print("sampling zeta'/zeta on sigma=2 ...", flush=True)
gz = []
for k in range(N+1):
    t = k*dt
    s = mpc(2, t)
    val = zeta(s, derivative=1)/zeta(s)
    gz.append(complex(val))
    if k % 1200 == 0: print(f"  {k}/{N}", flush=True)
targets = [("ln2", math.log(2)), ("ln3", math.log(3)), ("ln4", math.log(4)),
           ("ln18", math.log(18)), ("ln21", math.log(21)),
           ("ctrl2.75", 2.75), ("ctrl3.05", 3.05)]
def spec(gfun_vals, w):
    acc = 0j
    for k in range(N+1):
        t = k*dt
        wnd = 0.5*(1-math.cos(2*math.pi*t/T))
        acc += gfun_vals[k]*cmath.exp(+1j*w*t)*wnd
    return acc*dt*2/T
gc1 = [gz[k] + QlogD(complex(2, k*dt)) for k in range(N+1)]
print(f"{'target':>9} {'|S_zeta|':>12} {'|S_C1|':>12} {'ratio':>8}")
res = {}
for name, w in targets:
    a = abs(spec(gz, w)); b = abs(spec(gc1, w))
    res[name] = (a, b)
    print(f"{name:>9} {a:>12.3e} {b:>12.3e} {b/a:>8.2f}")
r18 = res["ln18"][1]/res["ln18"][0]; r21 = res["ln21"][1]/res["ln21"][0]
t2 = abs(res["ln2"][1]-res["ln2"][0])/res["ln2"][0]
print(f"null-violation ratios: ln18 {r18:.1f}, ln21 {r21:.1f} (rule: >=5 CONFIRMS)")
print(f"comb-tooth ln2 relative change: {t2:.3f} (control: should be small)")
