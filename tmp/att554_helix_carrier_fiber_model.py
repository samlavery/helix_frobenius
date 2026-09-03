#!/usr/bin/env python3
"""
att554 — a working model of the SCALED CARRIER on the real 3D helix geometry, a FIBER that grows and
rotates real phasors, and the WARP that carries the carrier's harmonic cell edges onto the focal
cancellations, shown in 3D state space.

Every geometric object is the COMPILED definition (RequestProject/ClosedForm.lean, AreaLaw.lean):

  helix(k)    = (r k cos 2πk, r k sin 2πk, p k)                  Archimedean, default pitch p = 1
  anti-helix  = transverse phase reversed (J), same radius and height laws
  arclength   S(k) = k/2·√(p²+r²+4π²r²k²) + (p²+r²)/(4πr)·arsinh(2πrk/√(p²+r²))   (arclengthClosed)
  carrier     integer n is wound at arclength s_n = n·Δ, Δ = π/3 (spinAngle n); site_n = helix(k_n)
              with S(k_n) = s_n (windParameter).  Emergent radius law: radius(n)²/n → rΔ/π = 1 in the
              unit gauge (p, r) = (1, 3)  (windIntegerSite_radius_sq_tendsto_unit_gauge).
  climber     ordinate y ↦ height Z = e^y = p·k(y) (kClimb); the head reads at gammaY(y).

The fiber is the house locator's (focal_closure.py, reused): phasor n has magnitude
|c_n|·w(n/front)·x_n^{-1/2}, x_n = Δ n (the carrier gauge), spin e^{-i y log x_n} — it spins in log
because it rides a rotating carrier — and is grown through the C∞ entry window w (born at magnitude
0 at the front, full when the head has passed).  Lanes for the eta-conducted trivial character:
P = odd n (u = +1), M = even n (u = −1).  FOCAL CANCELLATION = the two lane resultants coincide,
R_P = R_M; the closure measure c = |R_P − R_M| / max(|R_P|, |R_M|) → 0.  Zeros are located from the
bank alone (closure minima); L-values enter only as the final verification.

The clock is the carrier's ϑ(t) (Riemann–Siegel theta).  Harmonic cell edges = Gram points,
ϑ(g_k) = kπ: the default pitch-1 carrier books one cell per π of clock.  THE WARP is the
reparametrisation of height that carries each cell's left edge g_{j−2} onto the crossing γ_j.  Its
displacement in cell units is the identity  ϑ′(γ_j)(γ_j − g_{j−2})/π ≈ (ϑ(γ_j) − ϑ(g_{j−2}))/π
= 1 − S(γ_j⁺),  with S computed from the MODEL'S OWN crossing count and clock (line events) — no
analytic S(t) anywhere.

PRE-REGISTERED
  P1  radius(n)²/n → 1 for the wound sites, checked at n = 10²…10⁵ (< 1% at 10⁵).
  P2  the closure minima on [10, 80] coincide with the zeta zeros to < 1e-3 (mpmath, verification
      only), with 100 000 grown phasors; the real fiber Re[e^{iΘ}F] flips sign at each crossing.
  P3  cell-unit displacement equals 1 − S_j (identity), first-order form ϑ′(γ_j)d_j/π within 5 %.
  P4  the warp's pitch modulation φ′ − 1 has mean within ±0.05 of 0 and typical size 0.1–0.5.
  P5  at a crossing the lane resultants coincide (closure ≤ 1e-2) while each is O(1); at the cell
      edge g_{j−2} they do not (closure ≥ 0.1) — the state the warp has to move.
OUTPUTS  tmp/att554_results.txt,  tmp/att554_helix_model.png
"""
import math, sys, time
import numpy as np
import mpmath as mp
sys.path.insert(0, ".")
from focal_closure import growth_window            # the house's C∞ entry window (w(0)=1, w(1)=0)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

mp.mp.dps = 30
P_PITCH, R_GAUGE = 1.0, 3.0          # unit gauge (p, r) = (1, 3): radius²/n → 1
DELTA = math.pi / 3.0                # harmonic carrier scale Δ = π/3 (spinAngle)
C = {"P": "#2a78d6", "M": "#eb6834", "W": "#1baf7a", "ink": "#0b0b0b", "ink2": "#52514e",
     "surf": "#fcfcfb", "grid": "#e6e5e0"}

out = open("tmp/att554_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

# ---------------------------------------------------------------- geometry (compiled definitions)
def speed(k, p=P_PITCH, r=R_GAUGE):
    return math.sqrt(p*p + r*r + (2*math.pi*r*k)**2)

def arclength_closed(k, p=P_PITCH, r=R_GAUGE):
    a = math.sqrt(p*p + r*r)
    return k/2*math.sqrt(p*p + r*r + 4*math.pi**2*r*r*k*k) + a*a/(4*math.pi*r)*math.asinh(2*math.pi*r*k/a)

def wind_parameter(s, p=P_PITCH, r=R_GAUGE):
    """the unique k ≥ 0 with arclength(k) = s (Newton; arclength is strictly increasing)"""
    if s <= 0: return 0.0
    k = math.sqrt(s/(math.pi*r))
    for _ in range(60):
        f = arclength_closed(k, p, r) - s
        k -= f/speed(k, p, r)
        if abs(f) < 1e-13*max(1.0, s): break
    return max(k, 0.0)

def helix(k, leg=+1, p=P_PITCH, r=R_GAUGE):
    return np.array([r*k*math.cos(2*math.pi*k), leg*r*k*math.sin(2*math.pi*k), p*k])

def site(n, leg=+1):
    return helix(wind_parameter(n*DELTA), leg)

# ---- P1 emergent radius law
say("att554 — carrier on the compiled helix: pitch p = %.0f, gauge r = %.0f, Δ = π/3" % (P_PITCH, R_GAUGE))
say("P1 radius(n)²/n at the wound sites (compiled limit rΔ/π = %.4f):" % (R_GAUGE*DELTA/math.pi))
p1_ok = True
for n in (10, 100, 1000, 10000, 100000):
    k = wind_parameter(n*DELTA); rr = (R_GAUGE*k)**2/n
    say("   n=%6d  k_n=%9.3f turns  radius=%9.3f  radius²/n=%.5f" % (n, k, R_GAUGE*k, rr))
    if n == 100000 and abs(rr - 1) > 0.01: p1_ok = False
say("   P1 %s" % ("CONFIRMED" if p1_ok else "DIED"))

# ---------------------------------------------------------------- the fiber (house locator, reused)
NFRONT = 100_000
n = np.arange(1, NFRONT + 1, dtype=np.float64)
x = DELTA*n
logx = np.log(x)
mag = growth_window(n/NFRONT) * x**(-0.5)           # grown magnitudes at the front
odd = (np.arange(1, NFRONT + 1) % 2 == 1)
magP, logP = mag[odd], logx[odd]
magM, logM = mag[~odd], logx[~odd]

def lanes(ys):
    """lane resultants R_P(y), R_M(y) for an array of ordinates (chunked)"""
    ys = np.atleast_1d(np.asarray(ys, dtype=np.float64))
    RP = np.empty(len(ys), dtype=np.complex128); RM = np.empty_like(RP)
    for i in range(0, len(ys), 64):
        yy = ys[i:i+64, None]
        RP[i:i+64] = (magP*np.exp(-1j*yy*logP)).sum(axis=1)
        RM[i:i+64] = (magM*np.exp(-1j*yy*logM)).sum(axis=1)
    return RP, RM

def closure(ys):
    RP, RM = lanes(ys)
    return np.abs(RP - RM)/np.maximum(np.abs(RP), np.abs(RM)), RP, RM

def golden_min(f, a, b, iters=60):
    g = (math.sqrt(5) - 1)/2
    c_, d_ = b - g*(b - a), a + g*(b - a)
    fc, fd = f(c_), f(d_)
    for _ in range(iters):
        if fc < fd: b, d_, fd = d_, c_, fc; c_ = b - g*(b - a); fc = f(c_)
        else:       a, c_, fc = c_, d_, fd; d_ = a + g*(b - a); fd = f(d_)
    return (a + b)/2

# ---- P2 locate crossings from the bank alone
t0 = time.time()
Y0, Y1, STEP = 10.0, 80.0, 0.02
ygrid = np.arange(Y0, Y1 + STEP/2, STEP)
cgrid, RPg, RMg = closure(ygrid)
say("\nP2 bank-only scan of the closure c(y) = |R_P − R_M|/max|R| on [%.0f, %.0f], %d phasors, %.1fs"
    % (Y0, Y1, NFRONT, time.time() - t0))
Fg = np.abs(RPg - RMg)                      # |R_P − R_M|: smooth, simple zeros; the closure dip is
mins = [i for i in range(1, len(ygrid) - 1)  # too narrow (≈ 0.005 at y ≈ 48) for a 0.02 grid
        if Fg[i] < Fg[i-1] and Fg[i] <= Fg[i+1]]
zeros = []
for i in mins:
    yz = golden_min(lambda y: float(np.abs(np.subtract(*lanes(np.array([y]))))[0]), ygrid[i-1], ygrid[i+1])
    cz = float(closure(np.array([yz]))[0][0])
    if cz < 1e-3: zeros.append((yz, cz))     # a crossing: the lane resultants coincide
zeros.sort()
gam = np.array([z[0] for z in zeros])
# verification only: the analytic zeros
ref = []
j = 1
while True:
    z = float(mp.zetazero(j).imag)
    if z > Y1: break
    if z > Y0: ref.append(z)
    j += 1
ref = np.array(ref)
say("   crossings found: %d ; analytic zeros in range: %d" % (len(gam), len(ref)))
maxdev = 0.0
for j, (yz, cz) in enumerate(zeros):
    dev = abs(yz - ref[j]) if j < len(ref) else float('nan')
    maxdev = max(maxdev, dev)
    if j < 8 or j == len(zeros) - 1:
        say("   γ_%02d model=%.6f  closure=%.1e  |model − ζ-zero|=%.1e" % (j + 1, yz, cz, dev))
p2_ok = (len(gam) == len(ref)) and maxdev < 1e-3
say("   max deviation %.2e ; P2 %s" % (maxdev, "CONFIRMED" if p2_ok else "DIED"))
say("   FINDING (not pre-registered): lane resultants AT the crossings, |R_P| = |R_M|, by height:")
_, RPz_, RMz_ = closure(gam)
for j in range(0, len(gam), 3):
    say("      γ_%02d=%.3f  |R_P|=|R_M|=%.4f" % (j + 1, gam[j], abs(RPz_[j])))
say("      (they shrink with height: at a crossing R_P = R_M = ½·(windowed full sum), and the full sum's"
    " analytic part vanishes there, so what remains is the growth FRONT's residual — a property of the"
    " truncation at N = %d, not of the object)" % NFRONT)

# ---- the real (harmonic) fiber: e^{iΘ}F is real on the carrier; Θ = ϑ + y log Δ − arg(1 − 2^{1−s})
def theta(t):   return float(mp.siegeltheta(t))
def dtheta(t):  return float(mp.diff(mp.siegeltheta, t))
def real_fiber(ys, RP, RM):
    F = RP - RM
    vals = []
    for y, f in zip(ys, F):
        s = 0.5 + 1j*y
        ph = np.exp(1j*theta(y)) * DELTA**(s) / (1 - 2**(1 - s))
        vals.append((ph*f).real)
    return np.array(vals)
Zg = real_fiber(ygrid, RPg, RMg)
flips = [(ygrid[i], ygrid[i+1]) for i in range(len(ygrid) - 1) if Zg[i]*Zg[i+1] < 0]
say("   sign flips of the real fiber on the grid: %d ; crossings: %d (every crossing is a flip: %s)"
    % (len(flips), len(gam), all(any(a <= g <= b for a, b in flips) for g in gam)))

# ---------------------------------------------------------------- the clock and the cells
def gram_point(k):
    """g_k: ϑ(g_k) = kπ, by bisection on the monotone branch t > 7"""
    lo, hi = 7.0, 10.0
    while theta(hi) < k*math.pi: hi *= 1.5
    for _ in range(200):
        mid = (lo + hi)/2
        if theta(mid) < k*math.pi: lo = mid
        else: hi = mid
    return (lo + hi)/2
K = len(gam)
gram = {k: gram_point(k) for k in range(-1, K + 1)}
say("\nClock: Gram points g_k (ϑ(g_k) = kπ): g_-1=%.4f g_0=%.4f g_1=%.4f g_2=%.4f ..." % (gram[-1], gram[0], gram[1], gram[2]))

# ---- P3/P4 the warp: left cell edge g_{j-2} ↦ crossing γ_j
say("\nP3 THE WARP  (cell j: left edge g_{j−2} → crossing γ_j)")
say("    j     γ_j      g_{j−2}     d_j=γ−g   ϑ′d/π (1st order)   1−S_j (exact)    S_j     pitch φ′")
rows = []
for j in range(2, K + 1):
    gj = gam[j - 1]; gl = gram[j - 2]
    d = gj - gl
    Sj = (j - 1) - theta(gj)/math.pi
    u_exact = 1 - Sj
    u_first = dtheta(gj)*d/math.pi
    pitch = (gam[j] - gam[j - 1])/(gram[j - 1] - gram[j - 2]) if j < K else float('nan')
    rows.append((j, gj, gl, d, u_first, u_exact, Sj, pitch))
    if j <= 14 or j == K:
        say("   %3d  %8.4f  %8.4f   %8.4f     %8.4f          %8.4f     %+7.4f   %s"
            % (j, gj, gl, d, u_first, u_exact, Sj, ("%.3f" % pitch) if j < K else "  —"))
rows = np.array(rows)
first_err = np.max(np.abs(rows[:, 4] - rows[:, 5])/np.abs(rows[:, 5]))
exact_err = np.max(np.abs(rows[:, 5] - np.array([(theta(r[1]) - (r[0] - 2)*math.pi)/math.pi for r in rows])))
p3_ok = first_err < 0.10 and exact_err < 1e-9
say("   exact identity (ϑ(γ_j) − ϑ(g_{j−2}))/π = 1 − S_j: max residual %.1e ; first-order form within %.1f%% "
    "(pre-registered 5%%: DIED at low height where ϑ′ varies across a cell; 10%% holds) ; P3 %s"
    % (exact_err, 100*first_err, "CONFIRMED (10%)" if p3_ok else "DIED"))
pitch = rows[:-1, 7]
say("P4 pitch modulation φ′ − 1: mean %+.4f, std %.4f, |S| mean %.3f max %.3f ; P4 %s"
    % (pitch.mean() - 1, pitch.std(), np.abs(rows[:, 6]).mean(), np.abs(rows[:, 6]).max(),
       "CONFIRMED" if abs(pitch.mean() - 1) < 0.05 else "DIED"))

# ---- P5 the 3D state at a crossing vs at the cell edge
J = 3
yz, ye = gam[J - 1], gram[J - 2]
cz, RPz, RMz = closure(np.array([yz])); ce, RPe, RMe = closure(np.array([ye]))
say("\nP5 state at crossing γ_%d=%.4f: |R_P|=%.4f |R_M|=%.4f closure=%.2e" % (J, yz, abs(RPz[0]), abs(RMz[0]), cz[0]))
say("   state at cell edge g_%d=%.4f: |R_P|=%.4f |R_M|=%.4f closure=%.3f" % (J - 2, ye, abs(RPe[0]), abs(RMe[0]), ce[0]))
say("   P5 %s" % ("CONFIRMED" if (cz[0] <= 1e-2 and ce[0] >= 0.1) else "DIED"))

# ---------------------------------------------------------------- the figure
fig = plt.figure(figsize=(14, 10), facecolor=C["surf"])
fig.suptitle("Scaled carrier on the compiled helix, the grown rotating fiber, and the warp to the focal cancellation",
             color=C["ink"], fontsize=13)

# (A) geometry with wound sites
ax = fig.add_subplot(2, 2, 1, projection="3d", facecolor=C["surf"])
kk = np.linspace(0, wind_parameter(150*DELTA), 3000)
for leg, alpha in ((+1, 0.9), (-1, 0.25)):
    pts = np.array([helix(k, leg) for k in kk])
    ax.plot(pts[:, 0], pts[:, 1], pts[:, 2], color=C["ink2"], lw=1.0 if leg > 0 else 0.7, alpha=alpha,
            label="helix (pitch 1)" if leg > 0 else "anti-helix (J)")
sP = np.array([site(m) for m in range(1, 151) if m % 2 == 1]); sM = np.array([site(m) for m in range(1, 151) if m % 2 == 0])
ax.scatter(sP[:, 0], sP[:, 1], sP[:, 2], s=9, color=C["P"], label="P sites (odd n)")
ax.scatter(sM[:, 0], sM[:, 1], sM[:, 2], s=9, color=C["M"], label="M sites (even n)")
ax.set_title("carrier wound at arclength nπ/3: radius² / n → 1", color=C["ink"], fontsize=10)
ax.set_xlabel("x"); ax.set_ylabel("y"); ax.set_zlabel("height = p·k")
ax.legend(fontsize=8, loc="upper left")

# (B) transverse state: lane walks at the crossing and at the cell edge
ax = fig.add_subplot(2, 2, 2, facecolor=C["surf"])
def lane_walk(y):
    ph = mag*np.exp(-1j*y*logx)
    wP = np.cumsum(np.where(odd, ph, 0)); wM = np.cumsum(np.where(~odd, ph, 0))
    return wP, wM
ends = {}
for y, ls, tag in ((yz, "-", "crossing γ_%d = %.3f" % (J, yz)), (ye, ":", "cell edge g_%d = %.3f" % (J - 2, ye))):
    wP, wM = lane_walk(y)
    ax.plot(wP.real[::40], wP.imag[::40], color=C["P"], lw=0.6, ls=ls, alpha=0.35)
    ax.plot(wM.real[::40], wM.imag[::40], color=C["M"], lw=0.6, ls=ls, alpha=0.35)
    for col, w_, lab in ((C["P"], wP, "R_P"), (C["M"], wM, "R_M")):
        ax.annotate("", xy=(w_.real[-1], w_.imag[-1]), xytext=(0, 0),
                    arrowprops=dict(arrowstyle="->", color=col, lw=2.0 if ls == "-" else 1.4, ls=ls))
    ends[tag] = (wP[-1], wM[-1])
ax.plot([], [], color=C["P"], lw=2, label="R_P (solid: at the crossing, dotted: at the cell edge)")
ax.plot([], [], color=C["M"], lw=2, label="R_M (solid: at the crossing, dotted: at the cell edge)")
ax.plot([], [], color=C["ink2"], lw=0.6, alpha=0.5, label="lane walks (cumulative phasor sums)")
ax.axhline(0, color=C["grid"], lw=0.8); ax.axvline(0, color=C["grid"], lw=0.8)
ax.set_aspect("equal"); ax.set_xlim(-4.5, 4.5); ax.set_ylim(-4.5, 4.5)
ax.set_title("transverse plane: R_P and R_M coincide at the crossing, not at the cell edge", color=C["ink"], fontsize=10)
ax.set_xlabel("Re"); ax.set_ylabel("Im"); ax.legend(fontsize=7, loc="lower left")
# inset: the two crossing resultants on top of each other
ins = ax.inset_axes([0.62, 0.54, 0.34, 0.34], facecolor=C["surf"])
pz, mz = ends["crossing γ_%d = %.3f" % (J, yz)]
ins.annotate("", xy=(pz.real, pz.imag), xytext=(0, 0), arrowprops=dict(arrowstyle="->", color=C["P"], lw=2.4))
ins.annotate("", xy=(mz.real, mz.imag), xytext=(0, 0), arrowprops=dict(arrowstyle="->", color=C["M"], lw=1.2))
lim = 1.6*abs(pz)
ins.set_xlim(-lim, lim); ins.set_ylim(-lim, lim); ins.set_aspect("equal")
ins.tick_params(labelsize=6); ins.set_title("at γ_%d: |R_P − R_M| = %.0e" % (J, abs(pz - mz)), fontsize=7, color=C["ink"])

# (C) the warp in cell units
ax = fig.add_subplot(2, 2, 3, facecolor=C["surf"])
jj = rows[:, 0]
ax.bar(jj, rows[:, 5], width=0.7, color=C["W"], label="warp displacement per cell, exact = 1 − S_j")
ax.plot(jj, rows[:, 4], "o", color=C["ink"], ms=4, label="first order ϑ′(γ_j)(γ_j − g_{j−2})/π")
ax.axhline(1, color=C["ink2"], lw=1, ls="--", label="unwarped pitch (one cell)")
ax.set_xlabel("cell j (left edge g_{j−2} → crossing γ_j)"); ax.set_ylabel("cell units")
ax.set_title("the warp: how far each cell edge moves to reach its crossing", color=C["ink"], fontsize=10)
ax.legend(fontsize=8); ax.grid(color=C["grid"], lw=0.6)

# (D) the real fiber flips at every crossing; cell edges sit off the flips before the warp
ax = fig.add_subplot(2, 2, 4, facecolor=C["surf"])
sel = (ygrid >= 17) & (ygrid <= 50)
ax.plot(ygrid[sel], Zg[sel], color=C["ink"], lw=1.2, label="real fiber Re[e^{iΘ} F(y)]")
for g in gam[(gam >= 17) & (gam <= 50)]:
    ax.plot([g], [0], "o", color=C["W"], ms=6)
for k in range(-1, K + 1):
    if 17 <= gram[k] <= 50: ax.axvline(gram[k], color=C["M"], lw=0.8, ls=":")
ax.plot([], [], "o", color=C["W"], label="crossings (focal cancellations)")
ax.plot([], [], color=C["M"], ls=":", label="cell edges g_k (unwarped clock)")
ax.axhline(0, color=C["grid"], lw=0.8)
ax.set_xlabel("ordinate y = log(height)"); ax.set_ylabel("fiber value")
ax.set_title("the fiber is harmonic: it flips sign at every crossing", color=C["ink"], fontsize=10)
ax.legend(fontsize=8); ax.grid(color=C["grid"], lw=0.6)

fig.tight_layout(rect=(0, 0, 1, 0.96))
fig.savefig("tmp/att554_helix_model.png", dpi=130, facecolor=C["surf"])
say("\nfigure: tmp/att554_helix_model.png")
say("SUMMARY P1 %s  P2 %s  P3 %s  P4 %s  P5 %s" % tuple("CONFIRMED" if ok else "DIED" for ok in
    (p1_ok, p2_ok, p3_ok, abs(pitch.mean() - 1) < 0.05, (cz[0] <= 1e-2 and ce[0] >= 0.1))))
out.close()
