"""Refined per team-lead directives:
 (1) Upper bounds on any line at ln8=2.07944 and 2pi/3=2.09440 RELATIVE to ln7
     peak height, using local-maximum enumeration + parabolic interpolation.
 (2) ln7 vs ln13 strength puzzle: Satake predicts |a_13|^2/13 vs |a_7|^2/7,
     i.e. ln13 ~ (25/13)/(1/7) = 25*7/13 = 13.46x stronger in AMPLITUDE^2 weight.
     Measure proper peak heights over LOCAL median at long span.
All line claims via local-maximum enumeration, never max-in-window.
"""
import math
import numpy as np

def eta_sq_dilated(N, d):
    c = np.zeros(N, dtype=np.float64); k = 0
    while True:
        done = True
        for kk in (k, -k) if k else (0,):
            m = d * (kk * (3 * kk - 1) // 2)
            if 0 <= m < N: c[m] += (-1) ** kk; done = False
        if k and done: break
        k += 1
    L = 1
    while L < 2 * N: L *= 2
    f = np.fft.rfft(c, L)
    return np.round(np.fft.irfft(f * f, L)[:N])

def a27(N):
    A = eta_sq_dilated(N, 3); B = eta_sq_dilated(N, 9)
    L = 1
    while L < 2 * N: L *= 2
    prod = np.round(np.fft.irfft(np.fft.rfft(A, L)*np.fft.rfft(B, L), L)[:N])
    a = np.zeros(N + 1); a[1:] = prod[:N]
    assert a[7]**2 == 1 and a[13]**2 == 25
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1); lam[1:] = a[1:] / np.sqrt(n[1:])
    return lam, a

N = int(30 * 27 * (450.0 / (2*np.pi))**2)
lam, a = a27(N)
n = np.arange(1, N + 1, dtype=np.float64)
u = n / N
w = np.where(u < 1.0, np.exp(1.0 - 1.0/np.clip(1.0 - u*u, 1e-300, None)), 0.0)
amp = (lam[1:] * w * n**(-0.5))
ln = np.log(n)
nz = amp != 0
amp = amp[nz].copy(); ln = ln[nz].copy()

t_lo, t_hi, dy = 50.0, 450.0, 0.01
ny = int((t_hi - t_lo)/dy) + 1
z = (amp * np.exp(-1j*t_lo*ln)).astype(np.complex128)
stp = np.exp(-1j*dy*ln)
F = np.empty(ny, dtype=np.complex128)
for j in range(ny):
    F[j] = z.sum(); z *= stp
absF = np.abs(F)

x = np.log(np.maximum(absF, np.percentile(absF, 1.0)))
x -= x.mean()
X = np.fft.rfft(x*np.hanning(len(x)))
P = np.abs(X)**2
om = 2*math.pi*np.fft.rfftfreq(len(x), d=dy)
dom = om[1]-om[0]
res = 2*math.pi/(t_hi-t_lo)
print("span %.0f  bin %.5f  res %.5f" % (t_hi-t_lo, dom, res))

def parab(i):
    if i<=0 or i>=len(P)-1: return om[i], P[i]
    y0,y1,y2 = P[i-1],P[i],P[i+1]; d=(y0-2*y1+y2)
    if d==0: return om[i], y1
    delta = 0.5*(y0-y2)/d
    return om[i]+delta*dom, y1 - 0.25*(y0-y2)*delta

def local_maxima(lo, hi):
    idx = np.where((om>=lo)&(om<=hi))[0]
    out=[]
    for i in idx:
        if 0<i<len(P)-1 and P[i]>=P[i-1] and P[i]>=P[i+1]:
            oi,hi_ = parab(i)
            out.append((oi, hi_, i))
    return out

def local_median(om_center, lo=0.05, hi=0.20):
    sel = (np.abs(om-om_center)>lo)&(np.abs(om-om_center)<hi)
    return np.median(P[sel])

# --- ln7 reference peak (the giant line) ---
lm7 = [m for m in local_maxima(1.90, 2.00)]
lm7.sort(key=lambda r:-r[1]); om7, h7, i7 = lm7[0]
med7 = local_median(math.log(7))
print("\n[ln7 reference]  peak om=%.5f  height=%.4g  local-median=%.4g  h/lm=%.1f"
      % (om7, h7, med7, h7/med7))

# --- (1) upper bounds at ln8 and 2pi/3, RELATIVE to ln7 peak height ---
print("\n=== (1) Line search / upper bounds at candidate frequencies ===")
print("  (local-maximum enumeration; height relative to ln7 peak h7=%.4g)" % h7)
for name, tgt in [("ln8   ", math.log(8)), ("2pi/3 ", 2*math.pi/3)]:
    # find nearest local maximum within +-1.5 bins of the target
    win = 1.5*dom
    cands = [m for m in local_maxima(tgt-0.03, tgt+0.03) if abs(m[0]-tgt) < 0.03]
    lm = local_median(tgt)
    if cands:
        cands.sort(key=lambda r: abs(r[0]-tgt))
        oi, ht, i = cands[0]
        detected = (abs(oi-tgt) < 0.003) and (ht > 6*lm)
        # upper bound = max P in a tight core +-1.5 bins vs ln7 height
        core = np.where(np.abs(om-tgt) < win)[0]
        pmax_core = P[core].max()
        print("  %s tgt=%.5f  nearest-locmax om=%.5f (d=%.4f) ht=%.4g  locmed=%.4g  ht/locmed=%.2f"
              % (name, tgt, oi, abs(oi-tgt), ht, lm, ht/lm))
        print("           core-max/ln7 = %.2e   locmed/ln7 = %.2e   -> %s"
              % (pmax_core/h7, lm/h7, "DETECTION" if detected else "NO LINE (upper bound below)"))
        print("           UPPER BOUND on a line at %s: height < %.2e x ln7  (i.e. < %.4g abs, ~background)"
              % (name.strip(), pmax_core/h7, pmax_core))
    else:
        core = np.where(np.abs(om-tgt) < win)[0]
        pmax_core = P[core].max()
        print("  %s tgt=%.5f  NO local maximum within +-0.03. locmed=%.4g" % (name, tgt, lm))
        print("           UPPER BOUND: height < %.2e x ln7" % (pmax_core/h7))

# amplitude^2/sqrt scaling context: is even a resolvable line POSSIBLE here?
# a_8=0 exactly so ln8 has literally zero Euler content; 2pi/3 has no Euler term.
print("\n  (context: a_8 = %d exactly, so ln8 Euler content is ZERO by construction;" % int(a[8]))
print("   2pi/3 is not a log-integer, no Euler term exists there.)")

# --- (2) ln7 vs ln13 strength puzzle ---
print("\n=== (2) ln7 vs ln13 strength (proper peak height over LOCAL median) ===")
for name, k in [("ln7 ", 7), ("ln13", 13)]:
    tgt = math.log(k)
    cands = [m for m in local_maxima(tgt-0.02, tgt+0.02) if abs(m[0]-tgt)<0.02]
    cands.sort(key=lambda r:-r[1]); oi,ht,i = cands[0]
    lm = local_median(tgt)
    print("  %s om=%.5f (tgt %.5f, d=%.4f)  height=%.5g  locmed=%.5g  h/locmed=%.1f"
          % (name, oi, tgt, abs(oi-tgt), ht, lm, ht/lm))
h7c = [m for m in local_maxima(math.log(7)-0.02, math.log(7)+0.02)]; h7c.sort(key=lambda r:-r[1]); H7=h7c[0][1]
h13c=[m for m in local_maxima(math.log(13)-0.02,math.log(13)+0.02)]; h13c.sort(key=lambda r:-r[1]); H13=h13c[0][1]
print("\n  measured height ratio ln13/ln7 = %.3f" % (H13/H7))
print("  Satake amplitude^2 weight (lam_p^2 = a_p^2/p):  ln7 -> 1/7=%.4f, ln13 -> 25/13=%.4f"
      % (1/7, 25/13))
print("  predicted power ratio ln13/ln7 ~ (25/13)/(1/7) = %.2f  (in the log-amp spectrum this maps"
      % ((25/13)/(1/7)))
print("   nonlinearly through log|..|, so exact ratio is not expected; SIGN of inequality is the test.)")
print("  => ln13 %s ln7 as predicted." % ("STRONGER than" if H13>H7 else "NOT stronger than (puzzle persists!)"))

# Full local-maximum table across the whole comb for the record
print("\n=== Full local-maximum enumeration, omega in [0.6, 3.0], > 20x local median ===")
allm = local_maxima(0.6, 3.0)
rows=[]
for oi,ht,i in allm:
    lm = local_median(oi)
    if lm>0 and ht/lm > 20:
        # identify
        lab=""
        for kk in range(2,70):
            if abs(math.log(kk)-oi)<0.01: lab="ln%d"%kk; break
        rows.append((oi,ht,ht/lm,lab))
rows.sort(key=lambda r:r[0])
print("  %-10s %-12s %-11s %s" % ("om","height","x_locmed","label"))
for oi,ht,r,lab in rows:
    print("  %-10.5f %-12.4g %-11.1f %s" % (oi,ht,r,lab))
