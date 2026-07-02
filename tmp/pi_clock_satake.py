"""27.a Satake two-clock weight-law table at span 400, normalized to ln4.
Primes {2,5,7,11,13,17,19,23,29,31,37,43,61,67}; p=2 tower k<=4 (ln2 dead,
ln4 alive, ln8 dead, ln16 = last unverified tooth, |s_4|/4 * 16^-1/2 = 0.125),
k<=2 elsewhere. Local-maximum enumeration + parabolic interpolation throughout.
A(p,k) = |s_k|/k * p^-k/2 ; s_0=2, s_1=lam(p), s_k = lam*s_{k-1} - s_{k-2}.
lam(p) = a_p / sqrt(p) taken from the exact coefficient array (inert p: a_p=0
=> lam=0 => s_2=-2 EXACTLY: CM gives algebraically exact angles).
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
ampc = amp[nz].copy(); lnc = ln[nz].copy()

t_lo, t_hi, dy = 50.0, 450.0, 0.01
ny = int((t_hi - t_lo)/dy) + 1
z = (ampc * np.exp(-1j*t_lo*lnc)).astype(np.complex128)
stp = np.exp(-1j*dy*lnc)
F = np.empty(ny, dtype=np.complex128)
for j in range(ny):
    F[j] = z.sum(); z *= stp
absF = np.abs(F)

x = np.log(np.maximum(absF, np.percentile(absF, 1.0))); x -= x.mean()
P = np.abs(np.fft.rfft(x*np.hanning(len(x))))**2
om = 2*math.pi*np.fft.rfftfreq(len(x), d=dy)
dom = om[1]-om[0]
res = 2*math.pi/(t_hi-t_lo)

def parab(i):
    if i<=0 or i>=len(P)-1: return om[i], P[i]
    y0,y1,y2 = P[i-1],P[i],P[i+1]; d=(y0-2*y1+y2)
    if d==0: return om[i], y1
    delta = 0.5*(y0-y2)/d
    return om[i]+delta*dom, y1 - 0.25*(y0-y2)*delta

def local_median(omc, lo=0.05, hi=0.20):
    sel = (np.abs(om-omc)>lo)&(np.abs(om-omc)<hi)
    return np.median(P[sel])

def measure(target):
    """Nearest local maximum to target within +-0.02; return
    (om_i, height, h/locmed, sqrt(pow), locmed, detected, corepow)."""
    idx = np.where((om>=target-0.025)&(om<=target+0.025))[0]
    cands=[]
    for i in idx:
        if 0<i<len(P)-1 and P[i]>=P[i-1] and P[i]>=P[i+1]:
            oi,h = parab(i); cands.append((oi,h,i))
    lm = local_median(target)
    core = np.where(np.abs(om-target)<1.5*dom)[0]
    corepow = P[core].max()
    if not cands:
        return (target, 0.0, 0.0, math.sqrt(corepow), lm, False, corepow)
    cands.sort(key=lambda r: abs(r[0]-target))
    oi,h,i = cands[0]
    hlm = h/lm if lm>0 else 0.0
    detected = (abs(oi-target)<0.006) and (hlm>100)
    return (oi, h, hlm, math.sqrt(max(h,0.0)), lm, detected, corepow)

# Satake amplitude
def satake(p, k, lamp):
    s = [2.0, lamp]
    for j in range(2, k+1):
        s.append(lamp*s[-1] - s[-2])
    sk = s[k]
    A = abs(sk)/k * p**(-k/2.0)
    return sk, A

primes = [2,5,7,11,13,17,19,23,29,31,37,43,61,67]
lines = []  # (label, p, k, n=p^k)
for p in primes:
    kmax = 4 if p==2 else 2
    for k in range(1, kmax+1):
        lines.append((f"ln{p**k}", p, k, p**k))

# reference line = ln4
ref_p, ref_k = 2, 2
lam4 = float(lam[2]) if False else float(a[2]/math.sqrt(2))  # lam(2)=a_2/sqrt2, a_2=0 -> 0
# but s for p=2: lam(2)=0 -> s_1=0, s_2=-2, s_3=0, s_4=2 (alternating tower)
_, A_ref = satake(ref_p, ref_k, float(a[2]/math.sqrt(2)))
ref_meas = measure(math.log(4))
ref_sqrtpow = ref_meas[3]

rows=[]
print("== 27.a Satake weight-law build ==")
print("N=%d span %.0f dy=%.3f res=%.4f bin=%.5f  ref=ln4 (A_ref=%.5f)" % (N,t_hi-t_lo,dy,res,dom,A_ref))
for lbl,p,k,nn in lines:
    lamp = float(a[p]/math.sqrt(p))
    sk, A = satake(p,k,lamp)
    m = measure(math.log(nn))
    oi,h,hlm,sqrtpow,lm,det,corepow = m
    meas_rel = sqrtpow/ref_sqrtpow
    pred_rel = A/A_ref
    mp = meas_rel/pred_rel if pred_rel>0 else float('nan')
    rows.append(dict(lbl=lbl,p=p,k=k,n=nn,om=math.log(nn),lamp=lamp,sk=sk,A=A,
                     oi=oi,h=h,hlm=hlm,sqrtpow=sqrtpow,lm=lm,det=det,corepow=corepow,
                     meas_rel=meas_rel,pred_rel=pred_rel,mp=mp))

# print prime-clock table
print("\nPRIME-CLOCK  (local-max enumeration + parabolic)")
print("  %-6s %-3s %-2s %-2s %-8s %-9s %-8s %-9s %-9s" % ("line","p","k","n","omega","h/locmed","det","sqrt(pow)","om_interp"))
for r in rows:
    dtag = "YES" if r['det'] else ("bound" if r['h']==0 or r['hlm']<100 else ".")
    print("  %-6s %-3d %-2d %-2d %-8.4f %-9.1f %-8s %-9.3e %-9.5f" %
          (r['lbl'],r['p'],r['k'],r['n'],r['om'],r['hlm'],dtag,r['sqrtpow'],r['oi']))

print("\nSATAKE WEIGHT LAW  (rel to ln4)")
print("  %-6s %-8s %-9s %-10s %-10s %-9s %s" % ("line","lam(p)","s_k","meas/ln4","pred/ln4","meas/pred","det"))
for r in rows:
    dtag = "YES" if r['det'] else "bound"
    print("  %-6s %-8.4f %-9.4f %-10.4f %-10.4f %-9.3f %s" %
          (r['lbl'],r['lamp'],r['sk'],r['meas_rel'],r['pred_rel'],r['mp'],dtag))

# ln16 spotlight
r16 = next(r for r in rows if r['lbl']=='ln16')
print("\n== ln16 SPOTLIGHT (last unverified tooth of the 2-tower) ==")
print("  predicted A(2,4) = |s_4|/4 * 16^-1/2 = |%.4f|/4 * 0.25 = %.5f  (=0.125 as spec)" % (r16['sk'], r16['A']))
print("  pred/ln4 = %.5f" % r16['pred_rel'])
print("  measured: nearest local-max om=%.5f (d=%.4f from ln16=%.5f), h/locmed=%.1f, sqrt(pow)=%.3e"
      % (r16['oi'], abs(r16['oi']-math.log(16)), math.log(16), r16['hlm'], r16['sqrtpow']))
print("  DETECTED: %s  meas/pred=%.3f" % ("YES" if r16['det'] else "NO", r16['mp']))

# summary stats over DETECTED lines
mps = [r['mp'] for r in rows if r['det']]
mps = np.array(mps)
print("\n== SUMMARY (meas/pred over DETECTED lines) ==")
print("  detected: %d / %d lines" % (len(mps), len(rows)))
print("  median=%.3f mean=%.3f std=%.3f min=%.3f max=%.3f" %
      (np.median(mps), mps.mean(), mps.std(), mps.min(), mps.max()))
undetected=[r['lbl'] for r in rows if not r['det']]
print("  undetected (upper bounds): %s" % ", ".join(undetected))

# save rows for the append step
import json
with open("pi_clock_satake_rows.json","w") as fh:
    json.dump([{k:(float(v) if isinstance(v,(np.floating,np.integer)) or (isinstance(v,(float,int)) and not isinstance(v,bool)) else v) for k,v in r.items()} for r in rows], fh)
print("\n(rows saved)")
