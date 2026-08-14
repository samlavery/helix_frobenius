"""THE HARMONIZED BANK, done as a BANK.
cell factor splits the series into 6 channels (n mod 6); the readout is their SUM:
    zeta(s) = 6^{-s} * sum_{r=1..6} zeta(s, r/6)      (Hurwitz)
At a zero the six cell-phasors CLOSE (sum to zero).  Question: HOW do they close?
Are they at mu6 angles (successive gaps ~ pi/3)?  Compare zeros vs non-zeros.
"""
import mpmath as mp, numpy as np
mp.mp.dps = 30

def channels(s):
    return [mp.zeta(s, mp.mpf(r)/6) for r in range(1,7)]

def report(tag, s):
    v = channels(s)
    tot = sum(v)
    z = mp.power(6,-s)*tot
    args = np.array([float(mp.arg(x)) for x in v])
    mags = np.array([float(abs(x)) for x in v])
    gaps = np.diff(np.unwrap(args))
    print(f"  {tag}")
    print(f"    |sum of channels| = {float(abs(tot)):.3e}   |zeta(s)| = {float(abs(z)):.3e}")
    print(f"    channel |v_r| : " + " ".join(f"{m:7.4f}" for m in mags))
    print(f"    arg gaps /pi  : " + " ".join(f"{g/np.pi:+6.3f}" for g in gaps) + f"   (pi/3 = 0.333)")
    return mags, gaps

print("=== AT ZEROS (channels must close) ===")
allgaps=[]
for k in (1,2,3,5,10):
    g = mp.im(mp.zetazero(k)); s = mp.mpc(0.5, g)
    m,gp = report(f"zero #{k}, gamma={float(g):.4f}", s)
    allgaps.append(gp)
print("\n=== CONTROL: non-zero points on the line ===")
for t in (17.0, 27.5, 45.0):
    report(f"s = 1/2 + {t}i (not a zero)", mp.mpc(0.5, t))
print("\n=== CONTROL: off the line at a zero ordinate ===")
g=mp.im(mp.zetazero(1))
for sig in (0.3, 0.7):
    report(f"s = {sig} + i*gamma_1", mp.mpc(sig, g))

A=np.array(allgaps)
print(f"\nmean arg-gap over zeros /pi = {A.mean()/np.pi:.4f}  (mu6 would be 0.3333)")
print(f"per-gap means /pi: " + " ".join(f"{x:+.4f}" for x in A.mean(axis=0)/np.pi))
