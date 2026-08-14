"""Is the winding branch visible in LOCAL data?

N(t) = 1 + theta(t)/pi + S(t).  theta is explicit; S mod 2 is computable from arg zeta
mod 2pi.  So N mod 6 needs S mod 6, i.e. 3 branches beyond what the readout gives.
The ambiguity BITES only when |S| > 1.

PRECHECK: if local data carry no branch information, then within the |S|>1 set the local
quantities are distributed identically across branches.  If some local quantity separates
them, that is the handle.  Discriminating either way.
"""
import mpmath as mp, numpy as np, sys
mp.mp.dps = 15
def P(*a): print(*a); sys.stdout.flush()

rows=[]
t=20.0
while t < 900.0:
    N = int(mp.nzeros(t))
    th = float(mp.siegeltheta(t))
    S = N - 1 - th/mp.pi
    Z = float(mp.siegelz(t))
    zt = mp.zeta(mp.mpc(0.5,t))
    rows.append((t, N, float(S), Z, float(abs(zt)), float(mp.arg(zt)), th))
    t += 0.37
A=np.array([(r[0],r[1],r[2],r[3],r[4],r[5],r[6]) for r in rows])
t_,N_,S_,Z_,az_,ar_,th_ = A.T
P(f"samples: {len(A)}   S range [{S_.min():.3f}, {S_.max():.3f}]   |S|>1 : {np.sum(np.abs(S_)>1)}")
P(f"  check S mod 2 recoverable from sign of Z:  N mod 2 vs (Z>0)")
par = (N_.astype(int) % 2)
agree = max(np.mean(par == (Z_>0)), np.mean(par == (Z_<0)))
P(f"    agreement = {agree:.4f}   -> sign gives N mod 2 {'YES' if agree>0.99 else 'partially'}")

big = np.abs(S_) > 1
P(f"\n  WITHIN the |S|>1 set ({big.sum()} samples): does any local quantity separate branches?")
if big.sum() > 10:
    br = np.floor((S_[big]+3)/2).astype(int)      # branch index of S in windows of width 2
    P(f"    branches present: {sorted(set(br.tolist()))}")
    for nm,v in (('|zeta|',az_[big]),('arg zeta',ar_[big]),('|Z|',np.abs(Z_[big])),
                 ('theta mod 2pi',np.mod(th_[big],2*np.pi)),
                 ('t mod (pi/3)',np.mod(t_[big],np.pi/3))):
        stats=[]
        for b in sorted(set(br.tolist())):
            m=v[br==b]
            stats.append(f"b={b}:{m.mean():8.3f}+-{m.std():6.3f}(n={len(m)})")
        P(f"    {nm:<14} " + "  ".join(stats))
else:
    P("    too few |S|>1 samples at this height; extend the range")
