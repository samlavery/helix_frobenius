"""Does changing the CHART SCALE remove the S(t) growth?

One pass: locate sign changes of Z (each = a certified on-line zero).  Then bin them
by theta at cell width w.  Cell of width w expects w/pi zeros.  "Failure" = the cell
does not hold its expected count.

PRECHECK -- if the chart is inert, the failure-rate-vs-height curve is IDENTICAL for
every w.  If it is not inert, the curves differ.  Discriminating either way.
"""
import mpmath as mp, numpy as np, sys, time
mp.mp.dps = 15
def P(*a): print(*a); sys.stdout.flush()

def sign_changes(t0, t1, step):
    ts=np.arange(float(t0), float(t1), step)
    Z=np.array([float(mp.siegelz(t)) for t in ts])
    s=np.sign(Z); idx=np.nonzero(s[:-1]*s[1:] < 0)[0]
    return ts[idx] + step/2

WIN=[]
for n0 in (1000, 10000, 100000):
    g0=float(mp.grampoint(n0)); g1=float(mp.grampoint(n0+800))
    WIN.append((n0,g0,g1))

P(f"{'window':>10}{'T':>12}{'zeros':>8}   failure rate by cell width w (in units of pi)")
P(f"{'':>10}{'':>12}{'':>8}   " + "".join(f"{c:>9}" for c in
                                          ('w=pi/3','w=pi','w=2pi','w=3pi','w=6pi','w=12pi')))
for n0,g0,g1 in WIN:
    t0=time.time()
    sp = 2*np.pi/np.log(g0/(2*np.pi))
    sc = sign_changes(g0, g1, sp/10)
    th = np.array([float(mp.siegeltheta(t)) for t in sc])
    row=[]
    for c in (1/3, 1, 2, 3, 6, 12):
        w = c*np.pi
        cell = np.floor((th - th[0])/w).astype(int)
        ncell = cell.max()+1
        cnt = np.bincount(cell, minlength=ncell)
        cnt = cnt[1:-1]                      # drop partial end cells
        exp = w/np.pi
        if abs(exp-round(exp))<1e-9:
            fail = np.mean(cnt != round(exp))
        else:                                # non-integer expectation: |dev| >= 1
            fail = np.mean(np.abs(cnt-exp) >= 1)
        row.append(fail)
    P(f"{n0:>10}{g0:>12.0f}{len(sc):>8}   " + "".join(f"{r:>8.1%} " for r in row)
      + f"  [{time.time()-t0:.0f}s]")
P("")
P("growth across the three heights, per chart:")
