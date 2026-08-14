"""V8: the crossing point n* (015's ACTUAL threshold statistic) across the four specimens,
computed from my own lambda arrays, and its exponent -- contrasted with 030's headline
exponent, which is measured on n_half (an amplitude statistic with no prime model in it)."""
import os, sys, math, time
import numpy as np
from mpmath import mp, mpf, mpc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from att030_verify import (coeffs_on_circle, g_arith_chi, BL_trunc, detr, R2, CH,
                           amp_curve, n_half_of, HERE)

def P(*a):
    print(*a); sys.stdout.flush()

NM = 2000
g1 = {'zeta': 14.134725141734693, 'chi_-3': 8.039737155681467,
      'chi_5': 6.648453344727715, 'chi_8': 4.899973997007036}
m1 = {'zeta': 2, 'chi_-3': 2, 'chi_5': 2, 'chi_8': 3}
names = ['zeta', 'chi_-3', 'chi_5', 'chi_8']

Y = {'zeta': np.load(os.path.join(HERE, 'ver030_arith.npy'))[:NM]}
O = {'zeta': BL_trunc(NM, 32)}
for nm in CH:
    f = os.path.join(HERE, 'ver030_%s.npy' % nm.replace('_', '-', 1))
    if not os.path.exists(f):
        P("   my contour for %s (r=0.985, N=4096, dps=45) ..." % nm)
        cc = coeffs_on_circle(lambda z, k=nm: g_arith_chi(z, k), '0.985', 4096, 2500, 45, tag=nm)
        np.save(f, np.array([float(x.real) for x in cc]))
    Y[nm] = np.load(f)[:NM]
    t = np.load(os.path.join(HERE, 'att030_Y_%s.npy' % nm))[:NM]
    P("   %-7s my array vs theirs: max abs %.3e ; lambda_1 = %.12f" %
      (nm, np.abs(Y[nm] - t).max(), Y[nm][0]))
    q, a, tab = CH[nm]
    O[nm] = BL_trunc(NM, 32, chi=lambda r, T=tab: T.get(r, 0), q=q)

def crossing(y, o, ratio=2.0, basis='orig'):
    grid = np.unique(np.round(np.exp(np.linspace(math.log(8), math.log(NM / ratio),
                                                 220))).astype(int))
    for n0 in grid:
        n1 = int(n0 * ratio)
        if n1 > NM or n1 - n0 < 8:
            continue
        n = np.arange(n0, n1 + 1, dtype=float)
        if R2(n, y[n0 - 1:n1], o[n0 - 1:n1], basis) >= 0.5:
            ok = True
            for mf in (1.3, 1.8, 2.6):
                a2 = int(n0 * mf); b2 = int(a2 * ratio)
                if b2 > NM:
                    continue
                n2 = np.arange(a2, b2 + 1, dtype=float)
                if R2(n2, y[a2 - 1:b2], o[a2 - 1:b2], basis) < 0.5:
                    ok = False; break
            if ok:
                return n0
    return None

P("=" * 100)
P("V8  n*  = the R^2 crossing (015's threshold; 'n=138' refers to THIS object)")
P("    n_h = 030's amplitude turn-on (stage 4), the object the headline exponent uses")
P("    %-8s %8s %8s %8s %10s %10s %10s" %
  ("spec", "gamma_1", "n*", "n_half", "res.pred", "n*/pred", "n_h/g1"))
ns_, nh_ = {}, {}
for nm in names:
    c = crossing(Y[nm], O[nm])
    a, b = amp_curve(Y[nm], NM, 2.0)
    h = n_half_of(a, b, 0.3)[0]
    ns_[nm] = c; nh_[nm] = h
    pred = g1[nm] ** 2 * math.log(m1[nm])
    P("    %-8s %8.4f %8s %8.0f %10.1f %10s %10.2f" %
      (nm, g1[nm], c, h, pred, ("%.3f" % (c / pred)) if c else "-", h / g1[nm]))

x = np.log([g1[k] for k in names])
for lab, d in (("n*  (the actual threshold)", ns_), ("n_half (030's headline)", nh_)):
    v = [d[k] for k in names]
    if all(u is not None and np.isfinite(u) for u in v):
        y_ = np.log(np.array(v, float))
        p, _ = np.polyfit(x, y_, 1); r = np.corrcoef(x, y_)[0, 1]
        sp1 = max(a / b for a, b in zip(v, [g1[k] for k in names])) / \
              min(a / b for a, b in zip(v, [g1[k] for k in names]))
        sp2 = max(a / b ** 2 for a, b in zip(v, [g1[k] for k in names])) / \
              min(a / b ** 2 for a, b in zip(v, [g1[k] for k in names]))
        P("    %-28s values %s  ->  p = %+.3f   r = %+.4f   spread /g = %.2fx  /g^2 = %.2fx"
          % (lab, v, p, r, sp1, sp2))
P("\n    030's own reported n* row was 90 / 21 / 41 / 24 and its headline p=+0.982,r=+0.9987")
P("    came from the n_half row (113/68/54/40), not from n*.")
