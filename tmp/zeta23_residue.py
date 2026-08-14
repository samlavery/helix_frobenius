"""Residue-class decomposition of the off-diagonal O_1, at modulus q.

Integers placed at n*H: H = pi/3 gives period 6 in n, H = pi/6 gives period 12.
Since Lambda is supported on prime powers, the classes are almost all empty:
  q=6:  class 3 = {3^k} exactly (the "wall"),  classes 2,4 = {2^k},  class 0 = EMPTY,
        classes 1,5 = every p^k with p > 3, i.e. essentially all the mass.

Block decomposition.  Write V(delta, mbar) = sum_n a_n R_n(delta) e^{i mbar u_n}, so that
    minus_part = 2 sum_kl |V|^2 = D + O_1.
Splitting the n-sum by residue class a gives V = sum_a V_a and
    minus_part(a,b) = 2 sum_kl Re[V_a conj(V_b)] = sum_kl (P_a P_b + Q_a Q_b)/2
    O_1(a,b) = minus_part(a,b) - delta_ab D_a
Block (a,b) holds exactly the pairs with shift n - m = a - b (mod q), so the same table is
both the support decomposition and the SHIFT decomposition.
"""
import time
import numpy as np

from zeta23_bench import phihat
from zeta23_prime import prime_powers
from zeta23_o1_fast import R_table


def blocks(T, L, w, lam, u, q, c=1.0):
    """Return (classes, O1blk, Dvec, mass) for modulus q."""
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    keep = u < L
    a = (lam * np.exp(-0.5 * u))[keep]
    uu = u[keep]
    n = np.rint(np.exp(uu)).astype(np.int64)
    res = (n % q).astype(int)
    cls = np.array(sorted(set(res.tolist())))
    Rt = R_table(uu, L, w, d, h)
    jj = np.arange(d)
    C = np.cos(np.outer(jj * h, uu))
    S = np.sin(np.outer(jj * h, uu))
    A = T + np.arange(d) * h / 2.0
    nc = cls.size
    P = np.zeros((nc, d, d))
    Q = np.zeros((nc, d, d))
    for ci, cv in enumerate(cls):
        m = res == cv
        ang = np.outer(uu[m], A)
        base = a[m][:, None] * Rt[m]
        Gc, Gs = base * np.cos(ang), base * np.sin(ang)
        P[ci] = -2.0 * (C[:, m] @ Gc - S[:, m] @ Gs)
        Q[ci] = -2.0 * (S[:, m] @ Gc + C[:, m] @ Gs)
    wgt = (jj[:, None] <= (d - 1 - np.arange(d))[None, :]).astype(float)
    wgt *= np.where(np.arange(d)[None, :] == 0, 1.0, 2.0)
    minus = np.zeros((nc, nc))
    for i in range(nc):
        for j2 in range(nc):
            minus[i, j2] = 0.5 * float(np.sum(wgt * (P[i] * P[j2] + Q[i] * Q[j2])))
    cnt = np.concatenate([[d], 2 * (d - np.arange(1, d))])
    D = np.array([2.0 * float(np.sum(a[res == cv]**2 * (Rt[res == cv]**2 @ cnt)))
                  for cv in cls])
    O1 = minus - np.diag(D)
    mass = np.array([float(np.sum(a[res == cv])) for cv in cls])
    cnts = np.array([int(np.sum(res == cv)) for cv in cls])
    return cls, O1, D, mass, cnts, minus


def report(T, lam, eta, qs):
    l = np.log(T / (2 * np.pi))
    l1 = l + 2 * np.log(2) - 1
    L, w = lam * l, eta * lam * l / 2
    assert eta * L <= 2 * np.log(2)
    X = np.exp(L)
    lamv, u = prime_powers(X)
    pred = -(T / (6 * np.pi)) * max(L - l1, 0.0)**3
    print(f"\nT={T:.0f} lam={lam} eta={eta}  L={L:.4f}  X={X:.0f}  "
          f"Npp={u.size}  O1_main={pred:.1f}")
    for q in qs:
        t0 = time.time()
        cls, O1, D, mass, cnts, minus = blocks(T, L, w, lamv, u, q)
        tot = O1.sum() / L**2
        Dtot = D.sum() / L**2
        # "special" classes = those holding p^k for p | q
        sp = [i for i, cv in enumerate(cls)
              if cnts[i] > 0 and all(int(np.rint(x)) % qq == 0
                                     for qq in [p for p in (2, 3, 5, 7, 11, 13) if q % p == 0]
                                     for x in [np.exp(u[(u < L)][np.rint(np.exp(u[u < L])).astype(int) % q == cv][0])])]
        # simpler: a class is "special" iff every prime power in it shares a factor with q
        spec = []
        for i, cv in enumerate(cls):
            if cnts[i] == 0:
                continue
            nn = np.rint(np.exp(u[u < L])).astype(np.int64)
            mem = nn[(nn % q) == cv]
            if np.all(np.gcd(mem, q) > 1):
                spec.append(i)
        bulk = [i for i in range(cls.size) if i not in spec]
        O1_bulk = O1[np.ix_(bulk, bulk)].sum() / L**2
        mass_sp = mass[spec].sum() / mass.sum() if spec else 0.0
        print(f"  q={q:3d}  classes={list(cls)}")
        print(f"        counts={list(cnts)}")
        print(f"        special classes (all members share a factor with q): "
              f"{[int(cls[i]) for i in spec]}  carrying {100*mass_sp:.2f}% of mass")
        print(f"        O1(total)={tot:12.3f}   O1(bulk only)={O1_bulk:12.3f}   "
              f"change={100*(O1_bulk-tot)/abs(tot):+7.3f}%")
        print(f"        meas/main: full {tot/pred:6.4f}   bulk {O1_bulk/pred:6.4f}"
              f"   [{time.time()-t0:.0f}s]")
        if q in (6, 12):
            with np.printoptions(precision=1, suppress=True, linewidth=200):
                print(f"        O1 block matrix /L^2 (rows=n mod {q}, cols=m mod {q}):")
                print("        " + str(O1 / L**2).replace("\n", "\n        "))


if __name__ == "__main__":
    import sys
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 600.0
    lam = float(sys.argv[2]) if len(sys.argv) > 2 else 2.0
    report(T, lam, 0.02, [6, 12, 5, 7, 10, 15])
