"""att532 — THE DC-SUBTRACTED OPERATOR: its spectral measure against the first zeros (ledger 532).

Sam, 2026-09-02: "build it" — the operator with the three DCs subtracted, spectral measure read
directly against the zeros.

THE OBJECT, in the density register on the height axis z (s = 1/2 + iz).
  Unitary-clock direct integral for prime p (ClockPoissonBarycenter, read on the line): its spectral
  density is the Poisson density at radius r = p^{-1/2},
      rho_p(z) = (log p / 2pi) * (1 - r^2)/(1 - 2 r cos(z log p) + r^2)
               = (log p / 2pi) * Re[(1+w)/(1-w)],  w = p^{-1/2 - iz}
               = log p / 2pi  +  (1/pi) * sum_{k>=1} log p * p^{-k/2} cos(k z log p).
  Summing p <= Q:  rho_Q^clock(z) = DC_Q + (1/pi) Re sum_{n Q-smooth} Lambda(n) n^{-1/2 - iz},
  DC_Q = sum_{p<=Q} log p / 2pi.  (att530: the clock face carries NEGATIVE seat mass with DC sum log q.)
  Zero-counting density (Riemann-von Mangoldt, N = 1 + theta/pi + S, S = (1/pi) arg zeta):
      dN/dz = theta'(z)/pi + S'(z),   S'(z) = -(1/pi) Re sum_n Lambda(n) n^{-1/2 - iz}  (formal),
  so the marriage in the density register is
      D_Q(z) := theta'(z)/pi + DC_Q - rho_Q^clock(z)  =  theta'(z)/pi - (1/pi) Re sum_{Q-smooth} Lambda(n) n^{-1/2-iz}.
  The THREE DCs of ledger 531: the clock DC (subtracted here), the Gamma clock theta'/pi (added), and the
  end/dc residue "1" (the constant in N = 1 + ...), which drops out of every window integral.
  D_Q is the spectral density of the finite-Q marriage object; it is SIGNED at finite Q.

WHAT IS MEASURED (pre-registered)
  For Q in {10^2, 10^3, 10^4, 10^5, 10^6}, on z in [5, 65] (step 0.01):
  (a) window counts  int_{m_{k-1}}^{m_k} D_Q dz  over the window around each zero gamma_k (m = midpoints
      between consecutive zeros), for the 13 zeros in (10, 60): PREDICTION at Q = 10^6: all within +-0.15 of 1
      (resolution 2 pi / log Q = 0.45); mean |count - 1| decreasing monotonically from Q = 10^3.
  (b) peak positions of D_Q in each window vs gamma_k: PREDICTION at Q = 10^6: |displacement| < 0.25 for all 13.
  (c) the negative mass per window int max(-D_Q, 0) dz: recorded, not predicted (the finite-Q object is signed;
      whether its Krein defect shrinks with Q is the observation).
  (d) N_Q(60) - N_Q(10) vs the true 13.
  DECISION RULE: more than two windows with |count-1| > 0.3, or peaks off by > 0.5 at Q = 10^6, means the
  sharp-cutoff DC-subtracted operator does not resolve the zeros at this Q.

Read-only; no L-value is used except the reference zero ordinates in the validation columns.
"""

from __future__ import annotations

import math
import numpy as np
from mpmath import mp, mpf, mpc, digamma, log, pi

mp.dps = 20

ZEROS = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513,
         32.935061587739190, 37.586178158825671, 40.918719012147495, 43.327073280914999,
         48.005150881167160, 49.773832477672302, 52.970321477714461, 56.446247697063395,
         59.347044002602353, 60.831778524609809]   # the 14th is used only for the last midpoint

CUTS = [100, 1_000, 10_000, 100_000, 1_000_000]


def primes_upto(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return np.nonzero(sieve)[0]


def theta_prime_over_pi(z: np.ndarray) -> np.ndarray:
    """theta'(z)/pi with theta(z) = Im log Gamma(1/4 + iz/2) - (z/2) log pi:
    theta'(z) = (1/2) Re psi(1/4 + iz/2) - (1/2) log pi."""
    out = np.empty_like(z)
    lp = float(log(pi))
    for i, t in enumerate(z):
        ps = digamma(mpc(mpf(1) / 4, mpf(t) / 2))
        out[i] = (0.5 * float(ps.real) - 0.5 * lp) / math.pi
    return out


def prime_oscillation(primes: np.ndarray, z: np.ndarray, cuts, tol=1e-10):
    """Return dict cut -> (1/pi) Re sum_{n Q-smooth, p<=cut} Lambda(n) n^{-1/2-iz}, accumulated in prime order."""
    acc = np.zeros_like(z)
    snapshots = {}
    ci = 0
    block = 400                       # z-block to bound memory
    logp_all = np.log(primes.astype(np.float64))
    # process primes in chunks, in increasing order
    pchunk = 2000
    for start in range(0, len(primes), pchunk):
        p = primes[start:start + pchunk].astype(np.float64)
        lp = logp_all[start:start + pchunk]
        # powers k with weight p^{-k/2} >= tol for at least the smallest prime in the chunk
        kmax = int(math.floor(-2 * math.log(tol) / math.log(p[0]))) if p[0] > 1 else 1
        kmax = max(kmax, 1)
        for zs in range(0, len(z), block):
            zz = z[zs:zs + block]
            contrib = np.zeros_like(zz)
            for k in range(1, kmax + 1):
                wgt = lp * p ** (-k / 2.0)
                keep = wgt >= tol * 1e-3
                if not np.any(keep):
                    break
                ph = np.cos(np.outer(zz, k * lp[keep]))      # (block, nprimes)
                contrib += ph @ wgt[keep]
            acc[zs:zs + block] += contrib / math.pi
        # snapshot at cutoffs passed
        last_p = int(primes[min(start + pchunk, len(primes)) - 1])
        while ci < len(cuts) and last_p >= cuts[ci]:
            # exact cutoff: subtract primes in (cut, last_p] from this chunk
            over = primes[start:start + pchunk]
            over = over[over > cuts[ci]].astype(np.float64)
            corr = np.zeros_like(z)
            if len(over):
                lpo = np.log(over)
                kmax_o = int(math.floor(-2 * math.log(tol) / math.log(over[0])))
                for zs in range(0, len(z), block):
                    zz = z[zs:zs + block]
                    c2 = np.zeros_like(zz)
                    for k in range(1, max(kmax_o, 1) + 1):
                        wgt = lpo * over ** (-k / 2.0)
                        keep = wgt >= tol * 1e-3
                        if not np.any(keep):
                            break
                        c2 += np.cos(np.outer(zz, k * lpo[keep])) @ wgt[keep]
                    corr[zs:zs + block] = c2 / math.pi
            snapshots[cuts[ci]] = acc - corr
            ci += 1
    while ci < len(cuts):                 # cutoffs at or beyond the largest prime processed
        snapshots[cuts[ci]] = acc.copy()
        ci += 1
    return snapshots


def window_stats(z, D, dz):
    mids = [(ZEROS[i] + ZEROS[i + 1]) / 2 for i in range(len(ZEROS) - 1)]
    rows = []
    for k in range(1, len(ZEROS) - 1):          # zeros 2..13 have midpoints on both sides; add zero 1 with left edge 10
        pass
    windows = []
    # window for zero_1 : [10, m_1]; zero_k (k=2..13): [m_{k-1}, m_k]
    windows.append((10.0, mids[0], ZEROS[0]))
    for k in range(1, 13):
        windows.append((mids[k - 1], mids[k], ZEROS[k]))
    for a, b, g in windows:
        sel = (z >= a) & (z < b)
        cnt = float(np.sum(D[sel]) * dz)
        neg = float(np.sum(np.maximum(-D[sel], 0.0)) * dz)
        i = np.argmax(D[sel])
        peak = float(z[sel][i])
        rows.append((a, b, g, cnt, peak - g, neg))
    return rows


def main():
    out = []
    P = out.append
    P("att532 — the DC-subtracted operator's spectral measure vs the first zeros")
    dz = 0.01
    z = np.arange(5.0, 65.0 + dz / 2, dz)
    P("grid z in [5,65], step %.3f, %d points; cutoffs %s" % (dz, len(z), CUTS))
    thp = theta_prime_over_pi(z)
    primes = primes_upto(CUTS[-1])
    snaps = prime_oscillation(primes, z, CUTS)
    P("")
    P("D_Q(z) = theta'(z)/pi - (1/pi) Re sum_{Q-smooth} Lambda(n) n^{-1/2 - iz}   (= theta'/pi + DC_Q - rho_Q^clock)")
    P("D'_Q(z) = D_Q(z) + END_Q(z),  END_Q(z) = (1/pi) Re[ Q^{1/2 - iz} / (1/2 - iz) ]  — the third DC, the end term of")
    P("   the truncated explicit formula read on the line (ledger 531); omitted in the first pass, which DIED.")
    for c in CUTS:
        end = (1.0 / math.pi) * np.real((c ** (0.5 - 1j * z)) / (0.5 - 1j * z))
        for label, D in (("D_Q  (two DCs handled: clock DC subtracted, Gamma added)", thp - snaps[c]),
                         ("D'_Q (all three DCs: + END_Q)", thp - snaps[c] + end)):
            rows = window_stats(z, D, dz)
            P("=" * 100)
            P("Q <= %d    (resolution 2pi/log Q = %.3f)    %s" % (c, 2 * math.pi / math.log(c), label))
            _report(P, rows, D, z, dz)
    P("")
    P("END_Q amplitude sqrt(Q)/(pi t) at t = 14: " + ", ".join("Q=%d: %.2f" % (c, math.sqrt(c) / (math.pi * 14)) for c in CUTS))
    text = "\n".join(out)
    print(text)
    with open("/Users/samuellavery/work/helix_frobenius/tmp/att532_results.txt", "w") as f:
        f.write(text + "\n")
    return


def _report(P, rows, D, z, dz):
    if True:
        P("   window            zero      count     peak-zero   neg.mass")
        errs, disp, negs = [], [], []
        for a, b, g, cnt, d, neg in rows:
            P("   [%6.2f,%6.2f]  %8.4f  %+8.4f  %+9.4f  %8.4f" % (a, b, g, cnt, d, neg))
            errs.append(abs(cnt - 1)); disp.append(abs(d)); negs.append(neg)
        P("   mean|count-1| = %.4f   max|count-1| = %.4f   #windows off by >0.3: %d" % (np.mean(errs), np.max(errs), sum(e > 0.3 for e in errs)))
        P("   mean|peak-zero| = %.4f   max = %.4f   #peaks off by >0.5: %d" % (np.mean(disp), np.max(disp), sum(d > 0.5 for d in disp)))
        P("   mean negative mass per window = %.4f   (signed-measure defect of the finite-Q object)" % np.mean(negs))
        sel = (z >= 10) & (z < 60)
        P("   N_Q(60) - N_Q(10) = %.4f   (true count of zeros in (10,60): 13)" % (np.sum(D[sel]) * dz))


if __name__ == "__main__":
    main()
