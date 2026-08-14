"""ATTEMPT 018 -- the von Mangoldt expansion of the S(t) bridge's vertical leg.

THE PAPER'S OWN NAMED NEXT STEP.  universal.tex, sec:st-bridge (thm:st-explicit-bridge):

    pi S_Gamma(T) = Im( i \int_0^T (xi'/xi)(2+iy) dy ) - (3/2) Im A
                    - sum_rho m_rho P_T(rho) - theta(T) - pi

and the reading below it says, verbatim: "the vertical leg lives at Re s = 2, inside the
Euler-product regime --- it is the arithmetic side, and its expansion into the von Mangoldt
series is finite bookkeeping on absolutely convergent data, A NAMED NEXT STEP NOT PERFORMED
HERE."  This attempt performs it.

DERIVATION (done by hand first, then checked numerically).
Since ds = i dy on the segment, the vertical leg is a continuous logarithm increment:

    i \int_0^T (xi'/xi)(2+iy) dy = log xi(2+iT) - log xi(2),      so the leg = arg xi(2+iT).

With xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s),

    arg xi(2+iT) = arg(2+iT) + arg(1+iT) - (T/2) log pi
                   + Im logGamma((2+iT)/2) + arg zeta(2+iT),

each branch continuous from 0 at T = 0.  Only the last term is arithmetic, and on Re s = 2 the
Euler product gives log zeta(s) = sum_{p,k} 1/(k p^{ks}) absolutely, so

    arg zeta(2+iT) = - sum_{p,k} sin(k T log p) / (k p^{2k}).            (*)

CONSEQUENCE, which is the point of doing this.  (*) is dominated termwise by 1/(k p^{2k}),
whose total is sum_{p,k} 1/(k p^{2k}) = log zeta(2) = log(pi^2/6) = 0.4977046...  Hence

    | arithmetic part of the vertical leg |  <=  log zeta(2) = 0.49770,  for EVERY T.

So the arithmetic side of the bridge is bounded by an absolute constant; it contributes at most
log zeta(2)/pi = 0.1584 to S_Gamma itself.  ALL growth in the vertical leg is archimedean (the
Gamma term), and all the growth of S is therefore in the zero packets.  That is a DC-first
accounting statement: the prime side is evaluated exactly and is O(1), not estimated.

STATED NULL (pre-registered).  (*) fails to reproduce arg zeta(2+iT); or sup|arg zeta(2+iT)|
exceeds log zeta(2); or the arithmetic term is NOT small compared with the leg's growth, i.e.
the prime side does carry the size of S.  Any of those and this accounting is wrong.
"""
import mpmath as mp, sys
from math import log

def P(*a): print(*a); sys.stdout.flush()
mp.mp.dps = 30

# ---- prime powers p^k with p^{2k} up to a cutoff; the series converges like p^{-2k} -------
def prime_powers(limit):
    sieve = [True]*(limit+1); sieve[0:2] = [False, False]
    out = []
    for i in range(2, limit+1):
        if sieve[i]:
            for j in range(i*i, limit+1, i): sieve[j] = False
            q, k = i, 1
            while q <= limit:
                out.append((i, k, q)); q *= i; k += 1
    return out

PP = prime_powers(200000)
P(f"ATTEMPT 018 -- von Mangoldt expansion of the vertical leg.  {len(PP)} prime powers p^k <= 2e5.\n")

def vonmangoldt_arg(T):
    """(*)  -sum_{p,k} sin(kT log p)/(k p^{2k})"""
    T = mp.mpf(T); s = mp.mpf(0)
    for p, k, q in PP:
        s -= mp.sin(k*T*mp.log(p))/(k*mp.mpf(q)**2)
    return s

P("CHECK 1.  (*) against mpmath's arg zeta(2+iT), directly.")
P(f"  {'T':>12}{'von Mangoldt (*)':>22}{'arg zeta(2+iT)':>20}{'|diff|':>12}")
worst = mp.mpf(0)
for T in (0.5, 1, 2, 5, 14.134725, 50, 100, 1000, 12345.6789, 1e6+0.5):
    a = vonmangoldt_arg(T); b = mp.arg(mp.zeta(2+1j*mp.mpf(T)))
    d = abs(a-b); worst = max(worst, d)
    P(f"  {float(T):>12.4f}{mp.nstr(a,12):>22}{mp.nstr(b,12):>20}{mp.nstr(d,3):>12}")
P(f"  worst |diff| = {mp.nstr(worst,3)}   (truncation floor ~ sum_{{p^2k>2e5}} p^-2k)\n")

BOUND = mp.log(mp.zeta(2))
P("CHECK 2.  the absolute bound.  sum_{p,k} 1/(k p^{2k}) = log zeta(2) = log(pi^2/6).")
tot = sum(mp.mpf(1)/(k*mp.mpf(q)**2) for p, k, q in PP)
P(f"  termwise sum of |coefficients| : {mp.nstr(tot,15)}")
P(f"  log zeta(2)                    : {mp.nstr(BOUND,15)}")
P(f"  |diff|                         : {mp.nstr(abs(tot-BOUND),3)}\n")

P("CHECK 3.  is the bound anywhere near attained?  scan arg zeta(2+iT).")
mx = mp.mpf(0); at = 0; ss = mp.mpf(0); n = 0
for i in range(20001):
    T = mp.mpf(i)*mp.mpf('0.37')
    v = mp.arg(mp.zeta(2+1j*T))
    if abs(v) > mx: mx, at = abs(v), float(T)
    ss += v*v; n += 1
P(f"  max |arg zeta(2+iT)| over T in [0, 7400], 20001 samples : {mp.nstr(mx,10)}  at T={at:.2f}")
P(f"  rms                                                     : {mp.nstr(mp.sqrt(ss/n),10)}")
P(f"  absolute bound log zeta(2)                              : {mp.nstr(BOUND,10)}")
P(f"  -> contribution to S_Gamma is at most log zeta(2)/pi    = {mp.nstr(BOUND/mp.pi,10)}\n")

P("CHECK 4.  the FULL vertical leg = arg xi(2+iT), decomposed.  Which piece grows?")
P(f"  {'T':>10}{'arg(2+iT)':>12}{'arg(1+iT)':>12}{'-(T/2)logpi':>14}"
  f"{'Im logG':>14}{'arg zeta':>11}{'total leg':>14}")
for T in (10, 100, 1000, 10000, 100000):
    T = mp.mpf(T)
    a1 = mp.atan2(T, 2); a2 = mp.atan2(T, 1); a3 = -(T/2)*mp.log(mp.pi)
    a4 = mp.im(mp.loggamma((2+1j*T)/2)); a5 = mp.arg(mp.zeta(2+1j*T))
    P(f"  {float(T):>10.0f}{float(a1):>12.4f}{float(a2):>12.4f}{float(a3):>14.2f}"
      f"{float(a4):>14.2f}{float(a5):>11.4f}{float(a1+a2+a3+a4+a5):>14.2f}")
P("\n  READING.  The arithmetic column is the ONLY bounded-by-a-constant one and never leaves")
P("  a band of width ~0.5; the Gamma column carries every bit of the growth.  So the prime")
P("  side of the bridge is O(1) EXACTLY, with the explicit constant log zeta(2) = 0.49770,")
P("  and the entire size of S lives in the zero packets P_T(rho).")
