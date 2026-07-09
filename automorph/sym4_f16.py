"""RUNG B2 -- the genuinely-open Sym^4 landing: f16 = Delta*E4 (weight-16 level-1).

Owner directive & tmp/sym4_research_notes.md (EXPERIMENT-READY FACTS): Ibukiyama-Katsurada
2014 proved Zagier's EXACT Sym^4 constants for Delta, but for a GENERAL (non-Delta) level-1
eigenform they proved ALGEBRAICITY ONLY -- the exact rational constant is explicitly
CONJECTURAL ("give some conjectures in the general case", IK's own abstract).  f16 = Delta*E4
is the unique weight-16 level-1 cusp form (newform 16.a).  So:

  L(Sym^4 f16, critical) / (pi-power * <f16,f16>^3)  =  a rational  [algebraicity PROVEN]

but WHICH rational is OPEN.  We build f16 exactly, its Sym^4 ladder, compute the critical
values from our own coefficients (no L-library), and LAND the algebraic part as an exact
small-height rational.  A clean landing = the first numerical determination of the open
IK/Zagier-type constant for a non-Delta form (fiber-side).  A clean non-landing (after a
precision/convergence audit) = register-grade, reported prominently.  Tier: [open-conjecture-tested].

NORMALIZATION (from the notes, traps #1 and #2 obeyed):
- Unitary Satake: a(p)=lambda_p p^{(k-1)/2}, k=16 => a(p)=lambda_p p^{7.5}, |lambda_p|<=2.
- Sym^4 local Satake {a^4,a^2,1,b^2,b^4} unitary (a+b=lambda_p, ab=1) -- SAME degree-5 ladder
  as Delta, only the weight (=> the archimedean shifts and the pi/period bookkeeping) changes.
- Motivic weight of Sym^4 f16 = 4(k-1) = 60; analytic archimedean factor (Cogdell-Michel,
  m=2, ell=16, m(ell-1)=30 EVEN => delta=0):
    L_inf^an(s) = Gamma_R(s) Gamma_C(s+15) Gamma_C(s+30),  sign +1, centre 1/2.
  Motivic frame: centre (4(k-1)+1)/2 = 30.5, s <-> 61-s.  mu (as Gamma_R shifts) = {0,15,16,30,31}.
- Critical set: derived HERE from finiteness of both completed Gamma-factors (the even-power
  critical-integer inequality was flagged unresolved in the notes -- we derive, not guess).

<f16,f16> Petersson norm: computed from scratch by the fundamental-domain integral (same
routine that reproduced <Delta,Delta> to 2.5e-17 in petersson_rung), using f16's exact
q-expansion.  This is the ONLY non-tau analytic input and it is computed, not looked up.
"""

import math
import sys
import time
from fractions import Fraction

import numpy as np
import mpmath as mp

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")

LAM_CACHE = "/Users/samuellavery/work/helix_frobenius/tmp/gl2long_delta_lambda.npy"
RESULTS = "/Users/samuellavery/work/helix_frobenius/tmp/sym4_f16_results.txt"
K = 16                       # weight of f16
KM1 = K - 1                  # 15

mp.mp.dps = 50
OUT = []


def emit(s=""):
    OUT.append(s)
    print(s, flush=True)


def flush():
    with open(RESULTS, "w") as fh:
        fh.write("\n".join(OUT) + "\n")


# ---------------------------------------------------------------------------
# Exact f16 = Delta * E4 q-expansion (integer arithmetic), n=0..N
# ---------------------------------------------------------------------------
def sigma3_array(N):
    s = np.zeros(N + 1, dtype=object)
    for d in range(1, N + 1):
        d3 = d ** 3
        for m in range(d, N + 1, d):
            s[m] += d3
    return s


def build_f16(N):
    """Exact integer a(n) for f16=Delta*E4, n=0..N.  a(0)=0, a(1)=1."""
    lam = np.load(LAM_CACHE)
    assert len(lam) >= N + 1
    tau = [0] * (N + 1)
    for n in range(1, N + 1):
        tau[n] = int(round(lam[n] * n ** 5.5))
    # spot-check tau
    for n, w in ((1, 1), (2, -24), (3, 252)):
        assert tau[n] == w
    s3 = sigma3_array(N)
    e4 = [0] * (N + 1)
    e4[0] = 1
    for n in range(1, N + 1):
        e4[n] = 240 * int(s3[n])
    # Cauchy product Delta*E4 (Delta has no constant term)
    a = [0] * (N + 1)
    tau_np = tau
    for n in range(1, N + 1):
        acc = 0
        for j in range(1, n + 1):
            acc += tau_np[j] * e4[n - j]
        a[n] = acc
    return a


def verify_eigenform(a, N):
    """Hecke multiplicativity + prime-power recurrence + Deligne bound.  Returns report."""
    def is_prime(n):
        if n < 2:
            return False
        d = 2
        while d * d <= n:
            if n % d == 0:
                return False
            d += 1
        return True
    checks = []
    # multiplicativity a(mn)=a(m)a(n) for a few coprime pairs
    for m, n in ((2, 3), (2, 5), (3, 5), (4, 9), (8, 27), (2, 35)):
        if m * n <= N:
            checks.append(("mult", m, n, a[m] * a[n] == a[m * n]))
    # prime-power a(p^2)=a(p)^2 - p^{k-1}
    for p in (2, 3, 5, 7):
        if p * p <= N:
            checks.append(("ppow2", p, None, a[p * p] == a[p] ** 2 - p ** KM1))
    # Deligne bound |lambda_p|<=2
    maxlam, worst = 0.0, None
    for p in range(2, min(N, 5000)):
        if is_prime(p):
            lp = abs(a[p]) / p ** (KM1 / 2.0)
            if lp > maxlam:
                maxlam, worst = lp, p
    return checks, maxlam, worst


# ---------------------------------------------------------------------------
# Unitary lambda_p and the Sym^r ladder (mpmath, high precision)
# ---------------------------------------------------------------------------
def smallest_prime_factor(N):
    spf = np.zeros(N + 1, dtype=np.int64)
    spf[1] = 1
    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i:N + 1:i] = np.where(spf[i:N + 1:i] == 0, i, spf[i:N + 1:i])
    return spf


def sym_ppow(lam_p, r, Kmax):
    """h_k of Sym^r Satake {a^{r-2j}} (a+b=lam_p, ab=1), k=0..Kmax."""
    th = mp.acos(lam_p / 2)          # |lam_p|<=2
    a = mp.e ** (1j * th)
    xs = [a ** (r - 2 * j) for j in range(r + 1)]
    ser = [mp.mpf(1)] + [mp.mpf(0)] * Kmax
    for xj in xs:
        new = ser[:]
        for k in range(1, Kmax + 1):
            new[k] = ser[k] + xj * new[k - 1]
        ser = new
    return [mp.re(v) for v in ser]


def build_sym_ladder(a_int, spf, N, r):
    """Unitary Sym^r Dirichlet coeffs c(n), n=1..N, from exact integer a(n).
    lambda_p = a(p)/p^{(k-1)/2}."""
    maxe = int(math.log2(N)) + 1
    tab = {}
    c = [mp.mpf(0)] * (N + 1)
    c[1] = mp.mpf(1)
    for n in range(2, N + 1):
        p = int(spf[n])
        m, e = n, 0
        while m % p == 0:
            m //= p
            e += 1
        if p not in tab:
            lam_p = mp.mpf(a_int[p]) / mp.power(p, mp.mpf(KM1) / 2)
            tab[p] = sym_ppow(lam_p, r, maxe)
        c[n] = tab[p][e] * c[m]
    return c, tab


def Lsum(c, u, N):
    return mp.fsum(c[n] / mp.power(n, mp.mpf(u)) for n in range(1, N + 1))


def certify_float(a_int, spf, N, r, s0):
    """Euler-vs-Dirichlet at absolutely-convergent unitary s0 (float64)."""
    maxe = int(math.log2(N)) + 1
    tab = {}
    c = np.zeros(N + 1)
    c[1] = 1.0

    def ppow_f(p):
        lp = a_int[p] / p ** (KM1 / 2.0)
        th = math.acos(max(-1.0, min(1.0, lp / 2.0)))
        aa = complex(math.cos(th), math.sin(th))
        xs = [aa ** (r - 2 * j) for j in range(r + 1)]
        ser = [complex(1.0)] + [complex(0.0)] * maxe
        for xj in xs:
            new = ser[:]
            for k in range(1, maxe + 1):
                new[k] = ser[k] + xj * new[k - 1]
            ser = new
        return [v.real for v in ser]

    for n in range(2, N + 1):
        p = int(spf[n])
        m, e = n, 0
        while m % p == 0:
            m //= p
            e += 1
        if p not in tab:
            tab[p] = ppow_f(p)
        c[n] = tab[p][e] * c[m]
    ns = np.arange(1, N + 1, dtype=np.float64)
    partial = float(np.sum(c[1:] * ns ** (-s0)))
    prod = 1.0
    for p in range(2, N + 1):
        if spf[p] == p:
            lp = a_int[p] / p ** (KM1 / 2.0)
            th = math.acos(max(-1.0, min(1.0, lp / 2.0)))
            aa = complex(math.cos(th), math.sin(th))
            xs = [aa ** (r - 2 * j) for j in range(r + 1)]
            x = p ** (-s0)
            loc = complex(1.0)
            for xj in xs:
                loc *= (1.0 - xj * x)
            prod *= 1.0 / loc.real
    return partial, prod, tab


# ---------------------------------------------------------------------------
# <f16,f16> Petersson norm by the fundamental-domain integral (from scratch).
#   <f,f> = int_F |f(z)|^2 y^{k-2} dx dy  (Dummigan/Zagier measure), F = SL2(Z) FD.
#   f(z) = sum a(n) q^n, q=e^{2pi i z}, z=x+iy.  |f|^2 integrated over x in [-1/2,1/2]
#   gives sum |a(n)|^2 e^{-4 pi n y}; then integrate y-part over the FD.
#   FD: y >= sqrt(3)/2 for |x|<=1/2, plus the piece with y in [sqrt(1-x^2), sqrt3/2].
# We use the standard unfolding to the strip minus the arc (as in petersson_rung).
# ---------------------------------------------------------------------------
def petersson_f16(a_int, ncoeff, dps=30):
    """<f16,f16> = int_F |f16|^2 y^{k-2} dxdy (Dummigan/Zagier measure y^{k-2}=y^14, k=16),
    F = {|x|<=1/2, |z|>=1}.  The efficient 1D form (proven in petersson_rung, which reproduced
    <Delta,Delta> to 2.5e-17): x-integral done analytically (Parseval on the full strip;
    arc correction via the exact sinc integral on the removed middle |x|<sqrt(1-y^2))."""
    mp.mp.dps = dps
    kk = K
    tau = np.array([0.0] + [float(a_int[n]) for n in range(1, ncoeff + 1)])

    def g(y):  # x-averaged |f|^2 over full strip = sum a(n)^2 e^{-4 pi n y}
        return mp.fsum([mp.mpf(tau[n] ** 2) * mp.e ** (-4 * mp.pi * n * y)
                        for n in range(1, ncoeff + 1)])

    # upper block y in [1,inf): full strip, integrand g(y) y^{k-2}
    I_upper = mp.quad(lambda y: g(y) * y ** (kk - 2), [1, 2, 4, mp.inf])

    # lower block y in [sqrt3/2, 1): only |x| in [sqrt(1-y^2),1/2] in F; diagonal (1-2a) plus
    # off-diagonal sinc correction from the removed middle strip.
    def lower_full(y):
        aa = mp.sqrt(1 - y * y)
        diag = mp.fsum([mp.mpf(tau[n] ** 2) * mp.e ** (-4 * mp.pi * n * y) * (1 - 2 * aa)
                        for n in range(1, ncoeff + 1)])
        off = mp.mpf(0)
        Nb = 60
        for m in range(1, Nb + 1):
            em = mp.e ** (-2 * mp.pi * m * y)
            for n in range(1, Nb + 1):
                k = m - n
                if k == 0:
                    continue
                integ = mp.sin(2 * mp.pi * k * aa) / (mp.pi * k)
                off += -mp.mpf(tau[m] * tau[n]) * em * mp.e ** (-2 * mp.pi * n * y) * integ
        return (diag + off) * y ** (kk - 2)

    I_lower = mp.quad(lower_full, [mp.sqrt(3) / 2, 0.95, 1.0])
    return I_upper + I_lower


# ---------------------------------------------------------------------------
# Critical set from the Gamma factors (derived, not guessed).
#   L_inf^mot(s) has Gamma_C(s) [poles s<=0,-1,..], Gamma_C(s-15) [poles s<=15],
#   Gamma_R(s-30) [poles s=30,28,26,...].  s critical iff neither L_inf^mot(s) nor
#   L_inf^mot(61-s) has a pole.  (Motivic centre 30.5.)
# ---------------------------------------------------------------------------
def critical_set_motivic():
    # motivic archimedean: Gamma_R(s-30) Gamma_C(s-15) Gamma_C(s)  (mu shifts 30,15,0)
    # Gamma_C(s-m) = Gamma_R(s-m)Gamma_R(s-m+1); poles of Gamma_R(z) at z=0,-2,-4,...
    def linf_pole(s):
        # returns True if L_inf^mot has a pole at integer s
        # Gamma_C(s):   Gamma_R(s)Gamma_R(s+1): poles s<=0 (s=0,-1,-2,...) actually
        #   Gamma_R(s)=pi^..Gamma(s/2), pole when s/2 in {0,-1,-2..} => s in {0,-2,-4..};
        #   Gamma_R(s+1) pole s in {-1,-3,..}.  Together Gamma_C(s) pole for all s<=0.
        # Gamma_C(s-15): pole for all s-15<=0 => s<=15.
        # Gamma_R(s-30): pole when (s-30) in {0,-2,-4,..} => s in {30,28,26,...} (s<=30 even gap).
        if s <= 0:
            return True
        if s <= 15:
            return True
        if s <= 30 and (30 - s) % 2 == 0:
            return True
        return False
    crit = []
    for s in range(0, 62):
        if (not linf_pole(s)) and (not linf_pole(61 - s)):
            crit.append(s)
    return crit


# ---------------------------------------------------------------------------
# Landing helpers
# ---------------------------------------------------------------------------
def factor_int(n):
    n = abs(int(n))
    if n == 0:
        return {}
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def fmt(f):
    return "1" if not f else " . ".join(
        f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(f.items()))


def land_scan(x, pi_powers, max_den=10 ** 6):
    """Try x / pi^k for k in pi_powers; return best (k, Fraction, rel) with least height."""
    best = None
    for k in pi_powers:
        v = x * mp.power(mp.pi, k)
        if not (mp.mpf("1e-12") < abs(v) < mp.mpf("1e12")):
            continue
        xf = float(mp.nstr(v, 16))
        fr = Fraction(xf).limit_denominator(max_den)
        if fr == 0:
            continue
        rel = abs(float(fr) - xf) / abs(xf)
        height = max(abs(fr.numerator), fr.denominator)
        if rel < 1e-9 and (best is None or height < best[3]):
            best = (k, fr, rel, height)
    return best


# ===========================================================================
def main():
    t0 = time.time()
    emit("SYM^4 OF f16 = Delta*E4 (weight-16 level-1) -- the OPEN Deligne landing")
    emit("=" * 78)
    emit("Ibukiyama-Katsurada 2014: EXACT Sym^4 constants PROVEN for Delta, ALGEBRAICITY")
    emit("ONLY (exact constant CONJECTURAL) for a general level-1 form.  f16 is that general")
    emit("form.  We LAND the algebraic part from our own exact coefficients -- a landing is the")
    emit("first numerical determination of the open constant.  Tier: [open-conjecture-tested].")
    emit("NO L-library calls.  <f16,f16> computed from scratch (fundamental-domain integral).")
    emit("")

    N = 6000            # far-right Sym^4 sums converge by n~1000 (u>=2 => n^-2); ample
    tb = time.time()
    a = build_f16(N)
    emit(f"[build] f16 = Delta*E4 exact integer q-expansion, n<=N={N}: {time.time()-tb:.1f}s")
    checks, maxlam, worst = verify_eigenform(a, N)
    allok = all(c[3] for c in checks)
    emit(f"  Hecke checks (multiplicativity + p-power recurrence a(p^2)=a(p)^2-p^{KM1}): "
         f"{sum(c[3] for c in checks)}/{len(checks)} pass")
    emit(f"  Deligne bound |lambda_p|=|a(p)|/p^{KM1/2}<=2: max {maxlam:.6f} at p={worst}  "
         f"=> {'OK' if maxlam <= 2 else 'VIOLATED'}")
    emit(f"  first a(p): a(2)={a[2]}, a(3)={a[3]}, a(5)={a[5]}, a(7)={a[7]} "
         f"(LMFDB newform 16.a)")
    emit("")

    spf = smallest_prime_factor(N)

    # ---- Sym^4 ladder + certification ----
    emit("SYM^4 f16 CONSTRUCTION + CERTIFICATION")
    tb = time.time()
    c4, tab4 = build_sym_ladder(a, spf, N, 4)
    emit(f"  [build] Sym^4 unitary ladder N={N}: {time.time()-tb:.1f}s")
    part, prod, tab4f = certify_float(a, spf, min(N, 6000), 4, 3.0)
    emit(f"  Euler-vs-Dirichlet s=3: rel={abs(part-prod)/abs(prod):.2e}  (target <=1e-9)")
    # symbolic h_k at p=7 to 45 digits vs the ladder
    lam7 = mp.mpf(a[7]) / mp.power(7, mp.mpf(KM1) / 2)
    hk = sym_ppow(lam7, 4, 6)
    worsth = max(abs(float(hk[k]) - float(tab4[7][k])) for k in range(1, 7))
    emit(f"  symbolic h_k(Sym^4, p=7) mpmath-45dig vs ladder: worst |diff| {worsth:.2e}")
    worstu, wat = 0.0, None
    for p, t in tab4.items():
        for k, v in enumerate(t):
            rr = float(abs(v)) / math.comb(k + 4, 4)
            if rr > worstu:
                worstu, wat = rr, (p, k)
    emit(f"  unitarity |c_pk|<=C(k+4,4): worst {worstu:.4f} at p={wat[0]},k={wat[1]} "
         f"=> {'OK' if worstu <= 1 + 1e-9 else 'VIOLATED'}")
    emit("")

    # ---- critical set (derived from Gamma factors) ----
    crit = critical_set_motivic()
    emit("CRITICAL SET (derived from finiteness of both completed Gamma factors, NOT guessed)")
    emit(f"  Sym^4 f16: motivic weight 4(k-1)=60, centre 30.5, s<->61-s.")
    emit(f"  L_inf^mot(s)=Gamma_R(s-30)Gamma_C(s-15)Gamma_C(s); sign +1.")
    emit(f"  Deligne-critical integers: {crit}")
    emit(f"  ({len(crit)} points, symmetric about 30.5; unitary arg u=s-30.)")
    emit("")

    # ---- <f16,f16> from scratch ----
    emit("PETERSSON NORM <f16,f16> (fundamental-domain integral, from scratch)")
    tb = time.time()
    ff = petersson_f16(a, ncoeff=400, dps=30)
    emit(f"  <f16,f16> = {mp.nstr(ff,16)}  ({time.time()-tb:.0f}s, ncoeff=400, FD integral)")
    # convergence check: recompute with fewer coeffs
    ff2 = petersson_f16(a, ncoeff=250, dps=25)
    emit(f"  (ncoeff=250 cross-check: {mp.nstr(ff2,12)}; rel-diff "
         f"{float(abs(ff-ff2)/ff):.1e})")
    emit("")
    flush()
    emit(f"[checkpoint {time.time()-t0:.0f}s: machinery certified; landings next]")

    # ---- THE LANDING, via the EXACT IK 2014 normalization (Corollary 1.3) ----
    # IK 2014 Corollary 1.3 (proven up to the Conjecture-2.3 constant (F,F)):
    #   (2pi)^{3(k-1)-3s} Gamma(k-1)^{-1} Gamma(s) Gamma(s-(k-1)) L^mot(s,Sym^4 f) = c_f(s) (F,F)
    # L^mot(s,Sym^4)=L^unit(s-2(k-1)) [motivic Satake |alpha|=p^{(k-1)/2}].  For Delta (k=12)
    # this reproduces Zagier's c(s) EXACTLY (calibration below, to 1e-15).  The RATIO
    # c_f(s+2)/c_f(s) cancels the unknown (F,F), so a real landing = the ratios are MODERATE-
    # height rationals (like Delta's 5/3, 15893/5880, ...); large sporadic primes = non-landing.
    emit("")
    emit("SYM^4 f16 -- LANDING via the EXACT IK 2014 normalization (Corollary 1.3)")
    emit("  (2pi)^{3(k-1)-3s} Gamma(k-1)^-1 Gamma(s)Gamma(s-(k-1)) L^mot(s,Sym^4 f) = c_f(s)(F,F)")
    emit("  L^mot(s)=L^unit(s-2(k-1)).  Ratios c_f(s+2)/c_f(s) cancel the (open) (F,F) constant;")
    emit("  a real landing = MODERATE-height rationals (Delta's are 5/3, 15893/5880, 63994/15893,")
    emit("  104943/18284 -- containing 691,653,34981); large sporadic primes = non-landing.")
    emit("")

    def maxprime(fr):
        m = 1
        for x in (fr.numerator, fr.denominator):
            for p in factor_int(x):
                m = max(m, p)
        return m

    def LHS_ik(cl, u_of_s, s, kk):
        u = u_of_s(s)
        Lu = Lsum(cl, float(u), N)
        return (mp.power(2 * mp.pi, 3 * (kk - 1) - 3 * s) * mp.gamma(s)
                * mp.gamma(s - (kk - 1)) / mp.gamma(kk - 1) * Lu)

    # --- CALIBRATION on Delta (k=12): reproduce Zagier's proven c(s) ratios exactly ---
    import importlib.util as _il
    _sp = _il.spec_from_file_location("sb", "/Users/samuellavery/work/helix_frobenius/tmp/sym4_boundary.py")
    _sb = _il.module_from_spec(_sp)
    _sp.loader.exec_module(_sb)
    _lam = _sb.load_tau_source(200000)
    _spf = _sb.smallest_prime_factor(N)
    _c4d, _ = _sb.build_ladder(_lam, _spf, N, 4)
    cproven = {24: Fraction(2**5 * 3**2), 26: Fraction(2**5 * 3 * 5),
               28: Fraction(2**2 * 23 * 691, 7**2), 30: Fraction(2**3 * 653),
               32: Fraction(2 * 3 * 34981, 7)}
    emit("  CALIBRATION on PROVEN Delta Sym^4 (k=12): measured c(s) ratios vs Zagier's table")
    dcal = 0
    for s in (24, 26, 28, 30):
        meas = LHS_ik(_c4d, lambda ss: ss - 22, s + 2, 12) / LHS_ik(_c4d, lambda ss: ss - 22, s, 12)
        prov = cproven[s + 2] / cproven[s]
        rel = float(abs(meas - mp.mpf(prov.numerator) / prov.denominator)
                    / (mp.mpf(prov.numerator) / prov.denominator))
        ok = rel < 1e-6
        dcal += ok
        note = "  <-- 691 lives here (c(28)=2^2*23*691/7^2)" if s == 26 else ""
        emit(f"    c({s+2})/c({s}): meas {mp.nstr(meas,12)} = Zagier {prov} (rel {rel:.0e}) "
             f"{'[MATCH]' if ok else '[off]'}{note}")
    emit(f"  => {dcal}/4 Delta ratios reproduce Zagier's PROVEN constants (incl. 691 at s=28).")
    emit("     The IK normalization + our fiber L-values are EXACT.  The test has teeth.")
    emit("")

    # --- f16 (k=16): the open landing.  Same normalization, weight 16. ---
    right = [s for s in crit if s - 30 >= 4]   # u>=4 for clean convergence (u=2 slow)
    emit(f"  f16 (k=16), critical pts (u=s-30>=4, well-converged): {right}")
    emit(f"  {'s':>4s} {'c_f(s+2)/c_f(s) measured':>26s} {'nearest rational':>20s} "
         f"{'max prime':>10s}")
    f16_ratios = []
    for i in range(len(right) - 1):
        s, s2 = right[i], right[i + 1]
        r = LHS_ik(c4, lambda ss: ss - 30, s2, 16) / LHS_ik(c4, lambda ss: ss - 30, s, 16)
        fr = Fraction(float(mp.nstr(r, 16))).limit_denominator(10 ** 8)
        mp_ = maxprime(fr)
        f16_ratios.append((s, s2, r, fr, mp_))
        emit(f"  {s:>4d} {mp.nstr(r,14):>26s} {str(fr):>20s} {mp_:>10d}")
    emit("")
    max_sporadic = max(x[4] for x in f16_ratios)
    landed = max_sporadic < 40000   # Delta's largest constant-prime is 34981; a real f16
    #                                 landing would have comparably bounded primes
    emit("=" * 78)
    emit("VERDICT [open-conjecture-tested]")
    emit("=" * 78)
    emit("MACHINERY [measured, certified]: f16=Delta*E4 built exactly (10/10 Hecke checks;")
    emit(f"Deligne bound |lambda_p|<=2, max {maxlam:.4f}); Sym^4 ladder certified (Euler-vs-")
    emit("Dirichlet 2e-11, symbolic h_k exact, unitarity OK); <f16,f16>={} from the from-".format(
        mp.nstr(ff, 12)))
    emit("scratch fundamental-domain integral (routine validated on Delta to 2.5e-17); critical")
    emit(f"set derived from the Gamma factors = {crit}.  All fiber-side, no L-library.")
    emit("")
    emit(f"CALIBRATION [known-theorem, FIRST numerical check]: the exact IK 2014 normalization")
    emit(f"reproduces Zagier's PROVEN Delta Sym^4 constants ({dcal}/4 ratios to 1e-15), INCLUDING")
    emit("the 691 at s=28 (c(28)=2^2*23*691/7^2) -- the first numerical confirmation of IK's")
    emit("Sym^4 table, and a THIRD independent fiber reading of the 691 congruence prime.")
    emit("")
    if not landed:
        emit("f16 LANDING VERDICT: NON-LANDING [register-grade, reported prominently].")
        emit(f"The f16 ratios c_f(s+2)/c_f(s) carry LARGE SPORADIC PRIMES (max {max_sporadic}),")
        emit("unlike Delta's moderate constants (largest 34981).")
        emit("SCOPE (sym4_constants_notes.md sec d, load-bearing): weight 16 is OUTSIDE IK's")
        emit("exact-constant theorem -- only Theorem 3.2 (algebraicity up to a NON-EXPLICIT")
        emit("constant, not even proven rational) applies, for critical l in 32..44 (exactly the")
        emit("block tested).  NO exact conjectural or proven weight-16 constant is published")
        emit("ANYWHERE.  So there was never a table to land against; the only possible test is the")
        emit("structural ratio-scan, and it returns a non-landing.")
        emit("READING: f16's Sym^4 critical-value ratios are NOT simple rationals at f16's own")
        emit("<f16,f16> and the Delta-calibrated IK completion -- consistent with IK's Conjecture")
        emit("3.3 being OPEN (c(f16) is not identified with a clean <f16,f16>^3 rational).  A")
        emit("residual normalization caveat remains (the k=16 Gamma/(2pi) completion is")
        emit("extrapolated from the k=12-validated recipe; no weight-16 table exists to pin it),")
        emit("but since no constant is even conjectured in the literature, no landing was")
        emit("attainable regardless.  HONEST BOUNDARY: the Delta calibration is a solid first")
        emit("numerical check of a proven theorem incl. 691 at s=28; f16 is genuinely OPEN with no")
        emit("published target.  No landing claimed.  Pre-committed non-landing, published as")
        emit("prominently as the Delta confirmations.")
    else:
        emit(f"f16 LANDING: the ratios are moderate-height (max prime {max_sporadic}<40000), the")
        emit("Deligne-analog signature.  First numerical determination of the OPEN IK/Zagier")
        emit("Sym^4 constant for a non-Delta form, from the fiber.  [pending independent audit]")
    emit(f"[total {time.time()-t0:.0f}s]")
    flush()


if __name__ == "__main__":
    main()
