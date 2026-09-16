#!/usr/bin/env python3
"""
helix_extractor.py -- the random-access zero finder on the helix / carrier / fiber.

    given i, return the height of the i-th vanishing, computed on the geometric objects.

COMPLEXITY.  NOT constant time.  Measured, not assumed (ledger 819):
  * stage 1, coarse location, is O(polylog i): one inversion of the archimedean winding.
  * stage 3, the bank, is LINEAR IN THE ORDINATE.  The lane sign (-1)^{n-1} puts a pi*n in the term
    phase pi*n - T log(Delta n), whose derivative pi - T/n vanishes at a genuine stationary point
    n* = T/pi.  The head window's flat core must contain it, so X > 2T/pi.  Measured minimal head
    X_min/(2T/pi) = 2.12, 1.09, 0.98 at T = 143, 1419, 5000 -- converging to 2/pi -- while
    X_min/sqrt(T) GROWS (16.1, 26.1, 44.2).  So it is Theta(T), not O(sqrt T).
  * T = gamma_i ~ 2 pi i / log i, so the query cost is Theta(i / log i) terms.
A two-ended (approximate functional equation) head would be O(sqrt T), but its moment error analysis
is not the one measured here, so it is not what this tool runs.

THE OBJECTS (as the compiled modules define them).
  CARRIER.  Scale Delta (default pi/3); site n at arclength x_n = Delta n; phasor x_n^{-s}.
  LANES.    Odd sites P, even sites M, entering with opposite sign: the (-1)^{n-1}.
  FIBER.    F(s) = sum_n (-1)^{n-1} x_n^{-s} = Delta^{-s} (1 - 2^{1-s}) zeta(s).
  WELD.     w(t) = Delta^{-(1/2+it)} (1 - 2^{1/2-it}) / Gamma_R(1/2+it), and
            e^{-i arg w} F(1/2+it) = |w(t)| * Lambda(1/2+it)  is REAL
            (CarrierParityQuantization.weld_gauge_exact / weld_gauge_im_zero).
  READOUT.  u(t) = that real number.  Its zeros are exactly the on-line zeros of zeta
            (weldReadout_eq_zero_iff); its sign flips by (-1)^m across an event of multiplicity m
            (weldReadout_sign_flip); the sign is the same for every Delta > 0
            (weldReadout_sign_carrier_free).

WHAT IS CERTIFIED AND WHAT IS NOT.
  CERTIFIED by compiled theorems, GIVEN the count (ZeroEnclosure.lean, standard axioms, no sorry):
    count(a) = i-1 and count(b) = i  =>  a UNIQUE event in (a,b), and it is SIMPLE
                                         (unique_event_of_count_eq_one)
                                     =>  u(a) u(b) < 0, so bisection must make progress
                                         (sign_change_of_count_eq_one)
                                     =>  ANY sign-change sub-bracket holds that event
                                         (event_mem_of_sign_bracket)
    so the returned bracket is a certified enclosure of gamma_i.
  NOT CERTIFIED:
    (1) the count itself.  It is a swappable interface (CountRoutine).  This tool fills it with
        Selberg prime clocks plus the fiber's own parity bit; |S_x - S| < 1 is measured (max 0.518,
        ledger 812) and NOT proved.
    (2) the jet radius.  ratio_enclosure is compiled, but its alpha/beta need a tail bound that
        needs a zero-density input.  The jet estimate is reported with a MEASURED, not certified,
        radius; the certified interval comes from the sign bracket, which needs no tail bound.
    (3) float64.  The phase T log(Delta n) carries absolute error ~ T log(X) * 2.2e-16, which at
        i = 1e6 is ~2e-9 rad and limits the ordinate to ~1e-10.  Reported per run.
"""
import argparse, math, os, sys, time
import numpy as np
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harmonic_pencil import pencil as _pencil, nodes_to_y as _nodes_to_y

TWOPI = 2.0*math.pi

# ---------------------------------------------------------------- stage 1: the archimedean winding
def winding(T):
    """theta(T) = arg_cont Gamma_R(1/2+iT), the archimedean local factor's own winding.
    = Im loggamma(1/4 + iT/2) - (T/2) log pi.  No asymptotic series."""
    T = mp.mpf(T)
    return float(mp.im(mp.loggamma(mp.mpf(1)/4 + 1j*T/2)) - (T/2)*mp.log(mp.pi))

def winding_inverse(v):
    """solve theta(T) = v.  Lambert-W seed, then Newton on theta' = (1/2) log(T/2pi)."""
    A = v + math.pi/8.0
    c = A/(math.pi*math.e)
    T = float(2.0*A/mp.lambertw(c).real) if c > -1.0/math.e else 14.0
    T = max(T, 9.7)
    for _ in range(200):
        step = (winding(T) - v)/(0.5*math.log(T/TWOPI))
        T -= step
        if abs(step) < 1e-13*max(1.0, abs(T)):
            break
    return T

def mean_spacing(T):
    return TWOPI/math.log(T/TWOPI)

# ---------------------------------------------------------------- stage 2: the count interface
def prime_powers(X):
    sieve = np.ones(X+1, dtype=bool); sieve[:2] = False
    for i in range(2, int(X**0.5)+1):
        if sieve[i]: sieve[i*i::i] = False
    lam = np.zeros(X+1)
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= X:
            lam[q] = math.log(p); q *= int(p)
    idx = np.nonzero(lam)[0]
    return idx, lam[idx]

class Clocks:
    """Selberg-smoothed prime clocks: the fiber's phasors at the prime frequencies."""
    def __init__(self, x=100):
        X = x*x*x
        idx, lam = prime_powers(X)
        lx = math.log(x); lx2 = lx*lx
        w = np.ones_like(lam)
        mid = (idx > x) & (idx <= x*x)
        hi = idx > x*x
        w[mid] *= (np.log(X/idx[mid])**2 - 2.0*np.log(x*x/idx[mid])**2)/(2.0*lx2)
        w[hi] *= np.log(X/idx[hi])**2/(2.0*lx2)
        self.logm = np.log(idx.astype(float))
        self.w = lam*w/(np.sqrt(idx.astype(float))*self.logm)
        self.terms = len(idx)
    def S(self, t):
        return float(-(np.sin(t*self.logm)*self.w).sum()/math.pi)

# ---------------------------------------------------------------- stage 3: the bank, one pass
def taper(u, a=0.5):
    """C^infinity partition-of-unity window: flat to u = a, smoothly to 0 at u = 1."""
    w = np.zeros_like(u); w[u <= a] = 1.0
    m = (u > a) & (u < 1.0)
    if m.any():
        x = (1.0-u[m])/(1.0-a)
        f1 = np.exp(-1.0/np.clip(x, 1e-300, None)); f2 = np.exp(-1.0/np.clip(1.0-x, 1e-300, None))
        w[m] = f1/(f1+f2)
    return w

# the measured collapse (ledger 821):  |Mtilde_r - M_r|/|M_r| ~ exp(-c sqrt(pi X/2 - T)),
# c = 1.43 +- 0.03 for T >= 143, uniform in r <= 10 and in Delta.  Inverting for a target tol:
#     pi X/2 - T >= (ln(1/tol)/c)^2  =>  X >= 2(T + K)/pi,  K = (ln(1/tol)/c)^2.
# So the head is 2T/pi + O(1): the saddle sets the slope, the tolerance only sets the offset.
C_COLLAPSE = 1.43
def head_offset(tol):
    return (math.log(1.0/tol)/C_COLLAPSE)**2

class Bank:
    """the P/M-lane-balanced phasor bank on the Delta-carrier.  Head law from ledger 821."""
    def __init__(self, delta=math.pi/3, tol=1e-16, mmax=11):
        self.delta, self.tol, self.mmax = delta, tol, mmax
        self.K = head_offset(tol)
        self.terms = 0; self.passes = 0
        self._X = None
    def head(self, T):
        """X = 2(T + K)/pi: past the lane saddle n* = T/pi by enough for the target tolerance."""
        return max(256, int(math.ceil(2.0*(T + self.K)/math.pi)) + 8)
    def _prep(self, X):
        if X != self._X:
            n = np.arange(1, X+1, dtype=np.float64)
            x = self.delta*n
            amp = taper(n/X)*np.where(n % 2 == 1, 1.0, -1.0)/np.sqrt(x)
            self._X, self._lx, self._amp = X, np.log(x), amp
        return self._lx, self._amp
    def moments(self, T, X=None, mmax=None):
        """M_r = l(H^r v) for r = 0..mmax, in ONE pass over the head."""
        if X is None: X = self.head(T)
        if mmax is None: mmax = self.mmax
        lx, amp = self._prep(X)
        self.passes += 1; self.terms += X
        base = amp*np.exp(-1j*T*lx)
        out = np.empty(mmax+1, dtype=complex)
        cur = base.copy()
        for r in range(mmax+1):
            out[r] = cur.sum()
            if r < mmax: cur *= lx
        return out
    def F(self, T, X=None):
        return self.moments(T, X, mmax=0)[0]

def weld_phase(T, delta):
    """psi(T) = -arg w(T) = arg Gamma_R(1/2+iT) + arg(1-2^{1/2+iT}) + T log Delta."""
    return (winding(T) + math.atan2(-(2.0**0.5)*math.sin(T*math.log(2.0)),
                                    1.0 - (2.0**0.5)*math.cos(T*math.log(2.0)))
            + T*math.log(delta))

def readout(bank, T):
    """u(T) = Re(e^{i psi} F) -- real by weld_gauge_im_zero; sign is Delta-free."""
    return float(np.real(np.exp(1j*weld_phase(T, bank.delta))*bank.F(T)))

# ---------------------------------------------------------------- stage 4: moments -> log jets
def jets(M, mmax):
    """f_k = G^{(k)}/G = (-i)^k M_k/M_0; cumulant recursion; A_m = ((-1)^{m-1}/(m-1)!) L_m."""
    f = [((-1j)**k)*M[k]/M[0] for k in range(mmax+1)]
    L = [0j]*(mmax+1)
    for m in range(1, mmax+1):
        acc = f[m]
        for j in range(1, m):
            acc -= math.comb(m-1, j-1)*L[j]*f[m-j]
        L[m] = acc
    return [None] + [((-1)**(m-1)/math.factorial(m-1))*L[m] for m in range(1, mmax+1)]

# ---------------------------------------------------------------- the driver
def find_bracket(i, seed, sp, cbank, clocks, anchor):
    """Count is monotone non-decreasing, so BISECT on the predicate Count(t) >= i.

    A fixed-step march fails at a close pair: at Lehmer's pair (i = 6709/6710) the window where
    Count = 6709 is 0.0377 wide against a mean spacing of 0.895 -- 0.042 of a spacing -- so a step
    of 0.30 spacings walks straight over it.  Bisection cannot: it halves until each endpoint lands
    in its own window, however narrow."""
    lo = hi = seed
    w = 0.6*sp
    for _ in range(60):
        if count_at(lo, cbank, clocks, anchor) < i: break
        lo -= w; w *= 1.6
    else:
        return None
    w = 0.6*sp
    for _ in range(60):
        if count_at(hi, cbank, clocks, anchor) >= i: break
        hi += w; w *= 1.6
    else:
        return None
    for _ in range(200):
        if (count_at(lo, cbank, clocks, anchor) == i-1
                and count_at(hi, cbank, clocks, anchor) == i):
            return lo, hi
        mid = 0.5*(lo+hi)
        if count_at(mid, cbank, clocks, anchor) >= i: hi = mid
        else: lo = mid
        if hi - lo < 1e-13*max(1.0, abs(mid)): return None
    return None

def count_at(T, bank, clocks, anchor):
    """Count(T): the clock estimate, snapped to the parity the fiber reads.  THE INTERFACE."""
    v = winding(T)/math.pi + 1.0 + clocks.S(T)
    q = (np.angle(bank.F(T)) + weld_phase(T, bank.delta))/math.pi
    par = (int(round(q)) + anchor) % 2
    cands = np.arange(math.floor(v)-2, math.floor(v)+3)
    ok = cands[(cands % 2) == par]
    return int(ok[np.argmin(np.abs(ok - v))])

def calibrate(bank, clocks):
    """the parity anchor, from direct enumeration on a low window -- no table, no Gram."""
    lo, hi, step = 1.0, 25.0, 0.05
    ts = np.arange(lo, hi, step)
    us = np.array([readout(bank, t) for t in ts])
    n_below = int(np.sum(us[:-1]*us[1:] < 0))          # events in (1, 25)
    T0 = 24.0
    q = (np.angle(bank.F(T0)) + weld_phase(T0, bank.delta))/math.pi
    return (n_below - int(round(q))) % 2

def noise_floor(bank, T, umax):
    """what the arithmetic can support: the head's own tolerance plus float64 phase error.
    Reporting a bracket tighter than this would be a false certificate."""
    X = bank.head(T)
    phase = T*math.log(bank.delta*X)*2.2e-16*math.sqrt(X)   # accumulated float64 phase error
    return umax*(bank.tol + phase) + 1e-300

def gap_rank(S):
    """rank from the largest GAP in the singular-value profile, not a fixed threshold."""
    r = S/S[0]
    ratios = [r[k]/r[k+1] for k in range(len(r)-1) if r[k+1] > 0]
    return (int(np.argmax(ratios))+1) if ratios else 1

def height(i, bank, cbank, clocks, anchor, mm=9, K=8):
    rep = {'i': i}
    t0 = time.time()
    # -- stage 1: coarse location from the archimedean winding alone, O(polylog i)
    seed = winding_inverse((i - 1.5)*math.pi)
    sp = mean_spacing(seed)
    rep['seed'] = seed; rep['spacing'] = sp
    rep['head'] = bank.head(seed)
    # -- stage 2: the bracket, from the count INTERFACE.  A cheap bank suffices here: the parity
    #    bit only needs |Psi/pi - round| < 1/2, measured to 1e-9 even at 1e-5 cells from an event.
    br = find_bracket(i, seed, sp, cbank, clocks, anchor)
    if br is None:
        rep['a'], rep['b'] = seed - 1.2*sp, seed + 1.2*sp
        rep['Na'] = rep['Nb'] = -1; rep['count_ok'] = False
        a, b = rep['a'], rep['b']
    else:
        a, b = br
        rep['a'], rep['b'] = a, b
        rep['Na'], rep['Nb'] = i-1, i
        rep['count_ok'] = True
    # -- narrow by three bisections BEFORE taking jets, so the anchor is nearer the target than
    #    any neighbour (otherwise the jet ratio localises the wrong event -- seen at i = 100)
    lo, hi = a, b
    flo = readout(bank, lo); umax = abs(flo)
    for _ in range(3):
        mid = 0.5*(lo+hi); fm = readout(bank, mid); umax = max(umax, abs(fm))
        if flo*fm < 0: hi = mid
        else: lo, flo = mid, fm
    rep['narrow'] = (lo, hi)
    # -- stages 3+4: ONE bank pass at the anchor -> all moments -> the jets
    y0 = 0.5*(lo+hi)
    # one pass, enough moments for BOTH the ratio and the pencil (the extra orders are one
    # multiply-accumulate per term each)
    MM = max(mm+1, 2*K+2)
    M = bank.moments(y0, mmax=MM)
    A = jets(M, MM)
    d_hat = (A[mm]/A[mm+1]).real
    ghat = y0 - d_hat
    rep['y0'] = y0; rep['jet_m'] = mm; rep['jet'] = ghat
    rep['jet_in_bracket'] = (lo <= ghat <= hi)
    # -- the 3D harmonic pencil: eigenvalues and rank drop from the same moment vector.
    #    A node y = gamma - i(beta - 1/2), so Im(y) reports the abscissa directly.
    try:
        ev, S = _pencil(A, K, scale=max(hi-lo, 1e-12), m0=1)
        ys = sorted(_nodes_to_y(ev, y0), key=lambda z: abs(z-y0))
        rep['pencil'] = ys[0]
        rep['pencil_im'] = float(ys[0].imag)
        rep['pencil_beta'] = 0.5 - float(ys[0].imag)
        rep['pencil_rank'] = gap_rank(S)
        rep['pencil_gap'] = float(S[0]/max(S[1], 1e-300))
        rep['pencil_nodes'] = ys[:4]
    except Exception as e:
        rep['pencil'] = None; rep['pencil_im'] = float('nan')
        rep['pencil_rank'] = -1; rep['pencil_gap'] = float('nan')
        rep['pencil_beta'] = float('nan'); rep['pencil_nodes'] = []
    # -- stage 5: certify a TIGHT bracket around the jet estimate.  The compiled
    #    event_mem_of_sign_bracket says any sign-change sub-bracket of (a,b) holds the unique
    #    event, so two evaluations around a good estimate beat forty bisections.
    fl = readout(bank, lo); fh = readout(bank, hi)
    umax = max(umax, abs(fl), abs(fh))
    floor = noise_floor(bank, seed, umax)
    if lo <= ghat <= hi:
        d0 = 1e-13*max(1.0, abs(ghat))
        for _ in range(40):
            c, d = max(lo, ghat-d0), min(hi, ghat+d0)
            uc, ud = readout(bank, c), readout(bank, d)
            umax = max(umax, abs(uc), abs(ud)); floor = noise_floor(bank, seed, umax)
            if uc*ud < 0 and min(abs(uc), abs(ud)) > floor:
                lo, hi, fl, fh = c, d, uc, ud
                break
            d0 *= 3.0
            if d0 > (hi-lo): break
    rep['floor'] = floor
    rep['fast'] = (hi-lo) < 0.5*(rep['narrow'][1]-rep['narrow'][0])
    for _ in range(80):
        mid = 0.5*(lo+hi); fm = readout(bank, mid); umax = max(umax, abs(fm))
        floor = noise_floor(bank, seed, umax)
        if abs(fm) <= floor: break              # below the floor the sign is not trustworthy
        if fl*fm < 0: hi, fh = mid, fm
        else: lo, fl = mid, fm
        if hi - lo <= 4*np.finfo(float).eps*max(1.0, abs(mid)): break
    rep['lo'], rep['hi'] = lo, hi
    rep['event'] = 0.5*(lo+hi)
    rep['radius'] = 0.5*(hi-lo)
    rep['u_lo'], rep['u_hi'] = fl, fh
    rep['certified'] = (fl*fh < 0 and min(abs(fl), abs(fh)) > floor)
    rep['secs'] = time.time()-t0
    return rep

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('indices', nargs='*', type=int, default=[1, 10, 100, 1000, 10000])
    ap.add_argument('--delta', type=float, default=math.pi/3)
    ap.add_argument('--tol', type=float, default=1e-16, help='head tolerance -> X = 2(T+K)/pi')
    ap.add_argument('--x', type=int, default=100, help='Selberg x for the clocks')
    ap.add_argument('--m', type=int, default=9, help='jet order')
    ap.add_argument('--verify', action='store_true')
    ap.add_argument('--scales', action='store_true', help='rerun on several carrier scales')
    args = ap.parse_args()

    bank  = Bank(delta=args.delta, tol=args.tol)
    cbank = Bank(delta=args.delta, tol=1e-6)      # cheap bank: counting only needs the parity bit
    t0 = time.time(); clocks = Clocks(args.x); tc = time.time()-t0
    anchor = calibrate(bank, clocks)
    print(f"# carrier Delta = {args.delta:.6f}   head X = 2(T + K)/pi, K = {bank.K:.0f}"
          f" for tol {args.tol:g}   (lane saddle n* = T/pi)")
    print(f"# cheap count bank: K = {cbank.K:.0f}")
    print(f"# clocks: Selberg x = {args.x}, {clocks.terms:,} prime powers ({tc:.1f}s), parity anchor {anchor}")
    print(f"# certified GIVEN the count (ZeroEnclosure.lean); the count itself is the interface\n")
    for i in args.indices:
        b0 = bank.terms + cbank.terms; p0 = bank.passes + cbank.passes
        r = height(i, bank, cbank, clocks, anchor, mm=args.m)
        used = bank.terms + cbank.terms - b0; np_ = bank.passes + cbank.passes - p0
        print(f"i = {i}")
        print(f"   stage 1  archimedean seed   {r['seed']:.9f}   (mean spacing {r['spacing']:.4f})")
        print(f"   stage 2  bracket [{r['a']:.6f}, {r['b']:.6f}]   Count(a)={r['Na']} Count(b)={r['Nb']}"
              f"   {'OK' if r['count_ok'] else '** interface did not reach i-1 / i **'}")
        print(f"   stage 4  jet estimate (m={r['jet_m']}, ONE pass)  {r['jet']:.12f}"
              f"   {'' if r['jet_in_bracket'] else '(outside the narrowed bracket)'}")
        print(f"   stage 5  enclosure [{r['lo']:.12f}, {r['hi']:.12f}]   radius {r['radius']:.2e}"
              f"   {'CERTIFIED' if r['certified'] else 'NOT certified (hit the arithmetic floor)'}")
        if r.get('pencil') is not None:
            print(f"   pencil   rank {r['pencil_rank']} (sv gap {r['pencil_gap']:.1e})   "
                  f"node {r['pencil'].real:.12f} {r['pencil_im']:+.2e}i   "
                  f"beta = {r['pencil_beta']:.15f}")
        print(f"   cost     {np_} bank passes x {r['head']:,} terms = {used:,}   ({r['secs']:.2f}s)"
              f"   |jet - event| = {abs(r['jet']-r['event']):.2e}")
        if args.verify:
            ref = float(mp.im(mp.zetazero(i)))
            inside = (r['lo'] <= ref <= r['hi'])
            print(f"   verify   zetazero({i}) = {ref:.12f}   |err| = {abs(r['event']-ref):.2e}"
                  f"   inside the interval? {'YES' if inside else 'NO'}")
        print()
        sys.stdout.flush()
    if args.scales:
        print("=== the same indices on five carrier scales (the bit is Delta-free) ===")
        for D in [math.pi/6, math.pi/3, 1.0, 2.0, 30.0]:
            bk = Bank(delta=D, tol=args.tol); ck = Bank(delta=D, tol=1e-6)
            an = calibrate(bk, clocks)
            vals = [height(i, bk, ck, clocks, an, mm=args.m)['event'] for i in args.indices]
            print(f"   Delta = {D:8.5f}: " + "  ".join(f"{v:.9f}" for v in vals))

if __name__ == '__main__':
    main()
