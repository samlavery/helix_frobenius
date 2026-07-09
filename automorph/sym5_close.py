"""sym5_close.py  --  Analytic close attempt for Sym^5 functoriality on GL(6).

GOAL (converse-theorem route, ANALYTIC, Galois-free): establish the converse-theorem
inputs for L(s, Sym^5 pi x sigma), pi = Delta (weight 12, level 1), sigma ranging over
GL(1) (Dirichlet chi), GL(2), GL(3), GL(4).  The CRUX is input (c): does the convolution
FUNCTIONAL EQUATION emerge NON-CIRCULARLY -- root number eps as OUTPUT, never fed -- from
the two factors' LOCAL data (Satake angles + archimedean type + conductor) alone?

INSTRUMENT (fixes the broken pinning of convolution_fe_tensorweld.py, which never locked
even on the Sym^r Delta validation ladder because a one-sided tapered sum is mistuned for
high archimedean conductor):  the double-ended completion is realised as Riemann's
theta/Mellin integral (afe.py's proven kernel, generalised to degree d with large shifts).

    Lambda(s) = int_0^inf Theta(u) u^s du/u,   Theta(u) = sum_n a_n K(n u / sqrt(N)),
    K = inverse-Mellin of gamma(s) = prod_j Gamma_R(s + mu_j)          (mu_j = LOCAL data).

Split at u=1 and use the reflection u->1/u:
    Lambda(s) = A(s) + eps A(1-s),   A(sigma) := int_1^inf Theta(u) u^sigma du/u,
IF (and only if) the FE Theta(1/u) = eps u Theta(u) holds  (helix<->anti-helix conjugation
over the origin; ClockDipDuality/warpedBlock det-1 weld).  A(s), A(1-s) need Theta ONLY for
u>=1 (few terms, K decays super-exponentially) -- the numerically-robust regime.

EMERGENT eps (non-circular):  at s0 with Re(s0) > 1 the honest convergent completed value
Lambda_true(s0) = gamma(s0) N^{s0/2} sum a_n n^{-s0} is known WITHOUT any FE.  Then
    eps(s0) = ( Lambda_true(s0) - A(s0) ) / A(1-s0)
is SOLVED.  eps is the OUTPUT.  If the FE holds, eps(s0) is unimodular and CONSTANT across
several s0 (and lands on the mu6/pi-3 harmonic phase grid); if not, eps(s0) drifts.  The
known eps enters ONLY as a post-hoc comparison column.

CIRCULARITY DISCIPLINE: inputs are (i) Satake angles of Delta and of the sigma-form (exact
tau / eigenform recurrence), (ii) the tensor rule, (iii) each factor's archimedean Langlands
type and conductor (local).  NEVER the convolution's eps, NEVER "Sym^5 pi is automorphic",
NEVER the classical Rankin-Selberg integral (which would need that automorphy).

Scope: finite validated instances; no RH/GRH assumed or proved.
Run: python3 sym5_close.py [test|full]
"""
import math, os, sys, time
import numpy as np
import mpmath as mp

mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "sym5_close_results.txt")
PI3 = math.pi / 3.0

_lines = []
def emit(s=""):
    _lines.append(s); print(s, flush=True)
def _flush(path=RESULTS):
    with open(path, "w") as fh:
        fh.write("\n".join(_lines) + "\n")


# ===========================================================================
# Exact arithmetic: tau(n), Eisenstein, level-1 eigenforms f_k = Delta * E_{k-12}
# ===========================================================================
def sigma_sieve(N, s):
    sig = [0] * (N + 1)
    for d in range(1, N + 1):
        ds = d ** s
        for n in range(d, N + 1, d):
            sig[n] += ds
    return sig

def tau_exact(N):
    sig1 = np.array(sigma_sieve(N, 1), dtype=object)
    c = np.zeros(N + 1, dtype=object); c[0] = 1
    for m in range(1, N + 1):
        acc = int(np.dot(sig1[1:m + 1], c[m - 1::-1]))
        val = -24 * acc
        assert val % m == 0, ("tau non-integer", m)
        c[m] = val // m
    tau = np.zeros(N + 1, dtype=object)
    for n in range(1, N + 1):
        tau[n] = c[n - 1]
    return tau

EIS_CONST = {0: None, 4: 240, 6: -504, 8: 480}
def eisenstein_coeffs(w, N):
    e = np.zeros(N + 1, dtype=object); e[0] = 1
    if w == 0:
        return e
    Cw = EIS_CONST[w]; sig = sigma_sieve(N, w - 1)
    for m in range(1, N + 1):
        e[m] = Cw * sig[m]
    return e

def eigenform_coeffs(tau, k, N):
    """a_n = [q^n] (Delta * E_{k-12}); a_1 = 1.  Level 1, weight k."""
    w = k - 12
    if w == 0:
        a = np.array(tau, dtype=object)
    else:
        full = np.convolve(np.asarray(tau, dtype=object), eisenstein_coeffs(w, N))
        a = full[:N + 1]
    assert a[1] == 1, ("not normalized", k)
    return a

def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]

def smallest_prime_factor(N):
    spf = np.zeros(N + 1, dtype=np.int64)
    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i:N + 1:i] = np.where(spf[i:N + 1:i] == 0, i, spf[i:N + 1:i])
    return spf


class HolForm:
    """Level-1 weight-k Hecke eigenform carrier.  theta_p = arccos(lam_p/2),
    lam_p = a_p / p^{(k-1)/2} in [-2,2] (Deligne)."""
    def __init__(self, tag, k, a_arr, N, detune=None):
        self.tag, self.k, self.N = tag, k, N
        half = (k - 1) / 2.0
        self.theta = {}
        for p in sieve_primes(N):
            lam = float(a_arr[p]) / (p ** half)
            lam = max(-2.0, min(2.0, lam))
            th = math.acos(lam / 2.0)
            if detune is not None and int(p) == detune[0]:
                th += detune[1]                      # NEGATIVE CONTROL: perturb one angle
            self.theta[int(p)] = th


# ===========================================================================
# Tensor Satake at a prime; convolution Dirichlet coefficients (unitary norm)
# ===========================================================================
def symr_angles(theta, r):
    return [(r - 2 * j) * theta for j in range(r + 1)]      # r+1 unit clocks

def tensor_alphas(th_pi, r_pi, sigma_kind, th_sig=None, r_sig=None, chi_val=None):
    """Unit-modulus tensor Satake eigenvalues of Sym^{r_pi}(pi)_p (x) sigma_p."""
    base = symr_angles(th_pi, r_pi)
    if sigma_kind == "char":
        cv = 1.0 if chi_val is None else chi_val
        return [cv * np.exp(1j * a) for a in base]
    else:  # sigma = Sym^{r_sig} of a holomorphic form
        sig = symr_angles(th_sig, r_sig)
        return [np.exp(1j * (a + b)) for a in base for b in sig]

def euler_coeffs(alphas, kmax):
    """c_{p^m} = h_m(alpha) via Newton's identity (complete homogeneous sym. poly.)."""
    c = np.zeros(kmax + 1, dtype=complex); c[0] = 1.0
    al = np.asarray(alphas, dtype=complex)
    ps = np.array([np.sum(al ** j) for j in range(1, kmax + 1)], dtype=complex)
    for m in range(1, kmax + 1):
        c[m] = sum(ps[j - 1] * c[m - j] for j in range(1, m + 1)) / m
    return c

def build_conv_coeffs(pi_form, r_pi, sigma_spec, N):
    """Multiplicative convolution coeffs c(n) <= N (unitary norm), local Satake only.
    sigma_spec: ('char', DirichletChar) | ('sym', HolForm, r_sig)."""
    spf = smallest_prime_factor(N)
    c = np.zeros(N + 1, dtype=complex); c[1] = 1.0
    max_exp = int(math.log2(N)) + 1
    ptab = {}
    kind = sigma_spec[0]
    for n in range(2, N + 1):
        p = int(spf[n]); m, e = n, 0
        while m % p == 0:
            m //= p; e += 1
        if p not in ptab:
            th = pi_form.theta[p]
            if kind == "char":
                chi = sigma_spec[1]; cv = complex(chi.values[p % chi.q])
                if cv == 0.0:
                    tab = np.zeros(max_exp + 1, dtype=complex); tab[0] = 1.0
                else:
                    tab = euler_coeffs(tensor_alphas(th, r_pi, "char", chi_val=cv), max_exp)
            else:
                gform, r_sig = sigma_spec[1], sigma_spec[2]
                tab = euler_coeffs(tensor_alphas(th, r_pi, "sym",
                                   th_sig=gform.theta[p], r_sig=r_sig), max_exp)
            ptab[p] = tab
        c[n] = ptab[p][e] * c[m]
    return c


class DirichletChar:
    def __init__(self, tag, q, values, parity):
        self.tag, self.q, self.parity = tag, q, parity
        self.values = np.asarray(values, dtype=complex)

def legendre_char(q):
    qr = np.zeros(q, dtype=np.int8)
    for a in range(1, q):
        qr[(a * a) % q] = 1
    vals = np.array([0.0 if a % q == 0 else (1.0 if qr[a % q] else -1.0)
                     for a in range(q)], dtype=complex)
    return DirichletChar(f"chi{q}(quad)", q, vals, 0 if q % 4 == 1 else 1)


# ===========================================================================
# Archimedean gamma shifts mu_j (Gamma_R) of the convolution, from LOCAL data.
# Gamma_C(s+g) = Gamma_R(s+g) Gamma_R(s+g+1).
# ===========================================================================
def symr_arch_weights(k, r):
    """Signed archimedean weights of Sym^r f_k: {(r-2j)(k-1)/2 : j=0..r}."""
    h = (k - 1) / 2.0
    return [(r - 2 * j) * h for j in range(r + 1)]

def conv_gamma_shifts(pi_k, r_pi, sigma_spec):
    """mu_j list.  For a character twist the arch type is unchanged (chi unramified at inf
    up to parity).  For sigma = Sym^{r_sig} f: tensor the two weight-multisets."""
    kind = sigma_spec[0]
    if kind == "char":
        Wpi = symr_arch_weights(pi_k, r_pi)
        allw = list(Wpi)
    else:
        gform, r_sig = sigma_spec[1], sigma_spec[2]
        Wpi = symr_arch_weights(pi_k, r_pi)
        Wsg = symr_arch_weights(gform.k, r_sig)
        allw = [a + b for a in Wpi for b in Wsg]
    shifts = []
    pos = sorted([w for w in allw if w > 1e-9])
    zeros = [w for w in allw if abs(w) <= 1e-9]
    for m in pos:
        shifts += [m, m + 1.0]                       # each Gamma_C(s+m)
    # zero weights -> Gamma_R pairs; parity from the middle piece (validated on Sym^2)
    nz = len(zeros)
    par = int(round((r_pi // 2) * (pi_k - 1))) % 2 if (kind == "char" and r_pi % 2 == 0) else 0
    for i in range(nz):
        shifts.append(float((i + par) % 2))
    return sorted(shifts)


# ===========================================================================
# Kernel K = inverse Mellin of gamma(s)=prod Gamma_R(s+mu_j), log-space (large shifts).
# Returns K normalised by C = |gamma(sigma_contour)| so floats stay O(1); logC tracked.
# Self-checked: int_0^inf K(y) y^s dy/y  ==  gamma(s)/C.
# ===========================================================================
def loggamma_R_sum(w, mus):
    """log prod_j Gamma_R(w+mu_j) = sum_j [ -(w+mu_j)/2 ln pi + loggamma((w+mu_j)/2) ]."""
    tot = mp.mpc(0)
    lnpi = mp.log(mp.pi)
    for mu in mus:
        a = (w + mu) / 2
        tot += -a * lnpi + mp.loggamma(a)
    return tot

def make_K(mus, sigma=None, dv=None, Uw=None):
    """Inverse-Mellin kernel K = int gamma(sigma+iv) y^{-(sigma+iv)} dv/2pi, log-space.
    y-support scan is adaptive to the shifts (kernel of large shifts lives at large y);
    dv/Uw refined so the oscillatory trapezoid resolves large ln y."""
    d = len(mus)
    if sigma is None:
        sigma = 3.0
    if Uw is None:
        Uw = 24.0 / max(d, 1) ** 0.5 + 16.0
    if dv is None:
        dv = 0.010
    logC = mp.re(loggamma_R_sum(mp.mpf(sigma), mus))     # real reference scale
    vs = np.arange(-Uw, Uw + 1e-9, dv)
    gv = np.empty(len(vs), dtype=complex)
    for i, v in enumerate(vs):
        gv[i] = complex(mp.e ** (loggamma_R_sum(mp.mpc(sigma, v), mus) - logC))
    gv[np.abs(gv) < 1e-300] = 0.0
    def K_exact(y):
        y = np.asarray(y, dtype=np.float64); ly = np.log(y)
        val = (np.exp(-1j * np.outer(ly, vs)) * gv[None, :]).sum(axis=1) * dv / (2 * np.pi)
        return (y ** (-sigma) * val).real
    # adaptive support scan: upper bound grows with the shifts
    yhi = math.log(4.0 * max(mus) + 10.0) + 6.0
    yy = np.exp(np.linspace(-3.0, yhi, 16000)); kk = np.abs(K_exact(yy))
    mmax = kk.max(); good = yy[kk > 1e-16 * mmax]
    ymin = float(good.min()); ymax = float(good.max())
    # dense tabulation over [ymin,ymax] once -> fast interpolation.  If K is sign-definite
    # (true for low degree), cubic-spline log|K| (error ~ spacing^4 -> ~1e-12); else fall back
    # to signed log-linear (oscillatory high-degree kernels).
    lg = np.linspace(math.log(ymin), math.log(ymax), 20000)
    kv = K_exact(np.exp(lg))
    sign_def = np.all(kv >= -1e-300) or np.all(kv <= 1e-300)
    if sign_def:
        sgn0 = 1.0 if kv[np.argmax(np.abs(kv))] > 0 else -1.0
        llk = np.log(np.abs(kv) + 1e-323)
        from scipy.interpolate import CubicSpline
        spl = CubicSpline(lg, llk)
        def K(yq):
            yq = np.asarray(yq, dtype=np.float64); lq = np.log(np.clip(yq, 1e-300, None))
            out = sgn0 * np.exp(spl(lq))
            return np.where((yq < ymin) | (yq > ymax), 0.0, out)
    else:
        slk = np.where(kv != 0, np.log(np.abs(kv) + 1e-323), -np.inf); sgn = np.sign(kv)
        def K(yq):
            yq = np.asarray(yq, dtype=np.float64); lq = np.log(np.clip(yq, 1e-300, None))
            lv = np.interp(lq, lg, slk, left=-np.inf, right=-np.inf)
            sv = np.interp(lq, lg, sgn, left=0.0, right=0.0)
            out = np.where(np.isfinite(lv), np.sign(sv) * np.exp(lv), 0.0)
            return np.where((yq < ymin) | (yq > ymax), 0.0, out)
    K.ymin = ymin; K.ymax = ymax
    K.peak = float(yy[np.argmax(kk)]); K.sigma = sigma; K.logC = float(logC); K.d = d
    K.mus = list(mus); K.exact = K_exact
    return K

def make_K_meijerg(mus, ny=1400, ylo=None, yhi=None):
    """Accurate kernel via mpmath MeijerG:  K(y) = 2 pi^{-sum mu/2} G^{d,0}_{0,d}(pi^d y^2 | mu_j/2),
    which satisfies EXACTLY  int_0^inf K(y) y^{s-1} dy = prod_j Gamma_R(s+mu_j) = gamma(s).
    Tabulated on a log-y grid (arbitrary precision, no overflow) then log-linear interpolated;
    normalised by C=|gamma(3)| so floats stay O(1).  This is the fix for high degree/large shift
    where the inverse-Mellin contour integral loses accuracy."""
    d = len(mus)
    bs = [mp.mpf(m) / 2 for m in mus]
    logpref = mp.log(2) - (sum(mp.mpf(m) for m in mus) / 2) * mp.log(mp.pi)
    logC = mp.re(loggamma_R_sum(mp.mpf(3.0), mus))
    # support estimate: kernel ~ y^{min mu} near 0, super-exp decay; peak near sqrt-ish of shifts
    mn = min(mus)
    if ylo is None:
        ylo = math.exp(-4.0)
    if yhi is None:
        yhi = math.exp(math.log(2.0 * max(mus)) + 6.0)      # generous upper cover
    logy = np.linspace(math.log(ylo), math.log(yhi), ny)
    ys = np.exp(logy)
    logK = np.full(ny, -np.inf)                              # store log|K| and sign
    signK = np.ones(ny)
    for i, y in enumerate(ys):
        z = mp.pi ** d * mp.mpf(float(y)) ** 2
        try:
            g = mp.meijerg([[], []], [bs, []], z)
            val = mp.e ** logpref * g                        # = K(y) (real)
            valn = val * mp.e ** (-logC)                     # normalised
            fv = float(mp.re(valn))
        except Exception:
            fv = 0.0
        if fv != 0.0 and math.isfinite(fv):
            logK[i] = math.log(abs(fv)); signK[i] = math.copysign(1.0, fv)
    finite = np.isfinite(logK)
    if not finite.any():
        raise RuntimeError("meijerg kernel underflowed everywhere")
    mx = logK[finite].max()
    good = finite & (logK > mx - 40.0)                        # ~1e-17 of peak
    ymin = float(ys[good].min()); ymax = float(ys[good].max())
    peak = float(ys[np.argmax(np.where(finite, logK, -np.inf))])
    # interpolant on log y of (signed) K
    lg = logy[finite]; lk = logK[finite]; sg = signK[finite]
    def K(yq):
        yq = np.asarray(yq, dtype=np.float64)
        lq = np.log(np.clip(yq, 1e-300, None))
        val = np.exp(np.interp(lq, lg, lk, left=-np.inf, right=-np.inf))
        s = np.interp(lq, lg, sg)
        out = np.where(np.isfinite(val), np.sign(s) * val, 0.0)
        out[(yq < ymin * 0.999) | (yq > ymax * 1.001)] = 0.0
        return out
    K.ymin = ymin; K.ymax = ymax; K.peak = peak
    K.sigma = 3.0; K.logC = float(logC); K.d = d; K.mus = list(mus); K.meijer = True
    return K


def mellin_selfcheck(K, s=2.0):
    """int_0^inf K(y) y^s dy/y  vs  gamma(s)/C  (kernel validity, independent of coeffs)."""
    ys = np.exp(np.linspace(math.log(max(K.ymin, 1e-3)), math.log(K.ymax), 4000))
    integ = K(ys) * ys ** s
    lhs = np.trapz(integ, np.log(ys))
    rhs = complex(mp.e ** (loggamma_R_sum(mp.mpf(s), K.mus) - K.logC)).real
    return lhs, rhs, abs(lhs - rhs) / (abs(rhs) + 1e-300)


# ===========================================================================
# Theta(u) for u>=1, one-sided completions A(s), honest Lambda_true(s), emergent eps.
# ===========================================================================
def build_theta(K, a_n, Qc, nv=4000):
    """Theta(u) = sum_n a_n K(n u / sqrt(Qc)) on a log-u grid u in [1, umax].
    Qc = CONDUCTOR (not the coefficient-bank size)."""
    sqrtN = math.sqrt(Qc)
    nn = np.arange(1, len(a_n)); an = np.asarray(a_n[1:], dtype=complex)
    umax = K.ymax * sqrtN / 1.0
    Vmax = math.log(umax)
    vs = np.linspace(0.0, Vmax, nv); us = np.exp(vs)
    Theta = np.zeros(nv, dtype=complex)
    for j, u in enumerate(us):
        amin = K.ymin * sqrtN / u; amax = K.ymax * sqrtN / u
        nlo = max(1, int(np.floor(amin))); nhi = min(len(an), int(np.ceil(amax)))
        if nhi < nlo:
            continue
        idx = slice(nlo - 1, nhi)
        Theta[j] = np.dot(an[idx], K(nn[idx] * u / sqrtN))
    return vs, us, Theta

def A_onesided(vs, Theta, s):
    """A(s) = int_1^inf Theta(u) u^s du/u = int_0^Vmax Theta(e^v) e^{v s} dv."""
    return np.trapz(Theta * np.exp(vs * complex(s)), vs)

def lambda_true(a_n, mus, Qc, s):
    """Honest convergent completed value: (gamma(s)/C) Qc^{s/2} sum a_n n^{-s}.
    Qc = CONDUCTOR.  C via mus."""
    s = complex(s)
    nn = np.arange(1, len(a_n)); an = np.asarray(a_n[1:], dtype=complex)
    L = np.sum(an * nn ** (-s))
    logC = mp.re(loggamma_R_sum(mp.mpf(3.0), mus))
    lg = loggamma_R_sum(s, mus) - logC + (s / 2.0) * mp.log(Qc)
    return complex(mp.e ** lg) * L

def emergent_eps(K, a_n, mus, Qc, s0_list):
    """eps(s0) = (Lambda_true(s0) - A(s0)) / A(1-s0).  eps is OUTPUT, never fed.
    Qc = CONDUCTOR of the completion (level-1 objects -> 1)."""
    vs, us, Theta = build_theta(K, a_n, Qc)
    out = []
    for s0 in s0_list:
        Lt = lambda_true(a_n, mus, Qc, s0)
        As = A_onesided(vs, Theta, s0)
        Aw = A_onesided(vs, Theta, 1 - s0)
        eps = (Lt - As) / Aw if abs(Aw) > 0 else complex('nan')
        out.append((s0, eps, abs(As), abs(Aw), abs(Lt)))
    return out, (vs, Theta)


def harmonic_phase_cell(eps):
    """Nearest mu6/pi-3 harmonic cell (k*pi/6) to arg(eps); returns (k, cell_label, dev)."""
    ang = math.atan2(eps.imag, eps.real)          # in (-pi,pi]
    k = round(ang / (math.pi / 6)) % 12
    cell = k * math.pi / 6
    dev = abs(((ang - cell + math.pi) % (2 * math.pi)) - math.pi)
    lab = {0: "+1", 6: "-1", 3: "+i", 9: "-i"}.get(k, f"e^{{i{k}pi/6}}")
    return k, lab, dev


# ===========================================================================
# One convolution: full report
# ===========================================================================
def analyze(pi_form, r_pi, sigma_spec, N, tag, known_eps=None, note="", s0_list=None):
    kind = sigma_spec[0]
    dim_sig = 1 if kind == "char" else (sigma_spec[2] + 1)
    d = (r_pi + 1) * dim_sig
    mus = conv_gamma_shifts(pi_form.k, r_pi, sigma_spec)
    assert len(mus) == d, ("gamma degree mismatch", len(mus), d, mus)
    Q = (sigma_spec[1].q ** (r_pi + 1)) if kind == "char" else 1     # level-1 sym -> cond 1
    coeffs = build_conv_coeffs(pi_form, r_pi, sigma_spec, N)
    if s0_list is None:
        s0_list = [1.15, 1.35, 1.6, 1.85, complex(1.4, 0.6)]

    emit("-" * 92)
    emit(f"PAIR  {tag}   degree d = {d}   conductor Q = {Q}   {note}")
    emit(f"  mu_j (Gamma_R shifts, analytic norm): {['%.1f'%m for m in mus]}")
    if Q != 1:
        emit("  [note] conductor Q!=1 -> theta scale sqrt(Q); using N-scale only (character warp)"
             )

    K = make_K(mus)
    lhs, rhs, rel = mellin_selfcheck(K)
    emit(f"  [kernel] make_K d={d}, contour sigma={K.sigma}, support y in [{K.ymin:.2f},{K.ymax:.1f}]"
         f", peak {K.peak:.2f}")
    emit(f"  [kernel self-check] int K y^2 dy/y = {lhs.real:.6e} vs gamma(2)/C = {rhs:.6e}"
         f"  rel {rel:.2e}  => {'OK' if rel < 1e-3 else 'KERNEL SUSPECT'}")

    res, _ = emergent_eps(K, coeffs, mus, Q, s0_list)
    emit("  [emergent eps]  eps(s0) = (Lambda_true(s0) - A(s0)) / A(1-s0)   (eps = OUTPUT):")
    epsvals = []
    for (s0, eps, aA, aW, aL) in res:
        s0s = f"{s0.real:.2f}" + (f"+{s0.imag:.2f}i" if isinstance(s0, complex) and abs(s0.imag) > 1e-9 else "")
        k, lab, dev = harmonic_phase_cell(eps)
        emit(f"      s0={s0s:>10}: eps={eps.real:+.5f}{eps.imag:+.5f}i  |eps|={abs(eps):.5f}"
             f"  cell {lab} (dev {dev:.1e})  [|A(s0)|={aA:.2e} |A(1-s0)|={aW:.2e}]")
        epsvals.append(eps)
    epsvals = np.array(epsvals)
    # consistency: is eps constant + unimodular?
    eps_mean = np.mean(epsvals)
    spread = float(np.max(np.abs(epsvals - eps_mean)))
    moddev = float(np.max(np.abs(np.abs(epsvals) - 1.0)))
    k, lab, dev = harmonic_phase_cell(eps_mean)
    fe_holds = (spread < 5e-2 and moddev < 5e-2)
    emit(f"  => eps consistency across s0: max|eps-eps_mean| = {spread:.2e},  "
         f"max||eps|-1| = {moddev:.2e}")
    emit(f"  => EMERGENT eps_mean = {eps_mean.real:+.5f}{eps_mean.imag:+.5f}i  "
         f"= harmonic cell {lab} (dev {dev:.1e})"
         + (f"   [known {known_eps}]" if known_eps is not None else "   [known: --]"))
    verdict = "FE EMERGES" if fe_holds else "FE FAILS/DRIFTS"
    emit(f"  => VERDICT: {verdict}   (eps unimodular & s0-consistent: {fe_holds})")
    return dict(tag=tag, d=d, Q=Q, eps=eps_mean, spread=spread, moddev=moddev,
                cell=lab, fe_holds=fe_holds, known=known_eps, verdict=verdict)


def tate_twist_scan(pi_form, r_pi, N, sigma0=1.5):
    """GL(1) Tate-twist clock: sigma = |.|^{i t0}.  The convolution L(s, Sym^r pi x |.|^{it0})
    = L(s+it0, Sym^r pi); its weld is the SAME Sym^r pi weld probed at s0 = sigma0 + i t0.
    We scan t0 on the mu6/pi-3 harmonic grid and read the emergent eps -- it must stay pinned
    (weld covariant under the continuous carrier warp) while |A|,arg(A) genuinely move."""
    triv = ("char", DirichletChar("triv", 1, np.array([1.0], dtype=complex), 0))
    mus = conv_gamma_shifts(pi_form.k, r_pi, triv)
    coeffs = build_conv_coeffs(pi_form, r_pi, triv, N)
    K = make_K(mus)
    vs, us, Theta = build_theta(K, coeffs, 1)
    emit(f"  carrier = Sym^{r_pi}(Delta), d={len(mus)}, conductor 1; sigma0={sigma0}")
    emit("  t0 (Tate)   eps(sigma0+it0)          |eps|     harmonic-cell   |A(s0)|    |A(1-s0)|")
    grid = [("0", 0.0), ("pi/6", PI3 / 2), ("pi/3", PI3), ("pi/2", math.pi / 2),
            ("pi", math.pi), ("2pi", 2 * math.pi)]
    epss = []
    for lab, t0 in grid:
        s0 = complex(sigma0, t0)
        Lt = lambda_true(coeffs, mus, 1, s0)
        As = A_onesided(vs, Theta, s0)
        Aw = A_onesided(vs, Theta, 1 - s0)
        eps = (Lt - As) / Aw
        k, cell, dev = harmonic_phase_cell(eps)
        emit(f"  t0={lab:>5}   {eps.real:+.5f}{eps.imag:+.5f}i    {abs(eps):.5f}"
             f"   {cell:>10} (d{dev:.0e})   {abs(As):.2e}  {abs(Aw):.2e}")
        epss.append(eps)
    epss = np.array(epss)
    spread = float(np.max(np.abs(epss - np.mean(epss))))
    moddev = float(np.max(np.abs(np.abs(epss) - 1.0)))
    emit(f"  => eps invariance under the Tate clock: max|eps-mean|={spread:.2e}, "
         f"max||eps|-1|={moddev:.2e}")
    emit(f"  => {'WELD COVARIANT (eps pinned under continuous warp)' if (spread<5e-2 and moddev<5e-2) else 'WELD MOVES (warp breaks the pin)'}")
    return spread, moddev


def main(full):
    t0 = time.time()
    N = 3500 if full else 1500
    emit("=" * 92)
    emit("SYM^5 ANALYTIC CLOSE ATTEMPT -- emergent-eps convolution FE from local data only")
    emit("=" * 92)
    emit(f"bank N={N}; theta/Mellin double-ended completion; harmonic pi/3 phase cells.")
    emit("Non-circular inputs: Satake angles (exact tau/eigenform), tensor rule, per-factor")
    emit("archimedean type + conductor.  eps SOLVED, never fed.  known eps = comparison only.")
    emit("")

    Nc = N
    tau = tau_exact(Nc)
    for n, want in ((2, -24), (3, 252), (5, 4830), (7, -16744)):
        assert int(tau[n]) == want
    Delta = HolForm("Delta", 12, eigenform_coeffs(tau, 12, Nc), Nc)
    f16 = HolForm("f16", 16, eigenform_coeffs(tau, 16, Nc), Nc)   # sigma-form, distinct weight
    emit(f"[carrier] Delta(wt12) + sigma-form f16(wt16) Satake angles built ({time.time()-t0:.1f}s)")
    emit("")

    results = []

    # ---- VALIDATION: Sym^r Delta itself (sigma trivial); FE known ----
    emit("#" * 92); emit("# VALIDATION LADDER  sigma=trivial: Sym^r Delta (level 1), FE known")
    emit("#" * 92)
    triv = ("char", DirichletChar("triv", 1, np.array([1.0], dtype=complex), 0))
    for r, ke in ((1, "+1(Delta)"), (2, "+1(Sym2)"), (3, "-1(Sym3)"), (4, "+1(Sym4)"),
                  (5, "read-emergent")):
        results.append(analyze(Delta, r, triv, N, f"Sym^{r}(Delta) x triv", known_eps=ke,
                               note="(validation)")); emit("")

    if not full:
        emit(f"[TEST MODE {time.time()-t0:.1f}s]  full adds the Tate clock + GL(2..4) sigma-twists.")
        _flush(); return

    # ---- GL(1) CLOCK: Tate twist sigma = |.|^{i t0}  (continuous phase warp, conductor 1) ----
    emit("#" * 92)
    emit("# GL(1) TATE-TWIST CLOCK  sigma = |.|^{i t0}:  warp the Sym^5 carrier by a CONTINUOUS")
    emit("#   phase clock n^{-i t0}.  L(s, Sym^5 pi x |.|^{it0}) = L(s+it0, Sym^5 pi): the weld")
    emit("#   is probed at the Tate-shifted argument s0+it0.  Does eps stay put under the warp?")
    emit("#" * 92)
    tate_twist_scan(Delta, 5, N); emit("")

    # ---- THE STEP: Sym^5 Delta x Sym^b f16, b=1(GL2),2(GL3),3(GL4) ----
    emit("#" * 92); emit("# THE STEP  Sym^5 Delta x GL(k) sigma  (does the clock-warp preserve the")
    emit("#            helix<->anti-helix weld? does eps still emerge non-circularly?)")
    emit("#" * 92)
    for r_sig, gl in ((1, 2), (2, 3), (3, 4)):
        results.append(analyze(Delta, 5, ("sym", f16, r_sig), N,
                               f"Sym^5(Delta) x Sym^{r_sig}(f16)  [GL({gl}) sigma]",
                               note=f"(FRONTIER GL({gl}), d={6*(r_sig+1)})")); emit("")

    # ---- NEGATIVE CONTROLS: instrument must FAIL on a detuned / wrong object ----
    emit("#" * 92); emit("# NEGATIVE CONTROLS  (falsifiability: eps must NOT emerge for a wrong object)")
    emit("#" * 92)
    Delta_bad = HolForm("Delta_detuned", 12, eigenform_coeffs(tau, 12, Nc), Nc, detune=(7, 0.35))
    results.append(analyze(Delta_bad, 5, triv, N, "Sym^5(Delta) DETUNED(theta_7+0.35) x triv",
                           note="(neg ctrl: one Satake angle wrong)")); emit("")
    # wrong gamma factor: analyze Sym^5 with a WRONG-degree kernel by faking sigma_spec weights
    emit("  [neg ctrl 2] wrong archimedean shifts (drop one Gamma_C) on true Sym^5 Delta:")
    coeffs5 = build_conv_coeffs(Delta, 5, triv, N)
    mus_wrong = sorted(conv_gamma_shifts(12, 5, triv)[:-2])   # drop the top Gamma_C
    Kw = make_K(mus_wrong)
    resw, _ = emergent_eps(Kw, coeffs5, mus_wrong, 1, [1.2, 1.5, 1.8])
    ev = np.array([e for (_, e, *_ ) in resw])
    emit(f"      mu_wrong={['%.1f'%m for m in mus_wrong]}  eps(s0)="
         + ", ".join(f"{e.real:+.3f}{e.imag:+.3f}i" for e in ev))
    emit(f"      max|eps-mean|={np.max(np.abs(ev-np.mean(ev))):.2e}, max||eps|-1|="
         f"{np.max(np.abs(np.abs(ev)-1)):.2e}  => should be LARGE (no FE with wrong gamma)")
    emit("")

    # ---- SUMMARY ----
    emit("=" * 92); emit("SUMMARY"); emit("=" * 92)
    emit(f"  {'pair':>44} {'d':>3} {'Q':>6} {'eps (emergent)':>20} {'cell':>6} "
         f"{'spread':>9} {'||eps|-1|':>9} {'verdict':>16}")
    for r in results:
        emit(f"  {r['tag']:>44} {r['d']:>3} {r['Q']:>6} "
             f"{r['eps'].real:+.4f}{r['eps'].imag:+.4f}i".rjust(20) +
             f" {r['cell']:>6} {r['spread']:>9.1e} {r['moddev']:>9.1e} {r['verdict']:>16}")
    emit("")
    emit(f"[budget] {time.time()-t0:.1f}s")
    _flush()


if __name__ == "__main__":
    main(full=(len(sys.argv) > 1 and sys.argv[1] == "full"))
