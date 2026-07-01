"""
model.py -- canonical, single-source-of-truth model of the double-helix phasor fiber.

Everything the interactive explorer shows is computed from the formulas here, so the
conventions can never drift.  Run `python3 model.py` to print the behavior of every
spin/magnitude mode against the known first zero of each character.

ONTOLOGY (three distinct things):
    CARRIER  the fixed structure -- a spiral helix, parameterized by the single scaled
             coordinate x = (pi/3) n :  radius sqrt(x), winding angle x, height x.
    FIBER    grows ALONG the carrier from the origin upward (one phasor at a time).
    PHASORS  sit along the fiber: phasor n at carrier point x_n = (pi/3) n.
             The 3-D coordinate is scaled; the analytic L-term remains n^(-s).

CHANNELS (Dirichlet character chi):
    Positive P : chi(n) = +1 ;  Negative M : chi(n) = -1 ;  Neutral U : chi(n) = 0 (mass axis)
    focal channel  B = P - M = sum_n chi(n) a_n(H) exp(i phi_n)
    |B| -> 0 is a focal cancellation (a zero).

GRAM PENCIL:
    A = sum_n |chi(n)| a_n(H) is the unsigned live channel.
    H(A,B;mu,lambda) = [[A,B],[mu*A,lambda*B]].
    det H = (lambda-mu) A B and det(H* H)=|det H|^2, so when A != 0 and
    lambda != mu the Gram determinant vanishes exactly with the focal channel B.

PHASE (spin) modes -- phi_n, H = current head height = # terms:
    'winding'   phi_n = n*pi/3                                   (fixed; pins to 6 roots)
    'spin_step' phi_n = (pi/3)*n*(H-n)   faster-newer, entry 0   (pins to 6 roots)
    'spin_cont' phi_n = (pi/3)*n*y        continuous readout y
    'log_entry' phi_n = -omega*log(n)                            (regular L-term phase)

EIGENHEIGHT:
    A focal zero gamma selects the live head height H = round(exp(gamma)).
    At H = round(exp(gamma)) and omega = gamma, the signed L-phasor walk is
    sum_{n<=H} chi(n) a_n(H) exp(-i gamma log(n)), where a_n(H) grows
    continuously from 0 to n^(-1/2), which
    closes at the focal cancellation point up to truncation residual.

MAGNITUDE modes -- a_n(H):
    'absorb'     a_n = n^{-1/2} * clip(H - n + 1, 0, 1)   THE PARTIAL-ABSORPTION LAW (default
                 representation): phasor n starts growing as the head leaves site n-1 and
                 completes exactly AT its own integer site n -- one phasor partial at a time,
                 nothing pops (carrier/fiber harness law; at INTEGER heads absorb == static).
    'grow'       a_n = n^{-1/2} * clip((H - n)/tau, 0, 1) tau-window smoothing (the locator's
                 sharpening device; many phasors grow simultaneously)
    'static'     a_n = n^{-1/2}                           completed-value comparison mode
    'grow_equal' a_n = 1 * clip((H - n)/tau, 0, 1)        tau-window to block-constant amplitude
    'equal'      a_n = 1                                  completed block-constant comparison mode

TWO FINDINGS (see _report):
  * 'grow' SHARPENS the log_entry focus at the eigenheight: it smoothly tapers the newest terms (a window),
    cutting the truncation residual -- |B| drops from 0.006 (static) toward 0 as tau grows.
    A growing magnitude makes the cancellation *cleaner*, with the log phase.
  * 'equal' magnitude makes the WINDING cancel EXACTLY (|B| = 0) -- the mu6 six-cell
    closure.  But it is height-independent (fires at every complete block), so it does
    NOT single out the eigenheight; growth breaks it (newest cell incomplete).
  Neither makes the winding *locate* the eigenheight: that still needs the log phase.

FAST EVALUATOR (fast_focal_B / fast_focal_channels / fast_channel_resultants):
    The brute sum is O(N) and the eigenheight N = e^gamma explodes (gamma6 of chi3
    needs N = 2.8e10).  But every mode except spin_cont has residue-class structure:
      - log_entry: the summand chi(n) w(n) n^{-sigma} e^{-i omega log n} is chi-periodic
        mod q times the SMOOTH function n^{-s}, s = sigma + i*omega.
      - winding / spin_step: the phase is exactly periodic mod 12 (n(H-n) mod 6 is
        determined by n mod 6 for integer H), so e^{i phi} is constant per class mod 12.
    So: sum the first FAST_HEAD terms directly, evaluate each class tail with an
    Euler-Maclaurin expansion (integral + boundary + B2,B4,B6 corrections, all closed
    form for n^{-s}), and subtract the <= tau-term window deficit with a direct loop.
    Cost is O(FAST_HEAD + tau + classes), INDEPENDENT of N; abs error ~1e-9 (validated
    against the brute sum in _selftest across modes x magnitudes x characters).
    spin_cont (phase linear in n at irrational rate) has no class structure: brute only.
"""
from __future__ import annotations
import numpy as np

PI3 = np.pi / 3.0
SIGMA = 0.5

def _chi3(n): r = n % 3; return np.where(r == 1, 1.0, np.where(r == 2, -1.0, 0.0))
def _chi4(n): r = n % 4; return np.where(r == 1, 1.0, np.where(r == 3, -1.0, 0.0))
def _eta(n):  return np.where(n % 2 == 1, 1.0, -1.0)   # alternating (eta); periodic mod 2, zeros = zeta zeros
# real primitive characters of conductors 5, 7, 8, 11, 12 (Kronecker/Legendre value tables)
_T5  = np.array([0., 1., -1., -1., 1.])
_T7  = np.array([0., 1., 1., -1., 1., -1., -1.])
_T8  = np.array([0., 1., 0., -1., 0., -1., 0., 1.])
_T11 = np.array([0., 1., -1., 1., 1., 1., -1., -1., -1., 1., -1.])
_T12 = np.array([0., 1., 0., 0., 0., -1., 0., -1., 0., 0., 0., 1.])
def _chi5(n):  return _T5[np.asarray(n) % 5]
def _chi7(n):  return _T7[np.asarray(n) % 7]
def _chi8(n):  return _T8[np.asarray(n) % 8]
def _chi11(n): return _T11[np.asarray(n) % 11]
def _chi12(n): return _T12[np.asarray(n) % 12]

# ALL critical-line zeros gamma < 36 per character, refined to 10dp against the actual
# L-functions (Hurwitz-zeta Newton, mpmath); zeros[0] == gamma1.  36 is the honest cap:
# the eigenheight N = e^gamma must stay below 2^53 for exact integer arithmetic.
CHARS = {
    "trivial": {"mod": 2, "chi": _eta, "gamma1": 14.1347251417, "label": "zeta (trivial, eta)",
                "zeros": [14.1347251417, 21.0220396388, 25.0108575801, 30.4248761259, 32.9350615877]},
    "chi3": {"mod": 3, "chi": _chi3, "gamma1": 8.0397371557, "label": "chi mod 3",
             "zeros": [8.0397371557, 11.2492062078, 15.7046191767, 18.2619974957, 20.4557708077, 24.0594148565, 26.5778687358, 28.2181645062, 30.7450402614, 33.8973889273, 35.6084126539]},
    "chi4": {"mod": 4, "chi": _chi4, "gamma1": 6.0209489047, "label": "chi mod 4",
             "zeros": [6.0209489047, 10.2437703042, 12.9880980123, 16.3426071046, 18.2919931961, 21.4506113440, 23.2783765205, 25.7287564251, 28.3596343430, 29.6563840146, 32.5921865271, 34.1999575092]},
    "chi5": {"mod": 5, "chi": _chi5, "gamma1": 6.6484533447, "label": "chi mod 5 (quadratic, even)",
             "zeros": [6.6484533447, 9.8314444329, 11.9588456261, 16.0338211284, 17.5669942923, 19.5407326228, 22.2274054545, 24.5884662174, 26.7760959480, 28.4610351002, 29.7079093505, 33.0004560069, 34.7288129789, 35.8686383718]},
    "chi7": {"mod": 7, "chi": _chi7, "gamma1": 4.4757382837, "label": "chi mod 7 (quadratic, odd)",
             "zeros": [4.4757382837, 6.8454917125, 11.1601845431, 12.4896033430, 15.1128822587, 16.8028764757, 19.6118780567, 21.8999137033, 23.1629717997, 24.4988475554, 27.3614775190, 29.1788796664, 30.7218996445, 32.4758875915, 34.1112407830, 35.3118474590]},
    "chi8": {"mod": 8, "chi": _chi8, "gamma1": 4.8999739970, "label": "chi mod 8 (Kronecker 8, even)",
             "zeros": [4.8999739970, 7.6284288418, 10.8065881639, 12.3105429942, 15.1957542506, 17.0222859743, 18.8059589077, 21.1316459622, 23.0838499962, 24.2019635578, 26.9585351804, 28.0974449606, 29.9307642102, 31.6381394913, 33.8456308952, 34.7457770062]},
    "chi11": {"mod": 11, "chi": _chi11, "gamma1": 2.4772437112, "label": "chi mod 11 (quadratic, odd)",
              "zeros": [2.4772437112, 6.8007084084, 8.9712843685, 10.1083373574, 13.0401153288, 15.1091582467, 16.9907107010, 18.7972465362, 20.0675933286, 21.6381778183, 24.6728368611, 25.6859624354, 26.7868956841, 28.8323430013, 29.9746911725, 32.1099172408, 33.5228026453, 35.4850851876]},
    "chi12": {"mod": 12, "chi": _chi12, "gamma1": 3.8046276331, "label": "chi mod 12 (Kronecker 12, even)",
              "zeros": [3.8046276331, 6.6922233205, 8.8905929587, 11.1883927451, 12.9661788080, 15.1814808759, 16.6326332745, 18.8843694571, 20.1039281912, 22.2858391072, 23.5613197131, 25.4116338924, 27.0139439859, 28.4422032577, 30.2040065564, 31.6480776149, 33.0371328795, 35.0273784850, 35.7780445765]},
}
SPIN_MODES = ("winding", "spin_step", "spin_cont", "log_entry")
MAG_MODES = ("absorb", "grow", "static", "grow_equal", "equal")

def magnitude(n, H=None, mag_mode="grow", tau=400.0):
    """a_n(H): 'absorb' is the partial-absorption law (grows across [n-1, n], completes at
    its own site); the 'grow' modes are the tau-window smoothing devices."""
    base = n ** (-SIGMA)
    if mag_mode == "static":
        return base
    if mag_mode == "absorb":
        w = np.clip(H - n + 1.0, 0.0, 1.0) if H is not None else np.ones_like(n)
        return base * w
    grow = np.clip((H - n) / tau, 0.0, 1.0) if H is not None else np.ones_like(n)
    if mag_mode == "grow":       return base * grow
    if mag_mode == "equal":      return np.ones_like(n)
    if mag_mode == "grow_equal": return grow
    raise ValueError(f"unknown mag_mode {mag_mode!r}")

def _last_site(H, mag_mode):
    """Absorption loop bound: 'absorb' includes the one partially-absorbed phasor at
    site floor(H)+1 (weight H - floor(H)); every other mode stops at floor(H)."""
    return int(np.ceil(H)) if mag_mode == "absorb" else int(np.floor(H))

def eigenheight(gamma):
    return int(round(np.exp(gamma)))

def phase(n, mode, N, R):
    # winding/spin_step use exact mod-12/mod-6 forms (identical mod 2pi for integer n, N):
    # the raw products overflow float precision once n(N-n) > 2^53 (N ~ 1e8), and
    # cos/sin of ~1e14 rad have no accuracy left.
    if mode == "winding":   return PI3 * (n % 12)
    if mode == "spin_step": return PI3 * (((n % 6) * ((N - n) % 6)) % 6)
    if mode == "spin_cont": return PI3 * n * R
    if mode == "log_entry": return -R * np.log(n)
    raise ValueError(f"unknown mode {mode!r}")

def focal_B(char, mode, N, R, mag_mode="grow", tau=400.0):
    n = np.arange(1, _last_site(N, mag_mode) + 1, dtype=float)
    chi = CHARS[char]["chi"](n.astype(int))
    a = magnitude(n, N, mag_mode, tau)
    ph = phase(n, mode, N, R)
    return abs(np.sum(chi * a * np.exp(1j * ph)))

def focal_channels(char, mode, N, R, mag_mode="grow", tau=400.0):
    n = np.arange(1, _last_site(N, mag_mode) + 1, dtype=float)
    chi = CHARS[char]["chi"](n.astype(int))
    a = magnitude(n, N, mag_mode, tau)
    ph = phase(n, mode, N, R)
    A = np.sum(np.abs(chi) * a)
    B = np.sum(chi * a * np.exp(1j * ph))
    return complex(A), complex(B)

def gram_pencil_stats(A, B, mu=0.0 + 0.0j, lam=1.0 + 0.0j):
    det = (lam - mu) * A * B
    return abs(det), abs(det) ** 2

def pencil_operator(A, B, mu=0.0 + 0.0j, lam=1.0 + 0.0j):
    """Interlaced harmonic-pencil operator H(mu,lam) = [[A, B], [mu*A, lam*B]].

    Rows interlace the unsigned mass channel A with the signed focal channel B,
    scaled by the pencil pair (mu, lam).  Returns the matrix, det H via the
    closed formula (lam-mu)*A*B AND via direct expansion (their agreement is a
    live consistency check), det Gram = |det H|^2, and the singular values of H,
    so the rank drop can be stated scale-invariantly: sigma2/sigma1 -> 0 exactly
    when B -> 0, given A != 0 and lam != mu
    (Lean: harmonicGram_rank_drop_iff_channel_zero).

    CRUTCH-FREE: the detector is pure arithmetic on the SUPPLIED pair (A, B) --
    it never evaluates an L-function and is agnostic to where the channels came
    from (log_entry, native winding, ...).  The analytic L-calibration
    (A = L(3/2+i*gamma), B = (pi/3) L(1/2+i*gamma)) is a separate downstream
    instantiation living in carrier_fiber's validate mode, not here.

    Lean (RequestProject/HarmonicPencilCell.lean): harmonicPencil / harmonicPencil_det,
    gramH_posSemidef, gramH_rank_drop_iff_L_zero, projection_primacy; the finite
    crutch-free layer backing THIS function: harmonicGram_rank_drop_iff_channel_zero,
    finiteA_pos (admissibility by positivity), finite_gramH_rank_drop_iff_channel_zero,
    finite_gram_rank_drop_calibration_independent, finite_gramH_posSemidef.
    """
    A = complex(A); B = complex(B); mu = complex(mu); lam = complex(lam)
    H = np.array([[A, B], [mu * A, lam * B]], dtype=complex)
    det_formula = (lam - mu) * A * B
    det_direct = A * (lam * B) - B * (mu * A)
    gram = H.conj().T @ H
    t = float(gram[0, 0].real + gram[1, 1].real)
    d = float(abs(det_direct)) ** 2
    disc = max(0.0, t * t - 4.0 * d) ** 0.5
    s1 = ((t + disc) / 2.0) ** 0.5
    s2 = max(0.0, (t - disc) / 2.0) ** 0.5
    return {"H": H, "det_formula": det_formula, "det_direct": det_direct,
            "det_gram": d, "sigma1": s1, "sigma2": s2,
            "admissible": abs(A) > 0 and abs(lam - mu) > 0}

def channel_resultants(char, mode, N, R, mag_mode="grow", tau=400.0):
    n = np.arange(1, _last_site(N, mag_mode) + 1, dtype=float)
    chi = CHARS[char]["chi"](n.astype(int))
    a = magnitude(n, N, mag_mode, tau); ph = phase(n, mode, N, R)
    out = {}
    for name, sel in (("P", chi > 0), ("M", chi < 0), ("U", chi == 0)):
        if name == "U":
            out[name] = {"count": int(sel.sum()), "total_mag": float(a[sel].sum()),
                         "resultant": float(a[sel].sum()), "angle_deg": float("nan")}
        else:
            z = np.sum(a[sel] * np.exp(1j * ph[sel]))
            out[name] = {"count": int(sel.sum()), "total_mag": float(a[sel].sum()),
                         "resultant": float(abs(z)), "angle_deg": float(np.degrees(np.angle(z)) % 360)}
    return out


# ------------------------------------------------------------------ fast evaluator
FAST_HEAD = 6000   # direct head; EM tails need n0 >> Q*|s|  (Q<=12, |s|<~35 here)

def _em_tail(Q, r, lo, hi, s):
    """sum of n^{-s} over n = Q*m + r in (lo, hi], via Euler-Maclaurin in m.

    Exact closed forms for the integral and derivative terms of n^{-s}; with
    lo >= FAST_HEAD the B2/B4/B6 corrections leave ~1e-10 absolute error.
    """
    m1 = (lo - r) // Q + 1
    m2 = (hi - r) // Q
    if m2 < m1:
        return 0.0 + 0.0j
    a = float(Q * m1 + r); b = float(Q * m2 + r)
    if m2 - m1 < 64:   # tiny class: just sum it
        mm = np.arange(m1, m2 + 1, dtype=float)
        return complex(np.sum((Q * mm + r) ** (-s)))
    d1 = -s
    d3 = d1 * (s + 1) * (s + 2)
    d5 = d3 * (s + 3) * (s + 4)
    out  = (b ** (1 - s) - a ** (1 - s)) / (Q * (1 - s))          # integral
    out += (a ** (-s) + b ** (-s)) / 2                            # boundary
    out += (Q / 12.0)        * (d1 * b ** (-s - 1) - d1 * a ** (-s - 1))   # B2/2!
    out += (-Q ** 3 / 720.0) * (d3 * b ** (-s - 3) - d3 * a ** (-s - 3))   # B4/4!
    out += (Q ** 5 / 30240.0) * (d5 * b ** (-s - 5) - d5 * a ** (-s - 5))  # B6/6!
    return complex(out)

def _aggregate(chi, a, ph):
    """channel aggregates of an explicit term list (used for head / small-N cases)."""
    e = np.exp(1j * ph)
    pos = chi > 0; neg = chi < 0; zer = chi == 0
    return {"P": complex(np.sum(a[pos] * e[pos])), "M": complex(np.sum(a[neg] * e[neg])),
            "Pc": int(pos.sum()), "Mc": int(neg.sum()), "Uc": int(zer.sum()),
            "Ptot": float(a[pos].sum()), "Mtot": float(a[neg].sum()), "Utot": float(a[zer].sum())}

def _fast_core(char, mode, N, R, mag_mode="grow", tau=400.0):
    """All channel aggregates in O(FAST_HEAD + tau + classes) -- independent of N."""
    if mode == "spin_cont":
        raise ValueError("spin_cont phase has no residue-class structure; use the brute functions")
    H = float(N); Nl = int(np.floor(H))
    chifn = CHARS[char]["chi"]; q = CHARS[char]["mod"]
    sigma = 0.5 if mag_mode in ("absorb", "grow", "static") else 0.0
    windowed = mag_mode in ("grow", "grow_equal")
    if Nl <= FAST_HEAD + int(tau) + 8:
        n = np.arange(1, _last_site(H, mag_mode) + 1, dtype=float)
        return _aggregate(chifn(n.astype(np.int64)), magnitude(n, H, mag_mode, tau),
                          phase(n, mode, Nl, R))
    # exact head (window can't reach it: Nl - tau > FAST_HEAD)
    n = np.arange(1, FAST_HEAD + 1, dtype=float)
    agg = _aggregate(chifn(n.astype(np.int64)), magnitude(n, H, mag_mode, tau),
                     phase(n, mode, Nl, R))
    # class tails over (FAST_HEAD, Nl], unwindowed
    if mode == "log_entry":
        Q, s_osc = q, sigma + 1j * R      # smooth n^{-s} carries the oscillation
    else:
        Q, s_osc = int(np.lcm(12, q)), None   # phase constant per class mod 12
    for r in range(1, Q + 1):
        c = float(chifn(np.array([r], dtype=np.int64))[0])
        m1 = (FAST_HEAD - r) // Q + 1; m2 = (Nl - r) // Q
        if m2 < m1:
            continue
        cnt = m2 - m1 + 1
        tot = _em_tail(Q, r, FAST_HEAD, Nl, complex(sigma)).real
        if c == 0:
            agg["Uc"] += cnt; agg["Utot"] += tot
            continue
        if s_osc is not None:
            z = _em_tail(Q, r, FAST_HEAD, Nl, s_osc)
        else:
            z = tot * np.exp(1j * float(phase(np.array([float(r)]), mode, Nl, R)[0]))
        if c > 0: agg["Pc"] += cnt; agg["Ptot"] += tot; agg["P"] += z
        else:     agg["Mc"] += cnt; agg["Mtot"] += tot; agg["M"] += z
    # window deficit: only the last <= tau terms differ from the unwindowed tail
    if windowed:
        lo = max(FAST_HEAD, int(np.floor(H - tau)))
        nn = np.arange(lo + 1, Nl + 1, dtype=float)
        if nn.size:
            deficit = (1.0 - np.clip((H - nn) / tau, 0.0, 1.0)) * nn ** (-sigma)
            chn = chifn(nn.astype(np.int64))
            e = np.exp(1j * phase(nn, mode, Nl, R))
            pos = chn > 0; neg = chn < 0; zer = chn == 0
            agg["P"] -= complex(np.sum(deficit[pos] * e[pos]))
            agg["M"] -= complex(np.sum(deficit[neg] * e[neg]))
            agg["Ptot"] -= float(deficit[pos].sum()); agg["Mtot"] -= float(deficit[neg].sum())
            agg["Utot"] -= float(deficit[zer].sum())
    # 'absorb': the tails treat phasors 1..Nl as complete (window is 1 there); add the one
    # partially-absorbed phasor at site Nl+1, weight = the head's fractional part
    if mag_mode == "absorb":
        fr = H - Nl
        if fr > 0:
            n1 = Nl + 1
            c = float(chifn(np.array([n1], dtype=np.int64))[0])
            w = fr * float(n1) ** (-sigma)
            if c == 0:
                agg["Uc"] += 1; agg["Utot"] += w
            else:
                ph1 = float(phase(np.array([float(n1)]), mode, Nl, R)[0])
                z = w * np.exp(1j * ph1)
                if c > 0: agg["Pc"] += 1; agg["Ptot"] += w; agg["P"] += z
                else:     agg["Mc"] += 1; agg["Mtot"] += w; agg["M"] += z
    return agg

def fast_focal_channels(char, mode, N, R, mag_mode="grow", tau=400.0):
    g = _fast_core(char, mode, N, R, mag_mode, tau)
    return complex(g["Ptot"] + g["Mtot"]), complex(g["P"] - g["M"])

def fast_focal_B(char, mode, N, R, mag_mode="grow", tau=400.0):
    return abs(fast_focal_channels(char, mode, N, R, mag_mode, tau)[1])

PENCIL_FAMILY = ((0j, 1 + 0j), (1j, 2 - 1j), (-1 + 0j, 1 + 0j))

def pencil_family(A, B, pairs=PENCIL_FAMILY):
    """The pencil as the Lean has it: a FAMILY of harmonic Gram interlaced operators
    {H(mu,lam)} over the calibration pairs, all on ONE supplied channel pair (A, B).

    Lean (RequestProject/HarmonicPencilCell.lean): every member's Gram (H^H)*H is
    Hermitian positive semidefinite (gramH_posSemidef), the rank-drop event is governed
    solely by the signed channel (projection_primacy: det G = 0 <-> B = 0), and it is
    CALIBRATION-INDEPENDENT (gram_rank_drop_calibration_independent) -- all admissible
    members drop simultaneously.  Mirrors carrier_fiber whole_fiber_pencil_stats
    aggregates (abs A, max |det H|, max det Gram).
    """
    members = [dict(mu=mu, lam=lam, **pencil_operator(A, B, mu, lam)) for mu, lam in pairs]
    adm = [m for m in members if m["admissible"]]
    return {"members": members, "absA": abs(complex(A)), "absB": abs(complex(B)),
            "n_admissible": len(adm),
            "max_abs_det": max((abs(m["det_direct"]) for m in members), default=0.0),
            "max_gram_det": max((m["det_gram"] for m in members), default=0.0)}


def fast_channel_resultants(char, mode, N, R, mag_mode="grow", tau=400.0):
    g = _fast_core(char, mode, N, R, mag_mode, tau)
    out = {}
    for name, z, cnt, tot in (("P", g["P"], g["Pc"], g["Ptot"]), ("M", g["M"], g["Mc"], g["Mtot"])):
        out[name] = {"count": cnt, "total_mag": tot, "resultant": float(abs(z)),
                     "angle_deg": float(np.degrees(np.angle(z)) % 360)}
    out["U"] = {"count": g["Uc"], "total_mag": g["Utot"], "resultant": g["Utot"],
                "angle_deg": float("nan")}
    return out


def _selftest():
    ok = True
    for char in CHARS:
        g = CHARS[char]["gamma1"]; N = eigenheight(g)
        assert abs(phase(np.array([7.0]), "spin_step", 7, g)[0]) < 1e-9, "entry broken spin_step"
        assert focal_B(char, "log_entry", N, g) < 0.03            # log focuses
        A, B = focal_channels(char, "log_entry", N, g)
        detH, detG = gram_pencil_stats(A, B)
        assert abs(B) < 0.03 and detG < 1e-3                     # Gram pencil rank-drops with B
        assert focal_B(char, "spin_step", N, 0.0, "static") > 0.2  # spin_step does not
        # growth sharpens the log focus:
        assert focal_B(char, "log_entry", N, g, "grow", 400) < focal_B(char, "log_entry", N, g, "static")
        # equal magnitude makes the winding cancel exactly over COMPLETE blocks
        # (N = 120q is divisible by both 12 and the conductor q):
        assert focal_B(char, "winding", 120 * CHARS[char]["mod"], 0.0, "equal") < 1e-6
    # fast evaluator === brute, across characters x modes x magnitudes x sizes
    # the absorption law: absorb == static at INTEGER heads (window is 1 on completed
    # phasors, none partial), and exactly alpha-linear in the head's fraction between sites
    for char in CHARS:
        for mode in ("log_entry", "winding"):
            ba = focal_B(char, mode, 3102, 8.039737, "absorb", 1)
            bs = focal_B(char, mode, 3102, 8.039737, "static", 1)
            assert abs(ba - bs) < 1e-12, (char, mode, ba, bs)
    _, c0 = focal_channels("chi3", "log_entry", 100, 8.0, "absorb")
    _, c1 = focal_channels("chi3", "log_entry", 101, 8.0, "absorb")
    _, ch = focal_channels("chi3", "log_entry", 100.5, 8.0, "absorb")
    assert abs(ch - (c0 + 0.5 * (c1 - c0))) < 1e-12          # one phasor, half absorbed
    Abf, Bbf = focal_channels("chi3", "log_entry", 437179.6, 12.988098, "absorb")
    Aff, Bff = fast_focal_channels("chi3", "log_entry", 437179.6, 12.988098, "absorb")
    assert abs(Bbf - Bff) < 1e-8 and abs(Abf - Aff) < 1e-6   # fast partial-absorption matches
    checks = 0
    for char in CHARS:
        for mode in ("log_entry", "winding", "spin_step"):
            for mm, tau in (("absorb", 1), ("static", 1), ("grow", 400), ("equal", 1), ("grow_equal", 250)):
                for NN, RR in ((76819, 11.249206), (437179, 12.988098)):
                    Ab, Bb = focal_channels(char, mode, NN, RR, mm, tau)
                    Af, Bf = fast_focal_channels(char, mode, NN, RR, mm, tau)
                    assert abs(Bb - Bf) < 1e-8 * (1 + abs(Bb)), (char, mode, mm, NN, abs(Bb - Bf))
                    assert abs(Ab - Af) < 1e-6 * (1 + abs(Ab)), (char, mode, mm, NN, abs(Ab - Af))
                    checks += 1
        rb = channel_resultants(char, "log_entry", 437179, 12.988098)
        rf = fast_channel_resultants(char, "log_entry", 437179, 12.988098)
        for k in ("P", "M", "U"):
            assert rb[k]["count"] == rf[k]["count"], (char, k)
            for f in ("total_mag", "resultant"):
                assert abs(rb[k][f] - rf[k][f]) < 1e-6 * (1 + abs(rb[k][f])), (char, k, f)
    # one large brute anchor (chi3 gamma3, N=6.6e6): fast matches where brute is still feasible
    g3 = 15.704619; N3 = eigenheight(g3)
    bb = focal_B("chi3", "log_entry", N3, g3)
    fb = fast_focal_B("chi3", "log_entry", N3, g3)
    assert abs(bb - fb) < 1e-7 * (1 + bb), (bb, fb)
    # interlaced pencil operator: formula == direct det, sigma product == |det H|,
    # rank drop at the focal marker for every admissible (mu, lam), no false drop off-zero
    A1, B1 = focal_channels("chi3", "log_entry", 3102, 8.039737)
    for mu, lam in ((0j, 1 + 0j), (1j, 2 - 1j), (-1 + 0j, 1 + 0j)):
        st = pencil_operator(A1, B1, mu, lam)
        assert abs(st["det_formula"] - st["det_direct"]) < 1e-9 * (1 + abs(st["det_direct"]))
        assert abs(st["sigma1"] * st["sigma2"] - abs(st["det_direct"])) < 1e-6 * (1 + abs(st["det_direct"]))
        assert st["admissible"] and st["sigma2"] / st["sigma1"] < 1e-5, (mu, lam)
    A_off, B_off = focal_channels("chi3", "log_entry", 3102, 8.5)
    off = pencil_operator(A_off, B_off)
    assert off["sigma2"] / off["sigma1"] > 1e-4          # no false rank drop off-zero
    assert not pencil_operator(A1, B1, 1 + 0j, 1 + 0j)["admissible"]  # lam == mu is degenerate
    # crutch-free / channel-agnostic: the SAME detector fires on native winding channels
    # (no log, no L-function anywhere) -- equal-magnitude six-cell closure at N=1200
    A2, B2 = focal_channels("chi3", "winding", 1200, 0.0, "equal", 1)
    stn = pencil_operator(A2, B2, 1j, 2 - 1j)
    assert stn["admissible"] and abs(B2) < 1e-9 and stn["sigma2"] / stn["sigma1"] < 1e-9
    # the pencil is a FAMILY of harmonic Gram interlaced operators: every member Hermitian
    # PSD, and the rank-drop is calibration-independent -- all admissible members drop
    # simultaneously at the marker, none off-zero (Lean: gramH_posSemidef,
    # gram_rank_drop_calibration_independent, projection_primacy)
    fam_pairs = ((0j, 1 + 0j), (1j, 2 - 1j), (-1 + 0j, 1 + 0j), (0.5 - 0.5j, 2j))
    fam_on = pencil_family(A1, B1, fam_pairs)
    fam_off = pencil_family(A_off, B_off, fam_pairs)
    assert all(m["sigma2"] / m["sigma1"] < 1e-5 for m in fam_on["members"])
    assert not any(m["sigma2"] / m["sigma1"] < 1e-4 for m in fam_off["members"])
    for m in fam_on["members"] + fam_off["members"]:
        G = m["H"].conj().T @ m["H"]
        assert np.allclose(G, G.conj().T) and np.all(np.linalg.eigvalsh(G) >= -1e-9)  # Hermitian PSD
    print(f"selftest: PASS (spin_step entry holds; log L-phase focuses at eigenheight; growth sharpens it; "
          f"equal makes winding cancel exactly; fast==brute on {checks} configs + N=6.6e6 anchor)")
    return ok


def _report():
    print("=" * 80)
    print("phasor-helix model : spin modes and the GROWING-magnitude modes vs the first zero")
    print("=" * 80)
    for char in ("chi3", "chi4"):
        g = CHARS[char]["gamma1"]; z = np.exp(g); N = eigenheight(g)
        print(f"\n{CHARS[char]['label']}:  gamma = {g:.4f},  eigenheight e^gamma = {z:.1f}  (N={N})")
        print(f"  {'':22s}{'|B| log phase':>16}{'|B| winding':>14}")
        for mm, tau, lbl in [("static", 1, "static n^-1/2"),
                             ("grow", 1, "grow->n^-1/2  tau=1"),
                             ("grow", 50, "grow->n^-1/2  tau=50"),
                             ("grow", 800, "grow->n^-1/2  tau=800"),
                             ("equal", 1, "equal (block-const)"),
                             ("grow_equal", 50, "grow->equal   tau=50")]:
            bl = focal_B(char, "log_entry", N, g, mm, tau)
            bw = focal_B(char, "winding", N, 0.0, mm, tau)
            print(f"  {lbl:22s}{bl:16.4f}{bw:14.4f}")
        print("  -> growth sharpens the log focus; 'equal' makes the winding close exactly")
        print("     (but that closure is height-independent -- fires at every complete block).")

    print()
    print("=" * 80)
    print("fast evaluator: |B| at EVERY zero's eigenheight (brute is impossible past ~1e7)")
    print("=" * 80)
    for char in ("trivial", "chi3", "chi4"):
        for i, g in enumerate(CHARS[char]["zeros"]):
            N = eigenheight(g)
            bs = fast_focal_B(char, "log_entry", N, g, "static", 1)
            bg = fast_focal_B(char, "log_entry", N, g, "grow", 400)
            print(f"  {char:8s} g{i+1} = {g:10.6f}   N=e^g = {N:>18,d}   "
                  f"|B| static = {bs:.2e}   grow t400 = {bg:.2e}")


if __name__ == "__main__":
    _selftest()
    _report()
