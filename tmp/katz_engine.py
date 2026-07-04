"""KATZ ENGINE — p-GENERIC Lauder/Katz-basis overconvergent-forms engine for the
LHS of Conjecture ES (Darmon-Lauder-Rotger), tame level 124, nebentype chi = chi_4*chi_31.

Computes  I = gamma(e_{g_alpha*} e_ord(d^{-1}(f_breve^[p]) * h_breve))  entirely from
q-expansions (Lauder arXiv:1310.4421 Algorithm 2.1, adapted to weight 1 per DLR), with
NO oracle input: Eisenstein blocks from exact generalized Bernoulli numbers, the weight-1
exotic A4 form h from the 4-route-certified a_p engine (rung3_lhs, reused verbatim),
weight-2 f from the O(p) Legendre point count (rung3_lhs, reused verbatim).

SIZING (Lauder Alg 2.1 step 1), stated per run:
  n_rungs n = floor((p+1)/(p-1) * (m+1)),  m' = m + ceil(n/(p+1)),
  ell = dim M_{1+(p-1)n}(124, chi)  [Cohen-Oesterle, in-house],
  ell' = Sturm bound = ceil(k_n * mu / 12),  q-range = ell' * p  (the "~13x" truncation).
  p=13, m=8:  n=10, m'=9, ell=1922, ell'=1936, q-range 25168.
  p=37, m=8:  n=9,  m'=9, ell=5186, ell'=5200, q-range 192400.
  (All p^{floor(i/(p+1))} Katz scale factors are 1 since n < p+1 — asserted.)

TIERS: [exact] rational/root-of-unity identities; [p-adic certified] carried mod p^{m'}
with measured residual valuations, claims stated at p^m; agreement-to-precision for the
ES gate (NOT identification); [identified] only for bounded discrete targets (a_31 in mu12).

DELIBERATE DESIGN POINTS (honest flags live in the results file):
  * rung 0 is EISENSTEIN-ONLY (2 forms).  The cuspidal weight-1 directions enter at rung 1
    via products.  Reason: a_31(h) (U_31 eigenvalue, 31 | 124 ramified) is printed nowhere
    and is NOT covered by the good-prime a_p engine; we therefore keep h OUT of the basis
    and MEASURE a_31 from the ordinary space (discrete mu12 landing) before building Phi.
  * the incumbent rung3_lhs.weight1_h_qexp uses the CONJUGATE nebentype (chi(3)=zeta^10
    instead of DLR's zeta^2, forced by a_9(h)=0 in DLR's printed expansion); this engine
    carries its own chi (pinned by chi(3)=zeta^2, chi(13)=zeta3) and flags the discrepancy.

Run:  python3 katz_engine.py test        (gates 1-3 at p=13)
      python3 katz_engine.py run13       (full p=13 calibration: 26b, 52b, 124a anchors)
      python3 katz_engine.py sizing      (p=37 sizing arithmetic incl. the 26b/52b wall)
      python3 katz_engine.py run37       (p=37 deliverable: 124a both branches)
"""
import json
import math
import os
import sys
import time
from fractions import Fraction as Q

import numpy as np

TMP = os.path.dirname(os.path.abspath(__file__))
if TMP not in sys.path:
    sys.path.insert(0, TMP)

from rung3_lhs import a_p_h_exponent, _ap_ell_fast, _IND31   # certified engines: REUSED VERBATIM
from rung3_rhs import CURVE_26b, CURVE_52b, NumberField

CACHE = os.path.join(TMP, "katz_cache")
os.makedirs(CACHE, exist_ok=True)
RESULTS_PATH = os.path.join(TMP, "katz_engine_results.txt")

N_TAME = 124

# 124a (DLR Example 5.4 rank-(1,1) curve, conductor 124; printed p=13 integrals):
CURVE_124a = dict(label="124a", cond=124, ainv=(0, 1, 0, -2, 1),
                  intgral_ga=684158979097768450057 * 13,
                  intgral_gb=5953034774844704381281)


# ============================================================================
# logging
# ============================================================================
class Log:
    def __init__(self, path, append=False):
        self.path = path
        self.buf = open(path, "a" if append else "w")

    def __call__(self, s=""):
        print(s, flush=True)
        self.buf.write(s + "\n")
        self.buf.flush()


# ============================================================================
# SECTION A — configuration (p-generic), Teichmuller, characters
# ============================================================================
def teichmuller(res, p, mod):
    """The unique (p-1)th-root-of-unity lift of res mod p to Z/mod."""
    z = res % mod
    for _ in range(80):
        z2 = pow(z, p, mod)
        if z2 == z:
            break
        z = z2
    assert pow(z, p, mod) == z and z % p == res % p
    return z


class Cfg:
    """All p-dependent constants + sizing (Lauder Alg 2.1 step 1)."""

    def __init__(self, p, m, zeta_res):
        self.p, self.m = p, m
        self.n_rungs = ((p + 1) * (m + 1)) // (p - 1)          # Lauder n
        self.mp = m + (self.n_rungs + p) // (p + 1)            # m' = m + ceil(n/(p+1))
        assert self.n_rungs < p + 1, "p^{floor(i/(p+1))} factors would be nontrivial"
        self.MOD = p ** self.mp
        self.weights = [1 + (p - 1) * i for i in range(self.n_rungs + 1)]
        self.mu = 192                                          # [SL2:Gamma0(124)]
        kn = self.weights[-1]
        self.window = (kn * self.mu + 11) // 12                # Sturm bound ell'
        self.LQ = self.window * p
        # Teichmuller zeta12 (the pinned 12th root of unity: 7 mod 13 / 8 mod 37)
        self.zeta = teichmuller(zeta_res, p, self.MOD)
        assert pow(self.zeta, 12, self.MOD) == 1
        for k in range(1, 12):
            assert pow(self.zeta, k, self.MOD) != 1, "zeta not primitive 12th root"
        self.zpow = [pow(self.zeta, k, self.MOD) for k in range(12)]
        self.zeta3 = self.zpow[4]
        # limb bases: LIMB = p^ceil(mp/2) for elementwise ops (LIMB^2 ≡ 0 mod MOD),
        # BB = p^ceil(mp/3) for matmul (BB^3 ≡ 0 mod MOD).
        b = (self.mp + 1) // 2
        self.LIMB = p ** b
        self.LIMB_HI = self.MOD // self.LIMB
        assert self.LIMB * self.LIMB % self.MOD == 0
        e3 = (self.mp + 2) // 3
        self.BB = p ** e3
        assert self.BB ** 3 % self.MOD == 0
        self.BBH1 = self.MOD // self.BB          # p^{mp-e3}
        self.BBH2 = self.MOD // (self.BB * self.BB) if self.mp >= 2 * e3 else 1
        # ind31 table
        self.ind31 = np.zeros(31, dtype=np.int64)
        for a, e in _IND31.items():
            self.ind31[a % 31] = e
        # Kronecker slot size (bytes): conv max = (MOD-1)^2 * LQ
        need = ((self.MOD - 1) ** 2 * self.LQ).bit_length()
        self.SLOT = need // 8 + 1

    # ---- characters: key = (e4, t) with value zeta^{6*e4*[n=3 mod 4] + t*ind31(n)} ----
    def char_exp_table(self, ck):
        """exponent table mod 124 (−1 marks value 0)."""
        e4, t = ck
        tab = np.full(124, -1, dtype=np.int64)
        for a in range(124):
            if e4 and a % 2 == 0:
                continue
            if t and a % 31 == 0:
                continue
            if not e4 and not t:
                tab[a] = 0
                continue
            e = 0
            if e4 and a % 4 == 3:
                e += 6
            if t:
                e += int(t * self.ind31[a % 31])
            tab[a] = e % 12
        return tab

    def char_values(self, ck, L):
        """values chi(n) for n=0..L-1 as int64 mod MOD (0 where not coprime)."""
        tab = self.char_exp_table(ck)
        zp = np.array(self.zpow, dtype=np.int64)
        idx = np.arange(L, dtype=np.int64) % 124
        e = tab[idx]
        out = np.where(e >= 0, zp[np.maximum(e, 0)], 0)
        if not ck[0] and not ck[1]:
            out = np.ones(L, dtype=np.int64)
        out[0] = 0
        return out


def char_cond(ck):
    return (4 if ck[0] else 1) * (31 if ck[1] else 1)


def char_odd(ck):
    return (ck[0] + (1 if ck[1] in (2, 6, 10) else 0)) % 2 == 1


def char_mul(a, b):
    return ((a[0] + b[0]) % 2, (a[1] + b[1]) % 12)


CHI = (1, 8)          # the DLR nebentype: chi(3)=zeta^2, chi(13)=zeta3=zeta^4  (pinned below)
ALL_CHARS = [(e, t) for e in (0, 1) for t in (0, 2, 4, 6, 8, 10)]


# ============================================================================
# SECTION B — Kronecker-substitution polynomial arithmetic mod p^{m'}
# ============================================================================
def _pack_generic(a, slot):
    n = len(a)
    buf = np.zeros((n, slot), dtype=np.uint8)
    raw = a.astype("<u8").view(np.uint8).reshape(n, 8)
    w = min(8, slot)
    buf[:, :w] = raw[:, :w]
    return int.from_bytes(buf.tobytes(), "little")


def _unpack_fast(h, slot, nslots, cfg):
    """int64-safe unpack: value = lo + hi*2^64 with hi < 2^(8*slot-64); reduce mod MOD."""
    mod = cfg.MOD
    nb = slot * nslots
    # h is the FULL product (deg 2L-2); we only want the low L slots (low nb bytes).
    # Each product coefficient fits in `slot` bytes (SLOT sizing), so masking is exact.
    h_low = h & ((1 << (8 * nb)) - 1)
    b = h_low.to_bytes(nb, "little")
    arr = np.frombuffer(b, dtype=np.uint8).reshape(nslots, slot)
    buf16 = np.zeros((nslots, 16), dtype=np.uint8)
    buf16[:, :slot] = arr
    lo = buf16[:, :8].copy().view("<u8").reshape(nslots)
    hi = buf16[:, 8:16].copy().view("<u8").reshape(nslots)
    c64 = pow(2, 64, mod)
    lo_r = (lo % np.uint64(mod)).astype(np.int64)
    hi_r = (hi % np.uint64(mod)).astype(np.int64)          # hi < 2^(8*slot-64)
    return (lo_r + scal_mul(hi_r, c64, cfg)) % mod


def kron_mul(a, b, L, cfg):
    """(a*b)[:L] mod MOD via Kronecker substitution (Python big-int multiply)."""
    mod = cfg.MOD
    slot = cfg.SLOT
    a = np.ascontiguousarray(a[:L] % mod, dtype=np.int64)
    b = np.ascontiguousarray(b[:L] % mod, dtype=np.int64)
    ia = _pack_generic(a, slot)
    ib = _pack_generic(b, slot)
    h = ia * ib
    return _unpack_fast(h, slot, L, cfg)


def kron_mul_modp(a, b, L, p):
    """(a*b)[:L] mod p (small-slot Kronecker; conv max = (p-1)^2*L)."""
    need = ((p - 1) ** 2 * L).bit_length()
    slot = need // 8 + 1
    a = np.ascontiguousarray(a[:L] % p, dtype=np.int64)
    b = np.ascontiguousarray(b[:L] % p, dtype=np.int64)
    ia = _pack_generic(a, slot)
    ib = _pack_generic(b, slot)
    h = ia * ib
    nb = slot * L
    by = (h & ((1 << (8 * nb)) - 1)).to_bytes(nb, "little")
    arr = np.frombuffer(by, dtype=np.uint8).reshape(L, slot)
    buf8 = np.zeros((L, 8), dtype=np.uint8)
    buf8[:, :slot] = arr
    vals = buf8.view("<u8").reshape(L)
    return (vals % np.uint64(p)).astype(np.int64)


def series_inv(a, L, cfg):
    """1/a mod (MOD, q^L) by Newton iteration; a[0] must be a unit."""
    mod = cfg.MOD
    x = np.array([pow(int(a[0]), -1, mod)], dtype=np.int64)
    ln = 1
    while ln < L:
        ln = min(2 * ln, L)
        ax = kron_mul(a[:ln], np.pad(x, (0, ln - len(x))), ln, cfg)
        t = (-ax) % mod
        t[0] = (t[0] + 2) % mod
        x = kron_mul(np.pad(x, (0, ln - len(x))), t, ln, cfg)
    return x[:L]


def v_shift(a, d, L):
    """V_d: a(q) -> a(q^d), truncated at L."""
    out = np.zeros(L, dtype=np.int64)
    src = a[: (L - 1) // d + 1]
    out[::d][: len(src)] = src
    return out


# ---- int64 matmul mod MOD (6-product base-BB identity; BB^3 ≡ 0 mod MOD) ----
def mmod(A, B, cfg):
    """A @ B mod MOD, int64-safe for dims up to ~10^4 at p<=37, mp<=9."""
    MOD, BB = cfg.MOD, cfg.BB
    a2, r = np.divmod(A % MOD, BB * BB)
    a1, a0 = np.divmod(r, BB)
    b2, r = np.divmod(B % MOD, BB * BB)
    b1, b0 = np.divmod(r, BB)
    C0 = a0 @ b0
    C1 = (a0 @ b1 + a1 @ b0) % cfg.BBH1
    C2 = (a0 @ b2 + a1 @ b1 + a2 @ b0) % cfg.BBH2
    return (C0 + BB * C1 + (BB * BB) * C2) % MOD


def vmod(v, B, cfg):
    return mmod(v.reshape(1, -1), B, cfg)[0]


def modinv(x, mod):
    return pow(int(x) % mod, -1, mod)


def scal_mul(vec, scalar, cfg):
    """(vec * scalar) mod MOD, int64-safe (full 2-limb x 2-limb split)."""
    s1, s0 = divmod(int(scalar) % cfg.MOD, cfg.LIMB)
    a1, a0 = np.divmod(vec % cfg.MOD, cfg.LIMB)
    return (a0 * s0 + cfg.LIMB * ((a1 * s0 + a0 * s1) % cfg.LIMB_HI)) % cfg.MOD


def arr_mul(a, b, cfg):
    """elementwise (a*b) mod MOD, int64-safe (full 2-limb x 2-limb split)."""
    a1, a0 = np.divmod(a % cfg.MOD, cfg.LIMB)
    b1, b0 = np.divmod(b % cfg.MOD, cfg.LIMB)
    return (a0 * b0 + cfg.LIMB * ((a1 * b0 + a0 * b1) % cfg.LIMB_HI)) % cfg.MOD


def val_arr(A, p, cap):
    """min p-adic valuation over entries (vectorized; cap = full precision)."""
    A = np.asarray(A, dtype=np.int64) % (p ** cap)
    if not A.any():
        return cap
    v = 0
    while v < cap:
        if (A % p).any():
            return v
        A = A // p
        v += 1
    return v


def gauss_inv_modp(M, p):
    """Inverse of a square matrix over F_p (numpy int64 Gauss-Jordan)."""
    n = M.shape[0]
    A = M % p
    I = np.eye(n, dtype=np.int64)
    A = A.astype(np.int64)
    Aug = np.concatenate([A, I], axis=1)
    for c in range(n):
        piv = None
        for r in range(c, n):
            if Aug[r, c] % p:
                piv = r
                break
        assert piv is not None, f"singular mod {p} at col {c}"
        if piv != c:
            Aug[[c, piv]] = Aug[[piv, c]]
        Aug[c] = (Aug[c] * pow(int(Aug[c, c]), -1, p)) % p
        col = Aug[:, c].copy()
        col[c] = 0
        Aug = (Aug - np.outer(col, Aug[c])) % p
    return Aug[:, n:]


def newton_inv_matrix(E, inv_p, cfg, log=None):
    """E^{-1} mod MOD by Newton iteration X <- X(2I - E X), seeded with inv_p (mod p).
    All products via the int64-safe mmod.  Verifies E @ X ≡ I at the end."""
    n = E.shape[0]
    X = inv_p % cfg.MOD
    prec = 1
    it = 0
    while prec < cfg.mp:
        t0 = time.time()
        EX = mmod(E, X, cfg)
        T2 = (-EX) % cfg.MOD
        T2[np.arange(n), np.arange(n)] = (T2[np.arange(n), np.arange(n)] + 2) % cfg.MOD
        X = mmod(X, T2, cfg)
        prec = min(2 * prec, cfg.mp)
        it += 1
        if log:
            log(f"    newton_inv iter {it}: precision p^{prec}  [{time.time()-t0:.0f}s]")
    chk = mmod(E, X, cfg)
    chk[np.arange(n), np.arange(n)] = (chk[np.arange(n), np.arange(n)] - 1) % cfg.MOD
    assert not chk.any(), "newton matrix inverse failed"
    return X


def small_solve(A, B, cfg):
    """Solve X @ A = B mod MOD for small A (D x D, unit-invertible mod p), B (m x D)."""
    MOD, p = cfg.MOD, cfg.p
    n = A.shape[0]
    Aw = [[int(A[i, j]) for j in range(n)] for i in range(n)]
    Iw = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if Aw[r][c] % p)
        Aw[c], Aw[piv] = Aw[piv], Aw[c]
        Iw[c], Iw[piv] = Iw[piv], Iw[c]
        inv = modinv(Aw[c][c], MOD)
        Aw[c] = [x * inv % MOD for x in Aw[c]]
        Iw[c] = [x * inv % MOD for x in Iw[c]]
        for r in range(n):
            if r != c and Aw[r][c]:
                f = Aw[r][c]
                Aw[r] = [(x - f * y) % MOD for x, y in zip(Aw[r], Aw[c])]
                Iw[r] = [(x - f * y) % MOD for x, y in zip(Iw[r], Iw[c])]
    Ainv = np.array(Iw, dtype=object)
    Bo = B.astype(object)
    # X = B @ A^{-1}  (row convention: X A = B)
    X = (Bo @ Ainv) % MOD
    return np.array([[int(x) for x in row] for row in X], dtype=np.int64)


def mat_pow_small(A, e, cfg):
    """A^e for small object-safe matrices mod MOD."""
    MOD = cfg.MOD
    n = A.shape[0]
    R = np.eye(n, dtype=object)
    B = A.astype(object)
    while e:
        if e & 1:
            R = (R @ B) % MOD
        B = (B @ B) % MOD
        e >>= 1
    return np.array([[int(x) for x in row] for row in R], dtype=np.int64)


# ============================================================================
# SECTION C — exact Bernoulli / generalized Bernoulli (Fractions, Q(zeta12))
# ============================================================================
def bernoulli_upto(K):
    B = [Q(1)]
    for n in range(1, K + 1):
        s = Q(0)
        for k in range(n):
            s += Q(math.comb(n + 1, k)) * B[k]
        B.append(-s / (n + 1))
    B[1] = Q(-1, 2)
    return B


PHI12 = [1, 0, -1, 0, 1]  # x^4 - x^2 + 1 (ascending), Q(zeta12)


class Zeta12Exact:
    """Exact arithmetic in Q(zeta12) with Fraction coords (reuses house NumberField)."""

    def __init__(self):
        self.F = NumberField(PHI12)
        self.zpows = [self.F.one()]
        for _ in range(12):
            self.zpows.append(self.F.mul(self.zpows[-1], self.F.gen()))

    def zeta_pow(self, k):
        return self.zpows[k % 12]

    def embed(self, coords, cfg):
        """Q(zeta12) element -> Z/MOD via the pinned Teichmuller zeta."""
        acc = 0
        for i, c in enumerate(coords):
            c = Q(c)
            den = int(c.denominator)
            assert den % cfg.p != 0, "non-p-integral coordinate"
            acc = (acc + int(c.numerator) * modinv(den, cfg.MOD) * cfg.zpow[i % 12]) % cfg.MOD
        return acc


def gen_bernoulli(k, ck, cfg, nf):
    """B_{k,chi} exact in Q(zeta12) (list of Fraction coords).  chi = char key ck.
    B_{k,chi} = f^{k-1} sum_{a=1..f} chi(a) B_k(a/f).  Trivial chi -> B_k."""
    B = bernoulli_upto(k)
    if ck == (0, 0):
        out = nf.F.zero()
        out[0] = B[k]
        return out
    f = char_cond(ck)
    tab = None
    # chi(a) exponent (reuse Cfg table logic without needing zpow): recompute here
    e4, t = ck
    ind31 = cfg.ind31
    acc = nf.F.zero()
    for a in range(1, f + 1):
        if e4 and a % 2 == 0:
            continue
        if t and a % 31 == 0:
            continue
        e = 0
        if e4 and a % 4 == 3:
            e += 6
        if t:
            e += int(t * ind31[a % 31])
        # B_k(a/f) = sum_j C(k,j) B_j (a/f)^{k-j}
        x = Q(a, f)
        bk = sum(Q(math.comb(k, j)) * B[j] * x ** (k - j) for j in range(k + 1))
        acc = nf.F.add(acc, nf.F.scal(bk, nf.zeta_pow(e)))
    return nf.F.scal(Q(f) ** (k - 1), acc)


# ============================================================================
# SECTION D — Eisenstein block library
# ============================================================================
def eis_series(k, ck1, ck2, cfg, L, nf):
    """E_k(chi1,chi2) = c0 + sum_n (sum_{d|n} chi1(n/d) chi2(d) d^{k-1}) q^n, mod MOD."""
    MOD = cfg.MOD
    v1 = cfg.char_values(ck1, L)
    v2 = cfg.char_values(ck2, L)
    a = np.zeros(L, dtype=np.int64)
    # w2[d] = chi2(d) d^{k-1}
    if k > 1:
        dk = np.array([pow(d, k - 1, MOD) if d else 0 for d in range(L)], dtype=np.int64)
        w2 = arr_mul(v2, dk, cfg)
    else:
        w2 = v2 % MOD
    for d in range(1, L):
        w = int(w2[d])
        if w == 0:
            continue
        seg = v1[1:(L - 1) // d + 1]
        a[d::d] = (a[d::d] + scal_mul(seg, w, cfg)) % MOD
    # constant term
    if char_cond(ck1) == 1:
        bk = gen_bernoulli(k, ck2, cfg, nf)
        c0coords = [-c / (2 * k) for c in bk]
        if any(Q(c).denominator % cfg.p == 0 for c in c0coords):
            # non-p-integral constant (trivial chi2 with (p-1)|k, e.g. E_{p-1} itself):
            # the a_1 normalization has no mod-p reduction; switch to the constant-term-1
            # (Hasse) normalization, which IS p-integral (factor = -2k/B_k is p-integral).
            assert ck2 == (0, 0), "non-p-integral constant for a nontrivial character"
            factor = Q(-2 * k) / bk[0]
            assert factor.denominator % cfg.p != 0, "renormalization factor not p-integral"
            f = int(factor.numerator) % MOD * modinv(int(factor.denominator) % MOD, MOD) % MOD
            a = scal_mul(a, f, cfg)
            a[0] = 1
        else:
            a[0] = nf.embed(c0coords, cfg)
    return a


def build_block_library(cfg, log, nf):
    """All Eisenstein blocks E_k(chi1,chi2) with cond product | 124, weights 1..12,
    plus level-1 E4, E6, E_{p-1}, Delta, E2^(d), and V_d shifts.  Values mod MOD."""
    L = cfg.LQ
    MOD = cfg.MOD
    lib = {}   # key -> dict(weight, char, series)

    def add(key, wt, ck, arr):
        lib[key] = dict(w=wt, ck=ck, s=arr)

    t0 = time.time()
    # --- character Eisenstein blocks, weights 1..12 ---
    for k in range(1, 13):
        for ck1 in ALL_CHARS:
            for ck2 in ALL_CHARS:
                ck = char_mul(ck1, ck2)
                if char_odd(ck) != (k % 2 == 1):
                    continue
                if char_cond(ck1) * char_cond(ck2) > 124 or 124 % (char_cond(ck1) * char_cond(ck2)):
                    continue
                if k == 2 and ck1 == (0, 0) and ck2 == (0, 0):
                    continue                      # E2 quasi-modular: use E2^(d)
                if k == 1 and (ck1, ck2) > (ck2, ck1):
                    continue                      # E_1 symmetric: dedupe
                if k > 2 and ck1 == (0, 0) and ck2 == (0, 0) and k not in (4, 6, cfg.p - 1):
                    continue                      # keep level-1 set small
                arr = eis_series(k, ck1, ck2, cfg, L, nf)
                add(("E", k, ck1, ck2, 1), k, ck, arr)
                base_lvl = char_cond(ck1) * char_cond(ck2)
                for d in (2, 4, 31, 62, 124):
                    if (124 % (base_lvl * d)) == 0:
                        add(("E", k, ck1, ck2, d), k, ck, v_shift(arr, d, L))
    # --- E2^(d) = E2 - d V_d E2 (weight 2, trivial char, level d) ---
    e2 = np.zeros(L, dtype=np.int64)
    sig1 = np.zeros(L, dtype=np.int64)
    for d in range(1, L):
        sig1[d::d] = (sig1[d::d] + d) % MOD
    e2 = sig1.copy()
    e2[0] = (-modinv(24, MOD)) % MOD              # E2 = -1/24 + sum sigma_1 q^n
    for d in (2, 4, 31, 62, 124):
        arr = (e2 - d * v_shift(e2, d, L)) % MOD
        add(("E2d", d), 2, (0, 0), arr)
    # --- normalized E_{p-1} (constant term 1) and Delta ---
    B = bernoulli_upto(cfg.p - 1)
    pm1 = cfg.p - 1
    bk = B[pm1]
    coef_num = -2 * pm1 * bk.denominator
    coef_den = bk.numerator
    # E_{p-1} = 1 - (2k/B_k) sum sigma_{k-1} q^n
    sig = np.zeros(L, dtype=np.int64)
    for d in range(1, L):
        w = pow(d, pm1 - 1, MOD)
        seg = np.full((L - 1) // d, w, dtype=np.int64)
        sig[d::d] = (sig[d::d] + seg) % MOD
    assert abs(coef_den) % cfg.p != 0, "numerator of B_{p-1} divisible by p?!"
    coef = int(coef_num) * modinv(int(coef_den), MOD) % MOD
    Epm1 = scal_mul(sig, coef, cfg)
    Epm1[0] = 1
    assert val_arr(Epm1[1:] % cfg.p, cfg.p, 1) >= 1 or not (Epm1[1:] % cfg.p).any(), \
        "E_{p-1} != 1 mod p"
    add(("Epm1",), pm1, (0, 0), Epm1)
    # E4, E6 normalized (c0=1): 1 + 240 sig3, 1 - 504 sig5
    for (kk, cc) in ((4, 240), (6, -504)):
        s = np.zeros(L, dtype=np.int64)
        for d in range(1, L):
            w = (cc * pow(d, kk - 1, MOD)) % MOD
            seg = np.full((L - 1) // d, w, dtype=np.int64)
            s[d::d] = (s[d::d] + seg) % MOD
        s[0] = 1
        add((f"E{kk}n",), kk, (0, 0), s)
    # Delta = (E4^3 - E6^2)/1728
    e4 = lib[("E4n",)]["s"]
    e6 = lib[("E6n",)]["s"]
    d1 = kron_mul(e4, e4, L, cfg)
    d1 = kron_mul(d1, e4, L, cfg)
    d2 = kron_mul(e6, e6, L, cfg)
    delta = (d1 - d2) % MOD
    delta = (delta * modinv(1728, MOD)) % MOD
    add(("Delta", 1), 12, (0, 0), delta)
    for d in (2, 4, 31, 62, 124):
        add(("Delta", d), 12, (0, 0), v_shift(delta, d, L))
    log(f"  [blocks] library built: {len(lib)} series, L={L}  [{time.time()-t0:.0f}s]")
    return lib


def gate1(cfg, lib, log, nf):
    """GATE 1: exact Bernoulli identities + Hecke eigenvalue action on pure Eisenstein."""
    ok = True
    log("")
    log("GATE 1 — EISENSTEIN BLOCKS (constant terms exact; Hecke eigenvalues reproduced)")
    B = bernoulli_upto(36)
    checks = [("B_4 = -1/30", B[4] == Q(-1, 30)),
              ("B_6 = 1/42", B[6] == Q(1, 42)),
              ("B_12 = -691/2730", B[12] == Q(-691, 2730))]
    b1chi4 = gen_bernoulli(1, (1, 0), cfg, nf)
    checks.append(("B_{1,chi4} = -1/2 (exact, generalized-Bernoulli routine)",
                   b1chi4[0] == Q(-1, 2) and all(c == 0 for c in b1chi4[1:])))
    b1chi = gen_bernoulli(1, CHI, cfg, nf)
    v13ok = True
    for c in b1chi:
        if Q(c).denominator % cfg.p == 0:
            v13ok = False
    checks.append((f"B_(1,chi) p-integral at p={cfg.p} (exact coords in Q(zeta12))", v13ok))
    for name, res in checks:
        log(f"  [exact] {name}: {'PASS' if res else 'FAIL'}")
        ok = ok and res
    # tau values via Delta
    delta = lib[("Delta", 1)]["s"]
    tau = {2: -24, 3: 252, 4: -1472, 5: 4830, 6: -6048, 7: -16744}
    tau_ok = all(int(delta[n]) == t % cfg.MOD for n, t in tau.items())
    ok = ok and tau_ok
    log(f"  [exact] Delta=(E4^3-E6^2)/1728 reproduces tau(2..7) mod p^{cfg.mp}: "
        f"{'PASS' if tau_ok else 'FAIL'}")
    # Hecke eigenvalue gates on pure Eisenstein series (T_ell, ell coprime to level)
    def t_ell_gate(key, ell, lam, wt, ckprod):
        s = lib[key]["s"]
        tab = cfg.char_exp_table(ckprod)
        e = tab[ell % 124]
        chi_l = cfg.zpow[int(e)] if e >= 0 else 0
        Lw = min(cfg.window, (len(s) - 1) // ell + 1)
        # (T_l s)_n = s[l n] + chi(l) l^{w-1} s[n/l]
        tl = s[ell * np.arange(Lw)].copy()
        add2 = np.zeros(Lw, dtype=np.int64)
        idx = np.arange(0, Lw, ell)
        add2[idx] = s[np.arange(len(idx))]
        fac = (chi_l * pow(ell, wt - 1, cfg.MOD)) % cfg.MOD
        tls = (tl + scal_mul(add2, fac, cfg)) % cfg.MOD
        want = scal_mul(s[:Lw].copy(), lam, cfg)
        return not ((tls - want) % cfg.MOD).any()

    gates = []
    z = cfg.zpow
    # E_1(1, chi): lambda_ell = 1 + chi(ell); test ell=3,5
    for ell in (3, 5):
        tab = cfg.char_exp_table(CHI)
        lam = (1 + z[int(tab[ell % 124])]) % cfg.MOD
        gates.append((("E", 1, (0, 0), CHI, 1), ell, lam, 1, CHI))
    # E_1(chi4, psi8): lambda = chi4(ell) + psi8(ell)
    for ell in (3, 5):
        t4 = cfg.char_exp_table((1, 0))[ell % 124]
        t8 = cfg.char_exp_table((0, 8))[ell % 124]
        lam = (z[int(t4)] + z[int(t8)]) % cfg.MOD
        gates.append((("E", 1, (0, 8), (1, 0), 1), ell, lam, 1, CHI))
    # E_{p-1} level 1: lambda = 1 + ell^{p-2}
    for ell in (2, 3, 5):
        lam = (1 + pow(ell, cfg.p - 2, cfg.MOD)) % cfg.MOD
        gates.append((("Epm1",), ell, lam, cfg.p - 1, (0, 0)))
    # E4, E6
    for ell in (2, 3):
        gates.append(((f"E4n",), ell, (1 + pow(ell, 3, cfg.MOD)) % cfg.MOD, 4, (0, 0)))
        gates.append(((f"E6n",), ell, (1 + pow(ell, 5, cfg.MOD)) % cfg.MOD, 6, (0, 0)))
    # one nontrivial-chi1 higher-weight block: E_6(chi4, chi4*psi8-ish) if present
    allok = True
    for key, ell, lam, wt, ckp in gates:
        if key not in lib:
            continue
        g = t_ell_gate(key, ell, lam, wt, ckp)
        allok = allok and g
        if not g:
            log(f"  [FAIL] T_{ell} on {key}")
    log(f"  [p-adic certified] T_ell eigenvalue action on pure Eisenstein "
        f"({len(gates)} checks, full window): {'PASS' if allok else 'FAIL'}")
    # chi pins
    tab = cfg.char_exp_table(CHI)
    pin1 = int(tab[3]) == 2               # chi(3) = zeta^2 (from a_9(h)=0, DLR print)
    pin2 = int(tab[13 % 124]) == 4        # chi(13) = zeta3
    log(f"  [exact] nebentype pins: chi(3)=zeta^2 {'PASS' if pin1 else 'FAIL'}, "
        f"chi(13)=zeta3 {'PASS' if pin2 else 'FAIL'}")
    return ok and allok and pin1 and pin2


# ============================================================================
# SECTION E — the weight-1 layer: h, h' (certified a_p engine + CORRECT nebentype)
# ============================================================================
def smallest_prime_factors(L):
    spf = np.arange(L)
    i = 2
    while i * i < L:
        if spf[i] == i:
            spf[i * i::i] = np.where(spf[i * i::i] == np.arange(i * i, L, i), i,
                                     spf[i * i::i])
        i += 1
    return spf


def primes_upto(L):
    spf = smallest_prime_factors(L)
    return [int(q) for q in range(2, L) if spf[q] == q], spf


def h_qexp(cfg, L, conj=False, a31_exp=None, a2_exp=3):
    """q-expansion of the weight-1 exotic A4 form h (or its zeta->-zeta conjugate h'),
    coefficients as Teichmuller-embedded ints mod MOD.

    a_p for good p: the 4-route-certified engine a_p_h_exponent (rung3_lhs, verbatim).
    a_2 = zeta^3 (DLR print, U_2 eigenvalue); a_31: exponent a31_exp (None -> coefficients
    at 31|n left as ZERO and caller must treat them as UNKNOWN; the engine MEASURES a_31).
    Nebentype chi pinned by chi(3)=zeta^2 / chi(13)=zeta3 (NOT the incumbent's conjugate).
    conj: apply zeta -> -zeta (exponent k -> k+6 for odd k)."""
    MOD = cfg.MOD
    z = cfg.zpow
    tab = cfg.char_exp_table(CHI)
    a = np.zeros(L, dtype=np.int64)
    a[1] = 1
    primes, spf = primes_upto(L)

    def zval(k):
        if conj and k % 2 == 1:
            k += 6
        return z[k % 12]

    for q in primes:
        if 124 % q == 0:
            if q == 2:
                aq = zval(a2_exp)
            else:                                    # q = 31
                if a31_exp is None:
                    continue                          # unknown: leave 31-multiples zero
                aq = zval(a31_exp)
            chi_q = 0
        else:
            k = a_p_h_exponent(q)
            aq = 0 if k is None else zval(k)
            e = tab[q % 124]
            chi_q = z[int(e)] if e >= 0 else 0
        qe, aprev, acur = q, 1, int(aq)
        while qe < L:
            a[qe] = acur
            aprev, acur = acur, (int(aq) * acur - chi_q * aprev) % MOD
            qe *= q
    # multiplicative fill
    for n in range(2, L):
        p0 = int(spf[n])
        pe = p0
        t = n // p0
        while t % p0 == 0:
            pe *= p0
            t //= p0
        if t != 1:
            a[n] = int(a[pe]) * int(a[t]) % MOD
    return a


def gate_h_printed(cfg, log):
    """GATE: reproduce DLR's printed q-expansion of h through q^13 EXACTLY (incl a_9=0),
    and demonstrate the incumbent chi_val discrepancy at n=9 (honest flag)."""
    z = cfg.zpow
    MOD = cfg.MOD
    h = h_qexp(cfg, 16)
    # DLR: h = q + z^3 q^2 + z q^3 - q^4 - z^2 q^5 + (z^2-1) q^6 - z q^7 - z^3 q^8
    #        + 0 q^9 + (-z^3+z) q^10 + (z^3-z) q^11 - z q^12 + z^2 q^13
    want = {1: 1, 2: z[3], 3: z[1], 4: -1, 5: -z[2], 6: z[2] - 1, 7: -z[1], 8: -z[3],
            9: 0, 10: -z[3] + z[1], 11: z[3] - z[1], 12: -z[1], 13: z[2]}
    ok = all(int(h[n]) == w % MOD for n, w in want.items())
    log(f"  [exact] h reproduces DLR's printed a_n (n<=13, including a_9 = 0): "
        f"{'PASS' if ok else 'FAIL'}")
    # honest flag: the incumbent's chi gives a_9 = a_3^2 - chi_incumbent(3) != 0
    a9_incumbent = (z[1] * z[1] - z[10]) % MOD     # chi_incumbent(3) = zeta^10 (conjugate)
    a9_ours = (z[1] * z[1] - z[2]) % MOD           # chi(3) = zeta^2 (DLR pin)
    log(f"  [HONEST FLAG] incumbent rung3_lhs.weight1_h_qexp chi_val is the CONJUGATE "
        f"character: it would give a_9 = {int(a9_incumbent)} != 0; DLR's print forces "
        f"a_9 = {int(a9_ours)} = 0.  (Affects prime-square coefficients only; the "
        f"incumbent's a_p engine itself is correct and is what we reuse.)")
    return ok and int(a9_ours) == 0


def weight2_f_ints(cfg, ainv, cond, L):
    """weight-2 newform coefficients as ints mod MOD (a_p via rung3_lhs._ap_ell_fast)."""
    MOD = cfg.MOD
    a = np.zeros(L, dtype=np.int64)
    a[1] = 1
    primes, spf = primes_upto(L)
    for q in primes:
        ap = _ap_ell_fast(ainv, q)
        pfac = 0 if cond % q == 0 else q
        qe, aprev, acur = q, 1, ap % MOD
        while qe < L:
            a[qe] = acur
            aprev, acur = acur, (ap * acur - pfac * aprev) % MOD
            qe *= q
    for n in range(2, L):
        p0 = int(spf[n])
        pe = p0
        t = n // p0
        while t % p0 == 0:
            pe *= p0
            t //= p0
        if t != 1:
            a[n] = int(a[pe]) * int(a[t]) % MOD
    return a


def serre_dinv(a, cfg):
    """d^{-1} with p-depletion: a_n -> a_n/n (p not| n), 0 (p|n); a_0 -> 0."""
    L = len(a)
    out = np.zeros(L, dtype=np.int64)
    for n in range(1, L):
        if n % cfg.p == 0:
            continue
        out[n] = int(a[n]) * modinv(n, cfg.MOD) % cfg.MOD
    return out


# ============================================================================
# SECTION F — dimensions (Cohen-Oesterle, in-house) + the mod-p candidate phase
# ============================================================================
def dim_Sk_gamma0_chi(N, k, cond_chi, chi_exp_table_fn=None, chi_parity_odd=True):
    """Cohen-Oesterle dim S_k(Gamma0(N), chi) for k >= 2, chi(-1) = (-1)^k.
    For N=124/1612-type levels the elliptic terms are computed by brute force and
    asserted 0 for 4 | N.  Returns (dimS, mu, lam, eps4, eps3)."""
    fac = {}
    nn = N
    d = 2
    while d * d <= nn:
        while nn % d == 0:
            fac[d] = fac.get(d, 0) + 1
            nn //= d
        d += 1
    if nn > 1:
        fac[nn] = fac.get(nn, 0) + 1
    mu = N
    for q in fac:
        mu = mu // q * (q + 1)
    lam = 1
    for q, r in fac.items():
        s = 0
        cc = cond_chi
        while cc % q == 0:
            s += 1
            cc //= q
        if 2 * s <= r:
            lam *= (q ** (r // 2) + q ** (r // 2 - 1)) if r % 2 == 0 else 2 * q ** ((r - 1) // 2)
        else:
            lam *= 2 * q ** (r - s)
    eps4 = sum(1 for x in range(N) if (x * x + 1) % N == 0)
    eps3 = sum(1 for x in range(N) if (x * x + x + 1) % N == 0)
    assert eps4 == 0 and eps3 == 0, "elliptic terms nonzero; formula path not implemented"
    dimS = Q(k - 1, 12) * mu - Q(lam, 2)
    assert dimS.denominator == 1
    return int(dimS), mu, lam, eps4, eps3


def n_eis(N, k):
    """# Eisenstein series in M_k(124, chi) for our fixed chi (k odd): pairs (chi1,chi2),
    chi1*chi2 = chi, cond1*cond2*d | N.  For N=124: 4 ordered pairs, d=1 only; k=1: halved."""
    assert N == 124
    return 2 if k == 1 else 4


def dims_table(cfg, log):
    """d_i = dim M_{k_i}(124, chi) for the rung weights; states all the numbers."""
    ds = []
    for i, k in enumerate(cfg.weights):
        if k == 1:
            # weight 1: dim S_1 = 2 [ANCHOR-CITED: DLR S5.4 'S_1(124,chi) has dimension two'
            # — no in-house weight-1 dimension formula exists; honest flag], Eis_1 = 2.
            ds.append(2 + 2)
        else:
            dS, mu, lam, e4, e3 = dim_Sk_gamma0_chi(124, k, 124)
            ds.append(dS + n_eis(124, k))
    dS, mu, lam, e4, e3 = dim_Sk_gamma0_chi(124, cfg.weights[-1], 124)
    log(f"  [dims] mu=[SL2:Gamma0(124)]={mu}, lambda={lam}, eps4={e4}, eps3={e3}; "
        f"Sturm(k_n={cfg.weights[-1]}) = {cfg.window}")
    log(f"  [dims] d_i = dim M_(1+{cfg.p-1}i)(124,chi): {ds}   (ell = {ds[-1]})")
    log(f"  [dims] d_0 = 4 = 2 Eisenstein + dim S_1 = 2 [ANCHOR-CITED: DLR §5.4]; "
        f"the Katz rung 0 uses only the 2 Eisenstein forms (h stays OUT of the basis "
        f"pending the in-house a_31 measurement) — cumulative rank targets unchanged.")
    return ds


class EchelonFp:
    """Growing RREF echelon over F_p on a fixed column window (int64)."""

    def __init__(self, p, width):
        self.p = p
        self.width = width
        self.R = np.zeros((0, width), dtype=np.int64)
        self.pivcols = []

    def reduce(self, v):
        v = v % self.p
        if len(self.pivcols):
            coeff = v[self.pivcols]
            if coeff.any():
                v = (v - coeff @ self.R) % self.p
        return v

    def add(self, v):
        """Try to add v; returns pivot col if independent else None."""
        v = self.reduce(v)
        nz = np.nonzero(v)[0]
        if len(nz) == 0:
            return None
        c = int(nz[0])
        v = (v * pow(int(v[c]), -1, self.p)) % self.p
        if len(self.pivcols):
            col = self.R[:, c].copy()
            if col.any():
                self.R = (self.R - np.outer(col, v)) % self.p
        self.R = np.vstack([self.R, v[None, :]])
        self.pivcols.append(c)
        return c


def candidate_pool(cfg, lib, rung, rows13, row_meta, trivmul13):
    """Yield (recipe, vec13) candidates for the given rung (weight 1+(p-1)*rung).
    recipe forms:
      ('pair', key1, key2)        pure block product (rung 1 layer)
      ('rowlib', j, tkey)         rows13[j] * trivial-multiplier tkey (gap = rung - rung_j)
    vec13 is the mod-p q-window expansion of the KATZ-NORMALIZED element (== classical
    form mod p, since E_{p-1} == 1 mod p)."""
    p, W = cfg.p, cfg.window
    target_w = cfg.weights[rung]
    if rung >= 1:
        # (a) row * trivial-char multipliers, nearest rung first
        for gap in range(1, rung + 1):
            src_rung = rung - gap
            for tkey, (tw, tvec13) in trivmul13.items():
                if tw != gap * (p - 1):
                    continue
                for j in range(len(rows13)):
                    if row_meta[j]["rung"] != src_rung:
                        continue
                    yield ("rowlib", j, tkey), kron_mul_modp(rows13[j], tvec13, W, p)
        # (b) pure pairs of blocks with total weight = target, char product = chi
        if rung == 1:
            keys = sorted([k for k in lib if lib[k]["w"] < target_w],
                          key=lambda k: (lib[k]["w"], str(k)))
            for k1 in keys:
                for k2 in keys:
                    if lib[k1]["w"] + lib[k2]["w"] != target_w:
                        continue
                    if char_mul(lib[k1]["ck"], lib[k2]["ck"]) != CHI:
                        continue
                    if str(k2) < str(k1):
                        continue
                    v = kron_mul_modp(lib[k1]["s"][:W] % p, lib[k2]["s"][:W] % p, W, p)
                    yield ("pair", k1, k2), v


def build_trivial_multipliers(cfg, lib, log, max_gap=2):
    """Weight-g(p-1), trivial-character, level | 124 multipliers T (as forms), stored
    mod p on the window (for trials).  Full-precision versions (T * E_{p-1}^{-g}) are
    computed lazily at acceptance time.  Returns dict tkey -> (weight, vec13)."""
    p, W = cfg.p, cfg.window
    out = {}
    # products of level-1 blocks {E4, E6, Delta} with total weight g(p-1), plus V_d(Delta^b...)
    lvl1 = {"E4": (4, lib[("E4n",)]["s"]), "E6": (6, lib[("E6n",)]["s"]),
            "D": (12, lib[("Delta", 1)]["s"])}
    for g in range(1, max_gap + 1):
        tgt = g * (p - 1)
        # enumerate multisets of E4^a E6^b Delta^c with 4a+6b+12c = tgt, c >= 1 or (a,b) != trivial
        for c in range(0, tgt // 12 + 1):
            for b in range(0, (tgt - 12 * c) // 6 + 1):
                rem = tgt - 12 * c - 6 * b
                if rem % 4:
                    continue
                a = rem // 4
                if a == 0 and b == 0 and c == 0:
                    continue
                key = ("lvl1", a, b, c)
                out[key] = (tgt, ("lvl1", a, b, c))
        # V_d(Delta)-twisted variants for extra mod-p content
        for d in (2, 4, 31, 62):
            for c in range(1, tgt // 12 + 1):
                rem = tgt - 12 * c
                if rem % 4 == 0:
                    a = rem // 4
                    key = ("vD", d, c, a)
                    out[key] = (tgt, ("vD", d, c, a))
        # level-124 Eisenstein pairs with trivial product character, total weight tgt
        keys = sorted([k for k in lib if lib[k]["w"] <= tgt - 1 and lib[k]["w"] >= 1],
                      key=lambda k: (lib[k]["w"], str(k)))
        cnt = 0
        for k1 in keys:
            for k2 in keys:
                if lib[k1]["w"] + lib[k2]["w"] != tgt:
                    continue
                if char_mul(lib[k1]["ck"], lib[k2]["ck"]) != (0, 0):
                    continue
                if str(k2) < str(k1):
                    continue
                key = ("epair", k1, k2)
                out[key] = (tgt, ("epair", k1, k2))
                cnt += 1
                if cnt > 400:
                    break
            if cnt > 400:
                break
    # evaluate all to mod-p window vectors
    evald = {}
    for key, (tgt, spec) in out.items():
        evald[key] = (tgt, _eval_multiplier_modp(cfg, lib, spec))
    log(f"  [multipliers] trivial-char multiplier pool: {len(evald)} "
        f"(gaps 1..{max_gap})")
    return evald


def _eval_multiplier_modp(cfg, lib, spec):
    p, W = cfg.p, cfg.window
    if spec[0] == "lvl1":
        _, a, b, c = spec
        v = np.zeros(W, dtype=np.int64)
        v[0] = 1
        for _ in range(a):
            v = kron_mul_modp(v, lib[("E4n",)]["s"][:W], W, p)
        for _ in range(b):
            v = kron_mul_modp(v, lib[("E6n",)]["s"][:W], W, p)
        for _ in range(c):
            v = kron_mul_modp(v, lib[("Delta", 1)]["s"][:W], W, p)
        return v
    if spec[0] == "vD":
        _, d, c, a = spec
        v = np.zeros(W, dtype=np.int64)
        v[0] = 1
        for _ in range(a):
            v = kron_mul_modp(v, lib[("E4n",)]["s"][:W], W, p)
        vd = lib[("Delta", d)]["s"][:W] if ("Delta", d) in lib else None
        if vd is None:
            return v * 0
        for _ in range(c):
            v = kron_mul_modp(v, vd, W, p)
        return v
    if spec[0] == "epair":
        _, k1, k2 = spec
        return kron_mul_modp(lib[k1]["s"][:W], lib[k2]["s"][:W], W, cfg.p)
    raise ValueError(spec)


def eval_multiplier_full(cfg, lib, spec, epm1_inv_pows, gap, cache):
    """Full-precision multiplier: (multiplier form) * E_{p-1}^{-gap}, length LQ."""
    ck = ("full", spec, gap)
    if ck in cache:
        return cache[ck]
    L = cfg.LQ
    if spec[0] == "lvl1":
        _, a, b, c = spec
        v = None
        for _ in range(a):
            v = lib[("E4n",)]["s"] if v is None else kron_mul(v, lib[("E4n",)]["s"], L, cfg)
        for _ in range(b):
            v = lib[("E6n",)]["s"] if v is None else kron_mul(v, lib[("E6n",)]["s"], L, cfg)
        for _ in range(c):
            v = lib[("Delta", 1)]["s"] if v is None else kron_mul(v, lib[("Delta", 1)]["s"], L, cfg)
    elif spec[0] == "vD":
        _, d, c, a = spec
        v = None
        for _ in range(a):
            v = lib[("E4n",)]["s"] if v is None else kron_mul(v, lib[("E4n",)]["s"], L, cfg)
        for _ in range(c):
            vd = lib[("Delta", d)]["s"]
            v = vd if v is None else kron_mul(v, vd, L, cfg)
    elif spec[0] == "epair":
        _, k1, k2 = spec
        v = kron_mul(lib[k1]["s"], lib[k2]["s"], L, cfg)
    else:
        raise ValueError(spec)
    v = kron_mul(v, epm1_inv_pows[gap], L, cfg)
    cache[ck] = v
    return v


# ============================================================================
# SECTION G — basis build: mod-p trial phase (GATE 2) + full-precision Katz basis
# ============================================================================
def build_basis(cfg, lib, log, dims, a31_exp=None, allow_filtration_overshoot=False,
                seed_cusp_forms=False, accept_rank_price=False):
    """Two-phase Katz-basis construction.

    Phase 1 (mod p, window): greedy rank-building per rung against a global RREF
    echelon (E_{p-1} == 1 mod p makes all rungs coexist mod p).  GATE 2 per rung:
    cumulative rank == d_i from the dimension formula; then an overshoot probe
    (extra candidates must add NO rank — catches any non-modular junk vector).

    Phase 2 (mod p^{m'}, length LQ): the accepted recipes are evaluated at full
    precision, Katz-normalized (times E_{p-1}^{-i}); stores per-element windows:
      E_win[j]  = e_j coefficients at q^0..q^{W-1}
      E_upw[j]  = e_j coefficients at q^{p c}, c = 0..W-1   (the U_p image row)
    Full LQ arrays are kept only transiently (rows needed as future product factors).

    Returns dict with E_win, E_upw, pivcols, recipes, rung_of_row.
    """
    p, W, L = cfg.p, cfg.window, cfg.LQ
    ech = EchelonFp(p, W)
    rows13 = []          # mod-p window rows (kept for candidate generation)
    row_meta = []        # {'rung': i, 'recipe': ...}
    log("")
    log("GATE 2 — CLASSICAL BASES (rank vs Cohen-Oesterle dimension formula, per rung)")
    trivmul13 = build_trivial_multipliers(cfg, lib, log)
    # rung 0: the full weight-1 space M_1(124,chi) = 2 Eisenstein + the 2 exotic-A4 cusp
    # forms h, h'.  The cusp forms are their OWN Katz elements (weight 1, E_{p-1}^0), and
    # MUST be seeded here for the ordinary space to contain the g_alpha/g_beta stabilizations
    # (excluding them and hoping rung-1 products restore them as ordinary DOES NOT work —
    # measured).  a31_exp = trial exponent of the ramified U_31 eigenvalue a_31 = zeta^{a31_exp}
    # (or None => a_31 = 0); determined by the self-consistency scan (right value => h clean-
    # ordinary, i.e. h lands in O).  On 31-coprime columns h is independent of a31_exp.
    n0 = 0
    for key in (("E", 1, (0, 0), CHI, 1), ("E", 1, (0, 8), (1, 0), 1)):
        v = lib[key]["s"][:W] % p
        c = ech.add(v)
        assert c is not None, "rung-0 Eisenstein dependent mod p?!"
        rows13.append(v)
        row_meta.append(dict(rung=0, recipe=("w0", key)))
        n0 += 1
    if seed_cusp_forms:
        for conj in (False, True):
            v = h_qexp(cfg, W, conj=conj, a31_exp=a31_exp)[:W] % p
            c = ech.add(v)
            assert c is not None, "rung-0 cusp form h dependent mod p?!"
            rows13.append(v)
            row_meta.append(dict(rung=0, recipe=("w0h", conj)))
            n0 += 1
        log(f"  rung 0 (weight 1): rank {n0}/{dims[0]} = 2 Eisenstein + 2 cusp forms h,h' "
            f"(a_31 = {'0' if a31_exp is None else 'zeta^%d' % a31_exp}) [full M_1; DLR §5.4]")
    else:
        log(f"  rung 0 (weight 1): rank {n0}/2 Eisenstein [cusp forms h,h' NOT seeded; the "
            f"validated Eisenstein-only basis — set seed_cusp_forms=True to include them]")
    gate2_ok = True
    for rung in range(1, cfg.n_rungs + 1):
        target = dims[rung]
        tried = 0
        t0 = time.time()
        pool = candidate_pool(cfg, lib, rung, rows13, row_meta, trivmul13)
        for recipe, v in pool:
            # accept_rank_price: pay the RANK PRICE of the harmonization lift — keep EVERY
            # rank-increasing direction (mod p, the seeded weight-1 cusp forms drop filtration
            # and legitimately enlarge the space; tensor_lift_commutes: capturing g costs new
            # dimensions).  Otherwise cap at the char-0 dim (validated Eisenstein path).
            if not accept_rank_price and len(ech.pivcols) >= target:
                break
            tried += 1
            c = ech.add(v)
            if c is not None:
                rows13.append(v % p)
                row_meta.append(dict(rung=rung, recipe=recipe))
        got = len(ech.pivcols)
        if accept_rank_price:
            price = got - target
            gate2_ok = gate2_ok and (got >= target)
            log(f"  rung {rung} (weight {cfg.weights[rung]}): FULL mod-p rank {got} "
                f"(char-0 dim {target}, rank price +{price}; tried {tried})  "
                f"[{'OK' if got >= target else 'DEFICIT'}]  [{time.time()-t0:.0f}s]")
            if got < target:
                log(f"  *** DEFICIT at rung {rung}: below char-0 dim — HALT")
                raise SystemExit(1)
            continue
        # overshoot probe: next few candidates must add no rank.  NON-MUTATING (ech.reduce,
        # not ech.add — the old code silently grew the echelon during probing).
        probe_add = 0
        probed = 0
        if got >= target:
            for recipe, v in pool:
                probed += 1
                if ech.reduce(v).any():
                    probe_add += 1
                if probed >= 15:
                    break
        stat = "PASS" if (got == target and probe_add == 0) else "FAIL"
        gate2_ok = gate2_ok and (stat == "PASS")
        log(f"  rung {rung} (weight {cfg.weights[rung]}): rank {got}/{target} "
            f"(tried {tried}); overshoot probe +{probe_add} (0 required)  [{stat}] "
            f"[{time.time()-t0:.0f}s]")
        if got < target:
            log(f"  *** DEFICIT at rung {rung}: {target-got} missing — "
                f"pool exhausted; HALT per mission (no silent proceed)")
            raise SystemExit(1)
        if probe_add and not allow_filtration_overshoot:
            log(f"  *** OVERSHOOT at rung {rung}: non-modular junk detected — HALT")
            raise SystemExit(1)
        if probe_add:
            # EXPECTED when weight-1 cusp forms h,h' are seeded: mod p, E_{p-1}==1 so h is a
            # mod-p weight-(1+12r) form (filtration drop) and the mod-p rank exceeds the char-0
            # dim.  We TRUNCATE to the char-0 dimension `target` (decay-bound method-law: the
            # Katz truncation length is the char-0 dim; excess mod-p directions are filtration
            # ghosts, not overconvergent forms).  The full-precision U_p-closure gate is the
            # real arbiter of whether the selected `target` rows form a valid Katz basis.
            log(f"  [filtration] rung {rung}: mod-p overshoot +{probe_add} (weight-1 ghosts) "
                f"— truncated to char-0 dim {target}; full-precision Katz-closure will verify")
    ell = len(ech.pivcols)
    log(f"  GATE 2: cumulative rank {ell} == ell {dims[-1]}  "
        f"[{'PASS' if ell == dims[-1] else 'FAIL'}]; recipe census: " + recipe_census(row_meta))
    # ---- phase 2: full precision ----
    log(f"  [phase 2] evaluating {ell} recipes at full precision mod p^{cfg.mp}, "
        f"q-length {L} ...")
    t0 = time.time()
    epm1 = lib[("Epm1",)]["s"]
    epm1_inv = series_inv(epm1, L, cfg)
    chk = kron_mul(epm1, epm1_inv, L, cfg)
    assert int(chk[0]) == 1 and not chk[1:].any(), "E_{p-1} inverse failed"
    epm1_inv_pows = {0: None, 1: epm1_inv}
    for g in range(2, cfg.n_rungs + 1):
        epm1_inv_pows[g] = kron_mul(epm1_inv_pows[g - 1], epm1_inv, L, cfg)
    mulcache = {}
    rows_full = []       # KATZ-NORMALIZED rows (weight-1 oc functions), full length
    E_win = np.zeros((ell, W), dtype=np.int64)
    E_upw = np.zeros((ell, W), dtype=np.int64)
    for j, meta in enumerate(row_meta):
        rec = meta["recipe"]
        rung = meta["rung"]
        if rec[0] == "w0":
            v = lib[rec[1]]["s"].copy()
        elif rec[0] == "w0h":
            v = h_qexp(cfg, L, conj=rec[1], a31_exp=a31_exp)
        elif rec[0] == "pair":
            v = kron_mul(lib[rec[1]]["s"], lib[rec[2]]["s"], L, cfg)
            v = kron_mul(v, epm1_inv_pows[1], L, cfg)
        elif rec[0] == "rowlib":
            _, src, tkey = rec
            gap = rung - row_meta[src]["rung"]
            spec = tkey if isinstance(tkey, tuple) and tkey[0] in ("lvl1", "vD", "epair") \
                else tkey
            mul_full = eval_multiplier_full(cfg, lib, spec, epm1_inv_pows, gap, mulcache)
            v = kron_mul(rows_full[src], mul_full, L, cfg)
        else:
            raise ValueError(rec)
        rows_full.append(v)
        E_win[j] = v[:W]
        E_upw[j] = v[::p][:W]
        # consistency: mod-p reduction must reproduce the trial row
        if j % 500 == 0:
            assert not ((v[:W] - rows13[j]) % p).any(), f"phase-2 mismatch at row {j}"
        if j % 250 == 0 and j:
            log(f"    ... {j}/{ell} rows  [{time.time()-t0:.0f}s]")
    log(f"  [phase 2] done: {ell} Katz rows  [{time.time()-t0:.0f}s]")
    return dict(E_win=E_win, E_upw=E_upw, pivcols=np.array(ech.pivcols, dtype=np.int64),
                row_meta=row_meta, rows_full=rows_full)


def recipe_census(row_meta):
    from collections import Counter
    c = Counter(m["recipe"][0] for m in row_meta)
    return ", ".join(f"{k}:{v}" for k, v in sorted(c.items()))


# ============================================================================
# SECTION H — the finite U_p matrix (Lauder step 5) + full-window consistency gate
# ============================================================================
def build_up_matrix(cfg, basis, log):
    """A[i][j]: U_p e_i = sum_j A[i][j] e_j  (row convention: forms are row vectors of
    Katz coordinates, U_p acts by right multiplication with A... i.e. coords(U_p x) =
    coords(x) @ A).  Solved on the mod-p pivot columns; gated on the FULL window."""
    p, W = cfg.p, cfg.window
    E_win, E_upw, piv = basis["E_win"], basis["E_upw"], basis["pivcols"]
    ell = E_win.shape[0]
    t0 = time.time()
    E_piv = np.ascontiguousarray(E_win[:, piv])
    log("")
    log("GATE — U_p MATRIX (Lauder step 5: solve T = A E on pivot columns)")
    inv_p = gauss_inv_modp(E_piv % p, p)
    log(f"  [solve] F_p inverse of E_piv ({ell}x{ell})  [{time.time()-t0:.0f}s]")
    t0 = time.time()
    E_inv = newton_inv_matrix(E_piv, inv_p, cfg, log)
    log(f"  [solve] Newton lift of E_piv^-1 to mod p^{cfg.mp}  [{time.time()-t0:.0f}s]")
    t0 = time.time()
    T_piv = np.ascontiguousarray(E_upw[:, piv])
    A = mmod(T_piv, E_inv, cfg)
    log(f"  [solve] A = T_piv @ E_piv^-1  [{time.time()-t0:.0f}s]")
    # FULL-WINDOW consistency: A @ E_win must equal E_upw at EVERY window column.
    t0 = time.time()
    resid = (mmod(A, E_win, cfg) - E_upw) % cfg.MOD
    v = val_arr(resid, p, cfg.mp)
    log(f"  GATE (Katz-closure/integrality, Lauder Note 2.2(3)+2.3(1)): "
        f"min val_p(A@E - U_pE) over full {W}-column window = {v} "
        f"(mp={cfg.mp}; >= mp means EXACT at working precision)  "
        f"[{'PASS' if v >= cfg.mp else ('PASS at reduced precision' if v >= cfg.m else 'FAIL')}]"
        f"  [{time.time()-t0:.0f}s]")
    return A, E_inv, v


# ============================================================================
# SECTION I — ordinary subspace, e_ord, and GATE 3
# ============================================================================
def ordinary_space(cfg, A, log, n_squarings=None):
    """A^{2^k} until the non-ordinary part is EXACTLY 0 mod p^{m'} (slopes >= 1/2 =>
    k=5 gives exponent 32 >= 2 m').  Unit-pivot RREF rows of A^{32} = ordinary basis O
    (rows = Katz coords).  Returns O, A32, leftover valuation."""
    p, MOD = cfg.p, cfg.MOD
    ell = A.shape[0]
    ns = n_squarings or max(5, (2 * cfg.mp).bit_length())
    t0 = time.time()
    A2k = A.copy()
    for k in range(ns):
        A2k = mmod(A2k, A2k, cfg)
        log(f"    A^(2^{k+1})  [{time.time()-t0:.0f}s]")
    expo = 2 ** ns
    # unit-pivot RREF
    t0 = time.time()
    Aw = A2k.copy()
    orows = []
    opivs = []
    while True:
        # find a row with a unit entry, smallest column
        U = (Aw % p) != 0
        if not U.any():
            break
        cols = np.where(U.any(axis=0))[0]
        c = int(cols[0])
        r = int(np.where(U[:, c])[0][0])
        row = scal_mul(Aw[r], modinv(int(Aw[r, c]), MOD), cfg)
        fac = Aw[:, c].copy()
        # eliminate column c from all rows (2-limb outer product)
        f1, f0 = np.divmod(fac, cfg.LIMB)
        r1, r0 = np.divmod(row, cfg.LIMB)
        upd = (np.outer(f0, r0) + cfg.LIMB * ((np.outer(f1, r0) + np.outer(f0, r1))
                                              % cfg.LIMB_HI)) % MOD
        Aw = (Aw - upd) % MOD
        orows.append(row)
        opivs.append(c)
    leftover_v = val_arr(Aw, p, cfg.mp)
    D = len(orows)
    O = np.array(orows, dtype=np.int64)
    # RREF-ize among the found rows (make O[:, opivs] = I)
    opivs = np.array(opivs, dtype=np.int64)
    Osub = O[:, opivs]
    Oinv = small_solve(Osub, np.eye(D, dtype=np.int64), cfg)   # X @ Osub = I => X = Osub^{-1}
    O = mmod(Oinv, O, cfg)
    assert not ((O[:, opivs] - np.eye(D, dtype=np.int64)) % MOD).any()
    log(f"  [ordinary] dim = {D} unit-pivot rows of A^{expo}; leftover (non-ordinary) "
        f"min val = {leftover_v} (>= mp={cfg.mp} means slopes >= {cfg.mp}/{expo} — "
        f"clean gap)  [{time.time()-t0:.0f}s]")
    return O, opivs, A2k, expo, leftover_v, D


def stabilized(cfg, series, eigen_other, L):
    """p-stabilization  s(q) - beta * s(q^p)  (kills the beta root, keeps alpha)."""
    out = series[:L].copy()
    vp = v_shift(series, cfg.p, L)
    return (out - scal_mul(vp, eigen_other, cfg)) % cfg.MOD


def eight_eigenforms(cfg, lib, log, a31_exp=None, L=None):
    """The 8 predicted classical ordinary eigenforms (window length): stabilizations of
    h, h', E_1(1,chi), E_1(chi4,psi8).  Returns list of (name, U-eigenvalue, T3-eig,
    series) — h/h' entries carry a31_exp (None => 31-columns unknown)."""
    L = L or cfg.window
    z = cfg.zpow
    MOD = cfg.MOD
    tab = cfg.char_exp_table(CHI)
    chi13 = z[int(tab[cfg.p % 124])]
    out = []
    # cuspidal: Hecke roots of t^2 - a_p(h) t + chi(p)
    kp = a_p_h_exponent(cfg.p)
    ap = z[kp]
    # roots in mu12: enumerate
    roots = [z[i] for i in range(12) if (z[i] * z[i] - ap * z[i] + chi13) % MOD == 0]
    assert len(roots) == 2, "h not regular at p?"
    # BRANCH PIN: order the roots so that al/be = zeta3 (z^4) — same convention as
    # Stage-1's Case-3 combination (alpha_g/beta_g = zeta3); at p=13 this reproduces
    # DLR's stated assignment (alpha_g = 1 <-> kept U-eigenvalue zeta3).
    r0, r1 = int(roots[0]), int(roots[1])
    if r0 * modinv(r1, MOD) % MOD == z[4]:
        al, be = r0, r1
    else:
        assert r1 * modinv(r0, MOD) % MOD == z[4], "root ratio not zeta3^{+-1}?!"
        al, be = r1, r0
    hh = h_qexp(cfg, L, conj=False, a31_exp=a31_exp)
    hp = h_qexp(cfg, L, conj=True, a31_exp=None)
    # h' a_31 = sigma(a_31): defer (measured separately); keep None
    a3h = z[a_p_h_exponent(3)]
    a3hp = (-a3h) % MOD
    out.append(("h_al", int(al), int(a3h), stabilized(cfg, hh, be, L)))
    out.append(("h_be", int(be), int(a3h), stabilized(cfg, hh, al, L)))
    out.append(("hp_al", int(al), int(a3hp), stabilized(cfg, hp, be, L)))
    out.append(("hp_be", int(be), int(a3hp), stabilized(cfg, hp, al, L)))
    # Eisenstein E_1(1,chi): U-eigs {1, chi(p)}; T3 = 1 + chi(3)
    e1 = lib[("E", 1, (0, 0), CHI, 1)]["s"][:L]
    t3e1 = (1 + z[int(tab[3])]) % MOD
    out.append(("E1chi_a", int(chi13), int(t3e1), stabilized(cfg, e1, 1, L)))
    out.append(("E1chi_b", 1, int(t3e1), stabilized(cfg, e1, chi13, L)))
    # E_1(chi4, psi8): U-eigs {chi4(p), psi8(p)}; T3 = chi4(3) + psi8(3)
    e2s = lib[("E", 1, (0, 8), (1, 0), 1)]["s"][:L]
    t4 = cfg.char_exp_table((1, 0))
    t8 = cfg.char_exp_table((0, 8))
    u1_ = z[int(t4[cfg.p % 124])] if t4[cfg.p % 124] >= 0 else 0
    u2_ = z[int(t8[cfg.p % 124])] if t8[cfg.p % 124] >= 0 else 0
    t3e2 = (z[int(t4[3])] + z[int(t8[3])]) % MOD
    out.append(("E1s_a", int(u1_), int(t3e2), stabilized(cfg, e2s, u2_, L)))
    out.append(("E1s_b", int(u2_), int(t3e2), stabilized(cfg, e2s, u1_, L)))
    return out, (int(al), int(be))


def solve_in_O_window(cfg, O_win, qpiv, invq_p, vec):
    """coords c with c @ O_win == vec (solved at q-pivot columns, exact mod MOD)."""
    rhs = vec[qpiv].astype(np.int64)
    # c = rhs @ invq  where invq = (O_win[:, qpiv])^{-1}
    return vmod(rhs, invq_p, cfg)


def gate3_and_ordinary(cfg, lib, basis, A, log):
    """GATE 3: (i) known eigenforms reproduced; (ii) synthetic positive-slope crushed;
    (iii) e_ord idempotent + stabilized.  Returns the ordinary-space toolkit."""
    p, W, MOD = cfg.p, cfg.window, cfg.MOD
    E_win, piv = basis["E_win"], basis["pivcols"]
    log("")
    log("GATE 3 — KATZ BASIS + FINITE U_p MATRIX (ordinary projector)")
    O, opivs, A2k, expo, leftover_v, D = ordinary_space(cfg, A, log)
    O_win = mmod(O, E_win, cfg)
    # A_ord: U_p on O (RREF trick: coords read at opivs)
    OA = mmod(O, A, cfg)
    A_ord = np.ascontiguousarray(OA[:, opivs])
    resid = (mmod(A_ord, O, cfg) - OA) % MOD
    vA = val_arr(resid, p, cfg.mp)
    log(f"  [ordinary] A_ord ({D}x{D}) closure residual val = {vA} "
        f"[{'PASS' if vA >= cfg.m else 'FAIL'}]")
    # q-pivot columns for O_win coordinate solves (choose coprime-to-31 columns so that
    # h-partial data can be solved without knowing a_31)
    ech = EchelonFp(p, W)
    qpiv = []
    for j in range(D):
        # feed rows of O_win restricted to columns coprime to 31 (and nonzero)
        pass
    okcols = [c for c in range(1, W) if c % 31 != 0]
    Osub = O_win[:, okcols] % p
    ech2 = EchelonFp(p, len(okcols))
    order = []
    for j in range(D):
        c = ech2.add(Osub[j])
        assert c is not None, "O_win rows dependent mod p on 31-coprime columns"
        order.append(okcols[c])
    qpiv = np.array(order, dtype=np.int64)
    Oq = np.ascontiguousarray(O_win[:, qpiv])
    invq_p = gauss_inv_modp(Oq % p, p)
    invq = newton_inv_matrix(Oq, invq_p, cfg)
    # eigen-gates (Eisenstein ones now; cuspidal after a_31 measurement)
    eigs, hroots = eight_eigenforms(cfg, lib, log, a31_exp=None)
    gate_i_ok = True
    for name, uev, t3ev, s in eigs:
        if name.startswith(("E1",)):
            c = vmod(s[qpiv].astype(np.int64), invq, cfg)
            res = (vmod(c, O_win, cfg) - s[:W]) % MOD
            vres = val_arr(res, p, cfg.mp)
            cu = vmod(c, A_ord, cfg)
            dv = val_arr((cu - scal_mul(c, uev, cfg)) % MOD, p, cfg.mp)
            ok = vres >= cfg.m and dv >= cfg.m
            gate_i_ok = gate_i_ok and ok
            log(f"  GATE 3(i) {name}: in-space residual val {vres}, "
                f"U_p eigen residual val {dv}  [{'PASS' if ok else 'FAIL'}]")
    # e_ord projector, built WITHOUT any residue-degree period.  The ordinary space is
    # pure unit-eigenvalue, so A_ord is invertible mod p; and O.A = A_ord.O exactly, so
    #     P = C . A_ord^{-expo} . O ,     C = A^expo[:, opivs] = A2k[:, opivs]
    # satisfies OC = A_ord^expo, hence P^2 = P, P|_ord = id, P|_slope = 0.  A_ord^{-expo}
    # is a direct Newton-inverse power.  (The unit eigenvalues may live in an unramified
    # extension of large degree, but e_ord is Galois-invariant and lives over Z_p; the old
    # A_ord^{(p^f-1)p^mp} = I search was the wrong idea — f can exceed 12.)
    A_ord_invp = gauss_inv_modp(A_ord % p, p)
    A_ord_inv = newton_inv_matrix(A_ord, A_ord_invp, cfg, log)
    v_inv = val_arr((mmod(A_ord, A_ord_inv, cfg) - np.eye(D, dtype=np.int64)) % MOD, p, cfg.mp)
    C = np.ascontiguousarray(A2k[:, opivs])
    Mred = mat_pow_small(A_ord_inv, expo, cfg)          # A_ord^{-expo}
    OC = mmod(O, C, cfg)                                 # = A_ord^expo (since O.A = A_ord.O)
    v_fix = val_arr((mmod(OC, Mred, cfg) - np.eye(D, dtype=np.int64)) % MOD, p, cfg.mp)
    P_left = mmod(C, Mred, cfg)                          # ell x D
    inner = mmod(mmod(P_left, OC, cfg), Mred, cfg)       # ell x D (P^2 left factor)
    v_idem = val_arr(mmod((inner - P_left) % MOD, O, cfg), p, cfg.mp)
    ok3 = v_idem >= cfg.m and v_fix >= cfg.m and v_inv >= cfg.m
    log(f"  [ordinary] A_ord invertible mod p: val(A_ord.A_ord^-1 - I) = {v_inv}; "
        f"OC = A_ord^{expo}: val(A_ord^expo.A_ord^-expo - I) = {v_fix}")
    log(f"  GATE 3(iii) e_ord = C.A_ord^-expo.O: idempotency val(P^2-P) = {v_idem}, "
        f"fixes-ordinary val = {v_fix}  [{'PASS' if ok3 else 'FAIL'}]")
    # GATE 3(ii): synthetic positive-slope vector w = x - e_ord(x); U_p^k crushes it
    x = np.zeros(A.shape[0], dtype=np.int64)
    x[min(700, A.shape[0] - 1)] = 1
    xO = vmod(vmod(x, A2k, cfg)[opivs], Mred, cfg)
    x_ord = vmod(xO, O, cfg)
    w = (x - x_ord) % MOD
    slopes = []
    wk = w.copy()
    for k in range(min(2 * cfg.mp, 18)):
        wk = vmod(wk, A, cfg)
        slopes.append(val_arr(wk, p, cfg.mp))
    gate_ii_ok = slopes[-1] >= cfg.m and all(b >= a for a, b in zip(slopes, slopes[1:]))
    log(f"  GATE 3(ii) synthetic positive-slope vector: val_p(w A^k) k=1.. = {slopes} "
        f"(monotone growth to >= m={cfg.m} required)  [{'PASS' if gate_ii_ok else 'FAIL'}]")
    if D != 8:
        log(f"  [WARNING] measured ordinary dim D = {D} != 8 (classical prediction) — "
            f"extra eigensystems would need extra annihilators; constancy gate will judge")
    return dict(O=O, opivs=opivs, O_win=O_win, A2k=A2k, expo=expo, A_ord=A_ord,
                A_ord_inv=A_ord_inv, D=D, qpiv=qpiv, invq=invq, Mred=Mred, hroots=hroots,
                gate3=(gate_i_ok, gate_ii_ok, ok3), eigs_meta=eigs)


# ============================================================================
# SECTION J — a_31 measurement, Phi, and the branch projections
# ============================================================================
def measure_a31(cfg, lib, ordk, log):
    """MEASURE a_31(h): solve the partial h (coefficients at 31-coprime indices, all
    known from the certified a_p engine) in the ordinary space at 31-coprime q-pivots;
    predict the 31-columns; land a_31 on the discrete mu12 set.  [identified] tier.
    Same for h' (cross-gate: a_31(h') = sigma(a_31(h)))."""
    p, W, MOD = cfg.p, cfg.window, cfg.MOD
    z = cfg.zpow
    O_win, qpiv, invq = ordk["O_win"], ordk["qpiv"], ordk["invq"]
    al, be = ordk["hroots"]
    log("")
    log("a_31(h) — IN-HOUSE DETERMINATION (U_31 eigenvalue; printed nowhere; needed at "
        "31,62,... of Phi)")
    out = {}
    for conj, tag in ((False, "h"), (True, "hp")):
        hh = h_qexp(cfg, W, conj=conj, a31_exp=None)      # 31-multiples = 0 marker
        # stabilize (alpha branch: kill beta) — stabilization only mixes n and n/p,
        # and p != 31, so 31-coprime coefficients stay 31-coprime-determined
        hs = stabilized(cfg, hh, be, W)
        c = vmod(hs[qpiv].astype(np.int64), invq, cfg)
        pred = vmod(c, O_win, cfg)
        # residual at ALL 31-coprime window columns (the a_p-engine footprint gate)
        okcols = np.array([n for n in range(1, W) if n % 31 != 0], dtype=np.int64)
        res = (pred[okcols] - hs[okcols]) % MOD
        vres = val_arr(res, p, cfg.mp)
        # read a_31 = predicted coefficient at n=31 (stabilized form has same a_31)
        a31 = int(pred[31])
        # discrete landing on mu12 U {0}
        land = [k for k in range(12) if (a31 - z[k]) % MOD == 0]
        zero = (a31 % MOD == 0)
        v31 = val_arr(np.array([a31]), p, cfg.mp)
        log(f"  {tag}: in-space residual (31-coprime cols) val = {vres} "
            f"[{'PASS' if vres >= cfg.m else 'FAIL'}]; predicted a_31 lands on "
            f"{'0' if zero else ('zeta^' + str(land[0]) if land else 'NO mu12 element')} "
            f"(exact mod p^{cfg.mp})  "
            f"[{'IDENTIFIED (discrete mu12 landing)' if (land or zero) else 'FAIL'}]")
        out[tag] = dict(vres=vres, a31=a31, land=(land[0] if land else None), zero=zero)
    # cross-gate: a_31(h') = sigma(a_31(h)) (zeta -> -zeta: k -> k+6 for odd k)
    kh, khp = out["h"]["land"], out["hp"]["land"]
    if kh is not None and khp is not None:
        expect = (kh + 6) % 12 if kh % 2 == 1 else kh
        cross = (khp == expect)
    else:
        cross = out["h"]["zero"] and out["hp"]["zero"]
    log(f"  cross-gate a_31(h') = sigma(a_31(h)): {'PASS' if cross else 'FAIL'}")
    return out


def phi_and_project(cfg, lib, basis, ordk, curve, a31_exp, log, E_inv):
    """Build Phi = d^{-1}(f^[p]) * h, expand in the Katz basis, apply e_ord, project to
    each branch, and read the g_alpha*-coefficient by a_1-duality.  Returns per-branch
    (coefficient, diagnostics)."""
    p, W, L, MOD = cfg.p, cfg.window, cfg.LQ, cfg.MOD
    z = cfg.zpow
    E_win, piv = basis["E_win"], basis["pivcols"]
    O, opivs, O_win = ordk["O"], ordk["opivs"], ordk["O_win"]
    A2k, expo, A_ord, D = ordk["A2k"], ordk["expo"], ordk["A_ord"], ordk["D"]
    qpiv, invq, A_ord_inv = ordk["qpiv"], ordk["invq"], ordk["A_ord_inv"]
    al, be = ordk["hroots"]
    t0 = time.time()
    f = weight2_f_ints(cfg, curve["ainv"], curve["cond"], L)
    Fb = serre_dinv(f, cfg)
    hh = h_qexp(cfg, L, conj=False, a31_exp=a31_exp)
    Phi = kron_mul(Fb, hh, L, cfg)
    log(f"  [{curve['label']}] Phi = d^-1(f^[p]) * h built (q^{L})  [{time.time()-t0:.0f}s]")
    # Lauder step 6(a): U_p once on the q-expansion, then solve Katz coordinates
    UPhi = Phi[::p][:W]
    alpha = vmod(UPhi[piv].astype(np.int64), E_inv, cfg)
    res = (vmod(alpha, E_win, cfg) - UPhi) % MOD
    v_alpha = val_arr(res, p, cfg.mp)
    log(f"  [{curve['label']}] U_p(Phi) Katz-coordinate solve: full-window residual "
        f"val = {v_alpha} (Lauder Note 2.3(1) gate; m'-m = {cfg.mp - cfg.m} loss budget)  "
        f"[{'PASS' if v_alpha >= cfg.m else 'FAIL'}]")
    # e_ord: total exponent r_exp: alpha is U^1 Phi; apply A^{expo} then A_ord^{r-expo-1}
    y = vmod(alpha, A2k, cfg)                       # U^{1+expo} Phi
    yO = y[opivs]
    res2 = (vmod(yO, O, cfg) - y) % MOD
    v_inO = val_arr(res2, p, cfg.mp)
    # yO = ordinary coords of U^{1+expo}Phi = A_ord^{1+expo} . (e_ord(Phi) coords);
    # recover e_ord(Phi) by A_ord^{-(1+expo)} (direct inverse power, no period needed).
    Mred = mat_pow_small(A_ord_inv, expo + 1, cfg)
    v_ord = vmod(yO, Mred, cfg)                     # e_ord(Phi) coords in O
    log(f"  [{curve['label']}] U^(1+{expo})Phi lies in ordinary span: residual val = "
        f"{v_inO}  [{'PASS' if v_inO >= cfg.m else 'FAIL'}]; "
        f"e_ord = (.)_ord . A_ord^-(1+{expo})")
    # ---- branch projections ----
    tab3 = cfg.char_exp_table(CHI)
    a3h = z[a_p_h_exponent(3)]
    t3_eigs = {"h": int(a3h), "hp": int((-a3h) % MOD),
               "E1chi": int((1 + z[int(tab3[3])]) % MOD),
               "E1s": int((z[int(cfg.char_exp_table((1, 0))[3])]
                           + z[int(cfg.char_exp_table((0, 8))[3])]) % MOD)}
    # T_3 matrix on O (q-expansion route, solved at q-pivots)
    chi3 = z[int(tab3[3])]
    W3 = W // 3
    T3rows = np.zeros((D, W), dtype=np.int64)
    for j in range(D):
        row = O_win[j]
        t3 = row[3 * np.arange(W3)].copy()
        add2 = np.zeros(W3, dtype=np.int64)
        idx = np.arange(0, W3, 3)
        add2[idx] = row[np.arange(len(idx))]
        T3rows[j, :W3] = (t3 + scal_mul(add2, chi3, cfg)) % MOD
    # q-pivots must be < W3 for the T3 solve: build a second pivot set
    okc = [c for c in range(1, W3) if c % 31 != 0]
    ech3 = EchelonFp(p, len(okc))
    qp3 = []
    for j in range(D):
        cc = ech3.add(O_win[j, okc] % p)
        assert cc is not None
        qp3.append(okc[cc])
    qp3 = np.array(qp3, dtype=np.int64)
    invq3 = newton_inv_matrix(np.ascontiguousarray(O_win[:, qp3]),
                              gauss_inv_modp(O_win[:, qp3] % p, p), cfg)
    M_T3 = mmod(np.ascontiguousarray(T3rows[:, qp3]), invq3, cfg)
    resT3 = (mmod(M_T3, O_win[:, :W3], cfg) - T3rows[:, :W3]) % MOD
    v_T3 = val_arr(resT3, p, cfg.mp)
    M_U = A_ord
    out = {}
    for br, keep_u in (("alpha", al), ("beta", be)):
        # annihilate the other three T3-eigensystems, then the other U-eigenvalue
        v = v_ord.copy()
        keep_t3 = t3_eigs["h"]
        for name, mu in t3_eigs.items():
            if name == "h":
                continue
            v = (vmod(v, M_T3, cfg) - scal_mul(v, mu, cfg)) % MOD
            v = scal_mul(v, modinv(keep_t3 - mu, MOD), cfg)
        other_u = be if br == "alpha" else al
        # U-eigenvalues within the cusp block: {al, be}
        v = (vmod(v, M_U, cfg) - scal_mul(v, other_u, cfg)) % MOD
        v = scal_mul(v, modinv(keep_u - other_u, MOD), cfg)
        R = vmod(v, O_win, cfg)                    # the projected residue, window q-exp
        # g_alpha* = stabilization of h with U-eigenvalue keep_u (kill the other root)
        gstar = stabilized(cfg, h_qexp(cfg, W, conj=False, a31_exp=a31_exp), other_u, W)
        # constancy: R must be a CONSTANT multiple of gstar at every unit index
        ratios = {}
        c_val = None
        n_checked = 0
        distinct = set()
        for n in range(1, min(W, 400)):
            gv = int(gstar[n])
            if gv % p == 0:
                continue
            r = int(R[n]) * modinv(gv, MOD) % MOD
            n_checked += 1
            distinct.add(r)
            if c_val is None:
                c_val = r
        # exact agreement across indices (no averaging)
        const_ok = len(distinct) == 1
        # a_1-duality: c = R_1 / gstar_1 = R_1
        c1 = int(R[1]) % MOD
        out[br] = dict(c=c1, const_ok=const_ok, n_checked=n_checked,
                       n_distinct=len(distinct), v_alpha=v_alpha, v_inO=v_inO, v_T3=v_T3)
        log(f"  [{curve['label']}] branch {br} (U-eig kept = {'alpha_h' if keep_u == al else 'beta_h'}): "
            f"R = c * g_alpha* at {n_checked} unit indices, distinct multipliers = "
            f"{len(distinct)} (1 required)  [{'PASS' if const_ok else 'FAIL'}]; "
            f"c = {c1} mod p^{cfg.mp}")
    out["v_T3"] = v_T3
    return out


# ============================================================================
# SECTION K — drivers: sizing report, calibration/deliverable runs, GATE 5
# ============================================================================
def val_int(x, p, cap=40):
    x = int(x)
    if x == 0:
        return cap
    v = 0
    while x % p == 0 and v < cap:
        x //= p
        v += 1
    return v


def digits_of_agreement(a, b, p, cap):
    return val_int((int(a) - int(b)) % (p ** cap), p, cap)


def sizing_report(log):
    """The p=37 sizing arithmetic, BOTH configurations (per coordinator directive)."""
    log("")
    log("=" * 78)
    log("p=37 SIZING (Lauder Alg 2.1 step 1 arithmetic, stated before any run)")
    log("=" * 78)
    log("Tame level rule: N must satisfy cond(f) | N*p^inf and 124 | N*p^inf.")
    log("  * at p=13: cond(26b)=26=2*13, cond(52b)=52=4*13 -> the 13-part sits in the")
    log("    p-slot; N = 124.  (DLR: 'the prime 13 ... divides the level of f, which can")
    log("    thus be viewed as overconvergent 13-adic forms of tame level' 124.)")
    log("  * at p=37: 13 is now TAME -> N = lcm(26,124) = 1612 = 4*13*31 for 26b/52b;")
    log("    but N = 124 for the conductor-124 curve 124a (DLR Ex 5.4 rank-(1,1) curve).")
    for (name, N, mu, curves) in (("A: 124a at p=37 (FEASIBLE)", 124, 192, "124a"),
                                  ("B: 26b/52b at p=37 (THE WALL)", 1612, 2688, "26b, 52b")):
        log(f"  CONFIG {name}: tame level {N}, mu = {mu}, curves: {curves}")
        for m in (8, 6):
            p = 37
            n = ((p + 1) * (m + 1)) // (p - 1)
            kn = 1 + (p - 1) * n
            # dim S_k ~ (k-1)/12 mu - lam/2; lam = 4 (N=124), 8 (N=1612); Eis small
            lam = 4 if N == 124 else 8
            dS = (kn - 1) * mu // 12 - lam // 2
            eis = 4 if N == 124 else 50
            ell = dS + eis
            sturm = (kn * mu + 11) // 12
            lq = sturm * p
            mem = ell * ell * 8 / 1e9
            matmul_ops = 6 * ell ** 3
            log(f"    m={m}: n_rungs={n}, k_n={kn}, ell~{ell}, Sturm={sturm}, "
            f"q-range={lq}, matrix {ell}x{ell} ({mem:.1f} GB int64/matrix), "
            f"~{matmul_ops:.1e} int64-ops/matmul")
    log("  WALL (measured arithmetic, not opinion): config B at m=8 needs ell~72,600:")
    log("    42 GB per matrix (x3 live), ~2.3e15 int64-ops per matmul, ~25 matmuls,")
    log("    plus ~72,600 full-precision products of q-length 2.7e6 — months on this")
    log("    machine.  Even m=2 (2 digits, useless) needs ell~24,200 (4.7 GB/matrix).")
    log("    26b/52b at p=37 is a DIFFERENT INSTRUMENT CLASS (distributed/C++), not a")
    log("    parameter choice.  The feasible p=37 ES closure at tame level 124 is 124a.")


def run_curve_gate5(cfg, lib, basis, ordk, E_inv, curve, a31_exp, log, anchors=None):
    """Phi pipeline + GATE 5 anchor comparison for one curve.  anchors: dict with
    'alpha'/'beta' target integers (DLR printed integrals), or None (first determination)."""
    res = phi_and_project(cfg, lib, basis, ordk, curve, a31_exp, log, E_inv)
    out = {}
    for br in ("alpha", "beta"):
        c = res[br]["c"]
        rec = dict(c=c, const_ok=res[br]["const_ok"])
        if anchors and anchors.get(br) is not None:
            tgt = anchors[br] % cfg.MOD
            d = digits_of_agreement(c, tgt, cfg.p, cfg.mp)
            rec["anchor"] = int(tgt)
            rec["digits"] = d
            v_t = val_int(tgt, cfg.p)
            eff = d - v_t                     # significant digits past the valuation
            rec["pass"] = d >= cfg.m
            log(f"  GATE 5 [{curve['label']}] branch {br}: LHS c = {c}, anchor = {tgt} "
                f"(mod p^{cfg.mp}); val_p(c - anchor) = {d} (target >= m = {cfg.m})  "
                f"[{'AGREE-TO-PRECISION p^' + str(min(d, cfg.m)) if rec['pass'] else 'FAIL'}]")
        out[br] = rec
    return out


def cross_ratio_gate(cfg, label, resA, resB, anchA, anchB, log):
    """Cross-curve ratio: shared g,h normalization cancels."""
    for br in ("alpha", "beta"):
        cA, cB = resA[br]["c"], resB[br]["c"]
        vB = val_int(cB, cfg.p)
        if vB >= cfg.m:
            log(f"  [ratio {label} {br}] denominator non-unit to p^{cfg.m}; skipped")
            continue
        m_eff = cfg.mp - vB
        ratio_lhs = int(cA) * modinv(int(cB) // cfg.p ** vB, cfg.MOD) % cfg.MOD
        aA, aB = anchA[br] % cfg.MOD, anchB[br] % cfg.MOD
        ratio_anch = int(aA) * modinv(int(aB) // cfg.p ** vB, cfg.MOD) % cfg.MOD
        d = digits_of_agreement(ratio_lhs, ratio_anch, cfg.p, m_eff)
        log(f"  GATE 5-ratio [{label}] branch {br}: val_p(ratio_LHS - ratio_anchor) = {d} "
            f"(of {m_eff} available)  "
            f"[{'PASS' if d >= min(cfg.m, m_eff) else 'FAIL'}]")


def build_all(cfg, log, cache_tag, a31_exp=None, allow_filtration_overshoot=True):
    """Gates 1-3 + the machinery; caches the heavy matrices.  a31_exp seeds h,h' at rung 0."""
    nf = Zeta12Exact()
    a31tag = "a31none" if a31_exp is None else f"a31_{a31_exp}"
    cache_f = os.path.join(CACHE, f"katz_{cache_tag}_{a31tag}.npz")
    lib = build_block_library(cfg, log, nf)
    g1 = gate1(cfg, lib, log, nf)
    gh = gate_h_printed(cfg, log)
    dims = dims_table(cfg, log)
    if os.path.exists(cache_f):
        log(f"  [cache] loading basis+matrices from {cache_f}")
        z = np.load(cache_f, allow_pickle=True)
        basis = dict(E_win=z["E_win"], E_upw=z["E_upw"], pivcols=z["pivcols"],
                     row_meta=None, rows_full=None)
        A, E_inv = z["A"], z["E_inv"]
        vA = int(z["vA"])
        log(f"  [cache] Katz-closure residual val (recorded) = {vA}")
    else:
        basis = build_basis(cfg, lib, log, dims, a31_exp=a31_exp,
                            allow_filtration_overshoot=allow_filtration_overshoot)
        basis["rows_full"] = None            # release ~400 MB
        A, E_inv, vA = build_up_matrix(cfg, basis, log)
        np.savez_compressed(cache_f, E_win=basis["E_win"], E_upw=basis["E_upw"],
                            pivcols=basis["pivcols"], A=A, E_inv=E_inv, vA=vA)
        log(f"  [cache] saved {cache_f}")
    ordk = gate3_and_ordinary(cfg, lib, basis, A, log)
    return dict(nf=nf, lib=lib, dims=dims, basis=basis, A=A, E_inv=E_inv, vA=vA,
                ordk=ordk, g1=g1, gh=gh)


def run13(log, m=8, curves=("26b", "52b", "124a")):
    log("=" * 78)
    log(f"p = 13 CALIBRATION RUN (m = {m}; claims stated at 13^{m}, carried at 13^{m+1})")
    log("=" * 78)
    cfg = Cfg(13, m, zeta_res=7)
    log(f"  sizing: n_rungs={cfg.n_rungs}, m'={cfg.mp}, window(Sturm)={cfg.window}, "
        f"q-range={cfg.LQ}, MOD=13^{cfg.mp}")
    ctx = build_all(cfg, log, cache_tag=f"p13_m{m}")
    a31 = measure_a31(cfg, ctx["lib"], ctx["ordk"], log)
    a31_exp = a31["h"]["land"] if not a31["h"]["zero"] else None
    log(f"  a_31 status: measured in-house = "
        f"{'0' if a31['h']['zero'] else 'zeta^%d' % a31['h']['land']} "
        f"[identified: discrete mu12+{{0}} landing, gated by the {cfg.window}-column "
        f"31-coprime residual]; used for Phi below.")
    tab = {"26b": (CURVE_26b, dict(alpha=CURVE_26b['intgral_gα'], beta=CURVE_26b['intgral_gβ'])),
           "52b": (CURVE_52b, dict(alpha=CURVE_52b['intgral_gα'], beta=CURVE_52b['intgral_gβ'])),
           "124a": (CURVE_124a, dict(alpha=CURVE_124a['intgral_ga'], beta=CURVE_124a['intgral_gb']))}
    log("")
    log("GATE 4/5 — THE ES INTEGRAL vs DLR PRINTED ANCHORS (both branches, per curve)")
    log(f"  test-vector pin: (f_breve, h_breve) = (f, h) plain; gamma = dual basis to "
        f"g_alpha* (a_1-normalized stabilization), per DLR's own computations;")
    log(f"  branch pin: alpha <-> kept U-eigenvalue u with u/u' = zeta3 (Stage-1 Case-3 "
        f"combination convention; = DLR's alpha_g=1 branch at p=13).")
    results = {}
    for name in curves:
        cur, anch = tab[name]
        results[name] = run_curve_gate5(cfg, ctx["lib"], ctx["basis"], ctx["ordk"],
                                        ctx["E_inv"], cur, a31_exp, log, anchors=anch)
    if "26b" in results and "52b" in results:
        cross_ratio_gate(cfg, "26b/52b", results["26b"], results["52b"],
                         tab["26b"][1], tab["52b"][1], log)
    return cfg, ctx, results, a31


def run37(log, m=8):
    log("=" * 78)
    log(f"p = 37 DELIVERABLE RUN — 124a at tame level 124 (m = {m})")
    log("  (26b/52b at p=37 need tame level 1612: see the sizing WALL above.)")
    log("=" * 78)
    cfg = Cfg(37, m, zeta_res=8)     # Stage-1's own p=37 embedding pin (zeta = 8 mod 37)
    log(f"  sizing: n_rungs={cfg.n_rungs}, m'={cfg.mp}, window(Sturm)={cfg.window}, "
        f"q-range={cfg.LQ}, MOD=37^{cfg.mp}")
    ctx = build_all(cfg, log, cache_tag=f"p37_m{m}")
    a31 = measure_a31(cfg, ctx["lib"], ctx["ordk"], log)
    a31_exp = a31["h"]["land"] if not a31["h"]["zero"] else None
    log("")
    log("GATE 4 + FIRST DETERMINATION — the ES integral at p=37 for 124a, both branches")
    res = run_curve_gate5(cfg, ctx["lib"], ctx["basis"], ctx["ordk"], ctx["E_inv"],
                          CURVE_124a, a31_exp, log, anchors=None)
    for br in ("alpha", "beta"):
        c = res[br]["c"]
        log(f"  [first-determination] 124a p=37 branch {br}: "
            f"LHS integral = {c} mod 37^{cfg.mp} (v_37 = {val_int(c, 37)}) "
            f"[constancy {'PASS' if res[br]['const_ok'] else 'FAIL'}]")
    return cfg, ctx, res, a31


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run13"
    append = os.path.exists(RESULTS_PATH) and mode != "test"
    log = Log(RESULTS_PATH, append=append)
    t0 = time.time()
    log("")
    log("#" * 78)
    log(f"# KATZ ENGINE — mode {mode} — {time.strftime('%Y-%m-%d %H:%M:%S')}")
    log("#" * 78)
    if mode == "sizing":
        sizing_report(log)
    elif mode == "test":
        cfg = Cfg(13, 8, zeta_res=7)
        log(f"  sizing: n_rungs={cfg.n_rungs}, m'={cfg.mp}, window={cfg.window}, "
            f"q-range={cfg.LQ}")
        ctx = build_all(cfg, log, cache_tag="p13_m8")
        a31 = measure_a31(cfg, ctx["lib"], ctx["ordk"], log)
        log(f"  [test mode] gates 1-3 + a_31 measurement complete")
    elif mode == "run13":
        run13(log)
        sizing_report(log)
    elif mode == "run37":
        run37(log)
    else:
        raise SystemExit(f"unknown mode {mode}")
    log(f"\n  [runtime] mode {mode}: {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
