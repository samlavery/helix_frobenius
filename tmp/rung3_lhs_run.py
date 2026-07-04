"""RUNG 3 STAGE 2 driver — the LHS iterated integral by the eigenform-basis projection recipe,
gated against the Stage-1 RHS.  See rung3_lhs.py for the machinery.

Recipe (feasible, no q-explosion): isolate the g_α*-component of Φ = d^{-1}(f)·h by
  (T_ℓ − a_ℓ(h'*)) for a small good ℓ  [kills the Galois-conjugate h'-eigensystems and the
   non-ordinary part, costing only a factor ℓ of q-precision],
then (U_13 − β_g)/(α_g − β_g)  [splits g_α* from g_β*, the one U_p step],
then read the g_α* multiplier by the a_1-duality γ̆.

TIER: internal gates [p-adic certified]; the LHS-vs-RHS match is agreement-to-precision (NOT
identification); the g_α*-nonvanishing we divide by is a flagged numerical hypothesis.
"""
import sys
import time

import sympy as _sp
from rung3_lhs import (weight1_h_qexp, weight2_f_qexp, QExp, serre_dinv, U_p, T_ell,
                       a_p_h_exponent, _ind31_mod3, _legendre)
from rung3_rhs import Unramified, Qpf


def embedding(p, prec, zeta_res=7):
    mod = p ** prec

    def hensel12(seed):
        x = seed % mod
        for _ in range(2 * prec + 5):
            x = (x - (pow(x, 12, mod) - 1) * pow(12 * pow(x, 11, mod) % mod, -1, mod)) % mod
        return x
    zeta = hensel12(zeta_res)
    assert pow(zeta, 12, mod) == 1 and zeta % p == zeta_res % p
    return zeta, mod


def chi_exp(p):
    """Exponent m of χ(p) = ζ12^m (level-124 nebentype)."""
    i = _ind31_mod3(p)
    return ((0 if p % 4 == 1 else 6) + 4 * i) % 12


def build_forms(U, zeta, mod, Mq, ainv, cond):
    """Return (f, h) q-expansions to q^Mq."""
    zeta12 = Qpf.from_U(U, U.from_int_vec([zeta]))
    bad = {2: Qpf.from_U(U, U.from_int_vec([pow(zeta, 3, mod)]))}
    h = weight1_h_qexp(U, Mq, zeta12, bad_ap=bad)
    f = weight2_f_qexp(U, ainv, cond, Mq)
    return f, h


def galpha_star_qexp(U, zeta, mod, Mq, alpha_h_exp, conjugate=False):
    """g_α* = (g_α) ⊗ χ, with g = h*.  For good ℓ: a_ℓ(g_α*) = χ(ℓ)·a_ℓ(g) = χ(ℓ)·conj(a_ℓ(h)).
    conj(ζ12^k) = ζ12^{-k}.  Build its q-expansion (Hecke-multiplicative from prime values).
    `conjugate=True` builds h'*-based (the Galois conjugate ζ→−ζ, i.e. a_ℓ(h) → a_ℓ(h) with
    ζ12^k → ζ12^{-k+... }); here we build g_α* only (conjugate handled via a_ℓ)."""
    def zk(k):
        return pow(zeta, k % 12, mod)
    a = [0] * Mq
    if Mq > 1:
        a[1] = 1
    for q in _sp.primerange(2, Mq):
        q = int(q)
        if 124 % q == 0:
            aq = 0            # bad prime: leave (not needed for the small-ℓ separation)
            chiq = 0
        else:
            k = a_p_h_exponent(q)
            if k is None:
                aq = 0
            else:
                # a_ℓ(g_α*) = χ(ℓ)·conj(a_ℓ(h)) = ζ^{chi_exp - k}
                aq = zk(chi_exp(q) - k)
            chiq = zk(chi_exp(q))   # χ(ℓ)² enters the twisted-form power recursion... keep simple
        qe = q
        prev, cur = 1, aq
        while qe < Mq:
            a[qe] = cur % mod
            nxt = (aq * cur - (chiq if 124 % q else 0) * prev) % mod
            prev, cur = cur, nxt
            qe *= q
    _mult_fill(a, Mq, mod)
    return QExp(U, [Qpf.from_U(U, U.from_int_vec([x % mod])) for x in a], Mq)


def _mult_fill(a, M, mod):
    spf = list(range(M))
    i = 2
    while i * i < M:
        if spf[i] == i:
            for j in range(i * i, M, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    for n in range(2, M):
        p = spf[n]
        e, t = 0, n
        while t % p == 0:
            t //= p
            e += 1
        pe = p ** e
        m = n // pe
        if m != 1:
            a[n] = (a[pe] * a[m]) % mod


def _qpf_inv(a):
    U = a.U
    return Qpf.from_U_with_exp(U, -a.exp, U.inv_unit(a.u))


def run_p13(P, prec=12, Mq=3000):
    p = 13
    zeta, mod = embedding(p, prec)
    U = Unramified(p, [0, 1], prec)

    def zk(k):
        return Qpf.from_U(U, U.from_int_vec([pow(zeta, k % 12, mod)]))

    P(f"  embedding ζ12 ≡ 7 mod 13 (order 12); working precision 13^{prec}, q^{Mq}.")
    # α_g, β_g : g = h*, at p=13 the Hecke poly of h has roots β_h=1, α_h=ζ3 (DLR, level 124),
    # giving α_g = 1, β_g = ζ3² = ζ12^8.  (DLR Example 5.4.)
    alpha_g = zk(0)          # α_g = 1
    beta_g = zk(8)           # β_g = ζ3² = ζ12^8
    # a_3(h'*) : the Galois-conjugate eigensystem's T_3-eigenvalue, to annihilate.
    # a_3(g_α*) = χ(3)·conj(a_3(h)); a_3(h'*) = χ(3)·conj(a_3(h')) with a_3(h') = conj(a_3(h)).
    k3 = a_p_h_exponent(3)                    # a_3(h) = ζ12^{k3}
    a3_gas = zk(chi_exp(3) - k3)              # a_3(g_α*)
    a3_hps = zk(chi_exp(3) + k3)              # a_3(h'*) = χ(3)·conj(conj(a_3(h))) = ζ^{chi+ k3}
    chi3 = zk(chi_exp(3))

    for (label, ainv, cond, anchor) in CURVES13:
        t0 = time.time()
        f, h = build_forms(U, zeta, mod, Mq, ainv, cond)
        Fbar = serre_dinv(f)
        Phi = Fbar.mul(h)
        # (T_3 − a_3(h'*)) : kill the h'-systems (weight-1 T_ℓ)
        T3 = T_ell(Phi, 3, chi3, 1)
        R = T3.sub(Phi.scal(a3_hps))
        # (U_13 − β_g)/(α_g − β_g) : pick the α_g line
        UR = U_p(R)
        R = UR.sub(R.scal(beta_g)).scal(_qpf_inv(alpha_g.sub(beta_g)))
        # γ̆ : read the g_α* multiplier.  g_α* has a_1 = 1, so c = a_1(R)/a_1(g_α*) = a_1(R)
        # normalized by the same T_3+U_13 chain applied to g_α* itself (so the projector's
        # scalar cancels).  Compute the chain's action on g_α* at a_1:
        gas = galpha_star_qexp(U, zeta, mod, Mq, k3)
        T3g = T_ell(gas, 3, chi3, 1)
        Rg = T3g.sub(gas.scal(a3_hps))
        URg = U_p(Rg)
        Rg = URg.sub(Rg.scal(beta_g)).scal(_qpf_inv(alpha_g.sub(beta_g)))
        # both R and Rg are multiples of g_α*; the LHS iterated integral is their ratio at a_1
        a1R = R.coeff(1)
        a1g = Rg.coeff(1)
        hyp_ok = a1g.val() < prec
        if not hyp_ok:
            P(f"  {label}: g_α* normalization a_1 vanished (v={a1g.val()}); "
              f"projector degenerate — HYPOTHESIS FAIL"); continue
        c = a1R.div(a1g)
        cv = (pow(p, c.exp, mod) * c.u[0]) % mod if c.exp >= 0 else None
        P(f"  {label}: LHS c (g_α* multiplier) computed  [{time.time()-t0:.0f}s]")
        P(f"      v_13(LHS) = {c.val()},  LHS/13^v mod 13^6 = "
          f"{(cv // p ** c.val()) % p ** 6 if cv is not None else 'neg'}")
        # compare to DLR anchor (= the RHS Stage-1 reproduced): agreement-to-precision
        digits = min(6, prec - 2)
        m = p ** digits
        lhs_res = cv % m if cv is not None else None
        anchor_res = anchor % m
        agree = (lhs_res == anchor_res)
        P(f"      DLR/RHS anchor mod 13^{digits} = {anchor_res};  LHS mod 13^{digits} = "
          f"{lhs_res};  AGREE = {agree}  [agreement-to-precision, NOT identification]")


# 26b/52b at p=13; anchor = DLR published ∫_{γgα} f·h (α branch), = the Stage-1 RHS value.
CURVES13 = [
    ("26b", (1, -1, 1, -3, 3), 26, 6721481652857547558786),
    ("52b", (0, 0, 0, 1, -10), 52, -1602512412162131808818),
]


def main():
    def P(s=""):
        print(s)
        buf.append(s)
    buf = []
    P("RUNG 3 STAGE 2 — LHS iterated integral (eigenform-basis recipe) vs Stage-1 RHS")
    P("=" * 78)
    run_p13(P)
    with open("/Users/samuellavery/work/helix_frobenius/tmp/rung3_lhs_results.txt", "w") as f:
        f.write("\n".join(buf) + "\n")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        def P(s=""):
            print(s)
        run_p13(P, prec=6, Mq=500)
    else:
        main()
