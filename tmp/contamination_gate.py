"""GATE 1 (team-lead, decisive): SYNTHETIC-CONTAMINATION CONTROL.
Build a KNOWN non-ordinary q-expansion η (positive U_13-slope, verified: U_13^k η decays),
add it to Φ at O(1) amplitude, rerun the FULL T_3+U_13 projector + g_α* reading.  The g_α*
multiplier must be UNCHANGED to working precision.  If it moves, the finite T_ℓ·U_13 composite
does NOT kill the non-ordinary tail — silent leakage into the a_1 reading — and we measure the
suppression factor.

This directly tests the load-bearing claim ('T_ℓ also kills the non-ordinary part'), which is
FALSE in general (finite Hecke polynomial annihilates finitely many eigensystems).
"""
import sys
import time
import random
import sympy as sp

from rung3_lhs import (weight1_h_qexp, weight2_f_qexp, QExp, serre_dinv, U_p, T_ell,
                       a_p_h_exponent, _ind31_mod3)
from rung3_rhs import Unramified, Qpf
from rung3_lhs_run import embedding, chi_exp, build_forms, galpha_star_qexp, _qpf_inv


def project_read(Phi, gas, U, mod, p, prec, alpha_g, beta_g, a3_hps, chi3):
    """The T_3+U_13 projector + γ̆ read: returns c = a_1(R)/a_1(Rg) (the g_α* multiplier)."""
    T3 = T_ell(Phi, 3, chi3, 1)
    R = T3.sub(Phi.scal(a3_hps))
    UR = U_p(R)
    R = UR.sub(R.scal(beta_g)).scal(_qpf_inv(alpha_g.sub(beta_g)))
    T3g = T_ell(gas, 3, chi3, 1)
    Rg = T3g.sub(gas.scal(a3_hps))
    URg = U_p(Rg)
    Rg = URg.sub(Rg.scal(beta_g)).scal(_qpf_inv(alpha_g.sub(beta_g)))
    a1R, a1g = R.coeff(1), Rg.coeff(1)
    if a1g.val() >= prec:
        return None
    return a1R.div(a1g)


def build_nonordinary(U, mod, p, Mq, seed=1):
    """A KNOWN non-ordinary q-expansion η: random Z_p coefficients.  Verified non-ordinary by
    U_13^k η → 0 (positive slope).  (The ordinary space is finite-dim; a generic q-expansion is
    non-ordinary.)  Returns (η, verified_slope_positive)."""
    random.seed(seed)
    coeffs = [Qpf.from_int(U, 0)] + [Qpf.from_int(U, random.randrange(mod)) for _ in range(Mq - 1)]
    eta = QExp(U, coeffs, Mq)
    # verify: U_13^k η at low indices shrinks in q-support / decays.  A cleaner slope witness:
    # apply U_13 twice; a non-ordinary form's U_13-iterate valuations do NOT stay bounded like an
    # ordinary form's.  We report v_13 of (U_13^2 η)_1 vs η_1 as a coarse slope indicator.
    Ueta = U_p(eta)
    UUeta = U_p(Ueta)
    return eta, (eta.coeff(1).val(), Ueta.coeff(1).val(), UUeta.coeff(1).val())


def run(P, prec=12, Mq=1400):
    p = 13
    zeta, mod = embedding(p, prec)
    U = Unramified(p, [0, 1], prec)

    def zk(k):
        return Qpf.from_U(U, U.from_int_vec([pow(zeta, k % 12, mod)]))
    alpha_g, beta_g = zk(0), zk(8)
    k3 = a_p_h_exponent(3)
    a3_hps = zk(chi_exp(3) + k3)
    chi3 = zk(chi_exp(3))
    gas = galpha_star_qexp(U, zeta, mod, Mq, k3)

    for (label, ainv, cond) in [("26b", (1, -1, 1, -3, 3), 26)]:
        f, h = build_forms(U, zeta, mod, Mq, ainv, cond)
        Phi = serre_dinv(f).mul(h)
        c0 = project_read(Phi, gas, U, mod, p, prec, alpha_g, beta_g, a3_hps, chi3)
        if c0 is None:
            P(f"  {label}: projector degenerate (a_1(g_α*) vanished)"); continue
        v0 = c0.val()

        # synthetic non-ordinary contaminant at O(1) amplitude
        eta, slope = build_nonordinary(U, mod, p, Mq)
        P(f"  {label}: contaminant η slope witness v_13((U_13^k η)_1) k=0,1,2 = {slope} "
          f"(non-ordinary if not bounded-constant)")
        Phi_c = Phi.add(eta)
        c1 = project_read(Phi_c, gas, U, mod, p, prec, alpha_g, beta_g, a3_hps, chi3)
        if c1 is None:
            P(f"  {label}: projector degenerate after contamination"); continue
        # how much did the reading move?
        diff = c0.sub(c1)
        moved_at = diff.val()   # v_13 of (c0 - c1); >= prec means UNCHANGED to precision
        P(f"  {label}: v_13(clean read c0) = {v0};  v_13(c0 − c_contaminated) = {moved_at} "
          f"(/{prec})")
        clean = moved_at >= prec
        P(f"  {label}: GATE 1 — g_α* reading UNCHANGED under O(1) non-ordinary contamination: "
          f"{'PASS' if clean else 'FAIL — non-ordinary LEAKS into the read'}")
        if not clean:
            supp = moved_at - v0   # how many digits the contaminant is suppressed by
            P(f"      suppression: the O(1) contaminant moved the read at valuation {moved_at} "
              f"(vs read valuation {v0}); leakage is {'below' if supp>0 else 'AT/ABOVE'} the "
              f"read's own scale.  A finite T_3·U_13 cannot annihilate the infinite non-ord tail.")


if __name__ == "__main__":
    def P(s=""):
        print(s, flush=True)
    run(P)
