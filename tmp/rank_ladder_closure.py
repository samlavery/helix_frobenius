#!/usr/bin/env python3
"""
rank_ladder_closure.py -- the carrier-native rank ladder on the REAL trace-formula
terms, r = 0..13 (the r > 6 territory included), extending dual_closure_test.

Object: the actual master-formula dual terms dual_xi = pref * Kl_{l,f}(xi) * A_{l,f}(xi)
(poisson_dual.dual_profile; p=2, k=1, elliptic branch, f<=2, l<=3) with the Sym^r
weight U_r(x) -- the (r+1)-clock Satake character on the elliptic band.  No Altug
transform, no window, no nu-chart: the orbital data itself on its own clocks.

THE LADDER CLAIMS (pre-registered):
  ODD r (the mu_2 parity clock): U_r is odd, the assembly preserves x-parity, so
    * the DC term vanishes:            |dual_0| / M  <= 1e-8
    * the signed xi!=0 sum closes:     |S| / M       <= 1e-8   at xi_max = 80
    EXACTLY, at every odd rank 1..13 -- identity-class closure on real terms.
  EVEN r (the detecting channel): U_r has nonzero mean, so
    * the detecting residue is present: |dual_0| / M >= 1e-3
    * the xi!=0 signed tail CONVERGES:  |S(80) - S(40)| / M <= 1e-3
    and the ledger books T = dual_0 + S (the productivity split).
  CONTROL: a random +-1 x-mask (dual_profile_scrambled) destroys the parity
    clock: scrambled |S|/M at odd r must exceed the true value by >= 100x.
  FALSIFIER: any odd rank failing the closure criteria = parity-clock breaking
    in the real assembly at that rank; reported as prominently as a success.

Run: python3 tmp/rank_ladder_closure.py    Out: tmp/rank_ladder_closure_results.txt
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poisson_dual as PD

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "rank_ladder_closure_results.txt")

_f = open(OUT, "w")


def emit(s=""):
    print(s, flush=True)
    _f.write(s + "\n")
    _f.flush()


def measure(r, xi_max, nx=500):
    prof = PD.dual_profile(r, p=2, k=1, sign=-1, fmax=2, lmax=3,
                           xi_max=xi_max, nx=nx)
    d0 = prof.get(0, 0j)
    S = sum(v for xi, v in prof.items() if xi != 0)
    M = sum(abs(v) for xi, v in prof.items() if xi != 0)
    return d0, S, M


def main():
    t0 = time.time()
    emit("RANK LADDER on the real master-formula dual terms (p=2, k=1, elliptic)")
    emit("odd r: exact parity closure     even r: detecting residue + converged tail")
    emit("=" * 86)
    emit(f"{'r':>3} {'|dual_0|/M':>12} {'|S(40)|/M':>12} {'|S(80)|/M':>12} "
         f"{'|S80-S40|/M':>12}  verdict")
    odd_pass = odd_all = even_pass = even_all = 0
    s_true_odd = {}
    for r in range(0, 14):
        d0_40, S_40, M_40 = measure(r, 40)
        d0, S, M = measure(r, 80)
        if M <= 0:
            emit(f"{r:>3}  -- empty tail, skipped")
            continue
        rd0 = abs(d0) / M
        rS40 = abs(S_40) / M
        rS = abs(S) / M
        cauchy = abs(S - S_40) / M
        if r % 2 == 1:
            odd_all += 1
            ok = (rd0 <= 1e-8) and (rS <= 1e-8)
            odd_pass += int(ok)
            s_true_odd[r] = rS
            verdict = "EXACT parity closure" if ok else "PARITY BREAK (falsifier!)"
        else:
            even_all += 1
            ok = (rd0 >= 1e-3) and (cauchy <= 1e-3)
            even_pass += int(ok)
            verdict = "residue + converged tail" if ok else "check (residue/tail)"
        emit(f"{r:>3} {rd0:>12.3e} {rS40:>12.3e} {rS:>12.3e} {cauchy:>12.3e}  {verdict}")
    emit("-" * 86)
    # scrambled control at an r>6 odd rank
    r_c = 7
    prof_s = PD.dual_profile_scrambled(r_c, 2, 1, seed=20260728, fmax=2, lmax=3,
                                       xi_max=40, nx=400)
    S_s = sum(v for xi, v in prof_s.items() if xi != 0)
    M_s = sum(abs(v) for xi, v in prof_s.items() if xi != 0)
    rSs = abs(S_s) / M_s if M_s > 0 else float("nan")
    ctrl_ok = rSs >= 100.0 * max(s_true_odd.get(r_c, 0.0), 1e-16)
    emit(f"CONTROL scrambled r={r_c}: |S|/M = {rSs:.3e}  vs true {s_true_odd.get(r_c, 0):.3e}"
         f"  -> parity clock is load-bearing: {ctrl_ok}")
    # quadrature robustness at the top of the ladder
    d0a, Sa, Ma = measure(13, 60, nx=400)
    d0b, Sb, Mb = measure(13, 60, nx=800)
    emit(f"ROBUSTNESS r=13: |S|/M at nx=400: {abs(Sa)/Ma:.3e}   nx=800: {abs(Sb)/Mb:.3e}")
    emit("-" * 86)
    emit(f"odd ladder: {odd_pass}/{odd_all} exact   even ladder: {even_pass}/{even_all} "
         f"residue+converged   control: {'PASS' if ctrl_ok else 'FAIL'}")
    if odd_pass == odd_all and ctrl_ok:
        emit("VERDICT: the mu_2 parity clock closes the xi!=0 channel EXACTLY at every")
        emit("         odd rank through r=13 on the real trace-formula terms -- the")
        emit("         carrier-native ladder extends through r>6 with identity-class")
        emit("         closure; the even-rank detecting residues are the ledger.")
    else:
        emit("VERDICT: see falsifier lines above (reported per the register).")
    emit(f"[done] {time.time()-t0:.0f}s -- results in {OUT}")


if __name__ == "__main__":
    main()
