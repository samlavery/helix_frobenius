"""RUNG 3 STAGE 2 pipeline (Krylov-module realization, team-lead-approved):
  (1) readers-built + printed-a_p EXACT gate
  (2) full a_p footprint via readers, cross-checked pin vs Galois to p<=13000
  (3) re-verify Krylov dim d with the REAL a_p (sparse Phi), at large compare length
  (4) [next] 3x3 U_p matrix, spectral projector, g_alpha* line, gamma-bar, p=13 gate.
Cost (measured): sign reader ~7ms/prime, eps ~0.03ms/prime; sparse Phi ~32 coeffs.  Light.
"""
import time
import sys
import sympy as sp
from rung3_lhs import (a_p_h_exponent, a_p_h_exponent_galois, sign_bit_from_order,
                       eps_bit_explicit_frobenius)
from rung3_krylov import (embedding, f_coeffs_int, h_coeffs_int, dinv_f_coeffs, phi_coeff,
                          _solve_cols)
from rung3_rhs import Unramified, Qpf


def gate_printed_ap(P):
    P("(1) READER GATE — printed a_p reproduced EXACTLY by the Galois readers:")
    import cmath
    z = cmath.exp(2j * cmath.pi / 12)
    printed_k = {3: 1, 7: 7, 11: 5, 13: 2}   # a_5 abstains (ramified in 2T model)
    ok = True
    for p, k in sorted(printed_k.items()):
        kg = a_p_h_exponent_galois(p)
        exact = (kg == k)
        ok = ok and exact
        P(f"    a_{p}: printed ζ12^{k}, reader ζ12^{kg}  [{'EXACT' if exact else 'MISMATCH'}]")
    P(f"    a_5: abstains (ramified in the 2T model) — covered by mod-13 pin.  GATE: "
      f"{'PASS' if ok else 'FAIL'}")
    return ok


def gate_pin_vs_galois(P, pmax):
    P(f"(2) FOOTPRINT-WIDE REDUNDANCY (req 1): mod-13 pin vs Galois readers, ALL primes to p<={pmax} ...")
    t0 = time.time()
    mism = []
    checked = 0
    for p in sp.primerange(14, pmax):
        p = int(p)
        if 124 % p == 0:
            continue
        kp = a_p_h_exponent(p)
        kg = a_p_h_exponent_galois(p, eps_reader=eps_bit_explicit_frobenius)
        checked += 1
        if kg == 'ramified':
            continue           # reader abstains (ramified prime); pin covers it
        if kp != kg:
            mism.append((p, kp, kg))
    P(f"    checked {checked} primes to {pmax} in {time.time()-t0:.0f}s; "
      f"pin/reader mismatches (excl. ramified): {len(mism)}  "
      f"[{'PASS' if not mism else 'FAIL: ' + str(mism[:5])}]")
    return not mism


def reverify_krylov_dim(P, prec=12, L=8, max_d=5):
    P(f"(3) RE-VERIFY Krylov dim with REAL a_p (sparse Φ), compare-length {L} ...")
    p = 13
    zeta, mod = embedding(p, prec)
    W = L + 4
    M = p ** max_d * (W + 1)
    P(f"    building f,h to q^{M} (real a_p via readers) ...")
    t0 = time.time()
    fa = f_coeffs_int((1, -1, 1, -3, 3), 26, zeta, mod, M)
    ha = h_coeffs_int(zeta, mod, M)                 # uses a_p_h_exponent (reader-certified)
    F = dinv_f_coeffs(fa, p, mod, M)
    U = Unramified(p, [0, 1], prec)
    P(f"    built [{time.time()-t0:.0f}s]; probing dimension ...")

    def col(j):
        return [Qpf.from_U(U, U.from_int_vec([phi_coeff(F, ha, p ** j * n, mod) % mod]))
                for n in range(1, W + 1)]
    basis = []
    d = None
    for j in range(max_d + 1):
        c = col(j)
        if j > 0 and _solve_cols(basis, c, U) is not None:
            d = j
            break
        basis.append(c)
    if d is None:
        P(f"    Krylov module did NOT close by max_d={max_d} (dim > {max_d}) "
          f"[{time.time()-t0:.0f}s]")
    else:
        P(f"    Krylov module CLOSES at dim = {d}  [{time.time()-t0:.0f}s]")
    return d


def main():
    def P(s=""):
        print(s, flush=True)
    P("RUNG 3 STAGE 2 — Krylov-module pipeline (real a_p)")
    P("=" * 70)
    g1 = gate_printed_ap(P)
    g2 = gate_pin_vs_galois(P, pmax=13000)   # FULL footprint redundancy (req 1): 0/1540 mismatches
    d = reverify_krylov_dim(P, L=8, max_d=4)
    P("")
    P(f"SUMMARY: reader gate {'PASS' if g1 else 'FAIL'}; pin/reader agree {'PASS' if g2 else 'FAIL'}; "
      f"Krylov dim = {d}")


if __name__ == "__main__":
    main()
