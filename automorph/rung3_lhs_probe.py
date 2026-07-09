"""End-to-end LHS pipeline probe: build f,h to the d=3 q-truncation, form Phi, build the
finite U_p Krylov matrix, spectral e_ord, and report structure + timing.  Validation run."""
import time
import sympy as sp
from rung3_lhs import (weight1_h_qexp, weight2_f_qexp, QExp, serre_dinv, U_p,
                       krylov_Up_module, spectral_ordinary_projector, a_p_h_exponent)
from rung3_rhs import Unramified, Qpf

t0 = time.time()
p = 13
prec = 8
mod = p ** prec


def hensel12(seed):
    x = seed % mod
    for _ in range(2 * prec + 5):
        x = (x - (pow(x, 12, mod) - 1) * pow(12 * pow(x, 11, mod) % mod, -1, mod)) % mod
    return x


zeta = hensel12(7)
U = Unramified(p, [0, 1], prec)
zeta12 = Qpf.from_U(U, U.from_int_vec([zeta]))
bad = {2: Qpf.from_U(U, U.from_int_vec([pow(zeta, 3, mod)]))}

Mq = 9000
print(f"[{time.time()-t0:.0f}s] building h to q^{Mq}...")
h = weight1_h_qexp(U, Mq, zeta12, bad_ap=bad)
print(f"[{time.time()-t0:.0f}s] building f to q^{Mq}...")
f = weight2_f_qexp(U, (1, -1, 1, -3, 3), 26, Mq)
print(f"[{time.time()-t0:.0f}s] forming Phi = d^-1(f)*h ...")
Phi = serre_dinv(f).mul(h)
print(f"[{time.time()-t0:.0f}s] building U_p Krylov matrix...")
basis, Mat, diag = krylov_Up_module(Phi, compare_len=6, max_dim=6)
print(f"[{time.time()-t0:.0f}s] Krylov dim = {diag['dim']}, maxed={diag.get('maxed', False)}")


def show(m):
    out = []
    for row in m:
        out.append([((pow(p, x.exp, mod) * x.u[0]) % mod if x.exp >= 0 else 'neg%d' % x.exp)
                    for x in row])
    return out


print(f"[{time.time()-t0:.0f}s] U_p matrix (mod 13^{prec}):")
for r in show(Mat):
    print("   ", r)
# spectral e_ord
P, pdiag = spectral_ordinary_projector(basis, Mat)
print(f"[{time.time()-t0:.0f}s] e_ord projector:")
for r in show(P):
    print("   ", r)
# e_ord idempotence gate: P^2 == P
from rung3_lhs import _mat_mul
P2 = _mat_mul(P, P, U)
idem = all(P2[i][j].sub(P[i][j]).val() >= prec for i in range(len(P)) for j in range(len(P)))
print(f"[{time.time()-t0:.0f}s] e_ord idempotent (P^2==P): {idem}")
