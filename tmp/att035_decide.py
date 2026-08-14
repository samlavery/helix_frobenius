"""
att035 -- ADJUDICATION of the "strip repair" (attempt 033's 028b plan).

PRE-REGISTERED NULLS (written before running):
 N0 (restatement): the strip-constrained functional is NEW, i.e. it does not coincide
     with a published functional.  REJECT if the sech-weighted functional reproduces
     BGSTB (arXiv:2306.04799) eq (7.2) numbers 0.608612927 (Fejer) and 0.617483786 (M-T).
 N1 (agreement):  A and B disagree beyond discretisation.  REJECT if |Z_A - Z_B| is
     within each scheme's own Delta-extrapolation error at matched A.
 N2 (the prize):  max_A [ 2 - Z(A) - charge(A) ] > 0.6725007 using the ACTUAL Simonic
     constants.  REJECT (= route fails) if the max is below 0.6725007.
 N3 (charge form): the charge is a count.  REJECT if the kernel amplification
     e^{S|w|} multiplies it (BGSTB sec 6 does exactly this in print).

Positive controls chosen to fail by MISSING STRUCTURE:
 P1 Montgomery-Taylor constant from the closed form.
 P2 BGSTB's own two published proportions, recomputed from the sech functional.
 P3 S=1, W=0 SDP -> Montgomery-Taylor (the gate both A and B ran).
"""
import numpy as np
from scipy.integrate import quad
import cvxpy as cp

SEP = "=" * 78
MT = 0.5 + 2 ** -0.5 / np.tan(2 ** -0.5)          # 1/c*_1
print(SEP); print("P1  Montgomery-Taylor constant")
print(f"    1/2 + 2^-1/2 cot(2^-1/2) = {MT:.10f}   (zeta23 (7.4): 1.3274992...)")
print(f"    2 - that                 = {2-MT:.10f}   (zeta23 Thm D: 0.67250...)")

# ---------------------------------------------------------------- P2
# BGSTB (4.1): Khat(t) = j(2 pi t) sech(2 pi t);  their (7.2) proportion is
#     2 - [ jhat(0) + 2 int_0^1 a j(a) sech(a) da ] / [ 2 int_0^1 j(u) sech(u) du ]
# i.e. Z_BGSTB = num/den with the SAME shape as implementation B's continuum
#     Z(A) = [ h(0) + 2 int_0^1 a sech(a W) h(a) ] / [ 2 int_0^S sech(a W) h(a) ]
# at W = 1, S = 1, h = j.   NOTE Khat(0) = j(0) NOT jhat(0) -- read at source.
print(SEP); print("P2  reproduce BGSTB's published proportions from the sech functional")
jF = lambda a: max(0.0, 1.0 - abs(a))
r2 = np.sqrt(2.0)
cM = 1.0 - np.cos(r2)
def jM(a):
    return (1.0 / cM) * (0.5 / r2 * np.sin(r2 / 2) * jF(a) + jF(a) * np.cos(r2 * a) * 0.0
                         ) if False else None
# (4.4): jM(a) = 1/(1-cos sqrt2) * [ (1/(2 sqrt2)) sin(sqrt2/2) jF(a) + jF(a) cos(sqrt2 a) ]
# -- OCR of (4.4) is ambiguous; pin it instead by BGSTB's own stated jM(0)=1.0061271908
def jM_v1(a):   # reading: (1/(2 sqrt2)) sin(sqrt2 /2) jF + jF cos(sqrt2 a)
    return (0.5 / r2 * np.sin(r2 / 2) * jF(a) + jF(a) * np.cos(r2 * a)) / cM
def jM_v2(a):   # reading: (1/(2 sqrt2)) sin( sqrt2 (1/2) jF(a) ) + jF(a) cos(sqrt2 a)
    return (0.5 / r2 * np.sin(r2 * 0.5 * jF(a)) + jF(a) * np.cos(r2 * a)) / cM
for nm, j in (("jM_v1", jM_v1), ("jM_v2", jM_v2)):
    print(f"    {nm}(0) = {j(0.0):.10f}   (BGSTB state Khat(0)=jM(0)=1.0061271908)")
jM_ = jM_v2 if abs(jM_v2(0.0) - 1.0061271908) < 1e-8 else jM_v1

def Z_sech(j, W=1.0, S=1.0):
    num = j(0.0) + 2 * quad(lambda a: a * j(a) / np.cosh(a * W), 0, 1, limit=400)[0]
    den = 2 * quad(lambda a: j(a) / np.cosh(a * W), 0, S, limit=400)[0]
    return num / den

for nm, j, target in (("Fejer  j_F", jF, 0.608612927), ("M-Taylor j_M", jM_, 0.617483786)):
    Z = Z_sech(j); print(f"    {nm}: Z = {Z:.9f}   2-Z = {2-Z:.9f}   BGSTB print {target}"
                         f"   |diff| = {abs(2-Z-target):.2e}")
# also their intermediate integrals, as separate gates
print(f"    gate  2*int_0^1 a jF sech = "
      f"{2*quad(lambda a: a*jF(a)/np.cosh(a),0,1)[0]:.10f}  (BGSTB 0.2913876354)")
print(f"    gate  int_0^1 jF sech     = "
      f"{quad(lambda a: jF(a)/np.cosh(a),0,1)[0]:.10f}  (BGSTB piK(0)=0.4640648392)")
print(f"    gate  2*int_0^1 a jM sech = "
      f"{2*quad(lambda a: a*jM_(a)/np.cosh(a),0,1)[0]:.10f}  (BGSTB 0.2832624869)")
print(f"    gate  int_0^1 jM sech     = "
      f"{quad(lambda a: jM_(a)/np.cosh(a),0,1)[0]:.10f}  (BGSTB 0.4663199124)")

# ---------------------------------------------------------------- SDP (3rd impl)
# Independent re-implementation.  Atoms x_j = j*D, j=0..n-1 (n = S/D), c_{-j}=c_j.
# Strip variable in BGSTB units: w = -(beta-beta') log T, |w| <= W = 2A.
# Phragmen-Lindelof: Re g >= 0 on strip  <=>  Re g >= 0 on w = W  (bounded harmonic).
# Substitute b_j = c_j cosh(x_j W) -> b must be a nonneg cosine polynomial (Toeplitz PSD).
def Zsdp(A, S=2.0, D=0.04, dip=True, solver=cp.CLARABEL):
    n = int(round(S / D))                      # A's calibration (a): n = S/D atoms
    x = np.arange(n) * D
    W = 2.0 * A
    sech = 1.0 / np.cosh(x * W)
    Q = cp.Variable((n, n), symmetric=True)
    b = cp.hstack([cp.trace(Q)] + [sum(Q[k, k + j] for k in range(n - j)) for j in range(1, n)])
    c = cp.multiply(sech, b)                   # c_j = b_j sech(x_j W)
    w1 = np.where(x <= 1.0, x, 0.0) * 2.0      # 2*int weight; midpoint-free, x_j inside band
    w1[0] = D / 2.0                            # cell-averaged |a| at j=0 : (1/D)int_0^D a da *2
    obj = c[0] / D + w1 @ c
    cons = [Q >> 0, c[0] + 2 * cp.sum(c[1:]) == 1]
    if dip:
        cons.append(c[x >= 1.0 - 1e-12] <= 0)  # A's calibration (b): include the atom AT x=1
    else:
        cons.append(c[x > 1.0 + 1e-12] == 0)
        cons.append(b[n - 1] == 0)             # B's edge gauge
    p = cp.Problem(cp.Minimize(obj), cons)
    p.solve(solver=solver)
    return p.value, p.status

print(SEP); print("P3  positive control S=1, W=0  ->  Montgomery-Taylor")
for D in (0.04, 0.02, 0.01):
    v, st = Zsdp(0.0, S=1.0, D=D)
    print(f"    D={D:<6} Z = {v:.7f}  err = {MT-v:+.3e}   [{st}]")

print(SEP); print("Z(A):  independent third implementation (S=2, dip on)")
Agrid = [0.0, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40, 0.50, 0.75, 1.00]
rows = []
for A in Agrid:
    v4, s4 = Zsdp(A, S=2.0, D=0.04)
    v2, s2 = Zsdp(A, S=2.0, D=0.02)
    rich = v2 + (v2 - v4) / 3.0                # Richardson for O(D^2)
    rows.append((A, v4, v2, rich))
    print(f"    A={A:<5} Z(.04)={v4:.6f} Z(.02)={v2:.6f}  Richardson={rich:.6f}  [{s4}/{s2}]")
np.save("/Users/samuellavery/work/helix_frobenius/tmp/att035_ZA.npy", np.array(rows))
print(SEP)
