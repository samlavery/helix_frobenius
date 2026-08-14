#!/usr/bin/env python3
"""
Attempt 028c — the difference-of-families mechanism: measure the negative mass b~ of the
real Fejér–Riesz half w of the S=2 optimal kernel.

ghat = w * w (autocorrelation, w real, supp in [-1,1] after centering; ghat supp [-2,2]).
In atoms: c_j (j=0..n, x_j = j*Delta) are the autocorrelation of a real sequence (a_k):
    c_j = sum_k a_k a_{k+j}.
Real spectral factorization of the trig poly p(theta) = c0 + 2 sum c_j cos(j theta) >= 0:
inside-unit-circle roots come in conjugate pairs -> real a. Then
    b~  =  (sum of |a_k| over a_k<0 ... ) -- careful: the toll is the *grid mass* of w_-:
units: family-i per-zero weight c_i = (2pi/h) * int w_i ; alpha = 1/c1. The toll term is
4*beta*c2*N with beta chosen so ... = 4 * (int w_-) / (int w_+)?  NO — derive:
  alpha = 1/c_+ normalizes P; the Frobenius kernel is (alpha w_+ - beta w_-)**star-sq;
  to hit the LP-optimal ghat (normalized g(0)=1) we need alpha w_+ - beta w_- = w_opt
  with the SAME normalization as the LP; then the toll is 4*beta*c_- = 4*(2pi/h)*beta*int w_-,
  in the units where alpha*c_+ = 1.  With w_opt = w_+ - w_- (LP-normalized), alpha=beta=s
  a common scale: s*c_+ = 1 => toll = 4*s*(2pi/h)*int w_- = 4 * int(w_-)/int(w_+).
So   b~ = int w_- / int w_+   (ratio of L1 masses), toll = 4*b~.
Compare to the dip gain: 1.3274993 - Z*(2) = 0.00633.
"""
import numpy as np

REPO = "/Users/samuellavery/work/helix_frobenius"
dat = np.load(f"{REPO}/tmp/att027_c_S2.npy")
xs, cv = dat[0], dat[1]
Delta = xs[1] - xs[0]
n = len(xs) - 1

# lift tiny infeasibility
th = np.linspace(0, 2*np.pi, 400001)
def ptheta(c):
    return c[0] + 2*(np.cos(np.outer(th, np.arange(1, n+1))) * c[1:]).sum(axis=1)
p = ptheta(cv)
lift = max(0.0, -p.min()) + 1e-9
cv0 = cv.copy(); cv0[0] += lift
print(f"n={n}, min p = {p.min():+.2e}, lift {lift:.2e}")

# real spectral factorization via roots
coeffs = np.concatenate([cv0[::-1], cv0[1:]])
rts = np.polynomial.polynomial.Polynomial(coeffs).roots()
inside = rts[np.abs(rts) < 1 - 1e-11]
onc = rts[np.abs(np.abs(rts) - 1.0) <= 1e-11]
onc = onc[np.argsort(np.angle(onc))][::2]
sel = np.concatenate([inside, onc])
print(f"roots: total {len(rts)}, inside {len(inside)}, on-circle kept {len(onc)}, sel {len(sel)}")
a = np.polynomial.polynomial.polyfromroots(sel)
# make real (conjugate-closed root set) and rescale
imag_frac = np.max(np.abs(a.imag)) / np.max(np.abs(a.real))
a = a.real
a *= np.sqrt(cv0[0] / np.sum(a**2))
# verify autocorrelation
crec = np.array([np.sum(a[:n+1-j] * a[j:]) for j in range(n+1)])
err = np.max(np.abs(crec - cv0)) / np.max(np.abs(cv0))
print(f"factor: imag_frac {imag_frac:.1e}, autocorr rel err {err:.2e}")

# w atoms are a_k at u-grid points; sign structure and masses
neg = a[a < 0]; pos = a[a >= 0]
print(f"a: {len(a)} coeffs, {len(neg)} negative")
print(f"L1 masses: int w_+ = {pos.sum():.6f}, int |w_-| = {-neg.sum():.6f}")
btilde = -neg.sum() / pos.sum()
print(f"b~ = {btilde:.6f}   toll 4b~ = {4*btilde:.6f}")
print(f"dip gain available = 1.3274993 - 1.3211658 = {1.3274993-1.3211658:.7f}")
print(f"NET (naive) = gain - toll = {1.3274993-1.3211658 - 4*btilde:+.7f}")
# also: where do the negative coefficients live (u-position)?
uneg = np.where(a < 0)[0]
if len(uneg):
    print(f"negative a_k at k = {uneg[:20]}{'...' if len(uneg)>20 else ''} of 0..{n} "
          f"(u = k*Delta*l scale)")
