#!/usr/bin/env python3
"""
att584 — MULTIPLICITY READ FROM PRIMES: (2π/L)·D_{R,x}(γ_k) → m_k, with D_R the Riesz density of att567
  (ϑ′/π + END_R − (1/π)Σ_{n≤x}Λ(n)(1 − log n/L)n^{−½}cos(γ log n)),  L = log x.
  Prediction (RH range): (2π/L)D_R(γ_k) = 1 + (2/L)Σ_{j≠k}(1 − cos L(γ_j−γ_k))/(L(γ_j−γ_k)²) + O(x^{−1}),
  so |(2π/L)D_R(γ_k) − 1| ≲ (2/L²)Σ_{j≠k}1/(γ_j−γ_k)² ≈ 0.02 at x = 10³ down to 0.005 at x = 10⁵ for γ ≤ 60.
PRE-REGISTERED: P1 all 13 zeros within 0.03 of 1 at x = 10³ and within 0.01 at x = 10⁵; P2 the residual
  matches the predicted comb correction to 30%.
"""
import sys; sys.path.insert(0, "tmp")
import numpy as np, mpmath as mp, math
from att566_krein_constant import prime_powers, theta_prime_over_pi, ZEROS
def riesz_density(z, x, ns, lams):
    L = math.log(x); w = np.maximum(1 - np.log(ns)/L, 0)
    bank = (1/math.pi)*np.sum(w*lams*ns**-0.5*np.cos(z*np.log(ns)))
    s = 0.5 - 1j*z; wv = s  # END_R = Re[(x^w − 1)/(L w²)]/π at w = ½ − iz
    end = (( x**wv - 1)/(L*wv*wv)).real/math.pi
    return theta_prime_over_pi(np.array([z]))[0] + end - bank
zs = np.array(ZEROS[:13])
for x in (1e3, 1e4, 1e5):
    ns, lams = prime_powers(int(x)); ns = np.array(ns, float); lams = np.array(lams, float); L = math.log(x)
    vals = []; preds = []
    for k, g in enumerate(zs):
        d = riesz_density(g, x, ns, lams); r = 2*math.pi*d/L
        others = np.delete(zs, k); dz = others - g
        corr = (2/L)*np.sum((1 - np.cos(L*dz))/(L*dz*dz))
        vals.append(r); preds.append(1 + corr)
    vals = np.array(vals); preds = np.array(preds)
    print("x = %.0e (L = %.2f): (2π/L)D_R at the 13 zeros: mean %.4f  max|·−1| %.4f ; predicted 1+comb: max|·−1| %.4f ; |measured − predicted| max %.4f" % (
        x, L, vals.mean(), np.abs(vals-1).max(), np.abs(preds-1).max(), np.abs(vals-preds).max()))
    print("   values:", " ".join("%.3f" % v for v in vals))
