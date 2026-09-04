#!/usr/bin/env python3
"""
att589 — THE DC OF THE TRACK S FORM (2026-09-04).  Nodes x_ρ = 1/(w−ρ), x'_ρ = 1/(ρ−c), c = 1−w̄, w = σ₀+iγ.
  M_{jk}(w) := Σ_ρ m_ρ (w−ρ)^{−j} (ρ−c)^{−k}   (absolutely convergent, j+k ≥ 2; (1,1) too).
  CLAIM (residues, pencil): M_{jk}(w) = 2 H_{jk}·Re[arch(w)] + (bounded prime jets) + O(γ^{−1}),
  H_{jk} = C(j+k−2, j−1)/d^{j+k−1}, d = 2σ₀−1 > 0 (Pascal–Hankel, positive definite).
  TEST: the γ-growth of Re M_{jk} between heights γ₁, γ₂ equals 2H_{jk}·(Re arch(w₂) − Re arch(w₁)) up to the
  bounded/decaying parts; report the ratio  [Re M_{jk}(γ₂) − Re M_{jk}(γ₁)] / [2H_{jk}(Re arch(w₂) − Re arch(w₁))].
  Pre-registered: ratio → 1 as γ₁, γ₂ → ∞ (within 10% at γ ≥ 200), for (j,k) ∈ {(1,1),(1,2),(2,2)}, σ₀ = 1.2.
  Also: min eigenvalue of the 2×2 Hermitian matrix Re-part at several heights (positive under RH; measured).
"""
import mpmath as mp, numpy as np, math
mp.mp.dps = 20
NZ = 3000
gam = [mp.zetazero(k).imag for k in range(1, NZ+1)]
sigma0 = mp.mpf("1.2"); d = 2*sigma0 - 1
def arch(s): return 1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2
def M(j, k, g):
    w = mp.mpc(sigma0, g); c = 1 - mp.conj(w); s = mp.mpc(0)
    for t in gam:                      # zeros ρ = ½ ± it (RH range), multiplicity 1
        for rho in (mp.mpc(0.5, t), mp.mpc(0.5, -t)):
            s += (w-rho)**(-j) * (rho-c)**(-k)
    # tail beyond NZ: density log(t/2π)/2π, |terms| ~ t^{-(j+k)}: add ∫ (both signs) for j+k ≥ 2 as an estimate
    T = gam[-1]
    tail = 2*mp.quad(lambda t: mp.log(t/(2*mp.pi))/(2*mp.pi) * ((w-mp.mpc(0.5,t))**(-j)*(mp.mpc(0.5,t)-c)**(-k)).real, [T, 10*T, mp.inf])
    return s.real + tail
H = {(1,1): 1/d, (1,2): 1/d**2, (2,1): 1/d**2, (2,2): 2/d**3}
gs = [50, 200, 800, 3200]
vals = {jk: [M(*jk, g) for g in gs] for jk in [(1,1),(1,2),(2,2)]}
archs = [arch(mp.mpc(sigma0, g)).real for g in gs]
print("σ₀ = 1.2, d = %.2f ; Re arch(w) at γ = %s : %s" % (d, gs, ["%.4f" % a for a in archs]))
for jk in [(1,1),(1,2),(2,2)]:
    print("(j,k)=%s  Re M at γ=%s : %s" % (jk, gs, ["%.5f" % v for v in vals[jk]]))
    for i in range(len(gs)-1):
        num = vals[jk][i+1] - vals[jk][i]; den = 2*H[jk]*(archs[i+1]-archs[i])
        print("     growth ratio between γ=%d and %d : %.4f   (pre-registered → 1)" % (gs[i], gs[i+1], num/den))
for i, g in enumerate(gs):
    A = np.array([[float(vals[(1,1)][i]), float(vals[(1,2)][i])], [float(vals[(1,2)][i]), float(vals[(2,2)][i])]])
    print("γ=%d: 2×2 form min eigenvalue %.5f  (H-prediction of growth 2·λ_min(H)·Re arch = %.5f)" % (g, np.linalg.eigvalsh(A).min(), 2*np.linalg.eigvalsh(np.array([[float(H[(1,1)]), float(H[(1,2)])],[float(H[(1,2)]), float(H[(2,2)])]])).min()*float(archs[i])))
