import RequestProject.HeckeCancellation

/-!
# The invariant sup-bound layer: invariance, domain height, and the transport to Hecke's bound

The analytic base layer of the `r = 2` cancellation attack.  For a level-one form `f` of weight
`k`, the weight-invariant readout `P(z) = im(z)^k·|f(z)|²` is invariant under the level-one
group (`P_invariant`, GL-native), the fundamental domain sits above height `√3/2` (`fd_im_ge`),
and any bound for `P` on the fundamental domain transports to Hecke's pointwise bound everywhere
(`hecke_pointwise_of_fdBound`, via `ModularGroup.exists_smul_mem_fd`).  The remaining discharge —
`P` is bounded on the fundamental domain, by continuity on the compact band plus cusp decay above
it — is the named next composition; its two ingredients are compiled
(`CuspFormClass.exp_decay_atImInfty`, the band's compactness).  All from the base fiber's own
modularity; no RH/GRH, no tower input.
-/

open UpperHalfPlane Complex Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Real

namespace CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The weight-invariant readout `im^k · |f|²`. -/
noncomputable def P {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) (f : F) (z : ℍ) : ℝ :=
  z.im ^ k * Complex.normSq (f z)

/-- Members of `𝒮ℒ` have determinant one. -/
lemma det_eq_one {g : GL (Fin 2) ℝ} (hg : g ∈ 𝒮ℒ) : g.det.val = 1 := by
  obtain ⟨γ, rfl⟩ := hg
  simp

/-- **Invariance of the readout** under the level-one group, GL-natively. -/
theorem P_invariant {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒮ℒ k]
    (f : F) {g : GL (Fin 2) ℝ} (hg : g ∈ 𝒮ℒ) (z : ℍ) :
    P k f (g • z) = P k f z := by
  have hfe := SlashInvariantForm.slash_action_eqn' f hg z
  have him : (g • z).im = z.im / Complex.normSq (denom g z) := by
    rw [UpperHalfPlane.im_smul_eq_div_normSq, det_eq_one hg, abs_one, one_mul]
  have hDne : Complex.normSq (denom g z) ≠ 0 :=
    fun h => (denom_ne_zero g z) (Complex.normSq_eq_zero.mp h)
  unfold P
  rw [him, hfe]
  have hden : ((g 1 0 : ℂ) * z + g 1 1) = denom g z := rfl
  rw [hden, map_mul, map_zpow₀, ← mul_assoc, ← mul_zpow, div_mul_cancel₀ _ hDne]

/-- On the fundamental domain the height is at least `√3/2`. -/
lemma fd_im_ge {z : ℍ} (hz : z ∈ ModularGroup.fd) : Real.sqrt 3 / 2 ≤ z.im := by
  have h1 : 1 ≤ Complex.normSq (z : ℂ) := hz.1
  have h2 : |z.re| ≤ 1 / 2 := hz.2
  have hsq : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have habs := abs_le.mp h2
  have him2 : (Real.sqrt 3 / 2) ^ 2 ≤ z.im ^ 2 := by
    have h34 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [h34]
    nlinarith
  have h4 := Real.sqrt_le_sqrt him2
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq z.im_pos.le] at h4

/-- **The fundamental-domain transport.**  Any bound for the invariant readout on the fundamental
domain is a bound everywhere; pointwise this is Hecke's bound `|f(z)|² ≤ M·im(z)^{-k}`. -/
theorem hecke_pointwise_of_fdBound {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F 𝒮ℒ k] (f : F) (M : ℝ)
    (hfd : ∀ w ∈ ModularGroup.fd, P k f w ≤ M) (z : ℍ) :
    Complex.normSq (f z) ≤ M * z.im ^ (-k) := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  have hmem : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have haction : (mapGL ℝ γ) • z = γ • z := rfl
  have hval : P k f z ≤ M := by
    rw [← P_invariant f hmem z, haction]
    exact hfd (γ • z) hγ
  have himpos : (0 : ℝ) < z.im ^ k := zpow_pos z.im_pos k
  unfold P at hval
  calc Complex.normSq (f z) = (z.im ^ k * Complex.normSq (f z)) * z.im ^ (-k) := by
        rw [zpow_neg]
        field_simp
    _ ≤ M * z.im ^ (-k) := by
        apply mul_le_mul_of_nonneg_right hval
        rw [zpow_neg]
        positivity

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.P_invariant
#print axioms CriticalLinePhasor.HeckeSupBound.fd_im_ge
#print axioms CriticalLinePhasor.HeckeSupBound.hecke_pointwise_of_fdBound
