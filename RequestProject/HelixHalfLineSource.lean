import RequestProject.HelixNativeDilation

/-!
# Continuity of a source's functional, derived below the origin (ledger 1283)

Sam (2026-10-13): "try and derive it." The step was (1282): a source's native functional `Φ_v` is continuous on a
translation representation, with continuity derived rather than imposed.

**On the whole line it cannot be derived for an off-axis offset.** This is the contrapositive of the compiled
`HelixNativeDilation.covariant_functional_axis` (a theorem, not a claim about zeros). There, continuity is decided by
`Re v` alone.

**Below the origin it is derived, for free.** On the half-line `h ≤ 0` (the anti-helix side), with the native
measure `dh`:
* `memLp_expMode`, `integral_norm_sq_expMode`: for `Re v > 0` the native mode is square-integrable,
  `∫_{h ≤ 0} |e^{vh}|² dh = 1/(2 Re v)`.
* `ψ v`: the normalizable vector below the origin; `inner_ψ`: `⟪ψ_v, f⟫ = ∫_{h ≤ 0} e^{vh} f(h) dh`. **The source's
  functional is the inner product with a genuine Hilbert-space vector, so it is continuous, with no assumption.**
* `ψ_ne_zero`: `⟪ψ_v, ψ_v⟫ = 1/(2 Re v) ≠ 0`.
* `halfLine_covariance`: translation by `t ≥ 0` keeps functions below the origin and multiplies the functional by
  `e^{−vt}` (from the compiled `Φ_shift`).
* **`no_source_of_dense`**: for `Re v > 0`, no dense subspace of `L²(h ≤ 0, dh)` is annihilated by `⟪ψ_v, ·⟫`. So an
  off-axis offset on that side is excluded the moment its functional annihilates a dense family. J mirrors the
  statement to `Re v < 0` above the origin.

**What this leaves.** A family of functions below the origin, built from the construction, whose half-line
transforms vanish at every source and whose span is dense in `L²(h ≤ 0, dh)`. That family is not built here. Its
classical instance is Nyman–Beurling (fractional parts in the `dx` chart); the native counterpart is the carrier's
cell position read on the anti-helix side.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace CriticalLinePhasor.HelixHalfLineSource

open CriticalLinePhasor.HelixNativeDilation

/-- The half-line below the origin, with the native measure `dh`. -/
abbrev below : Measure ℝ := volume.restrict (Iic 0)

theorem norm_sq_expMode (v : ℂ) (h : ℝ) : ‖expMode v h‖ ^ 2 = Real.exp ((2 * v.re) * h) := by
  rw [norm_expMode, sq, ← Real.exp_add]
  ring_nf

theorem continuous_expMode (v : ℂ) : Continuous (expMode v) := by
  unfold expMode
  fun_prop

theorem expMode_conj (v : ℂ) (h : ℝ) : expMode (conj v) h = conj (expMode v h) := by
  simp only [expMode]
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- **The native mode is square-integrable below the origin**, for `Re v > 0`. -/
theorem memLp_expMode {v : ℂ} (hv : 0 < v.re) : MemLp (expMode v) 2 below := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_expMode v).aestronglyMeasurable]
  have := integrableOn_exp_mul_Iic (a := 2 * v.re) (by linarith) 0
  exact this.congr_fun (fun h _ => (norm_sq_expMode v h).symm) measurableSet_Iic

theorem integral_norm_sq_expMode {v : ℂ} (hv : 0 < v.re) :
    ∫ h in Iic (0 : ℝ), ‖expMode v h‖ ^ 2 = 1 / (2 * v.re) := by
  simp_rw [norm_sq_expMode]
  rw [integral_exp_mul_Iic (by linarith) 0]
  simp

/-- The source's normalizable vector below the origin: the native mode at `v̄`. -/
def ψ (v : ℂ) (hv : 0 < v.re) : Lp ℂ 2 below :=
  (memLp_expMode (v := conj v) (by rwa [Complex.conj_re])).toLp _

/-- **The source's functional is the inner product with `ψ_v`.** -/
theorem inner_ψ {v : ℂ} (hv : 0 < v.re) (f : Lp ℂ 2 below) :
    ⟪ψ v hv, f⟫_ℂ = ∫ h in Iic (0 : ℝ), expMode v h * f h := by
  unfold ψ
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_expMode (v := conj v) (by rwa [Complex.conj_re]))] with h hh
  rw [hh, RCLike.inner_apply', expMode_conj, Complex.conj_conj]

theorem inner_ψ_self {v : ℂ} (hv : 0 < v.re) : ⟪ψ v hv, ψ v hv⟫_ℂ = ((1 / (2 * v.re) : ℝ) : ℂ) := by
  rw [inner_ψ hv]
  have hcoe := MemLp.coeFn_toLp (memLp_expMode (v := conj v) (by rwa [Complex.conj_re]))
  calc ∫ h in Iic (0 : ℝ), expMode v h * (ψ v hv) h
      = ∫ h in Iic (0 : ℝ), ((‖expMode v h‖ ^ 2 : ℝ) : ℂ) := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with h hh
        unfold ψ
        rw [hh, expMode_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ((∫ h in Iic (0 : ℝ), ‖expMode v h‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [integral_norm_sq_expMode hv]

theorem ψ_ne_zero {v : ℂ} (hv : 0 < v.re) : ψ v hv ≠ 0 := by
  intro h
  have := inner_ψ_self hv
  rw [h, inner_zero_left] at this
  have hpos : (0 : ℝ) < 1 / (2 * v.re) := by positivity
  exact hpos.ne' (by exact_mod_cast this.symm)

/-- Translation by `t ≥ 0` keeps a function below the origin, and multiplies its half-line functional by
`e^{−vt}`. -/
theorem halfLine_covariance (v : ℂ) (g : ℝ → ℂ) (hg : ∀ h, 0 < h → g h = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∀ h, 0 < h → shift t g h = 0) ∧
      ∫ h in Iic (0 : ℝ), expMode v h * shift t g h =
        Complex.exp (-(v * t)) * ∫ h in Iic (0 : ℝ), expMode v h * g h := by
  have hsupp : ∀ h, 0 < h → shift t g h = 0 := fun h hh => hg (h + t) (by linarith)
  refine ⟨hsupp, ?_⟩
  have e1 : ∫ h in Iic (0 : ℝ), expMode v h * shift t g h = Φ v (shift t g) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · unfold Φ
      exact integral_congr_ae (Eventually.of_forall fun h => mul_comm _ _)
    · intro h hh
      rw [hsupp h (not_le.mp hh), mul_zero]
  have e2 : ∫ h in Iic (0 : ℝ), expMode v h * g h = Φ v g := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · unfold Φ
      exact integral_congr_ae (Eventually.of_forall fun h => mul_comm _ _)
    · intro h hh
      rw [hg h (not_le.mp hh), mul_zero]
  rw [e1, e2, Φ_shift]

/-- **An off-axis offset below the origin is excluded by any dense family its functional annihilates.** -/
theorem no_source_of_dense {v : ℂ} (hv : 0 < v.re) (K : Submodule ℂ (Lp ℂ 2 below))
    (hK : K.topologicalClosure = ⊤) (hann : ∀ f ∈ K, ⟪ψ v hv, f⟫_ℂ = 0) : False := by
  have hperp : ψ v hv ∈ Kᗮ := (K.mem_orthogonal' _).mpr hann
  rw [Submodule.topologicalClosure_eq_top_iff.mp hK] at hperp
  exact ψ_ne_zero hv ((Submodule.mem_bot ℂ).mp hperp)

end CriticalLinePhasor.HelixHalfLineSource

end

#print axioms CriticalLinePhasor.HelixHalfLineSource.memLp_expMode
#print axioms CriticalLinePhasor.HelixHalfLineSource.inner_ψ
#print axioms CriticalLinePhasor.HelixHalfLineSource.ψ_ne_zero
#print axioms CriticalLinePhasor.HelixHalfLineSource.halfLine_covariance
#print axioms CriticalLinePhasor.HelixHalfLineSource.no_source_of_dense
