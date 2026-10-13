import RequestProject.PencilTransverseRigidity

/-!
# Audit of `etaFactorEvent`: factor-induced rank drops versus ζ-representing rank drops (ledger 1200)

`LimitFocalEventNS.etaFactorEvent` (ledger 1156) is the η-routed limit cancellation at
`σ = 1`, `y = 2π/log 2`. This file locates its exponent and separates the two kinds of rank drop of
the η-routed limit detector.

* `etaPrefactor s = 1 − 2^{1−s}`, the factor in the η limit `(1 − 2^{1−s})·ζ(s)`
  (`lawFiber_eta_tendsto`). `etaPrefactor_eq_zero_iff`: it vanishes exactly when
  `log 2·(1 − s) ∈ 2πiℤ`. `etaPrefactor_zero_re`: every prefactor zero has `Re s = 1`.
* `eta_limit_cancel_iff`: for `Re s > 0`, `s ≠ 1`, the η fiber cancels in the limit iff
  `etaPrefactor s = 0` or `ζ(s) = 0`. `etaPrefactor_zero_zeta_ne`: the two never coincide.
  `zeta_rankDrop_nontrivial`: a ζ-representing rank drop with `Re s > 0` is a nontrivial zero.
* `eta_event_dichotomy`: every η-routed limit focal event is either factor-induced, at exponent
  exactly `1`, or a nontrivial ζ zero.
* `etaFactorEvent_audit`: `etaFactorEvent` has `σ = 1`, sits on a prefactor zero, is not a ζ zero,
  and its exponent is not balanced. It is factor-induced, outside the ζ-representing subclass, and
  not a native (balanced) event.
* `zetaSubclass_rigidity_iff`: transverse rigidity of the ζ-representing rank drops of the
  `D`-image pencil at reference exponent `σ₀`, for every `δ` with `σ₀ + δ > 0` (no strip
  restriction), holds iff every nontrivial ζ zero has real part `σ₀`. The factor-induced event
  does not bear on it.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.EtaFactorAudit

open CriticalLinePhasor CriticalLinePhasor.FiberDetectorChain CriticalLinePhasor.HarmonicCell
open CriticalLinePhasor.LimitFocalEventNS CriticalLinePhasor.EisensteinWheelBank
open CriticalLinePhasor.WarpFactorLocus CriticalLinePhasor.ThreeDFocal

/-- The η routing's prefactor `1 − 2^{1−s}`. -/
def etaPrefactor (s : ℂ) : ℂ := 1 - (2 : ℂ) ^ ((1 : ℂ) - s)

/-- **The prefactor vanishes exactly on `log 2·(1 − s) ∈ 2πiℤ`.** -/
theorem etaPrefactor_eq_zero_iff (s : ℂ) :
    etaPrefactor s = 0 ↔ ∃ n : ℤ, (Real.log 2 : ℂ) * (1 - s) = n * (2 * (Real.pi : ℂ) * I) := by
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold etaPrefactor
  rw [sub_eq_zero, eq_comm, Complex.cpow_def_of_ne_zero two_ne_zero, hlog, Complex.exp_eq_one_iff]

/-- **Every prefactor zero has real part `1`.** -/
theorem etaPrefactor_zero_re {s : ℂ} (h : etaPrefactor s = 0) : s.re = 1 := by
  obtain ⟨n, hn⟩ := (etaPrefactor_eq_zero_iff s).mp h
  have h1 : ((Real.log 2 : ℂ) * (1 - s)).re = Real.log 2 * (1 - s.re) := by
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  have h2 : ((n : ℂ) * (2 * (Real.pi : ℂ) * I)).re = 0 := by simp [Complex.mul_re]
  rw [hn, h2] at h1
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have := (mul_eq_zero.mp h1.symm).resolve_left hl
  linarith

theorem etaPrefactor_ne_zero_of_re_ne_one {s : ℂ} (h : s.re ≠ 1) : etaPrefactor s ≠ 0 :=
  fun h0 => h (etaPrefactor_zero_re h0)

/-- **The η-routed limit rank drops are the prefactor zeros and the ζ zeros.** -/
theorem eta_limit_cancel_iff {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun Z => lawFiber Routing.eta.coeff Z s) atTop (𝓝 0) ↔
      etaPrefactor s = 0 ∨ riemannZeta s = 0 := by
  have hT := lawFiber_eta_tendsto hs hs1
  constructor
  · intro h0
    exact mul_eq_zero.mp (tendsto_nhds_unique hT h0)
  · intro h
    have h0 : (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s = 0 := mul_eq_zero.mpr h
    rwa [h0] at hT

/-- **The two kinds never coincide**: at a prefactor zero, `ζ ≠ 0`. -/
theorem etaPrefactor_zero_zeta_ne {s : ℂ} (h : etaPrefactor s = 0) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (etaPrefactor_zero_re h).ge

/-- A ζ-representing rank drop with positive real part is a nontrivial zero. -/
theorem zeta_rankDrop_nontrivial {s : ℂ} (hs : 0 < s.re) (hz : riemannZeta s = 0) :
    s ∈ ZD.NontrivialZeros :=
  ⟨hs, lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz, hz⟩

/-- **Dichotomy for η-routed limit focal events**: factor-induced at exponent exactly `1`, or a
nontrivial ζ zero. -/
theorem eta_event_dichotomy (e : LimitFocalEvent) (hw : e.w = Routing.eta.coeff)
    (hpt : (e.σ : ℂ) + (e.y : ℂ) * I ≠ 1) :
    (etaPrefactor ((e.σ : ℂ) + (e.y : ℂ) * I) = 0 ∧ e.σ = 1) ∨
      (e.σ : ℂ) + (e.y : ℂ) * I ∈ ZD.NontrivialZeros := by
  have hre : ((e.σ : ℂ) + (e.y : ℂ) * I).re = e.σ := by simp
  have hpos : 0 < ((e.σ : ℂ) + (e.y : ℂ) * I).re := by rw [hre]; exact e.σ_pos
  have hc := e.cancel
  rw [hw] at hc
  rcases (eta_limit_cancel_iff hpos hpt).mp hc with h | h
  · exact Or.inl ⟨h, by rw [← hre]; exact etaPrefactor_zero_re h⟩
  · exact Or.inr (zeta_rankDrop_nontrivial hpos h)

/-- **`etaFactorEvent` is factor-induced**: exponent `1`, on a prefactor zero, not a ζ zero, and its
exponent is not balanced. -/
theorem etaFactorEvent_audit :
    etaFactorEvent.σ = 1 ∧
      etaPrefactor ((etaFactorEvent.σ : ℂ) + (etaFactorEvent.y : ℂ) * I) = 0 ∧
      riemannZeta ((etaFactorEvent.σ : ℂ) + (etaFactorEvent.y : ℂ) * I) ≠ 0 ∧
      ¬ CarrierScaleBalanced etaFactorEvent.σ :=
  ⟨rfl, dyadic_factor_zero, etaFactorEvent_not_zeta_zero, not_balanced_one⟩

/-- **Transverse rigidity of the ζ-representing subclass.** For every `δ` with `σ₀ + δ > 0`, a
ζ-representing limit rank drop of the `D_δ`-image of the η fiber at `σ₀ + iy` has `δ = 0`, iff every
nontrivial ζ zero has real part `σ₀`. No strip restriction is imposed; the subclass supplies it. -/
theorem zetaSubclass_rigidity_iff (σ₀ : ℝ) :
    (∀ δ y : ℝ, 0 < σ₀ + δ →
        Tendsto (fun Z => dilateFiber Routing.eta.coeff Z ((σ₀ : ℂ) + (y : ℂ) * I) δ) atTop (𝓝 0) →
        riemannZeta (((σ₀ + δ : ℝ) : ℂ) + (y : ℂ) * I) = 0 → δ = 0) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = σ₀ := by
  have hpt : ∀ δ y : ℝ, (σ₀ : ℂ) + (y : ℂ) * I + (δ : ℂ) = ((σ₀ + δ : ℝ) : ℂ) + (y : ℂ) * I := by
    intro δ y
    push_cast
    ring
  constructor
  · intro h ρ hρ
    obtain ⟨h0, h1, hz⟩ := hρ
    have hre : (((σ₀ + (ρ.re - σ₀) : ℝ) : ℂ) + (ρ.im : ℂ) * I) = ρ := by
      rw [show σ₀ + (ρ.re - σ₀) = ρ.re by ring]
      exact Complex.re_add_im ρ
    have hδ := h (ρ.re - σ₀) ρ.im (by linarith) (by
      simp_rw [dilateFiber_eq, hpt, hre]
      exact (limit_chain_eta h0 h1 0 1 one_ne_zero).1.mpr hz) (by rw [hre]; exact hz)
    linarith
  · intro h δ y hpos _ hz
    have hs0 : 0 < (((σ₀ + δ : ℝ) : ℂ) + (y : ℂ) * I).re := by simpa using hpos
    have hre := h _ (zeta_rankDrop_nontrivial hs0 hz)
    simp at hre
    linarith

end CriticalLinePhasor.EtaFactorAudit

end

#print axioms CriticalLinePhasor.EtaFactorAudit.etaPrefactor_eq_zero_iff
#print axioms CriticalLinePhasor.EtaFactorAudit.etaPrefactor_zero_re
#print axioms CriticalLinePhasor.EtaFactorAudit.eta_limit_cancel_iff
#print axioms CriticalLinePhasor.EtaFactorAudit.etaPrefactor_zero_zeta_ne
#print axioms CriticalLinePhasor.EtaFactorAudit.zeta_rankDrop_nontrivial
#print axioms CriticalLinePhasor.EtaFactorAudit.eta_event_dichotomy
#print axioms CriticalLinePhasor.EtaFactorAudit.etaFactorEvent_audit
#print axioms CriticalLinePhasor.EtaFactorAudit.zetaSubclass_rigidity_iff
