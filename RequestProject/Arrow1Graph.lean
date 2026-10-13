import RequestProject.ThreeDFocalEvent
import RequestProject.HarmonicPencilCell
import RequestProject.SourceIsCancellation

/-!
# Arrow 1: its identification, and the native attempt through the banks (ledger 922)

**Arrow 1** (the fixed forward node):
`LFunction χ ρ = 0 → ThreeDFocal.CompletedFocalCancellationRepresents χ ρ` on the open strip.

## 1. What Arrow 1 delivers (mechanical)
* `onCarrier_of_arrow1`: Arrow 1 puts every strip zero on the carrier, `Re ρ = carrierAbscissa`
  (a represented focal cancellation is an L-zero at a carrier point, `completedFocalCancellationRepresents_iff`).
* `everyZeroHasSource_of_arrow1`: Arrow 1 gives `HarmonicCell.EveryZeroHasSource χ`.

## 2. The native banks fold exactly (ledger 693's P/M banks)
* `bankM_eq_fold`: the even-site bank is `2^{−s}` times the full bank at half head, at every head `Z > 0`.
* `finiteFiber_eq_fold`: the fiber is `fullBank Z − 2^{1−s}·fullBank (Z/2)` at every head.
* `hasSource_iff_fold`: the source limit of `HasSource` is the limit of this fold.

## 3. The fold annihilates the carrier-scale common mode, at every `s`
* `fold_commonMode`: `c·Z^{1−s} ↦ 0` under the fold, for every `c` and every `s`.
* `norm_commonMode`: `‖Z^{1−s}‖ = Z^{1 − Re s}` — the annihilated component is the one whose growth exponent carries
  `Re s` (the exponent the area law compares with the carrier radius).
* `fiber_blind_to_commonMode`: the source limit is unchanged by adding `c·Z^{1−s}` to the full bank.

No `sorry`, no `axiom`.

**Scope (cleanup, ledger 1237).** `Arrow1` is an OBSERVER-SIDE coverage statement. Its representation
predicate `CompletedFocalCancellationRepresents` is readout-defined (`Dcell` is a nonzero constant times the
L-value; see the `ThreeDFocalEvent` header). It is NOT the canonical native missing theorem, and no replacement
"remaining theorem" is formulated here. Repository status, recorded as absences:
* (a) the rich finite native geometry runs forward: `FocalEventProjection.FocalEvent` (bank-level cancellation at the
  native head) → pencil rank drop → J / two-ended state → post-cancellation state `(M, Z)` → geometric readout;
* (b) the completed drift-free phasor closure runs forward to analytic vanishing
  (`GeometricPhasorClosure.Phi_zero_iff_closure`);
* (c) no compiled bridge connects (a) and (b);
* (d) native exhaustiveness (every analytic vanishing measured by a native event) is unresolved.
§§2–3 (the η conductor's bank fold) are native bank-level facts.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace CriticalLinePhasor.Arrow1Graph

variable {q : ℕ} [NeZero q]

/-! ## 1. Arrow 1 and what it delivers -/

/-- **Arrow 1 over the open strip**: every measured vanishing is a completed focal cancellation representing it.
Observer-side coverage statement (readout-defined representation); not the canonical native exhaustiveness theorem. -/
def Arrow1 (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
    ThreeDFocal.CompletedFocalCancellationRepresents χ ρ

/-- **Arrow 1 puts every strip zero on the carrier.** -/
theorem onCarrier_of_arrow1 (χ : DirichletCharacter ℂ q) (h : Arrow1 χ) :
    ∀ ρ : ℂ, HarmonicCell.NontrivialZeroChi χ ρ → ρ.re = ThreeDFocal.carrierAbscissa := by
  rintro ρ ⟨hL, h0, h1⟩
  exact ((ThreeDFocal.completedFocalCancellationRepresents_iff χ ρ).1 (h ρ h0 h1 hL)).2

/-- **Arrow 1 gives the corpus's `HarmonicCell.EveryZeroHasSource`.** -/
theorem everyZeroHasSource_of_arrow1 (χ : DirichletCharacter ℂ q) (h : Arrow1 χ) :
    HarmonicCell.EveryZeroHasSource χ := by
  intro ρ hnt
  have h' := onCarrier_of_arrow1 χ h ρ hnt
  rw [ThreeDFocal.carrierAbscissa_eq_half] at h'
  exact HarmonicCell.source_of_re_half χ h'

/-! ## 2. The native banks fold exactly -/

open CriticalLinePhasor.Source CriticalLinePhasor.CarrierHeadFiniteFiber

theorem smoothEntry_eq_zero {u : ℝ} (hu : 1 ≤ u) : smoothEntry u = 0 := by
  unfold smoothEntry
  exact ite_eq_right (not_lt.mpr hu)

theorem siteTerm_eq_zero {Z : ℝ} (hZ : 0 < Z) (s : ℂ) {k : ℕ} (hk : Z ≤ ((k + 1 : ℕ) : ℝ)) :
    siteTerm Z s k = 0 := by
  unfold siteTerm
  rw [smoothEntry_eq_zero ((one_le_div hZ).2 hk)]
  simp

/-- An odd site at head `Z` is `2^{−s}` times the matching site at head `Z/2`. -/
theorem siteTerm_odd (Z : ℝ) (s : ℂ) (j : ℕ) :
    siteTerm Z s (2 * j + 1) = (2 : ℂ) ^ (-s) * siteTerm (Z / 2) s j := by
  unfold siteTerm
  have h1 : (((2 * j + 1 + 1 : ℕ) : ℝ) / Z) = (((j + 1 : ℕ) : ℝ) / (Z / 2)) := by
    rw [div_div_eq_mul_div]
    congr 1
    push_cast
    ring
  have h2 : Real.log ((2 * j + 1 + 1 : ℕ) : ℝ) = Real.log 2 + Real.log ((j + 1 : ℕ) : ℝ) := by
    rw [show ((2 * j + 1 + 1 : ℕ) : ℝ) = 2 * ((j + 1 : ℕ) : ℝ) by push_cast; ring]
    exact Real.log_mul (by norm_num) (by positivity)
  have hlog2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]
    norm_num
  have h3 : (2 : ℂ) ^ (-s) = Complex.exp (-s * ((Real.log 2 : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero two_ne_zero, hlog2]
    congr 1
    ring
  rw [h1, h2, h3]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-- **The even-site bank is the full bank at half head**, times `2^{−s}`, exactly at every head. -/
theorem bankM_eq_fold {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    bankM Z s = (2 : ℂ) ^ (-s) * fullBank (Z / 2) s := by
  unfold bankM fullBank
  rw [Finset.mul_sum]
  refine Finset.sum_bij_ne_zero (fun k _ _ => k / 2) ?_ ?_ ?_ ?_
  · intro k _ hne
    have hodd : ¬ Even k := fun he => hne (by simp [he])
    have hsite : siteTerm Z s k ≠ 0 := fun h0 => hne (by simp [hodd, h0])
    have hlt : ((k + 1 : ℕ) : ℝ) < Z := by
      by_contra hge
      exact hsite (siteTerm_eq_zero hZ s (not_lt.mp hge))
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 :=
      ⟨k / 2, by have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd); omega⟩
    show (2 * j + 1) / 2 ∈ Finset.range ⌈Z / 2⌉₊
    rw [show (2 * j + 1) / 2 = j by omega, Finset.mem_range, Nat.lt_ceil]
    push_cast at hlt
    linarith
  · intro k₁ _ h₁ k₂ _ h₂ heq
    have o₁ : ¬ Even k₁ := fun he => h₁ (by simp [he])
    have o₂ : ¬ Even k₂ := fun he => h₂ (by simp [he])
    have e₁ := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp o₁)
    have e₂ := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp o₂)
    have heq' : k₁ / 2 = k₂ / 2 := heq
    omega
  · intro j _ hne
    have hsite : siteTerm (Z / 2) s j ≠ 0 := fun h0 => hne (by simp [h0])
    have hlt : ((j + 1 : ℕ) : ℝ) < Z / 2 := by
      by_contra hge
      exact hsite (siteTerm_eq_zero (by linarith) s (not_lt.mp hge))
    have hodd : ¬ Even (2 * j + 1) := by
      rw [Nat.even_add_one]
      simp
    refine ⟨2 * j + 1, ?_, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_ceil]
      push_cast at hlt ⊢
      linarith
    · rw [ite_eq_right hodd, siteTerm_odd]
      exact mul_ne_zero (by simp) hsite
    · show (2 * j + 1) / 2 = j
      omega
  · intro k _ hne
    have hodd : ¬ Even k := fun he => hne (by simp [he])
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 :=
      ⟨k / 2, by have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd); omega⟩
    show (if Even (2 * j + 1) then 0 else siteTerm Z s (2 * j + 1))
      = (2 : ℂ) ^ (-s) * siteTerm (Z / 2) s ((2 * j + 1) / 2)
    rw [ite_eq_right hodd, siteTerm_odd, show (2 * j + 1) / 2 = j by omega]

/-- **The fiber is the fold of the full bank**: `finiteFiber Z s = fullBank Z s − 2^{1−s}·fullBank (Z/2) s`. -/
theorem finiteFiber_eq_fold {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    finiteFiber Z s = fullBank Z s - (2 : ℂ) ^ (1 - s) * fullBank (Z / 2) s := by
  have hP : bankP Z s = fullBank Z s - bankM Z s := by
    rw [fullBank_eq_bankP_add_bankM]
    ring
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  rw [finiteFiber_eq_bankP_sub_bankM, hP, bankM_eq_fold hZ s, h2]
  ring

/-! ## 3. The fold and the carrier-scale common mode -/

/-- The 2-adic fold of a head-indexed bank: `f(Z) − 2^{1−s} f(Z/2)`. -/
def fold (s : ℂ) (f : ℝ → ℂ) (Z : ℝ) : ℂ := f Z - (2 : ℂ) ^ (1 - s) * f (Z / 2)

/-- The source limit of `HasSource` is the limit of the fold of the full bank. -/
theorem hasSource_iff_fold (s : ℂ) :
    HasSource s ↔ (∀ᶠ Z in atTop, bankP Z s ≠ 0 ∧ bankM Z s ≠ 0) ∧
      Tendsto (fold s (fun Z => fullBank Z s)) atTop (𝓝 0) := by
  unfold HasSource
  refine and_congr Iff.rfl (tendsto_congr' ?_)
  filter_upwards [Filter.eventually_gt_atTop 0] with Z hZ
  rw [← finiteFiber_eq_bankP_sub_bankM]
  exact finiteFiber_eq_fold hZ s

/-- **The fold annihilates the carrier-scale common mode `c·Z^{1−s}`, for every `c` and every `s`.** -/
theorem fold_commonMode (s c : ℂ) {Z : ℝ} (hZ : 0 < Z) :
    fold s (fun Z => c * (Z : ℂ) ^ (1 - s)) Z = 0 := by
  unfold fold
  have hsplit : ((Z / 2 : ℝ) : ℂ) ^ (1 - s) = (Z : ℂ) ^ (1 - s) * ((1 / 2 : ℝ) : ℂ) ^ (1 - s) := by
    rw [show (Z / 2 : ℝ) = Z * (1 / 2) by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hZ.le (by norm_num)]
  have hone : (2 : ℂ) ^ (1 - s) * ((1 / 2 : ℝ) : ℂ) ^ (1 - s) = 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      ← Complex.mul_cpow_ofReal_nonneg (a := 2) (b := 1 / 2) (by norm_num) (by norm_num) (1 - s)]
    norm_num
  beta_reduce
  rw [hsplit]
  linear_combination (-(c * (Z : ℂ) ^ (1 - s))) * hone

/-- The annihilated component carries `Re s` in its growth exponent: `‖Z^{1−s}‖ = Z^{1 − Re s}`. -/
theorem norm_commonMode {Z : ℝ} (hZ : 0 < Z) (s : ℂ) : ‖(Z : ℂ) ^ (1 - s)‖ = Z ^ (1 - s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  simp

theorem fold_add_commonMode (s c : ℂ) (f : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    fold s (fun Z => f Z + c * (Z : ℂ) ^ (1 - s)) Z = fold s f Z := by
  have h := fold_commonMode s c hZ
  unfold fold at h ⊢
  linear_combination h

/-- **The source limit is blind to the common mode**: adding `c·Z^{1−s}` to the full bank (any `c`, any `s`) leaves
the fold's limit unchanged. -/
theorem fiber_blind_to_commonMode (s c : ℂ) (f : ℝ → ℂ) (L : ℂ) :
    Tendsto (fold s (fun Z => f Z + c * (Z : ℂ) ^ (1 - s))) atTop (𝓝 L) ↔
      Tendsto (fold s f) atTop (𝓝 L) :=
  tendsto_congr' ((Filter.eventually_gt_atTop 0).mono fun _ hZ => fold_add_commonMode s c f hZ)

end CriticalLinePhasor.Arrow1Graph

#print axioms CriticalLinePhasor.Arrow1Graph.onCarrier_of_arrow1
#print axioms CriticalLinePhasor.Arrow1Graph.everyZeroHasSource_of_arrow1
#print axioms CriticalLinePhasor.Arrow1Graph.bankM_eq_fold
#print axioms CriticalLinePhasor.Arrow1Graph.finiteFiber_eq_fold
#print axioms CriticalLinePhasor.Arrow1Graph.hasSource_iff_fold
#print axioms CriticalLinePhasor.Arrow1Graph.fold_commonMode
#print axioms CriticalLinePhasor.Arrow1Graph.norm_commonMode
#print axioms CriticalLinePhasor.Arrow1Graph.fiber_blind_to_commonMode
