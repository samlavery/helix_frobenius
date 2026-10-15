import RequestProject.HelixWeilWitnessDoor

/-!
# The Weil witness, Case B dissolved: the finite-energy ascent (ledger 1341)

Case B of the Gaussian witness (1337–1340) was the possibility that no off-axis zero is locally maximal in
deviation within height distance `2`. The dominance argument (W2b/W2c) never needed local maximality: it needs
only that every near zero other than the pair has Gaussian exponent `Mexp` strictly below the pair's
`4d² = (2β − 1)²` — the **Gaussian peak** condition `GaussPeak` (now the hypothesis of `gaussianWitness_of_peak`).

Here the Gaussian peak is shown to exist whenever an off-axis zero exists (Sam's route, 2026-10-14):

* `ascent_step` — if an off-axis zero `ρ₀` is not a Gaussian peak, a competitor `ρ` has
  `(d + d')² − Δ² ≥ 4d²`, i.e. `Δ² ≤ (d' − d)(d' + 3d)`; so `d' > d` (the pair excluded) and
  `Δ² ≤ 2(d' − d)` (both deviations below `½`).
* `ascent` — iterating gives a sequence of off-axis zeros with strictly increasing deviations and
  **finite energy** `Σ_k Δ_k² ≤ 2(d_n − d_0) < 1`.
* `exists_gaussPeak` — by Cauchy–Schwarz `(γ_n − γ_0)² ≤ n`, so `|ρ_n|² ≤ 1 + 2γ_0² + 2n`; the zeros are
  distinct, so `Σ_ρ m_ρ/|ρ|² ≥ Σ_n 1/(C + 2n) = ∞`, against the compiled summability
  `ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`. No zero counting is needed: the harmonic series does it.
* `axis_of_carrierPositivePair'`, `riemannHypothesis_of_carrierPositivePair'` — **the Gaussian-class door with
  a single hypothesis**: `CarrierPositivePair a b → RiemannHypothesis`.

No `sorry`, no `axiom`, no window.
-/

open Complex
open scoped Real ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixWeilWitness

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.HelixCarrierWeil

/-! ## Deviation -/

/-- The deviation of a zero from the axis. -/
def dev (ρ : Zero) : ℝ := |ρ.val.re - 1 / 2|

theorem dev_nonneg (ρ : Zero) : 0 ≤ dev ρ := abs_nonneg _

theorem dev_lt_half (ρ : Zero) : dev ρ < 1 / 2 := by
  unfold dev
  rw [abs_lt]
  have h0 := ρ.2.1
  have h1 := ρ.2.2.1
  constructor <;> linarith

theorem off_of_dev_pos {ρ : Zero} (h : 0 < dev ρ) : ρ.val.re ≠ 1 / 2 := by
  intro heq
  have : dev ρ = 0 := by unfold dev; rw [heq]; simp
  linarith

/-! ## The ascent step -/

/-- **The ascent step**: if an off-axis zero is not a Gaussian peak, some zero has strictly larger deviation,
and its squared height displacement is at most twice the gain in deviation. -/
theorem ascent_step {ρ₀ : Zero} (hβ : ρ₀.val.re ≠ 1 / 2) (hno : ¬ GaussPeak ρ₀) :
    ∃ ρ : Zero, dev ρ₀ < dev ρ ∧ (ρ.val.im - ρ₀.val.im) ^ 2 ≤ 2 * (dev ρ - dev ρ₀) := by
  unfold GaussPeak at hno
  push_neg at hno
  obtain ⟨ρ, _hn, h1, h2, hM⟩ := hno
  refine ⟨ρ, ?_⟩
  unfold Mexp at hM
  unfold dev
  set s : ℝ := ρ₀.val.re - 1 / 2 with hs
  set s' : ℝ := ρ.val.re - 1 / 2 with hs'
  have e1 : (ρ.val.re - ρ₀.val.re) ^ 2 = (s' - s) ^ 2 := by rw [hs, hs']; ring
  have e2 : (ρ.val.re - (1 - ρ₀.val.re)) ^ 2 = (s' + s) ^ 2 := by rw [hs, hs']; ring
  have e3 : (2 * ρ₀.val.re - 1) ^ 2 = 4 * s ^ 2 := by rw [hs]; ring
  rw [e1, e2, e3] at hM
  set Δ : ℝ := ρ.val.im - ρ₀.val.im with hΔ
  -- both abscissa gaps are at most `(|s'| + |s|)²`
  have hss1 := neg_abs_le (s' * s)
  have hss2 := le_abs_self (s' * s)
  rw [abs_mul] at hss1 hss2
  have hA : (s' - s) ^ 2 ≤ (|s'| + |s|) ^ 2 := by nlinarith [sq_abs s, sq_abs s']
  have hB : (s' + s) ^ 2 ≤ (|s'| + |s|) ^ 2 := by nlinarith [sq_abs s, sq_abs s']
  have hmax : max ((s' - s) ^ 2) ((s' + s) ^ 2) ≤ (|s'| + |s|) ^ 2 := max_le hA hB
  -- the key inequality `Δ² ≤ (|s'| − |s|)(|s'| + 3|s|)`
  have hkey : Δ ^ 2 ≤ (|s'| - |s|) * (|s'| + 3 * |s|) := by nlinarith [hM, hmax, sq_abs s]
  have hs_pos : 0 < |s| := abs_pos.mpr (sub_ne_zero.mpr hβ)
  have hs'_nn : 0 ≤ |s'| := abs_nonneg _
  have hs_lt : |s| < 1 / 2 := by rw [hs]; exact dev_lt_half ρ₀
  have hs'_lt : |s'| < 1 / 2 := by rw [hs']; exact dev_lt_half ρ
  have hΔsq : 0 ≤ Δ ^ 2 := sq_nonneg _
  -- `|s| ≤ |s'|`
  have hle : |s| ≤ |s'| := by
    by_contra hlt
    push_neg at hlt
    have : (|s'| - |s|) * (|s'| + 3 * |s|) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  -- `|s| ≠ |s'|`: equality forces the same height and the pair
  have hne : |s| ≠ |s'| := by
    intro heq
    have hΔ0 : Δ = 0 := by
      have h0 : Δ ^ 2 ≤ 0 := by rw [← heq] at hkey; simpa using hkey
      exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h0 hΔsq)
    have hsq : s' ^ 2 = s ^ 2 := (sq_eq_sq_iff_abs_eq_abs s' s).mpr heq.symm
    have hfac : (s' - s) * (s' + s) = 0 := by
      have : (s' - s) * (s' + s) = s' ^ 2 - s ^ 2 := by ring
      rw [this, hsq, sub_self]
    have him : ρ.val.im = ρ₀.val.im := by rw [hΔ] at hΔ0; linarith
    rcases mul_eq_zero.mp hfac with h | h
    · apply h1
      apply Complex.ext
      · rw [hs, hs'] at h; linarith
      · exact him
    · apply h2
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; rw [hs, hs'] at h; linarith
      · simp [Complex.conj_im]; exact him
  have hlt : |s| < |s'| := lt_of_le_of_ne hle hne
  refine ⟨hlt, ?_⟩
  have h3 : |s'| + 3 * |s| ≤ 2 := by linarith
  calc Δ ^ 2 ≤ (|s'| - |s|) * (|s'| + 3 * |s|) := hkey
    _ ≤ (|s'| - |s|) * 2 := mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = 2 * (|s'| - |s|) := by ring

/-! ## The ascent as a sequence -/

/-- Off-axis zeros. -/
abbrev OffZero := {ρ : Zero // ρ.val.re ≠ 1 / 2}

/-- One ascent step: strictly larger deviation, squared height displacement at most twice the gain. -/
def Step (ρ ρ' : OffZero) : Prop :=
  dev ρ.1 < dev ρ'.1 ∧ (ρ'.1.val.im - ρ.1.val.im) ^ 2 ≤ 2 * (dev ρ'.1 - dev ρ.1)

/-- The ascent sequence, built from a step function by choice. -/
def ascent (hstep : ∀ ρ : OffZero, ∃ ρ' : OffZero, Step ρ ρ') (ρ₀ : OffZero) : ℕ → OffZero
  | 0 => ρ₀
  | n + 1 => Classical.choose (hstep (ascent hstep ρ₀ n))

theorem ascent_spec (hstep : ∀ ρ : OffZero, ∃ ρ' : OffZero, Step ρ ρ') (ρ₀ : OffZero) (n : ℕ) :
    Step (ascent hstep ρ₀ n) (ascent hstep ρ₀ (n + 1)) :=
  Classical.choose_spec (hstep (ascent hstep ρ₀ n))

/-! ## Case B dissolved -/

/-- **A Gaussian peak exists whenever an off-axis zero exists.** An infinite ascent would have finite energy
`Σ_k Δ_k² < 1`, hence heights `(γ_n − γ_0)² ≤ n` by Cauchy–Schwarz and moduli `|ρ_n|² ≤ 1 + 2γ_0² + 2n`; the
zeros are distinct, so `Σ_ρ m_ρ/|ρ|²` dominates a harmonic series, against its compiled summability. -/
theorem exists_gaussPeak (ρ₀ : Zero) (hβ : ρ₀.val.re ≠ 1 / 2) :
    ∃ ρ₁ : Zero, ρ₁.val.re ≠ 1 / 2 ∧ GaussPeak ρ₁ := by
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ ρ : OffZero, ∃ ρ' : OffZero, Step ρ ρ' := by
    intro ρ
    obtain ⟨ρ', h1, h2⟩ := ascent_step ρ.2 (hcon ρ.1 ρ.2)
    have hoff : ρ'.val.re ≠ 1 / 2 := off_of_dev_pos (lt_of_le_of_lt (dev_nonneg ρ.1) h1)
    exact ⟨⟨ρ', hoff⟩, h1, h2⟩
  set f : ℕ → OffZero := ascent hstep ⟨ρ₀, hβ⟩ with hf
  have hspec : ∀ n, Step (f n) (f (n + 1)) := fun n => ascent_spec hstep ⟨ρ₀, hβ⟩ n
  -- deviations strictly increase, so the zeros are distinct
  have hmono : StrictMono (fun n => dev (f n).1) := strictMono_nat_of_lt_succ (fun n => (hspec n).1)
  have hinj : Function.Injective (fun n => (f n).1) := by
    intro m n h
    apply hmono.injective
    show dev (f m).1 = dev (f n).1
    simp only at h
    rw [h]
  -- finite energy
  have henergy : ∀ n, ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im) ^ 2
      ≤ 2 * (dev (f n).1 - dev (f 0).1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := (hspec n).2
      linarith
  have henergy1 : ∀ n, ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im) ^ 2 ≤ 1 := by
    intro n
    have h1 := henergy n
    have h2 := dev_lt_half (f n).1
    have h3 := dev_nonneg (f 0).1
    linarith
  -- heights grow at most like `√n`
  have hheight : ∀ n : ℕ, ((f n).1.val.im - (f 0).1.val.im) ^ 2 ≤ n := by
    intro n
    have htel : ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im)
        = (f n).1.val.im - (f 0).1.val.im := Finset.sum_range_sub (fun k => (f k).1.val.im) n
    rw [← htel]
    calc (∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im)) ^ 2
        ≤ ((Finset.range n).card : ℝ) * ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (n : ℝ) * 1 := by
          rw [Finset.card_range]
          exact mul_le_mul_of_nonneg_left (henergy1 n) (Nat.cast_nonneg _)
      _ = n := mul_one _
  -- the moduli grow at most linearly
  set γ₀ : ℝ := (f 0).1.val.im with hγ₀
  have hnorm : ∀ n : ℕ, ‖(f n).1.val‖ ^ 2 ≤ 1 + 2 * γ₀ ^ 2 + 2 * n := by
    intro n
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (f n).1.val.re * (f n).1.val.re ≤ 1 := by
      have h0 := (f n).1.2.1
      have h1 := (f n).1.2.2.1
      nlinarith
    have him : (f n).1.val.im * (f n).1.val.im ≤ 2 * γ₀ ^ 2 + 2 * n := by
      have := hheight n
      nlinarith [sq_nonneg ((f n).1.val.im - 2 * γ₀)]
    linarith
  -- summability transported along the ascent
  have hsum : Summable (fun n : ℕ => (ZD.xiOrderNat (f n).1.val : ℝ) / ‖(f n).1.val‖ ^ 2) :=
    ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.comp_injective hinj
  -- each term dominates a harmonic term
  have hC : (0 : ℝ) < 1 + 2 * γ₀ ^ 2 + 2 := by positivity
  have hlow : ∀ n : ℕ, 1 / ((1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ))
      ≤ (ZD.xiOrderNat (f n).1.val : ℝ) / ‖(f n).1.val‖ ^ 2 := by
    intro n
    have hm : (1 : ℝ) ≤ (ZD.xiOrderNat (f n).1.val : ℝ) :=
      Nat.one_le_cast.mpr (Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros (f n).1.2))
    have hpos : 0 < ‖(f n).1.val‖ ^ 2 := by
      have hne : (f n).1.val ≠ 0 := by
        intro h
        have := (f n).1.2.1
        rw [h] at this
        simp at this
      positivity
    have hle : ‖(f n).1.val‖ ^ 2 ≤ (1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ) := by
      have := hnorm n
      push_cast
      nlinarith [sq_nonneg γ₀, Nat.cast_nonneg (α := ℝ) n]
    calc 1 / ((1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ)) ≤ 1 / ‖(f n).1.val‖ ^ 2 :=
          one_div_le_one_div_of_le hpos hle
      _ ≤ (ZD.xiOrderNat (f n).1.val : ℝ) / ‖(f n).1.val‖ ^ 2 := by
          rw [div_le_div_iff_of_pos_right hpos]; exact hm
  have hharm : Summable (fun n : ℕ => 1 / ((1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hlow hsum
  -- the harmonic series diverges
  have h2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    have := hharm.mul_left (1 + 2 * γ₀ ^ 2 + 2)
    refine this.congr (fun n => ?_)
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    field_simp
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp h2)

/-- Case B as a statement: an off-axis zero gives an off-axis Gaussian peak. -/
theorem gaussPeakExists : (∃ ρ : Zero, ρ.val.re ≠ 1 / 2) → ∃ ρ₀ : Zero, ρ₀.val.re ≠ 1 / 2 ∧ GaussPeak ρ₀ :=
  fun ⟨ρ, hρ⟩ => exists_gaussPeak ρ hρ

/-! ## The Gaussian-class door, with a single hypothesis -/

/-- **Carrier positivity on the pair profiles alone puts every zero on the axis.** -/
theorem axis_of_carrierPositivePair' {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hpos : CarrierPositivePair a b) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ρ, hρ, hne⟩ := hcon
  obtain ⟨ρ₀, hβ, hpeak⟩ := exists_gaussPeak ⟨ρ, hρ⟩ hne
  obtain ⟨lam, hlam, hneg⟩ := gaussianWitness_of_peak ρ₀ hβ hpeak
  have hρ0 : 0 ≤ ρ₀.val.re := ρ₀.2.1.le
  have hρ1 : ρ₀.val.re ≤ 1 := ρ₀.2.2.1.le
  have hge := hpos lam hlam ρ₀.val hρ0 hρ1
  rw [carrierSide_pair_eq_zeroSide hlam hρ0 hρ1 ha hb] at hge
  unfold zeroSide at hge
  linarith

/-- **The Gaussian-class door**: positivity of the prime–Γ functional on the autocorrelations of the pair
profiles (`λ ≥ 1`, centre in the closed strip) implies the Riemann Hypothesis. -/
theorem riemannHypothesis_of_carrierPositivePair' {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hpos : CarrierPositivePair a b) : RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (axis_of_carrierPositivePair' ha hb hpos)

end CriticalLinePhasor.HelixWeilWitness

end

#print axioms CriticalLinePhasor.HelixWeilWitness.ascent_step
#print axioms CriticalLinePhasor.HelixWeilWitness.exists_gaussPeak
#print axioms CriticalLinePhasor.HelixWeilWitness.gaussPeakExists
#print axioms CriticalLinePhasor.HelixWeilWitness.axis_of_carrierPositivePair'
#print axioms CriticalLinePhasor.HelixWeilWitness.riemannHypothesis_of_carrierPositivePair'
