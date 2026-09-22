import RequestProject.ChartKernelInformation
import RequestProject.FiberZeroMidpointWindow
import RequestProject.DVPZeroFreeRegion

/-!
# The moment statement: the midpoint state is never annihilated by both `cosh(δH)` and `sinh(δH)`

`MomentRigidityAt δ y` says the carrier's state at height `y`, `m(y) = phasor3D χ₂ ½ y`, is not
annihilated by both the `cosh(δ·log)`- and the `sinh(δ·log)`-weighted lane sums;
`MomentRigidity` says this for every `0 < |δ| < ½` and every height.

Proved here, unconditionally:

* `momentRigidityAt_iff_chart` / `momentRigidityAt_iff_zeta` — the statement at `(δ, y)` is the
  non-vanishing of the chart at `(½+δ, y)`, i.e. of `ζ(½+δ+iy)`.
* `momentRigidityAt_neg_iff` — the statement is symmetric under `δ ↦ −δ` (the partner mechanism).
* **`momentRigidityAt_of_below`** — it holds for every `δ` at every height `|y| ≤ 1269/2`
  (the station ladder).
* **`momentRigidityAt_of_zeroFree`** — it holds for `|δ| > ½ − c/(log|y|)⁹`, `|y| ≥ e²+1`
  (the house zero-free region `DVP.zero_free_region`, carried to `δ < 0` by the symmetry).
* **`momentRigidityAt_eventually`, `momentRigidity_small`** — at every height the deformations at
  which both moments vanish are isolated; in particular every height has an `ε > 0` with the
  statement true for `0 < |δ| < ε`: the midpoint state is rigid under small deformations.
* `momentRigidity_partial` — the regions assembled.
* **`rh_of_momentRigidity`** — the door: the full moment statement puts every nontrivial zero on
  the line.
* `MomentRigidityResidual` — exactly what is not proved: the statement above height `1269/2`
  outside the zero-free region — and `momentRigidity_of_residual`.

No `axiom`, no `sorry`.
-/

open CriticalLinePhasor
open Filter Topology

noncomputable section

namespace CarrierReadout

/-- **The moment statement at `(δ, y)`**: the midpoint state at height `y` is not annihilated by
both the `cosh(δ·log)`- and the `sinh(δ·log)`-weighted lane sums. -/
def MomentRigidityAt (δ y : ℝ) : Prop := ¬ (coshMoment δ y = 0 ∧ sinhMoment δ y = 0)

/-- **The moment statement**: for every `0 < |δ| < ½` and every height. -/
def MomentRigidity : Prop := ∀ δ y : ℝ, 0 < |δ| → |δ| < 1 / 2 → MomentRigidityAt δ y

theorem momentRigidityAt_iff_chart {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    MomentRigidityAt δ y ↔ laneChart3D (1 / 2 + δ) y ≠ 0 := by
  unfold MomentRigidityAt; rw [ne_eq, chart_zero_iff_moments hδ]

theorem half_add_lt_one {δ : ℝ} (hδ : |δ| < 1 / 2) : 1 / 2 + δ < 1 := by
  have := (abs_lt.mp hδ).2; linarith

theorem momentRigidityAt_iff_zeta {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    MomentRigidityAt δ y ↔ riemannZeta (((1 / 2 + δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  rw [momentRigidityAt_iff_chart hδ, ne_eq, ne_eq,
    ← fiber3D_vanishes_iff_zero (half_add_pos hδ) (half_add_lt_one hδ)]

/-- The statement is symmetric under `δ ↦ −δ` (the partner mechanism, `partner_vanishing_iff`). -/
theorem momentRigidityAt_neg_iff {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    MomentRigidityAt (-δ) y ↔ MomentRigidityAt δ y := by
  have hδ' : |-δ| < 1 / 2 := by rwa [abs_neg]
  rw [momentRigidityAt_iff_chart hδ', momentRigidityAt_iff_chart hδ]
  have h := partner_vanishing_iff (σ := 1 / 2 + δ) (y := y) (half_add_pos hδ) (half_add_lt_one hδ)
  rw [show (1 - (1 / 2 + δ) : ℝ) = 1 / 2 + -δ by ring] at h
  exact not_congr h

/-! ### The certified window -/

/-- **The moment statement holds at every height `|y| ≤ 1269/2`, for every `δ`.** -/
theorem momentRigidityAt_of_below {δ y : ℝ} (hδ0 : 0 < |δ|) (hδ : |δ| < 1 / 2)
    (hy : |y| ≤ 1269 / 2) : MomentRigidityAt δ y := by
  rw [momentRigidityAt_iff_chart hδ]
  intro h
  have := midpoint_of_fiber3D_zero_below (half_add_pos hδ) (half_add_lt_one hδ) hy h
  have hδz : δ = 0 := by linarith
  rw [hδz, abs_zero] at hδ0
  exact lt_irrefl _ hδ0

/-! ### The zero-free region -/

/-- **The moment statement holds in the zero-free region**: there is `c > 0` such that for
`|y| ≥ e² + 1` and `½ − c/(log|y|)⁹ < |δ| < ½` the midpoint state is not annihilated by both
weightings.  (The house region `DVP.zero_free_region`, carried to `δ < 0` by the symmetry.) -/
theorem momentRigidityAt_of_zeroFree : ∃ c : ℝ, 0 < c ∧ ∀ δ y : ℝ, 0 < |δ| → |δ| < 1 / 2 →
    Real.exp 2 + 1 ≤ |y| → 1 / 2 - c / (Real.log |y|) ^ 9 < |δ| → MomentRigidityAt δ y := by
  obtain ⟨c, hc, hzf⟩ := DVP.zero_free_region
  refine ⟨c, hc, ?_⟩
  have hpos : ∀ δ y : ℝ, 0 < δ → |δ| < 1 / 2 → Real.exp 2 + 1 ≤ |y| →
      1 / 2 - c / (Real.log |y|) ^ 9 < |δ| → MomentRigidityAt δ y := by
    intro δ y hδpos hδ hy hbig
    rw [momentRigidityAt_iff_zeta hδ]
    intro hζ
    have hζ' : riemannZeta (((1 / 2 + δ : ℝ) : ℂ) + Complex.I * (y : ℂ)) = 0 := by
      rw [mul_comm]; exact hζ
    have hβ := hzf (1 / 2 + δ) y hζ' (by linarith) (half_add_lt_one hδ).le hy
    rw [abs_of_pos hδpos] at hbig
    linarith
  intro δ y hδ0 hδ hy hbig
  rcases lt_or_gt_of_ne (abs_pos.mp hδ0) with hneg | hposδ
  · rw [← momentRigidityAt_neg_iff hδ]
    have h1 : |-δ| < 1 / 2 := by rwa [abs_neg]
    have h2 : 1 / 2 - c / (Real.log |y|) ^ 9 < |-δ| := by rwa [abs_neg]
    exact hpos (-δ) y (by linarith) h1 hy h2
  · exact hpos δ y hposδ hδ hy hbig

/-! ### Isolation: at every height the annihilating deformations are isolated -/

/-- The chart along the horizontal line at height `y`, as a function of the complex deformation
`w` (the analytic continuation of `δ ↦ laneChart3D (½+δ) y`). -/
def horizontalProfile (y : ℝ) (w : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ ((1 : ℂ) - ((1 / 2 : ℂ) + w + (y : ℂ) * Complex.I)))
    * riemannZeta ((1 / 2 : ℂ) + w + (y : ℂ) * Complex.I)

theorem horizontalProfile_real {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    horizontalProfile y (δ : ℂ) = laneChart3D (1 / 2 + δ) y := by
  have hne : (((1 / 2 + δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [re_add_mul_I, Complex.one_re] at this
    linarith [half_add_lt_one hδ]
  rw [laneChart3D_eq_lane_mul_zeta (half_add_pos hδ) hne]
  unfold horizontalProfile
  have e : (1 / 2 : ℂ) + (δ : ℂ) + (y : ℂ) * Complex.I = ((1 / 2 + δ : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast; ring
  rw [e]

/-- The lane factor does not vanish to the right of the strip either. -/
theorem lane_factor_ne_zero_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s) ≠ 0 := by
  intro h
  have h2 : (2 : ℂ) ^ ((1 : ℂ) - s) = 1 := by linear_combination -h
  have hn : ‖(2 : ℂ) ^ ((1 : ℂ) - s)‖ = 1 := by rw [h2, norm_one]
  have hcast : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  rw [hcast, Complex.norm_natCast_cpow_of_pos (by norm_num)] at hn
  have hre : ((1 : ℂ) - s).re < 0 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hlt : (2 : ℝ) ^ ((1 : ℂ) - s).re < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hre
  have : ((2 : ℕ) : ℝ) ^ ((1 : ℂ) - s).re = (2 : ℝ) ^ ((1 : ℂ) - s).re := by norm_num
  rw [this] at hn
  linarith

/-- The excluded point of the horizontal profile. -/
def profilePole (y : ℝ) : ℂ := (1 / 2 : ℂ) - (y : ℂ) * Complex.I

theorem profile_arg_ne_one_iff (y : ℝ) (w : ℂ) :
    (1 / 2 : ℂ) + w + (y : ℂ) * Complex.I ≠ 1 ↔ w ≠ profilePole y := by
  unfold profilePole
  constructor
  · intro h hw; apply h; rw [hw]; ring
  · intro h hw; apply h; linear_combination hw

theorem horizontalProfile_differentiableAt (y : ℝ) {w : ℂ} (hw : w ≠ profilePole y) :
    DifferentiableAt ℂ (horizontalProfile y) w := by
  have hne : (1 / 2 : ℂ) + w + (y : ℂ) * Complex.I ≠ 1 := (profile_arg_ne_one_iff y w).mpr hw
  have haff : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w + (y : ℂ) * Complex.I) w := by
    fun_prop
  unfold horizontalProfile
  apply DifferentiableAt.mul
  · apply DifferentiableAt.const_sub
    apply DifferentiableAt.const_cpow (differentiableAt_const _ |>.sub haff)
    exact Or.inl (by norm_num)
  · exact (differentiableAt_riemannZeta hne).comp w haff

theorem horizontalProfile_analyticOnNhd (y : ℝ) :
    AnalyticOnNhd ℂ (horizontalProfile y) {profilePole y}ᶜ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro w hw
  exact (horizontalProfile_differentiableAt y hw).differentiableWithinAt

/-- The profile is not identically zero: at `w = 2` it is `(1 − 2^{−3/2−iy}) ζ(5/2+iy) ≠ 0`. -/
theorem horizontalProfile_two_ne_zero (y : ℝ) : horizontalProfile y 2 ≠ 0 := by
  unfold horizontalProfile
  have hre : (1 : ℝ) < ((1 / 2 : ℂ) + 2 + (y : ℂ) * Complex.I).re := by
    simp [Complex.add_re, Complex.mul_re]; norm_num
  exact mul_ne_zero (lane_factor_ne_zero_of_one_lt hre) (riemannZeta_ne_zero_of_one_lt_re hre)

theorem two_ne_profilePole (y : ℝ) : (2 : ℂ) ≠ profilePole y := by
  intro h
  have := congrArg Complex.re h
  unfold profilePole at this
  simp [Complex.sub_re, Complex.mul_re] at this
  norm_num at this

/-- The profile is not eventually zero near any point off the pole. -/
theorem horizontalProfile_not_eventually_zero (y : ℝ) {w₀ : ℂ} (hw : w₀ ≠ profilePole y) :
    ¬ (∀ᶠ w in 𝓝 w₀, horizontalProfile y w = 0) := by
  intro hev
  have hconn : IsPreconnected ({profilePole y}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (profilePole y)).isPreconnected
  have hmem : w₀ ∈ ({profilePole y}ᶜ : Set ℂ) := hw
  have heq := (horizontalProfile_analyticOnNhd y).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconn hmem hev
  exact horizontalProfile_two_ne_zero y (heq (two_ne_profilePole y))

theorem ofReal_ne_profilePole {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) : (δ : ℂ) ≠ profilePole y := by
  rw [← profile_arg_ne_one_iff]
  intro h
  have := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re] at this
  linarith [half_add_lt_one hδ]

/-- **Isolation.**  At every height, near every deformation `δ₀` in the strip, the deformations
at which both moments vanish are isolated: the moment statement holds on a punctured
neighbourhood of `δ₀`. -/
theorem momentRigidityAt_eventually (y : ℝ) {δ₀ : ℝ} (hδ₀ : |δ₀| < 1 / 2) :
    ∀ᶠ δ in 𝓝[≠] δ₀, MomentRigidityAt δ y := by
  have hA : AnalyticAt ℂ (horizontalProfile y) (δ₀ : ℂ) :=
    horizontalProfile_analyticOnNhd y _ (ofReal_ne_profilePole hδ₀ y)
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h (horizontalProfile_not_eventually_zero y (ofReal_ne_profilePole hδ₀ y))
  · have hmap : Tendsto (fun δ : ℝ => (δ : ℂ)) (𝓝[≠] δ₀) (𝓝[≠] (δ₀ : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        rw [Set.mem_compl_singleton_iff] at hδ ⊢
        exact fun h' => hδ (Complex.ofReal_injective h')
    have hnear : ∀ᶠ δ in 𝓝[≠] δ₀, |δ| < 1 / 2 := by
      have hopen : IsOpen {δ : ℝ | |δ| < 1 / 2} := isOpen_lt continuous_abs continuous_const
      have h1 : ∀ᶠ δ in 𝓝 δ₀, |δ| < 1 / 2 := hopen.mem_nhds hδ₀
      exact h1.filter_mono nhdsWithin_le_nhds
    filter_upwards [hmap.eventually h, hnear] with δ hδne hδlt
    rw [momentRigidityAt_iff_chart hδlt, ← horizontalProfile_real hδlt]
    exact hδne

/-- **Rigidity under small deformations.**  Every height has an `ε > 0` such that for
`0 < |δ| < ε` the midpoint state is not annihilated by both weightings. -/
theorem momentRigidity_small (y : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < |δ| → |δ| < ε → MomentRigidityAt δ y := by
  have h := momentRigidityAt_eventually y (δ₀ := 0) (by norm_num)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hP⟩ := h
  refine ⟨ε, hε, fun δ h0 hδ => hP ?_ ?_⟩
  · rwa [Real.dist_eq, sub_zero]
  · rw [Set.mem_compl_singleton_iff]; exact abs_pos.mp h0

/-! ### Assembly, the door, and the residual -/

/-- **The moment statement, where it is proved**: in the window `|y| ≤ 1269/2`, and in the
zero-free region `½ − c/(log|y|)⁹ < |δ|` for `|y| ≥ e² + 1`. -/
theorem momentRigidity_partial : ∃ c : ℝ, 0 < c ∧ ∀ δ y : ℝ, 0 < |δ| → |δ| < 1 / 2 →
    (|y| ≤ 1269 / 2 ∨ (Real.exp 2 + 1 ≤ |y| ∧ 1 / 2 - c / (Real.log |y|) ^ 9 < |δ|)) →
    MomentRigidityAt δ y := by
  obtain ⟨c, hc, hzf⟩ := momentRigidityAt_of_zeroFree
  refine ⟨c, hc, fun δ y hδ0 hδ h => ?_⟩
  rcases h with hy | ⟨hy, hbig⟩
  · exact momentRigidityAt_of_below hδ0 hδ hy
  · exact hzf δ y hδ0 hδ hy hbig

/-- **The door.**  The full moment statement puts every nontrivial zero on the line. -/
theorem rh_of_momentRigidity (h : MomentRigidity) : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  rintro ρ ⟨h0, h1, hζ⟩
  by_contra hne
  have hδ0 : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hδ : |ρ.re - 1 / 2| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hm := h (ρ.re - 1 / 2) ρ.im hδ0 hδ
  rw [momentRigidityAt_iff_zeta hδ] at hm
  apply hm
  have e : (((1 / 2 + (ρ.re - 1 / 2) : ℝ)) : ℂ) + (ρ.im : ℂ) * Complex.I = ρ := by
    apply Complex.ext <;> simp
  rw [e]; exact hζ

/-- **The residual**: the moment statement above the certified window.  This is exactly what is
not proved here (inside the zero-free region it is; between the two it is open). -/
def MomentRigidityResidual : Prop :=
  ∀ δ y : ℝ, 0 < |δ| → |δ| < 1 / 2 → 1269 / 2 < |y| → MomentRigidityAt δ y

theorem momentRigidity_of_residual (h : MomentRigidityResidual) : MomentRigidity := by
  intro δ y hδ0 hδ
  rcases le_or_gt |y| (1269 / 2) with hy | hy
  · exact momentRigidityAt_of_below hδ0 hδ hy
  · exact h δ y hδ0 hδ hy

end CarrierReadout
