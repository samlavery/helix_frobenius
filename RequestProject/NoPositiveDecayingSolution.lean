import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# No eventually-positive solution of `g'' − 4πg' = r²g/y²` tends to zero

This is the real-analysis core of the general-`r` emptiness argument for
`GenuineMaassCuspForm3D`.  The structure's `radial_equation`, after stripping `e^{−2πy}`, says
exactly `g'' − 4πg' = r²g/y²` (`realReduced_equation`), while `radial_normalization` says
`2√y·g(y) → 1` — so `g` is eventually positive and tends to `0`.  Those are contradictory.

**The argument uses no integrals.**  Two monotone quantities do all the work:

* `Φ(y) := e^{−4πy}·g'(y)` has `Φ' = e^{−4πy}·r²g/y² ≥ 0`, so `Φ` is nondecreasing.  If `Φ` were
  ever positive then `g' > 0` from there on, so `g` would be bounded below by a positive value —
  contradicting `g → 0`.  Hence **`g' ≤ 0`**: `g` is nonincreasing.
* `V(y) := g'(y) − 4π·g(y)` has `V' = r²g/y² ≥ 0`, so `V` is nondecreasing, and `V ≤ 0` because
  `g' ≤ 0 < g`.  Bounded and monotone, it converges; its limit is `0`, since `g' → L < 0` would
  drive `g` below zero linearly.

The comparison that finishes it is the third monotone quantity, and it replaces the improper
integral `∫_y^∞ g/t²` that the classical argument would use: for fixed `y`,

  **`W(t) := V(t) + r²·g(y)/t`  has  `W'(t) = r²(g(t) − g(y))/t² ≤ 0`**

for `t ≥ y`, because `g` is nonincreasing.  So `W(Z) ≤ W(y)`, and `W(Z) → 0`, giving
`V(y) ≥ −r²g(y)/y` — whence

  **`g'(y) = V(y) + 4π·g(y) ≥ g(y)·(4π − r²/y) > 0`  for  `y > r²/(4π)`,**

flatly contradicting `g' ≤ 0`.
-/

open Filter Set
open scoped Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- **No eventually-positive solution of `g'' − 4πg' = c·g/y²` tends to zero, for any `c ≥ 0`.**

The sign of `c` is the whole story, and it is sharp.  The structure's `radial_equation` gives
`c = r² ≥ 0`, so this applies and the structure is empty.  The **Whittaker** equation — the one
`K_{ir}(2πy)` actually satisfies — gives `c = −(1/4 + r²) < 0`, where every monotonicity below
reverses and the conclusion is false: that is exactly the regime in which `2√y·e^{2πy}K → 1`
lives. -/
theorem no_positive_decaying_solution
    {c : ℝ} {g : ℝ → ℝ} {Y : ℝ} (hc : 0 ≤ c) (hY : 0 < Y)
    (hg1 : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ g y)
    (hg2 : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (deriv g) y)
    (hode : ∀ y : ℝ, 0 < y →
      deriv (deriv g) y - 4 * Real.pi * deriv g y = c * g y / y ^ 2)
    (hzero : Tendsto g atTop (𝓝 0))
    (hpos : ∀ y : ℝ, Y ≤ y → 0 < g y) : False := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hquot : ∀ y : ℝ, 0 < y → Y ≤ y → 0 ≤ c * g y / y ^ 2 := by
    intro y hy hYy
    exact div_nonneg (mul_nonneg hc (hpos y hYy).le) (sq_nonneg y)
  -- ## The exponentially weighted derivative `Φ = e^{-4πy} g'`
  have hexp : ∀ y : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-(4 * Real.pi) * t))
      (Real.exp (-(4 * Real.pi) * y) * (-(4 * Real.pi))) y := by
    intro y
    have h0 : HasDerivAt (fun t : ℝ => -(4 * Real.pi) * t) (-(4 * Real.pi)) y := by
      simpa using (hasDerivAt_id y).const_mul (-(4 * Real.pi))
    exact h0.exp
  have hΦ : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun t : ℝ => Real.exp (-(4 * Real.pi) * t) * deriv g t)
        (Real.exp (-(4 * Real.pi) * y) * (c * g y / y ^ 2)) y := by
    intro y hy
    refine ((hexp y).mul (hg2 y hy).hasDerivAt).congr_deriv ?_
    have h := hode y hy
    linear_combination Real.exp (-(4 * Real.pi) * y) * h
  have hΦmono : MonotoneOn (fun t : ℝ => Real.exp (-(4 * Real.pi) * t) * deriv g t)
      (Set.Ici Y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici Y) ?_ ?_ ?_
    · exact fun y hy => ((hΦ y (lt_of_lt_of_le hY hy)).continuousAt).continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hΦ y (lt_trans hY hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hΦ y (lt_trans hY hy)).deriv]
      exact mul_nonneg (Real.exp_pos _).le (hquot y (lt_trans hY hy) hy.le)
  -- ## `g` is nonincreasing past `Y`
  have hg'nonpos : ∀ y : ℝ, Y ≤ y → deriv g y ≤ 0 := by
    intro y₀ hy₀
    by_contra hcon
    push_neg at hcon
    have hΦ0 : 0 < Real.exp (-(4 * Real.pi) * y₀) * deriv g y₀ :=
      mul_pos (Real.exp_pos _) hcon
    have hg'pos : ∀ y : ℝ, y₀ ≤ y → 0 ≤ deriv g y := by
      intro y hy
      have h1 := hΦmono (Set.mem_Ici.mpr hy₀) (Set.mem_Ici.mpr (le_trans hy₀ hy)) hy
      have h2 : 0 < Real.exp (-(4 * Real.pi) * y) * deriv g y := lt_of_lt_of_le hΦ0 h1
      by_contra hneg
      push_neg at hneg
      nlinarith [Real.exp_pos (-(4 * Real.pi) * y)]
    have hy₀pos : 0 < y₀ := lt_of_lt_of_le hY hy₀
    have hgmono : MonotoneOn g (Set.Ici y₀) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici y₀) ?_ ?_ ?_
      · exact fun y hy => ((hg1 y (lt_of_lt_of_le hy₀pos hy)).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        exact (hg1 y (lt_trans hy₀pos hy)).differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        exact hg'pos y hy.le
    have hgy₀ : 0 < g y₀ := hpos y₀ hy₀
    obtain ⟨y, hy1, hy2⟩ :=
      ((hzero.eventually_lt_const hgy₀).and (eventually_ge_atTop y₀)).exists
    exact absurd (hgmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy2) hy2) (not_le.mpr hy1)
  have hganti : AntitoneOn g (Set.Ici Y) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici Y) ?_ ?_ ?_
    · exact fun y hy => ((hg1 y (lt_of_lt_of_le hY hy)).continuousAt).continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hg1 y (lt_trans hY hy)).differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact hg'nonpos y hy.le
  -- ## The shifted derivative `V = g' - 4πg`, nondecreasing and nonpositive
  have hV : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun t : ℝ => deriv g t - 4 * Real.pi * g t) (c * g y / y ^ 2) y := by
    intro y hy
    refine (((hg2 y hy).hasDerivAt).sub (((hg1 y hy).hasDerivAt).const_mul
      (4 * Real.pi))).congr_deriv ?_
    have h := hode y hy
    linarith [h]
  have hVnonpos : ∀ y : ℝ, Y ≤ y → deriv g y - 4 * Real.pi * g y ≤ 0 := by
    intro y hy
    have h1 := hg'nonpos y hy
    have h2 := hpos y hy
    nlinarith
  have hVmono : MonotoneOn (fun t : ℝ => deriv g t - 4 * Real.pi * g t) (Set.Ici Y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici Y) ?_ ?_ ?_
    · exact fun y hy => ((hV y (lt_of_lt_of_le hY hy)).continuousAt).continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hV y (lt_trans hY hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hV y (lt_trans hY hy)).deriv]
      exact hquot y (lt_trans hY hy) hy.le
  -- ## `V` converges, and its limit is `0`
  have hVlim : Tendsto (fun t : ℝ => deriv g t - 4 * Real.pi * g t) atTop (𝓝 0) := by
    set V : ℝ → ℝ := fun t => deriv g t - 4 * Real.pi * g t with hVdef
    set V₁ : ℝ → ℝ := fun t => V (max t Y) with hV₁def
    have hV₁mono : Monotone V₁ := by
      intro a b hab
      exact hVmono (Set.mem_Ici.mpr (le_max_right a Y)) (Set.mem_Ici.mpr (le_max_right b Y))
        (max_le_max hab le_rfl)
    have hV₁bdd : BddAbove (Set.range V₁) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hVnonpos _ (le_max_right t Y)
    have hV₁lim := tendsto_atTop_ciSup hV₁mono hV₁bdd
    set L : ℝ := ⨆ t : ℝ, V₁ t with hLdef
    have hVlimL : Tendsto V atTop (𝓝 L) := by
      refine hV₁lim.congr' ?_
      filter_upwards [eventually_ge_atTop Y] with t ht
      rw [hV₁def]
      simp [max_eq_left ht]
    have hLle : L ≤ 0 := ciSup_le fun t => hVnonpos _ (le_max_right t Y)
    -- the derivative converges to `L` as well
    have hderivlim : Tendsto (deriv g) atTop (𝓝 L) := by
      have := hVlimL.add (hzero.const_mul (4 * Real.pi))
      simpa [hVdef] using this
    rcases eq_or_lt_of_le hLle with hL0 | hLneg
    · rw [← hL0]; exact hVlimL
    -- if `L < 0` then `g` is dragged below zero linearly
    exfalso
    set c : ℝ := -L / 2 with hcdef
    have hc : 0 < c := by rw [hcdef]; linarith
    obtain ⟨Y₂, hY₂⟩ := (hderivlim.eventually_lt_const (by linarith : L < -c)).exists_forall_of_atTop
    set Y₃ : ℝ := max Y₂ Y with hY₃def
    have hY₃pos : 0 < Y₃ := lt_of_lt_of_le hY (le_max_right Y₂ Y)
    have hshift : AntitoneOn (fun t : ℝ => g t + c * t) (Set.Ici Y₃) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici Y₃) ?_ ?_ ?_
      · exact fun y hy => (((hg1 y (lt_of_lt_of_le hY₃pos hy)).continuousAt).add
          (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        exact ((hg1 y (lt_trans hY₃pos hy)).add
          ((differentiable_id.const_mul c).differentiableAt)).differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hd : deriv (fun t : ℝ => g t + c * t) y = deriv g y + c := by
          have h2 : HasDerivAt (fun t : ℝ => c * t) c y := by
            simpa using (hasDerivAt_id y).const_mul c
          exact ((hg1 y (lt_trans hY₃pos hy)).hasDerivAt.add h2).deriv
        rw [hd]
        have := hY₂ y (le_trans (le_max_left Y₂ Y) hy.le)
        linarith
    -- pick a point where the linear bound is already negative
    obtain ⟨y, hy1, hy2⟩ := ((eventually_ge_atTop Y₃).and
      (eventually_ge_atTop ((g Y₃ + c * Y₃) / c))).exists
    have hle := hshift (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy1) hy1
    have hgy : 0 < g y := hpos y (le_trans (le_max_right Y₂ Y) hy1)
    have : (g Y₃ + c * Y₃) / c ≤ y := hy2
    rw [div_le_iff₀ hc] at this
    simp only at hle
    nlinarith
  -- ## The integral-free comparison: `V(y) ≥ -r²g(y)/y`
  set y₁ : ℝ := max Y (c / (4 * Real.pi) + 1) with hy₁def
  have hy₁Y : Y ≤ y₁ := le_max_left _ _
  have hy₁pos : 0 < y₁ := lt_of_lt_of_le hY hy₁Y
  have hy₁big : c / (4 * Real.pi) < y₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hW : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun u : ℝ => (deriv g u - 4 * Real.pi * g u) + c * g y₁ / u)
        (c * g t / t ^ 2 - c * g y₁ / t ^ 2) t := by
    intro t ht
    have hinv : HasDerivAt (fun u : ℝ => c * g y₁ / u)
        (-(c * g y₁ / t ^ 2)) t := by
      have h := (hasDerivAt_inv ht.ne').const_mul (c * g y₁)
      refine h.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · field_simp
      · filter_upwards with u
        rw [div_eq_mul_inv]
    refine ((hV t ht).add hinv).congr_deriv ?_
    ring
  have hWanti : AntitoneOn (fun u : ℝ => (deriv g u - 4 * Real.pi * g u) + c * g y₁ / u)
      (Set.Ici y₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici y₁) ?_ ?_ ?_
    · exact fun t ht => ((hW t (lt_of_lt_of_le hy₁pos ht)).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hW t (lt_trans hy₁pos ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hW t (lt_trans hy₁pos ht)).deriv]
      have hgt : g t ≤ g y₁ :=
        hganti (Set.mem_Ici.mpr hy₁Y) (Set.mem_Ici.mpr (le_trans hy₁Y ht.le)) ht.le
      have ht2 : (0:ℝ) < t ^ 2 := pow_pos (lt_trans hy₁pos ht) 2
      have : c * g t ≤ c * g y₁ := mul_le_mul_of_nonneg_left hgt hc
      rw [sub_nonpos, div_le_div_iff_of_pos_right ht2]
      exact this
  have hWlim : Tendsto (fun u : ℝ => (deriv g u - 4 * Real.pi * g u) + c * g y₁ / u)
      atTop (𝓝 0) := by
    have hc : Tendsto (fun u : ℝ => c * g y₁ / u) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    simpa using hVlim.add hc
  have hWle : (0:ℝ) ≤ (deriv g y₁ - 4 * Real.pi * g y₁) + c * g y₁ / y₁ := by
    refine le_of_tendsto hWlim ?_
    filter_upwards [eventually_ge_atTop y₁] with Z hZ
    exact hWanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hZ) hZ
  -- ## `g'(y₁) > 0`, contradicting `g' ≤ 0`
  have hgy₁ : 0 < g y₁ := hpos y₁ hy₁Y
  have hkey : 0 < deriv g y₁ := by
    have hr : c / y₁ < 4 * Real.pi := by
      rw [div_lt_iff₀ hy₁pos]
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < 4 * Real.pi)] at hy₁big
      linarith
    have hdiv : c * g y₁ / y₁ = (c / y₁) * g y₁ := by ring
    rw [hdiv] at hWle
    nlinarith
  exact absurd hkey (not_lt.mpr (hg'nonpos y₁ hy₁Y))

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.no_positive_decaying_solution
