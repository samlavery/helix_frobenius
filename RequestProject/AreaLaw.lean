import RequestProject.ClosedForm

/-!
# The area law: √n is the *emergent* radius of the wound integer line

This closes the gap flagged in review. Previously `helixPt n := √n · wind n` *posited* the `√n`, and
the only genuine placement of integers on the carrier (`HelixExhaustion.numberSite`, parameter
`k = n`) has cylindrical radius `|r·n|` — **linear** in `n`. Nothing derived the `√n`.

Here we formalize the placement the model intends:

> a line with all integers at `π/3` intervals, wound around the helix.

The unwound line carries integer `n` at arclength coordinate `s_n = n·(π/3) = n·Δ`
(`Geometry.spinAngle`). *Winding it onto the helix* places `n` at the helix parameter `kₙ` with
`arclength p r kₙ = n·Δ` (arclength-uniform, not parameter-uniform). The cylindrical radius there is
`r·kₙ`, and we prove

  `(r·kₙ)² / n → r·Δ/π`,   i.e.  radius `~ √(rΔ/π)·√n`,   area `π(r·kₙ)² ~ rΔ·n` (linear in `n`).

So `√n` is **derived from the arclength geometry**, exact (`radius ~ √n`) in the gauge `rΔ = π`,
i.e. `r = 3` at `Δ = π/3` (the demo's `r = 1` gives the constant `1/√3`).

Engine: the elementary two-sided bound `π r k² ≤ S(k) ≤ π r k² + 2 k √(p²+r²)` (`k ≥ 0`, `r > 0`).
The derivative of `S` comes from the FTC (`S` is `∫₀ᵏ speed`), so no closed-form-derivative copy.
-/

open scoped BigOperators Real Topology
open Filter Topology

namespace CriticalLinePhasor.Geometry

open Real

/-! ## 1. Elementary bounds on the closed-form arclength -/

/-- `arsinh` grows at most linearly on `[0,∞)`: `arsinh x ≤ 2x`. -/
private lemma arsinh_le_two_mul {x : ℝ} (hx : 0 ≤ x) : Real.arsinh x ≤ 2 * x := by
  have hsqrt : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    rw [show (1 : ℝ) + x = Real.sqrt ((1 + x) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hpos : 0 < x + Real.sqrt (1 + x ^ 2) :=
    add_pos_of_nonneg_of_pos hx (Real.sqrt_pos.mpr (by positivity))
  rw [Real.arsinh]
  rw [show (1 : ℝ) + x ^ 2 = x ^ 2 + 1 by ring] at *
  calc Real.log (x + Real.sqrt (x ^ 2 + 1))
      ≤ (x + Real.sqrt (x ^ 2 + 1)) - 1 := Real.log_le_sub_one_of_pos hpos
    _ ≤ (x + (1 + x)) - 1 := by linarith
    _ = 2 * x := by ring

/-- The closed-form arclength vanishes at the origin: `S(0) = 0`. -/
theorem arclengthClosed_zero (p r : ℝ) : arclengthClosed p r 0 = 0 := by
  simp [arclengthClosed, Real.arsinh_zero]

/-- **Lower area-law bound** `π r k² ≤ S(k)` (`k ≥ 0`, `r > 0`). -/
theorem arclengthClosed_lower_bound (p r k : ℝ) (hr : 0 < r) (hk : 0 ≤ k) :
    Real.pi * r * k ^ 2 ≤ arclengthClosed p r k := by
  unfold arclengthClosed
  have h2 : 0 ≤ 2 * Real.pi * r * k := by positivity
  have hsqrtA : 2 * Real.pi * r * k
      ≤ Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2) := by
    rw [show 2 * Real.pi * r * k = Real.sqrt ((2 * Real.pi * r * k) ^ 2) from
      (Real.sqrt_sq h2).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hterm1 : Real.pi * r * k ^ 2
      ≤ k / 2 * Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrtA (show (0:ℝ) ≤ k / 2 by positivity)]
  have hterm2 : 0 ≤ (p ^ 2 + r ^ 2) / (4 * Real.pi * r)
      * Real.arsinh (2 * Real.pi * r * k / Real.sqrt (p ^ 2 + r ^ 2)) := by
    apply mul_nonneg (by positivity)
    exact Real.arsinh_nonneg_iff.mpr (by positivity)
  linarith

/-- **Upper area-law bound** `S(k) ≤ π r k² + 2 k √(p²+r²)` (`k ≥ 0`, `r > 0`). -/
theorem arclengthClosed_upper_bound (p r k : ℝ) (hr : 0 < r) (hk : 0 ≤ k) :
    arclengthClosed p r k ≤ Real.pi * r * k ^ 2 + 2 * k * Real.sqrt (p ^ 2 + r ^ 2) := by
  unfold arclengthClosed
  have hDpos : 0 < p ^ 2 + r ^ 2 := by positivity
  have hsqrtD : (Real.sqrt (p ^ 2 + r ^ 2)) ^ 2 = p ^ 2 + r ^ 2 := Real.sq_sqrt hDpos.le
  have hsqrtA : Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2)
      ≤ Real.sqrt (p ^ 2 + r ^ 2) + 2 * Real.pi * r * k := by
    have hnn : 0 ≤ Real.sqrt (p ^ 2 + r ^ 2) + 2 * Real.pi * r * k := by positivity
    rw [show Real.sqrt (p ^ 2 + r ^ 2) + 2 * Real.pi * r * k
          = Real.sqrt ((Real.sqrt (p ^ 2 + r ^ 2) + 2 * Real.pi * r * k) ^ 2) from
      (Real.sqrt_sq hnn).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hsqrtD,
      show (0:ℝ) ≤ 4 * Real.pi * r * k * Real.sqrt (p ^ 2 + r ^ 2) by positivity])
  have hterm1 : k / 2 * Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2)
      ≤ Real.pi * r * k ^ 2 + k / 2 * Real.sqrt (p ^ 2 + r ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrtA (show (0:ℝ) ≤ k / 2 by positivity)]
  have harsinh := arsinh_le_two_mul
    (show (0:ℝ) ≤ 2 * Real.pi * r * k / Real.sqrt (p ^ 2 + r ^ 2) by positivity)
  have hsD : Real.sqrt (p ^ 2 + r ^ 2) ≠ 0 := by positivity
  have hterm2 : (p ^ 2 + r ^ 2) / (4 * Real.pi * r)
      * Real.arsinh (2 * Real.pi * r * k / Real.sqrt (p ^ 2 + r ^ 2))
      ≤ k * Real.sqrt (p ^ 2 + r ^ 2) := by
    have hco : 0 ≤ (p ^ 2 + r ^ 2) / (4 * Real.pi * r) := by positivity
    have hstep := mul_le_mul_of_nonneg_left harsinh hco
    have hcollapse : (p ^ 2 + r ^ 2) / (4 * Real.pi * r)
        * (2 * (2 * Real.pi * r * k / Real.sqrt (p ^ 2 + r ^ 2)))
        = k * Real.sqrt (p ^ 2 + r ^ 2) := by
      rw [eq_comm, show k * Real.sqrt (p ^ 2 + r ^ 2)
            = k * ((p ^ 2 + r ^ 2) / Real.sqrt (p ^ 2 + r ^ 2)) by rw [Real.div_sqrt]]
      field_simp
      ring
    linarith [hstep, hcollapse.ge, hcollapse.le]
  have hknn : 0 ≤ k * Real.sqrt (p ^ 2 + r ^ 2) := by positivity
  linarith

/-! ## 2. The arclength is a strictly monotone continuous bijection of `[0,∞)` -/

/-- `speed` is continuous. -/
theorem speed_continuous (p r : ℝ) : Continuous (speed p r) := by
  unfold speed; fun_prop

/-- `speed > 0` for `r > 0`. -/
theorem speed_pos (p r k : ℝ) (hr : 0 < r) : 0 < speed p r k := by
  unfold speed; exact Real.sqrt_pos.mpr (by positivity)

/-- **FTC.** The arclength has derivative `speed` (it is `∫₀ᵏ speed`). -/
theorem arclength_hasDerivAt (p r k : ℝ) : HasDerivAt (arclength p r) (speed p r k) k := by
  have hcont := speed_continuous p r
  have h := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 k)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  exact h

/-- The arclength is continuous (differentiable everywhere). -/
theorem arclength_continuous (p r : ℝ) : Continuous (arclength p r) := by
  have h : Differentiable ℝ (arclength p r) := fun k => (arclength_hasDerivAt p r k).differentiableAt
  exact h.continuous

/-- The arclength is strictly monotone (positive speed). -/
theorem arclength_strictMono (p r : ℝ) (hr : 0 < r) : StrictMono (arclength p r) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(arclength_hasDerivAt p r x).deriv]
  exact speed_pos p r x hr

/-- `arclength = arclengthClosed` as functions, for `r > 0`. -/
theorem arclength_eq_closed (p r : ℝ) (hr : 0 < r) : arclength p r = arclengthClosed p r :=
  funext (fun k => arclength_closed_form p r k hr)

/-- `arclength p r 0 = 0`. -/
theorem arclength_zero (p r : ℝ) (hr : 0 < r) : arclength p r 0 = 0 := by
  rw [arclength_eq_closed p r hr, arclengthClosed_zero]

/-- The arclength tends to `+∞` (the leading area-law term `π r k²` does). -/
theorem arclength_tendsto_atTop (p r : ℝ) (hr : 0 < r) :
    Tendsto (arclength p r) atTop atTop := by
  have hpoly : Tendsto (fun k : ℝ => Real.pi * r * k ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) (tendsto_pow_atTop (by norm_num))
  apply tendsto_atTop_mono' atTop _ hpoly
  filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
  rw [arclength_eq_closed p r hr]
  exact arclengthClosed_lower_bound p r k hr hk

/-- **Placement is well-defined.** For `r > 0` and target arclength `s ≥ 0`, there is a unique helix
parameter `k ≥ 0` with `arclength p r k = s`. -/
theorem exists_unique_windParameter (p r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s) :
    ∃! k : ℝ, 0 ≤ k ∧ arclength p r k = s := by
  have hmono := arclength_strictMono p r hr
  have hcont := arclength_continuous p r
  have h0 : arclength p r 0 = 0 := arclength_zero p r hr
  obtain ⟨K, hKs, hK0⟩ : ∃ K, s ≤ arclength p r K ∧ 0 ≤ K := by
    obtain ⟨K, hK⟩ := (((arclength_tendsto_atTop p r hr).eventually_ge_atTop s).and
      (eventually_ge_atTop (0:ℝ))).exists
    exact ⟨K, hK.1, hK.2⟩
  have hsub : Set.Icc (arclength p r 0) (arclength p r K) ⊆ arclength p r '' Set.Icc 0 K :=
    intermediate_value_Icc hK0 hcont.continuousOn
  have hmem : s ∈ Set.Icc (arclength p r 0) (arclength p r K) := by rw [h0]; exact ⟨hs, hKs⟩
  obtain ⟨k, hk_mem, hk_eq⟩ := hsub hmem
  refine ⟨k, ⟨hk_mem.1, hk_eq⟩, ?_⟩
  rintro y ⟨_, hy_eq⟩
  exact hmono.injective (hy_eq.trans hk_eq.symm)

/-- **The wind parameter** `kₛ`: the unique `k ≥ 0` with `arclength p r k = s`. -/
noncomputable def windParameter (p r s : ℝ) : ℝ :=
  if h : 0 < r ∧ 0 ≤ s then (exists_unique_windParameter p r h.1 s h.2).choose else 0

theorem windParameter_spec (p r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) :
    0 ≤ windParameter p r s ∧ arclength p r (windParameter p r s) = s := by
  rw [windParameter, dif_pos ⟨hr, hs⟩]
  exact (exists_unique_windParameter p r hr s hs).choose_spec.1

/-! ## 3. Winding the integer line onto the helix, and the emergent √n radius -/

/-- **The wound integer site**: integer `n`, at arclength `s_n = n·Δ = spinAngle n` on the unwound
line, wound onto the helix. The correct (arclength-uniform) placement, replacing the
parameter-uniform `HelixExhaustion.numberSite`. -/
noncomputable def windIntegerSite (p r : ℝ) (n : ℕ) : ℝ × ℝ × ℝ :=
  helix p r (windParameter p r (spinAngle n))

theorem spinAngle_nonneg (n : ℕ) : 0 ≤ spinAngle n := by unfold spinAngle; positivity

/-- The cylindrical radius of the wound site `n` is `r · kₙ` (`kₙ ≥ 0`). -/
theorem windIntegerSite_cyl_radius (p r : ℝ) (hr : 0 < r) (n : ℕ) :
    Real.sqrt ((windIntegerSite p r n).1 ^ 2 + (windIntegerSite p r n).2.1 ^ 2)
      = r * windParameter p r (spinAngle n) := by
  have hk : 0 ≤ windParameter p r (spinAngle n) := (windParameter_spec p r _ hr (spinAngle_nonneg n)).1
  rw [windIntegerSite, helix_cyl_radius, abs_of_nonneg (by positivity)]

/-- Auxiliary: `(√n)⁻¹ → 0`. -/
private theorem tendsto_inv_sqrt_nat : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (Real.continuous_sqrt.tendsto 0).comp hinv
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_inv] at h
  exact h

/-- **Emergent √n (relation form).** Given any arclength-uniform winding `kₙ ≥ 0` of the `Δ`-spaced
integer line onto the helix (`S(kₙ) = n·Δ`), the squared cylindrical radius satisfies
`(r·kₙ)²/n → r·Δ/π`. So radius `~ √(rΔ/π)·√n`: the `√n` is *derived*, not posited. -/
theorem emergent_radius_sq_tendsto
    (p r Δ : ℝ) (hr : 0 < r) (_hΔ : 0 < Δ)
    (k : ℕ → ℝ) (hk0 : ∀ n, 0 ≤ k n)
    (hplace : ∀ n, arclength p r (k n) = (n : ℝ) * Δ) :
    Tendsto (fun n : ℕ => (r * k n) ^ 2 / (n : ℝ)) atTop (𝓝 (r * Δ / Real.pi)) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  set D : ℝ := Real.sqrt (p ^ 2 + r ^ 2) with hDdef
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  -- transported bounds
  have hlb : ∀ n : ℕ, Real.pi * r * (k n) ^ 2 ≤ (n : ℝ) * Δ := fun n => by
    rw [← hplace n, arclength_eq_closed p r hr]; exact arclengthClosed_lower_bound p r (k n) hr (hk0 n)
  have hub : ∀ n : ℕ, (n : ℝ) * Δ ≤ Real.pi * r * (k n) ^ 2 + 2 * (k n) * D := fun n => by
    rw [← hplace n, arclength_eq_closed p r hr]; exact arclengthClosed_upper_bound p r (k n) hr (hk0 n)
  -- key: kₙ/n → 0
  have hkn_div : Tendsto (fun n : ℕ => k n / (n : ℝ)) atTop (𝓝 0) := by
    have hbnd : Tendsto (fun n : ℕ => Real.sqrt (Δ / (Real.pi * r)) * (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_sqrt_nat.const_mul (Real.sqrt (Δ / (Real.pi * r)))
    refine squeeze_zero (fun n => div_nonneg (hk0 n) (Nat.cast_nonneg n)) (fun n => ?_) hbnd
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hm0 : (0:ℝ) < n := by exact_mod_cast hn
      have hsqn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hm0
      have hA : (k n) ^ 2 ≤ (n : ℝ) * Δ / (Real.pi * r) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [hlb n]
      have hB : k n ≤ Real.sqrt n * Real.sqrt (Δ / (Real.pi * r)) := by
        rw [← Real.sqrt_mul (by positivity),
          show (n : ℝ) * (Δ / (Real.pi * r)) = (n : ℝ) * Δ / (Real.pi * r) by ring,
          ← Real.sqrt_sq (hk0 n)]
        exact Real.sqrt_le_sqrt hA
      have hn_eq : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
        rw [inv_mul_eq_div, div_eq_iff hsqn.ne', Real.mul_self_sqrt hm0.le]
      rw [div_le_iff₀ hm0, mul_assoc, hn_eq,
        mul_comm (Real.sqrt (Δ / (Real.pi * r))) (Real.sqrt n)]
      exact hB
  -- squeeze:  L - (2rD/π)(kₙ/n)  ≤  f n  ≤  L
  have hg : Tendsto (fun n : ℕ => r * Δ / Real.pi - (2 * r * D / Real.pi) * (k n / (n : ℝ)))
      atTop (𝓝 (r * Δ / Real.pi)) := by
    simpa using tendsto_const_nhds.sub (hkn_div.const_mul (2 * r * D / Real.pi))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hm0 : (0:ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hm0]
    have hubn := hub n
    have hrw : (r * Δ / Real.pi - 2 * r * D / Real.pi * (k n / (n : ℝ))) * (n : ℝ)
        = r * ((n : ℝ) * Δ - 2 * (k n) * D) / Real.pi := by
      field_simp
    rw [hrw, div_le_iff₀ hπ]
    nlinarith [hubn, hr.le]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hm0 : (0:ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hm0]
    have hlbn := hlb n
    rw [show r * Δ / Real.pi * (n : ℝ) = r * ((n : ℝ) * Δ) / Real.pi by ring, le_div_iff₀ hπ]
    nlinarith [hlbn, hr.le]

/-- **Emergent √n (concrete form).** For the wound integer sites, the squared cylindrical radius
divided by `n` tends to `r·Δ/π` (with `Δ = π/3`). -/
theorem windIntegerSite_radius_sq_tendsto (p r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ =>
        (Real.sqrt ((windIntegerSite p r n).1 ^ 2 + (windIntegerSite p r n).2.1 ^ 2)) ^ 2 / (n : ℝ))
      atTop (𝓝 (r * (Real.pi / 3) / Real.pi)) := by
  have hΔ : (0:ℝ) < Real.pi / 3 := by positivity
  have hk0 : ∀ n : ℕ, 0 ≤ windParameter p r (spinAngle n) := fun n =>
    (windParameter_spec p r _ hr (spinAngle_nonneg n)).1
  have hplace : ∀ n : ℕ,
      arclength p r (windParameter p r (spinAngle n)) = (n : ℝ) * (Real.pi / 3) := by
    intro n
    rw [(windParameter_spec p r _ hr (spinAngle_nonneg n)).2]; unfold spinAngle; ring
  refine (emergent_radius_sq_tendsto p r (Real.pi / 3) hr hΔ
    (fun n => windParameter p r (spinAngle n)) hk0 hplace).congr (fun n => ?_)
  rw [windIntegerSite_cyl_radius p r hr n]

/-- **Unit gauge.** With `Δ = π/3` the area-law constant `rΔ/π = r/3` is `1` iff `r = 3`. In that
gauge `radius²/n → 1`, i.e. `radius ~ √n` exactly — the model's `√n`, now derived. (`r = 1` gives
`1/3`, i.e. `radius ~ √(n/3)`.) -/
theorem windIntegerSite_radius_sq_tendsto_unit_gauge :
    Tendsto (fun n : ℕ =>
        (Real.sqrt ((windIntegerSite 1 3 n).1 ^ 2 + (windIntegerSite 1 3 n).2.1 ^ 2)) ^ 2 / (n : ℝ))
      atTop (𝓝 1) := by
  have h := windIntegerSite_radius_sq_tendsto 1 3 (by norm_num)
  have he : (3 : ℝ) * (Real.pi / 3) / Real.pi = 1 := by field_simp
  rwa [he] at h

end CriticalLinePhasor.Geometry
