import RequestProject.ClosedForm
import RequestProject.LogWeightOperator
import RequestProject.LFunctionPhasor
import RequestProject.GeometricPhasorClosure

/-!
# The geometry consumed: the site weight is forced, the climber registers the sites,
# the cell is the helix's angle, and the arclength bounds the head

The paper *A carrier readout for the zeros of ζ* fixes a geometry (§2: the double-ended
Archimedean helix, its climber and its closed-form arclength) and a carrier (§3: a
numberline laid along it, sites at arclength `x_n = Δ n`, harmonically scaled), and then
writes the fiber as the phasors `x_n^{−s}`.  A referee observed, correctly, that as
written nothing in §§2–3 is *consumed* by a later proof: the site weight `log x_n` is
posited, the climber and the arclength theorem are never used again.  This file makes
the geometry load-bearing, by theorems:

* `gaugeWeight_eq_log` — **the logarithm is forced, not posited.**  Call a weight `w` on
  the carrier *gauge* if rescaling the carrier by `Δ` shifts every site's weight by one
  constant `c(Δ)` — that is, if the carrier scale acts on the fiber by a common factor,
  which is the gauge property the paper states as a design fact.  Then a continuous
  gauge weight is `a·log x + b`.  This is Cauchy's equation on the multiplicative carrier.
  `log_isGaugeWeight` is the converse; `logWeight_gauge_shift` is the paper's
  `H_Δ = H + log Δ·I` as the gauge constant `c(Δ) = log Δ`.
* `climber_reaches_site_at_weight`, `Nindex_at_site` — **the climber registers the sites.**
  On the axial rail (`r = 0`, pitch `p`), where the carrier's arclength is its height
  (`arclength_r_zero`), the climber `k(y) = e^y/p` reaches the site at arclength `Δ(n+1)`
  exactly at the ordinate `log(Δ(n+1))` — the eigenvalue of `H_Δ` on the `n`-th phasor —
  and the carrier index `N(y)` at that ordinate is `n+1`.  So `H` is the climber read on
  the sites.
* `mellinSpin_eq_registrations` — **the phase is the product of two registrations** by the
  same climber: the reading ordinate `y = log z` and the site's ordinate `log x_n`.
* `cell_eq_helix_angle`, `helix_at_sixth_turn` — **the μ6 cell is the helix's angle at six
  sites per turn**: `cell n = exp(i·2π·(n/6))`, and the helix at turn parameter `n/6` has
  that angle; the antipode `n+3` is half a turn up (`cell_antipodal_cancel`).
* `arclength_ge_pi_r_sq`, `Nindex_ge_exp` — **the closed-form arclength bounds the geometric
  head**: `S(k) ≥ π r k²`, so at `Δ = π/3` the carrier index satisfies
  `N(y) ≥ (3r/p²) e^{2y}` — exponential in the ordinate, against the lane saddle's linear
  `2y/π`.
-/

open CriticalLinePhasor.Geometry

noncomputable section

namespace CarrierReadout

/-! ### 1. The gauge law forces the logarithm -/

/-- A weight on the carrier is **gauge** if rescaling the carrier by `Δ > 0` shifts the
weight of every site by one constant `c Δ`: the carrier scale acts on the fiber by a common
factor. -/
def IsGaugeWeight (w : ℝ → ℝ) : Prop :=
  ∃ c : ℝ → ℝ, ∀ Δ x : ℝ, 0 < Δ → 0 < x → w (Δ * x) = w x + c Δ

/-- The logarithm is a gauge weight, with gauge constant `c Δ = log Δ`. -/
theorem log_isGaugeWeight : IsGaugeWeight Real.log :=
  ⟨Real.log, fun Δ x hΔ hx => by rw [Real.log_mul hΔ.ne' hx.ne', add_comm]⟩

/-- **The logarithm is forced.**  A gauge weight that is continuous on the carrier
`(0, ∞)` is `a · log x + b`. -/
theorem gaugeWeight_eq_log {w : ℝ → ℝ} (hw : IsGaugeWeight w)
    (hc : ContinuousOn w (Set.Ioi 0)) :
    ∃ a b : ℝ, ∀ x : ℝ, 0 < x → w x = a * Real.log x + b := by
  obtain ⟨c, hgauge⟩ := hw
  -- φ u := w (e^u) − w 1 is additive
  have hadd : ∀ u v : ℝ,
      w (Real.exp (u + v)) - w 1 = (w (Real.exp u) - w 1) + (w (Real.exp v) - w 1) := by
    intro u v
    have h1 := hgauge (Real.exp u) (Real.exp v) (Real.exp_pos u) (Real.exp_pos v)
    have h2 := hgauge (Real.exp u) 1 (Real.exp_pos u) one_pos
    rw [mul_one] at h2
    rw [Real.exp_add, h1, h2]
    ring
  let φ : ℝ →+ ℝ :=
    { toFun := fun u => w (Real.exp u) - w 1
      map_zero' := by simp
      map_add' := hadd }
  have hφc : Continuous φ := by
    show Continuous (fun u => w (Real.exp u) - w 1)
    exact (hc.comp_continuous Real.continuous_exp (fun u => Real.exp_pos u)).sub
      continuous_const
  refine ⟨φ 1, w 1, fun x hx => ?_⟩
  have hlin : φ (Real.log x) = Real.log x * φ 1 := by
    have := map_real_smul φ hφc (Real.log x) (1 : ℝ)
    simpa [smul_eq_mul] using this
  have hφx : φ (Real.log x) = w x - w 1 := by
    show w (Real.exp (Real.log x)) - w 1 = w x - w 1
    rw [Real.exp_log hx]
  linarith [hlin, hφx]

/-- The weight of the paper's `H_Δ` is the gauge shift of the weight of `H`:
`log(Δ(n+1)) = log(n+1) + log Δ` — Theorem `carrierLogWeight_eq_shift` read as the gauge
constant `c Δ = log Δ`. -/
theorem logWeight_gauge_shift (Δ : ℝ) (hΔ : 0 < Δ) (n : ℕ) :
    carrierLogWeight Δ n = logWeight n + Real.log Δ := by
  rw [carrierLogWeight_eq Δ hΔ n, add_comm]

/-! ### 2. The climber registers the sites -/

/-- The arclength position of the site of index `n` (site number `n+1`) on a carrier of
scale `Δ`: `x_{n+1} = Δ (n+1)`. -/
def siteArclength (Δ : ℝ) (n : ℕ) : ℝ := Δ * ((n : ℝ) + 1)

/-- On the axial rail the climber reaches arclength `x` at the ordinate `log x`. -/
theorem climber_reaches_arclength (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    arclength p 0 (kClimb p (Real.log x)) = x := by
  rw [arclength_r_zero p _ hp.le, kClimb, Real.exp_log hx]
  field_simp

/-- **The climber reaches each site at its own weight.**  On the axial rail of pitch `p`,
the climber reaches the site at arclength `Δ(n+1)` exactly at the ordinate
`carrierLogWeight Δ n = log(Δ(n+1))`, the eigenvalue of `H_Δ` on the `n`-th phasor
(`H_phasor`, `carrierLogWeight_eq_shift`). -/
theorem climber_reaches_site_at_weight (p Δ : ℝ) (hp : 0 < p) (hΔ : 0 < Δ) (n : ℕ) :
    arclength p 0 (kClimb p (carrierLogWeight Δ n)) = siteArclength Δ n := by
  unfold carrierLogWeight siteArclength
  exact climber_reaches_arclength p _ hp (by positivity)

/-- **The carrier index counts the site.**  At the harmonic scale `Δ = π/3`, the index
`N(y) = S(k(y))/Δ` at the ordinate of site `n` is `n+1`. -/
theorem Nindex_at_site (p : ℝ) (hp : 0 < p) (n : ℕ) :
    Nindex p 0 (carrierLogWeight Delta n) = (n : ℝ) + 1 := by
  have hΔ : 0 < Delta := by unfold Delta; positivity
  unfold Nindex
  rw [climber_reaches_site_at_weight p Delta hp hΔ n, siteArclength]
  field_simp

/-! ### 3. The phase is the product of two registrations -/

/-- **The phasor's phase is the product of two registrations by the climber**: the reading
ordinate `y` and the site's ordinate `log(n+1)` (the weight of `H`). -/
theorem mellinSpin_eq_registrations (y : ℝ) (n : ℕ) :
    CriticalLinePhasor.LFunctionPhasor.mellinSpin y (n + 1)
      = Complex.exp (-(y * logWeight n) * Complex.I) := by
  unfold CriticalLinePhasor.LFunctionPhasor.mellinSpin logWeight
  push_cast
  rfl

/-! ### 4. The μ6 cell is the helix's angle -/

/-- **The cell is the helix's angle at six sites per turn**: `cell n = exp(i · 2π · (n/6))`. -/
theorem cell_eq_helix_angle (n : ℕ) :
    CriticalLinePhasor.Geometric.cell n
      = Complex.exp (Complex.I * (2 * Real.pi * ((n : ℝ) / 6))) := by
  unfold CriticalLinePhasor.Geometric.cell
  congr 1
  push_cast
  ring

/-- The helix at turn parameter `n/6` sits at the angle of `cell n`, at radius `r n/6` and
height `p n/6`; the antipode `n+3` is half a turn up. -/
theorem helix_at_sixth_turn (p r : ℝ) (n : ℕ) :
    helix p r ((n : ℝ) / 6)
      = (r * ((n : ℝ) / 6) * (CriticalLinePhasor.Geometric.cell n).re,
         r * ((n : ℝ) / 6) * (CriticalLinePhasor.Geometric.cell n).im,
         p * ((n : ℝ) / 6)) := by
  have hθ : (2 : ℝ) * Real.pi * ((n : ℝ) / 6) = Real.pi / 3 * (n : ℝ) := by ring
  have hcast : Complex.I * ((Real.pi : ℂ) / 3 * ((n : ℝ) : ℂ))
      = ((Real.pi / 3 * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hre : (CriticalLinePhasor.Geometric.cell n).re = Real.cos (Real.pi / 3 * (n : ℝ)) := by
    unfold CriticalLinePhasor.Geometric.cell
    rw [hcast, Complex.exp_ofReal_mul_I_re]
  have him : (CriticalLinePhasor.Geometric.cell n).im = Real.sin (Real.pi / 3 * (n : ℝ)) := by
    unfold CriticalLinePhasor.Geometric.cell
    rw [hcast, Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  unfold helix
  rw [hθ]

/-! ### 5. The closed-form arclength bounds the geometric head -/

/-- `S(k) ≥ π r k²`: from the closed form, bounding the root below by `2π r k` and
dropping the (non-negative) `arsinh` term. -/
theorem arclength_ge_pi_r_sq (p r k : ℝ) (hr : 0 < r) (hk : 0 ≤ k) :
    Real.pi * r * k ^ 2 ≤ arclength p r k := by
  rw [arclength_closed_form p r k hr, arclengthClosed]
  have h1 : 2 * Real.pi * r * k ≤ Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [sq_nonneg p, sq_nonneg r]
  have h2 : 0 ≤ (p ^ 2 + r ^ 2) / (4 * Real.pi * r)
      * Real.arsinh (2 * Real.pi * r * k / Real.sqrt (p ^ 2 + r ^ 2)) := by
    apply mul_nonneg (by positivity)
    rw [Real.arsinh_nonneg_iff]
    positivity
  have h3 : k / 2 * (2 * Real.pi * r * k)
      ≤ k / 2 * Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [h2, h3]

/-- **The geometric head grows exponentially in the ordinate.**  At `Δ = π/3`,
`N(y) ≥ (3r/p²) e^{2y}`: the carrier index laid down by the ordinate `y` is exponential in
`y`, against the lane saddle's linear requirement `2y/π`. -/
theorem Nindex_ge_exp (p r y : ℝ) (hp : 0 < p) (hr : 0 < r) :
    3 * r / p ^ 2 * Real.exp (2 * y) ≤ Nindex p r y := by
  rw [Nindex_eq]
  have hk : 0 ≤ kClimb p y := by unfold kClimb; positivity
  have h := arclength_ge_pi_r_sq p r (kClimb p y) hr hk
  have hsq : kClimb p y ^ 2 = Real.exp (2 * y) / p ^ 2 := by
    unfold kClimb
    rw [div_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hpi : 0 < Real.pi := Real.pi_pos
  calc 3 * r / p ^ 2 * Real.exp (2 * y)
      = 3 / Real.pi * (Real.pi * r * (Real.exp (2 * y) / p ^ 2)) := by field_simp
    _ = 3 / Real.pi * (Real.pi * r * kClimb p y ^ 2) := by rw [hsq]
    _ ≤ 3 / Real.pi * arclength p r (kClimb p y) :=
        mul_le_mul_of_nonneg_left h (by positivity)

end CarrierReadout
