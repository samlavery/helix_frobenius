import RequestProject.HelixCollapseReality
import RequestProject.UnitMidpoint

/-!
# Hinge kernels: the turning point, and the weld ray

Formal anchors for the hinge (§5 of `FIBER_DYNAMICS.md`): the origin of the double-ended
helix is the midpoint of the conjugation involution, and three structural facts follow.

* `even_deriv_zero` — an even real function has derivative `0` at the origin (no
  differentiability hypothesis: Mathlib's junk-value `deriv` satisfies the identity
  unconditionally, and `collapseWave_differentiableAt` makes it honest here).
* `collapseWave` / `collapseWave_even` / `hinge_turning_point` — the self-dual collapse
  wave `Z(t) = Λ(½+it)` (real by `completedRiemannZeta_critical_line_im_zero`) is EVEN in
  `t` — one functional-equation line — hence the hinge is a **turning point**:
  `Z′(0) = 0`.  This is why the first vanishing sits a quarter cycle (`π/2`), not a half
  cycle, from the hinge: the oscillator starts at an extremum, not a crossing.  Measured:
  first crossing `0.499–0.500·π`, every subsequent cell `0.999–1.000·π`
  (`tmp/oscillator.py`).
* `weld_pins_half_phase` — for complex (non-self-dual) characters the functional equation
  `Λ(s,χ) = ε·Λ(1−s,χ̄)` plus conjugation symmetry gives the anti-involution
  `Λ(½+it,χ) = e^{i·arg ε}·conj Λ(½+it,χ)` at EVERY `t`, so the completed phase is pinned
  to the ray `arg(ε)/2` — `UnitMidpoint.mirror_fixed_iff` with `Δ = arg ε`.  The root
  number is readable from the line phase (and from the hinge's first-cell offset).
  Measured exactly: χ₅ (order 4) `0.0881·π`, χ₇ (order 6) `0.1868·π`, conjugates mirrored,
  Gauss-sum ground truth matched to 4 decimals with zero circular spread
  (`tmp/root_hinge.py`).
* `weld_minus_one_forces_zero` — if the weld phase is `−1` (root number `ε = −1`) a real
  collapse-wave value at the hinge is forced to vanish: the structural kernel behind the
  forced central zero of rank-one elliptic curves (the 37.a experiment).

Mathlib-only + this repo; unconditional; no `sorry`, no `axiom`; no zero-location claims.
-/

open Complex

namespace CriticalLinePhasor.HingeKernel

/-- **An even function has a turning point at the origin**: `deriv f 0 = 0`.
Unconditional (`deriv` is junk-`0` where `f` is not differentiable, and the identity
`deriv (f ∘ neg) = −(deriv f) ∘ neg` holds unconditionally). -/
theorem even_deriv_zero {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have h : deriv (fun x : ℝ => f (-x)) 0 = -deriv f (-(0 : ℝ)) := deriv_comp_neg f 0
  rw [funext heven, neg_zero] at h
  linarith

/-- **Evenness of the completed zeta along the line** — the functional equation
`Λ(1−s) = Λ(s)` read at `s = ½ + it`, where `1 − s = ½ − it`. -/
theorem completed_zeta_line_even (t : ℝ) :
    completedRiemannZeta (1 / 2 + ((-t : ℝ) : ℂ) * Complex.I)
      = completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) := by
  rw [show (1 / 2 + ((-t : ℝ) : ℂ) * Complex.I : ℂ)
        = 1 - (1 / 2 + (t : ℂ) * Complex.I) by push_cast; ring]
  exact completedRiemannZeta_one_sub _

/-- The self-dual collapse wave: the (real) value of the completed zeta on the line.
By `completedRiemannZeta_critical_line_im_zero` the real part IS the whole value. -/
noncomputable def collapseWave (t : ℝ) : ℝ :=
  (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re

/-- The collapse wave is even: the hinge `t = 0` is the mirror of the double helix. -/
theorem collapseWave_even (t : ℝ) : collapseWave (-t) = collapseWave t := by
  unfold collapseWave
  rw [completed_zeta_line_even]

/-- **The hinge is a turning point**: `Z′(0) = 0`.  The oscillator starts at an extremum,
which is why the first vanishing is a quarter cycle (`π/2`) out, not a half cycle. -/
theorem hinge_turning_point : deriv collapseWave 0 = 0 :=
  even_deriv_zero collapseWave_even

/-- The collapse wave is honestly differentiable at the hinge (`½` is neither pole of `Λ`),
so `hinge_turning_point` is a statement about a real derivative, not a junk value. -/
theorem collapseWave_differentiableAt : DifferentiableAt ℝ collapseWave 0 := by
  have hline : DifferentiableAt ℝ (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I) 0 :=
    (differentiableAt_const _).add (Complex.ofRealCLM.differentiableAt.mul_const Complex.I)
  have hpt : ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (1 / 2 : ℂ) := by
    push_cast
    ring
  have hΛ : DifferentiableAt ℂ completedRiemannZeta ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by
    rw [hpt]
    exact differentiableAt_completedZeta (by norm_num) (by norm_num)
  exact Complex.reCLM.differentiableAt.comp 0 ((hΛ.restrictScalars ℝ).comp 0 hline)

/-- Turning point in honest form: `Z` has derivative `0` at the hinge. -/
theorem hinge_turning_point' : HasDerivAt collapseWave 0 0 := by
  have h := collapseWave_differentiableAt.hasDerivAt
  rwa [hinge_turning_point] at h

/-- **The weld pins the line phase to half the root number.**  A value satisfying the weld
anti-involution `z = e^{iΔ}·conj z` — as `Λ(½+it,χ)` does with `Δ = arg ε` at every `t`,
by the functional equation plus conjugation symmetry — lies on the `Δ/2` ray.  UNIT/2 on
the circle: the measurable face is `arg Λ(½+it,χ) ≡ arg(ε)/2 (mod π)`, verified exactly
for χ₅/χ₇ against Gauss sums (`tmp/root_hinge.py`). -/
theorem weld_pins_half_phase (Δ : ℝ) (z : ℂ)
    (hweld : z = Complex.exp (Complex.I * Δ) * (starRingEnd ℂ) z) :
    (z * Complex.exp (-(Complex.I * ((Δ / 2 : ℝ) : ℂ)))).im = 0 :=
  (CriticalLinePhasor.UnitMidpoint.mirror_fixed_iff Δ z).mp hweld.symm

/-! ## Jet parity: the dimension parity at the hinge IS the weld parity

The dimension principle (every vanishing carries a dimension = the dead depth of its jet
tower) meets the weld: an even collapse wave (`ε = +1`) can only die to EVEN depth at the
hinge, an odd one (`ε = −1`) only to ODD depth — the parity conjecture's analytic shadow,
here as unconditional single-function kernels.  Measured: the rank ladder 0–4 shows dead
layers alternating by parity at `10⁻¹³`–`10⁻¹⁶` exactly (`tmp/bsd_rank_ladder.py`,
`tmp/rank4_weld.py`). -/

/-- **An even function's odd jets all die at the origin** (generalizes `even_deriv_zero`
to the whole tower; unconditional). -/
theorem even_odd_jets_dead {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t)
    {k : ℕ} (hk : Odd k) : iteratedDeriv k f 0 = 0 := by
  have h := iteratedDeriv_comp_neg k f 0
  rw [funext heven, neg_zero, hk.neg_one_pow] at h
  have h2 : iteratedDeriv k f 0 = -iteratedDeriv k f 0 := by
    simpa using h
  linarith

/-- **An odd function's even jets all die at the origin** (unconditional). -/
theorem odd_even_jets_dead {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t)
    {k : ℕ} (hk : Even k) : iteratedDeriv k f 0 = 0 := by
  have h := iteratedDeriv_comp_neg k f 0
  rw [funext hodd, neg_zero, hk.neg_one_pow, one_smul] at h
  have h2 : -iteratedDeriv k f 0 = iteratedDeriv k f 0 := by
    simpa using h
  linarith

/-- **Weld `+1` forces even hinge dimension**: if the `k`-th jet of an even wave is alive,
`k` is even. -/
theorem even_live_jet_is_even {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t)
    {k : ℕ} (hne : iteratedDeriv k f 0 ≠ 0) : Even k := by
  by_contra h
  exact hne (even_odd_jets_dead heven (Nat.not_even_iff_odd.mp h))

/-- **Weld `−1` forces odd hinge dimension**: if the `k`-th jet of an odd wave is alive,
`k` is odd. -/
theorem odd_live_jet_is_odd {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t)
    {k : ℕ} (hne : iteratedDeriv k f 0 ≠ 0) : Odd k := by
  by_contra h
  exact hne (odd_even_jets_dead hodd (Nat.not_odd_iff_even.mp h))

/-- The self-dual collapse wave's odd jets are all dead at the hinge (`ζ`: `ε = +1`). -/
theorem collapseWave_odd_jets_dead {k : ℕ} (hk : Odd k) :
    iteratedDeriv k collapseWave 0 = 0 :=
  even_odd_jets_dead collapseWave_even hk

/-- **The hinge is the midpoint between the two endings** (Sam's framing).  The completed
L of a curve is the period integral along the geodesic between the two cusps (`0` and
`i∞` — the endings); in the log-cusp coordinate `u = log y` the Fricke involution
`y ↦ 1/(Ny)` reads `u ↦ −log N − u`, and its fixed point — the hinge, where the helix and
antihelix strands of the split kernel weigh equally — is `u = −(log N)/2`: **UNIT/2 with
the conductor as the unit** (`UnitMidpoint.affine_reflection_fixed_iff` with `c = −log N`).
Measured: the two incomplete-Γ strands of the exact kernel split exactly there, and the
single-strand bank fails precisely at the hinge (`tmp/bsd_rank_ladder.py`). -/
theorem fricke_midpoint_is_half_conductor_unit (N : ℝ) (u : ℝ) :
    -(Real.log N) - u = u ↔ u = -(Real.log N) / 2 :=
  CriticalLinePhasor.UnitMidpoint.affine_reflection_fixed_iff (-(Real.log N)) u

/-- **Weld phase `−1` forces a hinge zero**: a real value fixed by `z ↦ −conj z` is `0`.
The structural kernel of the forced central zero when the root number is `−1`
(rank-one elliptic curves; the 37.a experiment). -/
theorem weld_minus_one_forces_zero (z : ℂ) (hreal : z.im = 0)
    (hweld : z = -((starRingEnd ℂ) z)) : z = 0 := by
  have hconj : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr hreal
  rw [hconj] at hweld
  have h2 : (2 : ℂ) * z = 0 := by linear_combination hweld
  simpa using h2

end CriticalLinePhasor.HingeKernel
