import Mathlib

/-!
# Helix definitions — the single source of truth

One file for the parameterized helix geometry. Every per-character helix is a value of
`Helix.Channel`; all the geometric defs read their constants from the channel, so nothing
is hardcoded to χ₃ (π/3) anymore. Other files import this and use `Helix.*`.

## The configurator table (one law, four channels)

```
  angle unit U = π/helixUnit     radial slope = e^mode     character
  π/6   (helixUnit 6)            e³  (mode 3)               trivial χ₀ mod 3  (ζ·(1−3⁻ˢ))
  π/3   (helixUnit 3)            e⁶  (mode 6)               χ₃
  π/2   (helixUnit 2)            e⁸  (mode 8)               mode-8  (χ₄/χ₈)
  π/1   (helixUnit 1)            e¹² (mode 12)              mode-12
```

## The radial law is LINEAR (Archimedean spiral), not exponential

The radius is **linear in the loop number** `k`: `R(k) = e^mode · k`. Each loop **adds**
the constant `e^mode`; it does **not** compound (`×e^mode`). The helix climbs (pitch) and
widens (radius) at constant rates — evenly spaced loops, not an exponential trumpet. With
the area law `n ≈ k²` this gives `R ∝ √n` — the √x / σ=½ frame, emergent from the geometry.
The realized radial drift of a zero is then `n^{σ−½}` (the slope `e^mode` cancels; only the
defect `σ−½` survives), so no-drift ⟺ σ=½ for every channel, independent of its slope.
-/

noncomputable section
open Complex Real

namespace Helix

/-- A helix channel: the per-character configuration. `helixUnit` is the angular spacing
    denominator `d` (the **pitch / main helix-unit variable**), giving angle unit `U = π/d`;
    `mode` is the radial exponent = modulus = conductor, giving radial slope `e^mode`. -/
structure Channel where
  /-- Angular spacing denominator `d`: the angle unit is `U = π / d`. -/
  helixUnit : ℝ
  /-- Radial exponent / modulus / conductor `M`: the linear radial slope is `e^M`. -/
  mode : ℝ

/-- π/6 → e³ → trivial χ₀ mod 3 (the regular ζ zeros). -/
def chTrivial3 : Channel := ⟨6, 3⟩
/-- π/3 → e⁶ → χ₃. -/
def chChi3 : Channel := ⟨3, 6⟩
/-- π/2 → e⁸ → mode-8 (χ₄/χ₈). -/
def chMode8 : Channel := ⟨2, 8⟩
/-- π/1 → e¹² → mode-12. -/
def chMode12 : Channel := ⟨1, 12⟩

/-- The four configured channels. -/
def channels : List Channel := [chTrivial3, chChi3, chMode8, chMode12]

/-- The angular unit `U = π / helixUnit` (the pitch). -/
def angleUnit (C : Channel) : ℝ := Real.pi / C.helixUnit

/-- The all-unit winding character of a channel: `t ↦ exp(i·U·t)` valued in `Circle`. -/
def unitary (C : Channel) : ℝ → Circle := fun t => Circle.exp (angleUnit C * t)

/-- The helix angle of `x > 0` on a channel: `U · log x`. -/
def angle (C : Channel) (x : ℝ) : ℝ := angleUnit C * Real.log x

/-- The channel's primitive winding value `exp(i·U)`. -/
def omega (C : Channel) : ℂ := Complex.exp (↑(angleUnit C) * Complex.I)

/-- **The LINEAR radial law.** Radius at loop `k`: slope `e^mode` times `k`. -/
def loopRadius (C : Channel) (k : ℝ) : ℝ := Real.exp C.mode * k

/-! ### Anchoring facts (the geometry is sound and linear) -/

/-- Every winding value is a unit. -/
theorem unitary_norm (C : Channel) (t : ℝ) : ‖(unitary C t : ℂ)‖ = 1 :=
  Circle.norm_coe _

/-- The winding is a homomorphism `(ℝ,+) → S¹`. -/
theorem unitary_add (C : Channel) (s t : ℝ) :
    unitary C (s + t) = unitary C s * unitary C t := by
  simp only [unitary, mul_add, Circle.exp_add]

/-- **Linear (additive) radial growth.** Each loop adds the same constant `e^mode`. -/
theorem loopRadius_linear (C : Channel) (k : ℝ) :
    loopRadius C (k + 1) - loopRadius C k = Real.exp C.mode := by
  unfold loopRadius; ring

/-- The area law turns the linear-in-`k` radius into `√n` (the geometric-mean / σ=½ frame). -/
theorem loopRadius_eq_sqrt_area (C : Channel) (k : ℝ) (hk : 0 ≤ k) :
    loopRadius C k = Real.exp C.mode * Real.sqrt (k ^ 2) := by
  unfold loopRadius; rw [Real.sqrt_sq hk]

/-- **No radial drift ⟺ on the line — the linear law, slope-independent.** A zero at `σ`
    drifts off the `√n` frame by `n^{σ−½}`; the channel slope `e^mode` does not appear. -/
theorem no_radial_drift_iff_half (n σ : ℝ) (hn : 1 < n) :
    n ^ (σ - 1 / 2) = 1 ↔ σ = 1 / 2 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos hn
  constructor
  · intro h
    have hl : (σ - 1 / 2) * Real.log n = 0 := by
      have hc := congrArg Real.log h
      rwa [Real.log_rpow hn0, Real.log_one] at hc
    rcases mul_eq_zero.mp hl with h1 | h2
    · linarith
    · exact absurd h2 (ne_of_gt hlogpos)
  · intro h; subst h
    rw [show (1 : ℝ) / 2 - 1 / 2 = 0 from by ring, Real.rpow_zero]

/-! ### χ₃ instances (recover the old hardcoded values as `chChi3`) -/

/-- `U = π/3` for the χ₃ channel. -/
theorem angleUnit_chi3 : angleUnit chChi3 = Real.pi / 3 := by
  simp [angleUnit, chChi3]

/-- The χ₃ radial slope is `e⁶`. -/
theorem loopRadius_chi3 (k : ℝ) : loopRadius chChi3 k = Real.exp 6 * k := by
  simp [loopRadius, chChi3]

/-- The trivial-mod-3 (ζ) radial slope is `e³`. -/
theorem loopRadius_trivial3 (k : ℝ) : loopRadius chTrivial3 k = Real.exp 3 * k := by
  simp [loopRadius, chTrivial3]

/-! ### Integer placement: constant arc spacing by the helix unit

Integers are placed at **constant arc spacing** (the helix unit) along the spiral. Because
the radius is linear in the loop number, an outer loop has more circumference and therefore
carries proportionally **more** integers (inner loops few, outer loops many). The cumulative
count through loop `k` is the area law `k²`, so the loop index of integer `n` is `√n` and its
radius is `e^mode · √n` — constant spacing forces the √n frame. Anything that places integers
on the helix must use this rule. -/

/-- Cumulative integers placed through loop `k` under constant arc spacing: the area law `k²`. -/
def integersThroughLoop (k : ℝ) : ℝ := k ^ 2

/-- The loop index of integer `n` (inverse area law): `k = √n`. -/
def loopOfInteger (n : ℝ) : ℝ := Real.sqrt n

/-- **Constant spacing ⇒ more integers on higher loops.** The count added on the next loop is
    `2k+1`, strictly increasing in `k`: inner loops carry few integers, outer loops many. -/
theorem integersOnLoop_increasing (k : ℝ) :
    integersThroughLoop (k + 1) - integersThroughLoop k = 2 * k + 1 := by
  unfold integersThroughLoop; ring

/-- Integer `n` sits at radius `e^mode · √n` — constant arc spacing forces the √n frame. -/
def integerRadius (C : Channel) (n : ℝ) : ℝ := loopRadius C (loopOfInteger n)

/-- The placement radius of integer `n` is `e^mode · √n`. -/
theorem integerRadius_eq (C : Channel) (n : ℝ) :
    integerRadius C n = Real.exp C.mode * Real.sqrt n := rfl

end Helix

end
