import Mathlib

/-!
# C3 batch 5, block A4 — two exact refutations, and the convexity mechanism

## What is refuted

`tmp/att545_c3b5_families.py` proposed three decomposition families.  Two of them are
"positive semidefinite kernel ⟹ the leaf closes for **every** `x` at once", and both are
refuted here by exact algebra rather than by an eigenvalue computation.

* **Family 3** — the quadratic ramp `U_x(s) = (1/8)∫∫(α+β)_+²ψ(α)\overline{ψ(β)}`
  would be nonnegative for every `ψ` if `K(α,β) = (α+β)_+²` were PSD.  It is not:
  `K(0,0) = 0` while `K(0,1) = 1`, so the `2×2` minor is `−1`.  `rampKernel_not_psd`
  exhibits an explicit two-atom witness with quadratic form `−4`.

* **Family 1** — `C(u,x) = 8π²e^{5u}·⟨c, G c⟩` with `c_n = n²n^{ix}` and
  `G_{nm} = F(2πnm e^{2u}, x)`.  `G` is a multiplicative Hankel kernel `f(log n + log m)`,
  PSD at all node sets iff `f` is exponentially convex (Widder).  `F` decays like `e^{−A}`,
  i.e. `f` decays *doubly* exponentially in `log A`, and `exp_exp_hankel_minor_neg` shows
  that alone kills the `2×2` minor: the obstruction is the decay rate, not any arithmetic.

## What is kept

`even_convex_monotone` is the mechanism the whole leaf runs on.  Writing
`Λ(μ) = ∫_ℝ e^{μu}C(u,x)du = |ξ((μ+1)/2 + ix)|²`, the functional equation makes `Λ` even,
and *if* `C ≥ 0` then `Λ` is log-convex by Hölder, hence `log Λ` is even and convex, hence
nondecreasing on `[0,∞)` — which is the target.  So `C ≥ 0` on all of `ℝ` would give RH.
The lemma is compiled here because it is the only step of that chain that is not
classical bookkeeping, and because it makes precise what the compact window `[0,u₀]`
has to survive.

SCOPE: no `Ξ`, no zeros, no RH — finite algebra and one convexity argument.
-/

open Real Set

noncomputable section

namespace C3B5.A4

/-! ### 1. Family 3: the quadratic ramp kernel is not positive semidefinite -/

/-- The ramp kernel `(α+β)_+²`, as a function of the Hankel variable `t = α+β`. -/
def rampKernel (t : ℝ) : ℝ := if 0 < t then t ^ 2 else 0

/-- **`(α+β)_+²` is NOT a positive semidefinite kernel.**  Two atoms at `0` and `1` with
weights `−4` and `1` give quadratic form `−4`.  The mechanism is that the kernel vanishes
at a node (`K(0,0) = 0`) while an off-diagonal entry does not — no arithmetic involved. -/
theorem rampKernel_not_psd :
    (-4 : ℝ) * (-4) * rampKernel (0 + 0) + (-4 : ℝ) * 1 * rampKernel (0 + 1)
      + (1 : ℝ) * (-4) * rampKernel (1 + 0) + (1 : ℝ) * 1 * rampKernel (1 + 1)
      = -4 := by
  norm_num [rampKernel]

theorem rampKernel_not_psd' :
    ∃ c₀ c₁ t₀ t₁ : ℝ,
      c₀ * c₀ * rampKernel (t₀ + t₀) + c₀ * c₁ * rampKernel (t₀ + t₁)
        + c₁ * c₀ * rampKernel (t₁ + t₀) + c₁ * c₁ * rampKernel (t₁ + t₁) < 0 :=
  ⟨-4, 1, 0, 1, by rw [rampKernel_not_psd]; norm_num⟩

/-- The diagonal vanishing that causes it: `K(0,0) = 0` but `K(0,1) = 1`. -/
theorem rampKernel_diag_zero : rampKernel (0 + 0) = 0 ∧ rampKernel (0 + 1) = 1 := by
  constructor <;> norm_num [rampKernel]

/-! ### 2. Family 1: the Hankel/exponential-convexity obstruction -/

/-- **The `2×2` Hankel obstruction.**  If `f 0 > 0` and `f 0 · f(2ξ) < f(ξ)²` then the
Gram matrix of the Hankel kernel `f(·+·)` at nodes `{0, ξ}` is not PSD, with the explicit
witness `c = (−f ξ, f 0)`. -/
theorem hankel_not_psd {f : ℝ → ℝ} {ξ : ℝ} (hf0 : 0 < f 0)
    (h : f 0 * f (2 * ξ) < f ξ ^ 2) :
    (-f ξ) * (-f ξ) * f (0 + 0) + (-f ξ) * (f 0) * f (0 + ξ)
      + (f 0) * (-f ξ) * f (ξ + 0) + (f 0) * (f 0) * f (ξ + ξ) < 0 := by
  rw [show (0 : ℝ) + 0 = 0 by ring, show (0 : ℝ) + ξ = ξ by ring,
    show ξ + (0 : ℝ) = ξ by ring, show ξ + ξ = 2 * ξ by ring]
  have hkey : 0 < f 0 * (f ξ ^ 2 - f 0 * f (2 * ξ)) :=
    mul_pos hf0 (sub_pos.mpr h)
  nlinarith [hkey]

/-- **Doubly-exponential decay alone kills exponential convexity.**  For
`f t = exp(−exp t)` — the decay profile of `F(A,x) ≍ A²e^{−A}` read in `t = log A` —
the `2×2` minor `f 0·f(2ξ) − f(ξ)²` is strictly negative for every `ξ ≠ 0`.
Hence no Hankel kernel with this decay is PSD, whatever its arithmetic content. -/
theorem exp_exp_hankel_minor_neg {ξ : ℝ} (hξ : ξ ≠ 0) :
    Real.exp (-Real.exp 0) * Real.exp (-Real.exp (2 * ξ))
      < Real.exp (-Real.exp ξ) ^ 2 := by
  have hpos : (0 : ℝ) < (Real.exp ξ - 1) ^ 2 := by
    have hne : Real.exp ξ - 1 ≠ 0 := by
      intro hc
      apply hξ
      have h1 : Real.exp ξ = Real.exp 0 := by rw [Real.exp_zero]; linarith
      exact Real.exp_eq_exp.mp h1
    positivity
  have hsq : Real.exp (2 * ξ) = Real.exp ξ * Real.exp ξ := by
    rw [← Real.exp_add]; congr 1; ring
  have hlt : -(1 : ℝ) - Real.exp (2 * ξ) < -(2 * Real.exp ξ) := by
    rw [hsq]; nlinarith [hpos]
  calc Real.exp (-Real.exp 0) * Real.exp (-Real.exp (2 * ξ))
      = Real.exp (-1 - Real.exp (2 * ξ)) := by
        rw [← Real.exp_add, Real.exp_zero]; congr 1
    _ < Real.exp (-(2 * Real.exp ξ)) := Real.exp_lt_exp.mpr hlt
    _ = Real.exp (-Real.exp ξ) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; ring

/-! ### 3. The mechanism: even + convex ⟹ nondecreasing on `[0,∞)` -/

/-- **An even convex function is nondecreasing on `[0,∞)`.**  Applied to `log Λ` with
`Λ(μ) = |ξ((μ+1)/2 + ix)|²`: evenness is the functional equation, convexity of `log Λ`
would follow from `C ≥ 0` by Hölder, and the conclusion is the target inequality
`∂_y|Ξ(x+iy)|² ≥ 0`. -/
theorem even_convex_monotone {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t)
    (hconv : ConvexOn ℝ Set.univ f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    f a ≤ f b := by
  rcases eq_or_lt_of_le (le_trans ha hab) with hb | hb
  · have ha0 : a = 0 := le_antisymm (by linarith [hb]) ha
    have hb0 : b = 0 := hb.symm
    rw [ha0, hb0]
  · set l : ℝ := (b - a) / (2 * b) with hl
    set m : ℝ := (b + a) / (2 * b) with hm
    have hb2 : (0 : ℝ) < 2 * b := by linarith
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hb2.le
    have hm0 : 0 ≤ m := div_nonneg (by linarith) hb2.le
    have hlm : l + m = 1 := by rw [hl, hm]; field_simp; ring
    have harg : l • (-b) + m • b = a := by
      simp only [smul_eq_mul, hl, hm]
      field_simp
      ring
    have hineq := hconv.2 (Set.mem_univ (-b)) (Set.mem_univ b) hl0 hm0 hlm
    rw [harg] at hineq
    simp only [smul_eq_mul, heven b] at hineq
    have : l * f b + m * f b = f b := by
      rw [← add_mul, hlm, one_mul]
    linarith [hineq, this]

/-- The step from monotonicity to zero-freeness: a nonnegative function that is
nondecreasing on `[0,∞)` and vanishes at some `y₀ > 0` already vanishes at `0`.
This is why "‖Ξ(x+iy)‖ nondecreasing in `y`" excludes off-line zeros. -/
theorem vanish_pull_back {g : ℝ → ℝ} (hnn : ∀ t, 0 ≤ g t)
    (hmono : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → g s ≤ g t)
    {y₀ : ℝ} (hy : 0 < y₀) (hz : g y₀ = 0) : g 0 = 0 := by
  have h1 : g 0 ≤ g y₀ := hmono le_rfl hy.le
  rw [hz] at h1
  exact le_antisymm h1 (hnn 0)

end C3B5.A4

section AxiomAudit
#print axioms C3B5.A4.rampKernel_not_psd
#print axioms C3B5.A4.rampKernel_not_psd'
#print axioms C3B5.A4.rampKernel_diag_zero
#print axioms C3B5.A4.hankel_not_psd
#print axioms C3B5.A4.exp_exp_hankel_minor_neg
#print axioms C3B5.A4.even_convex_monotone
#print axioms C3B5.A4.vanish_pull_back
end AxiomAudit
