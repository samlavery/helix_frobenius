import Mathlib

/-!
# The K-sweep completion theorem: one nonzero Weil component suffices

The correspondent's completion theorem (2026-07-30), formalized in its
exact abstract shape.  Setting: the middle Hodge space decomposes as
`L ⊕ W` with `L` algebraic (Lefschetz), `W` a one-dimensional `K`-line
(`K = ℚ(ζ₃)`), and `K` acting by algebraic correspondences.  Then ONE
algebraic cycle `F` with nonzero `W`-component makes every class in
`L ⊕ W` algebraic:

* subtract the Lefschetz part: `w₀ = cl F − cl Z_F` is algebraic and
  purely `W`;
* the `K`-action (algebraic!) sweeps the `K`-line from `w₀`;
* the sum of algebraic subspaces is algebraic.

**What this changes for the explicit Prym sixfold `B`:** hypothesis (3)
is FREE — `K` acts through the `ζ₃`-multiplication, an automorphism of
`B`, whose graph is an algebraic correspondence by construction.  And
**no algebraicity of the projector `π_W` is required anywhere**: the
projector's only role is to certify `π_W(cl F) ≠ 0` — a measurement —
while the algebra is done by subtraction and the sweep.  The
motivated-presentation / standard-conjecture pricing of the collective
wall is thereby BYPASSED for `B`: the completion implication

    m(F) ≠ 0  ⟹  W algebraic  ⟹  Hdg³(B) algebraic

is closed, modulo the two named inputs it consumes: the decomposition
`Hdg³(B) = L ⊕ W` with `L` algebraic (the Mumford–Tate computation,
conventional), and the discovery node `m(C1) ≠ 0` itself.  Scope: does
not assume or prove the Hodge conjecture; this is the downstream
implication, exact and unconditional in its hypotheses.
-/

namespace CriticalLinePhasor.KSweep

variable {H : Type*} [AddCommGroup H] [Module ℚ H]
variable {K : Type*} [Field K] [Algebra ℚ K] [Module K H]
variable [IsScalarTower ℚ K H]

/-- **The K-sweep completion theorem.**  Hypotheses: the algebraic
classes form a ℚ-subspace `Alg` stable under the (algebraic) `K`-action;
`L ≤ Alg`; `W` is `K`-stable and `K`-spanned by any nonzero element
(dim_K W = 1, phrased operationally); one algebraic `F = ℓ + w₀` with
`w₀ ∈ W` nonzero.  Conclusion: every `α = ℓ' + w'` with `ℓ' ∈ L`,
`w' ∈ W` is algebraic. -/
theorem completion
    (Alg : Submodule ℚ H)
    (algSMul : ∀ (a : K) (x : H), x ∈ Alg → a • x ∈ Alg)
    (L W : Submodule ℚ H)
    (hL : L ≤ Alg)
    (hdim : ∀ w₀ w : H, w₀ ∈ W → w₀ ≠ 0 → w ∈ W → ∃ a : K, w = a • w₀)
    (F ℓ w₀ : H) (hF : F ∈ Alg) (hsplit : F = ℓ + w₀)
    (hℓ : ℓ ∈ L) (hw₀ : w₀ ∈ W) (hw₀ne : w₀ ≠ 0) :
    ∀ α ℓ' w' : H, α = ℓ' + w' → ℓ' ∈ L → w' ∈ W → α ∈ Alg := by
  -- the pure Weil class, by subtraction of the Lefschetz component
  have hw₀alg : w₀ ∈ Alg := by
    have : w₀ = F - ℓ := by rw [hsplit, add_sub_cancel_left]
    rw [this]
    exact Submodule.sub_mem Alg hF (hL hℓ)
  -- the sweep: every element of W is a K-multiple of w₀, hence algebraic
  intro α ℓ' w' hα hℓ' hw'
  obtain ⟨a, ha⟩ := hdim w₀ w' hw₀ hw₀ne hw'
  have hw'alg : w' ∈ Alg := by
    rw [ha]
    exact algSMul a w₀ hw₀alg
  rw [hα]
  exact Submodule.add_mem Alg (hL hℓ') hw'alg

/-- The boxed completion implication, packaged: under the standing
hypotheses, nonvanishing of the `W`-component of ONE algebraic cycle
class makes the whole decomposed space algebraic. -/
theorem completion_implication
    (Alg : Submodule ℚ H)
    (algSMul : ∀ (a : K) (x : H), x ∈ Alg → a • x ∈ Alg)
    (L W : Submodule ℚ H)
    (hL : L ≤ Alg)
    (hdim : ∀ w₀ w : H, w₀ ∈ W → w₀ ≠ 0 → w ∈ W → ∃ a : K, w = a • w₀)
    (F ℓ w₀ : H) (hF : F ∈ Alg) (hsplit : F = ℓ + w₀)
    (hℓ : ℓ ∈ L) (hw₀ : w₀ ∈ W) (hw₀ne : w₀ ≠ 0) :
    W ≤ Alg := by
  intro w' hw'
  have := completion (K := K) Alg algSMul L W hL hdim F ℓ w₀ hF hsplit
    hℓ hw₀ hw₀ne w' 0 w' (zero_add w').symm (Submodule.zero_mem L) hw'
  simpa using this

end CriticalLinePhasor.KSweep

#print axioms CriticalLinePhasor.KSweep.completion
#print axioms CriticalLinePhasor.KSweep.completion_implication
