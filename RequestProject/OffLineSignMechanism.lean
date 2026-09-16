import Mathlib

/-!
# The sign mechanism: an off-line quadruple contributes negatively at a root of the test function

In the ring register (RH_LEDGER 722k–722m) a zero `ρ` contributes to the trace through
`G(γ_ρ)`, `γ_ρ = -i(ρ - ½)`.  An ON-LINE conjugate pair at height `γ` contributes `2‖G(γ)‖²`, a planar Gram,
manifestly `≥ 0`.  An OFF-LINE quadruple at `½ ± δ + iγ` contributes instead
`4 Re[G(γ - iδ) · conj (G(γ + iδ))]`, and this file compiles the exact algebra showing that quantity carries a
factor `-δ²` as soon as `G` has a root at `γ`:

    `G = (· - γ) * H`  ⟹  `G(γ - iδ) * conj (G(γ + iδ)) = -δ² * (H(γ - iδ) * conj (H(γ + iδ)))`.

So at a simple root (`H γ ≠ 0`, `H` continuous) the quadruple's term is `≈ -δ²‖G′(γ)‖²` — NEGATIVE — while every
on-line term stays `≥ 0`.  That is the sign mechanism behind "Weil positivity ⟹ RH", isolated as algebra: no
analysis, no explicit formula, no growth estimate.  What the mechanism does NOT give is an exclusion: the identity
`0 ≤ Q(g) = Σ_{on-line}(≥0) + T(g)` tolerates `T(g) < 0` (RH_LEDGER 722u), so a negative term at one zero is
compensated, not contradictory, unless the on-line sum is controlled.
-/

open Complex

namespace CriticalLinePhasor.OffLineSign

/-- **The exact factorisation.**  If `G` vanishes at `γ` with cofactor `H`, the off-line quadruple's pairing
carries the factor `-δ²`. -/
theorem quadruple_pairing (H : ℂ → ℂ) (γ δ : ℝ) :
    (((γ : ℂ) - δ * I - γ) * H ((γ : ℂ) - δ * I)) *
        (starRingEnd ℂ) (((γ : ℂ) + δ * I - γ) * H ((γ : ℂ) + δ * I))
      = (-(δ : ℂ) ^ 2) * (H ((γ : ℂ) - δ * I) * (starRingEnd ℂ) (H ((γ : ℂ) + δ * I))) := by
  have h1 : ((γ : ℂ) - δ * I - γ) = -(δ : ℂ) * I := by ring
  have h2 : ((γ : ℂ) + δ * I - γ) = (δ : ℂ) * I := by ring
  rw [h1, h2, map_mul]
  have h3 : (starRingEnd ℂ) ((δ : ℂ) * I) = -(δ : ℂ) * I := by
    simp [Complex.ext_iff]
  rw [h3]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The sign.**  At a root of `G` where the cofactor pairing has positive real part — in particular at a simple
root, for small `δ`, where it is near `‖G′(γ)‖²` — the quadruple's contribution is strictly negative. -/
theorem quadruple_re_neg (H : ℂ → ℂ) (γ δ : ℝ) (hδ : δ ≠ 0)
    (hH : 0 < (H ((γ : ℂ) - δ * I) * (starRingEnd ℂ) (H ((γ : ℂ) + δ * I))).re) :
    ((((γ : ℂ) - δ * I - γ) * H ((γ : ℂ) - δ * I)) *
        (starRingEnd ℂ) (((γ : ℂ) + δ * I - γ) * H ((γ : ℂ) + δ * I))).re < 0 := by
  rw [quadruple_pairing]
  have hd : (0 : ℝ) < δ ^ 2 := by positivity
  have : ((-(δ : ℂ) ^ 2) * (H ((γ : ℂ) - δ * I) * (starRingEnd ℂ) (H ((γ : ℂ) + δ * I)))).re
      = -(δ ^ 2) * (H ((γ : ℂ) - δ * I) * (starRingEnd ℂ) (H ((γ : ℂ) + δ * I))).re := by
    have hd2 : ((δ : ℂ) ^ 2) = ((δ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hd2, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
  rw [this]
  nlinarith [hH, hd]

/-- **The contrast.**  An on-line conjugate pair contributes `2‖G(γ)‖²`, which is never negative. -/
theorem online_pair_nonneg (G : ℂ → ℂ) (γ : ℝ) : 0 ≤ 2 * ‖G (γ : ℂ)‖ ^ 2 := by positivity

end CriticalLinePhasor.OffLineSign

#print axioms CriticalLinePhasor.OffLineSign.quadruple_pairing
#print axioms CriticalLinePhasor.OffLineSign.quadruple_re_neg
#print axioms CriticalLinePhasor.OffLineSign.online_pair_nonneg
