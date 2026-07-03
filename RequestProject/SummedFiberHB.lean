import RequestProject.ChiralityHB
import RequestProject.DeBranges

/-!
# The summed fiber and Hermite–Biehler: partial kernels, wall located

The multiplicative side is closed (`ChiralityHB.carrier_zeros_real`).  The additive side
— the summed fiber, where the L-vanishings live — is the wall de Branges worked at for
decades.  Per the discipline: we do not claim the wall; we prove the partial kernels
that name exactly where it stands.  `Estar E z = conj (E (conj z))` throughout
(`DeBranges.Estar`).

* `estar_add` / `estar_sum` — the star is additive: the antihelix of a sum is the sum of
  the antihelices (the two strands never mix under superposition).
* `product_stays_boundary` — products of boundary (A-type) functions stay on the
  boundary: `‖E*‖ = ‖E‖` is multiplicative.  With `carrier_zeros_real` this closes the
  multiplicative sector completely.
* `common_weld_sum_stays_boundary` — **the coherence kernel**: if all summands share ONE
  weld phase (`Eⱼ* = u·Eⱼ`, common unimodular `u`), the sum stays exactly on the
  boundary: `‖(ΣE)*‖ = ‖ΣE‖`.  Phase alignment across terms is sufficient — this is the
  carrier's winding coherence as a hypothesis.
* `aligned_strict_sum_HB` — **the strict kernel**: if at a point the summands are
  phase-aligned with margin (some direction `θ` sees every term's helix strand beat its
  own antihelix strand: `‖Eⱼ*(z)‖ < Re(e^{iθ}·Eⱼ(z))`), then the SUM satisfies the
  strict HB inequality there.  Alignment defeats the triangle inequality — without it,
  strict summand-wise HB does NOT suffice (the big sides can cancel while the small
  sides conspire); THAT failure mode is precisely the open wall.

Consequence recorded honestly: the completion-membership question (WeilDuality
`conj_axis_is_membership_boundary`) and the summed-fiber HB question are ONE wall — the
membership dichotomy already has the exclusion shape (off-axis ⇒ inside the Hilbert
space ⇒ excluded by `von_neumann_reality`/`hb_no_zero_upper`; on-axis ⇒ boundary ⇒
permitted), and what remains in both formulations is the same coherence statement:
the fiber's winding is one-handed enough to align the strands.  No `sorry`; standard
axioms.
-/

open Complex Finset

namespace CriticalLinePhasor.SummedFiberHB

/-- The star (antihelix) of a function: `E*(z) = conj (E (conj z))` (as in
`DeBranges.Estar`, restated here to keep this file self-contained). -/
noncomputable def star' (E : ℂ → ℂ) (z : ℂ) : ℂ := (starRingEnd ℂ) (E ((starRingEnd ℂ) z))

/-- The star is additive: the antihelix of a sum is the sum of the antihelices. -/
theorem estar_add (E F : ℂ → ℂ) (z : ℂ) :
    star' (E + F) z = star' E z + star' F z := by
  unfold star'
  simp

/-- The star of a finite sum. -/
theorem estar_sum {ι : Type*} (s : Finset ι) (E : ι → ℂ → ℂ) (z : ℂ) :
    star' (fun w => ∑ j ∈ s, E j w) z = ∑ j ∈ s, star' (E j) z := by
  unfold star'
  simp

/-- **Products of boundary functions stay on the boundary**: `‖E*‖ = ‖E‖` is
multiplicative, so the whole multiplicative carrier is A-type as soon as its factors are
(the clocks are: `symClock_selfdual_modulus`). -/
theorem product_stays_boundary {E F : ℂ → ℂ} {z : ℂ}
    (hE : ‖star' E z‖ = ‖E z‖) (hF : ‖star' F z‖ = ‖F z‖) :
    ‖star' (E * F) z‖ = ‖(E * F) z‖ := by
  unfold star' at *
  simp only [Pi.mul_apply, map_mul, norm_mul]
  rw [hE, hF]

/-- **The coherence kernel**: if every summand carries the SAME weld phase
(`Eⱼ* = u·Eⱼ` pointwise at `z`, `‖u‖ = 1`), the sum stays exactly on the boundary.
Winding coherence — one weld phase across the bank — is sufficient for the summed fiber
to be A-type. -/
theorem common_weld_sum_stays_boundary {ι : Type*} (s : Finset ι) (E : ι → ℂ → ℂ)
    {u : ℂ} (hu : ‖u‖ = 1) (z : ℂ) (h : ∀ j ∈ s, star' (E j) z = u * E j z) :
    ‖star' (fun w => ∑ j ∈ s, E j w) z‖ = ‖∑ j ∈ s, E j z‖ := by
  rw [estar_sum, Finset.sum_congr rfl h, ← Finset.mul_sum, norm_mul, hu, one_mul]

/-- **The strict kernel — alignment defeats the triangle inequality**: if at `z` some
direction `θ` sees every summand's helix strand beat its own antihelix strand
(`‖Eⱼ*(z)‖ < Re(e^{iθ}·Eⱼ(z))`), then the sum satisfies the strict Hermite–Biehler
inequality at `z`.  The hypothesis is the carrier's winding coherence; without it the
big sides can cancel while the small sides conspire — that failure mode is the open
wall, now named. -/
theorem aligned_strict_sum_HB {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (E : ι → ℂ → ℂ) (z : ℂ) (θ : ℝ)
    (h : ∀ j ∈ s, ‖star' (E j) z‖ < (Complex.exp (Complex.I * θ) * E j z).re) :
    ‖star' (fun w => ∑ j ∈ s, E j w) z‖ < ‖∑ j ∈ s, E j z‖ := by
  have step1 : ‖star' (fun w => ∑ j ∈ s, E j w) z‖ ≤ ∑ j ∈ s, ‖star' (E j) z‖ := by
    rw [estar_sum]
    exact norm_sum_le _ _
  have step2 : ∑ j ∈ s, ‖star' (E j) z‖ < ∑ j ∈ s, (Complex.exp (Complex.I * θ) * E j z).re :=
    Finset.sum_lt_sum_of_nonempty hs h
  have step3 : ∑ j ∈ s, (Complex.exp (Complex.I * θ) * E j z).re
      = (Complex.exp (Complex.I * θ) * ∑ j ∈ s, E j z).re := by
    rw [Finset.mul_sum, Complex.re_sum]
  have step4 : (Complex.exp (Complex.I * θ) * ∑ j ∈ s, E j z).re
      ≤ ‖Complex.exp (Complex.I * θ) * ∑ j ∈ s, E j z‖ := Complex.re_le_norm _
  have step5 : ‖Complex.exp (Complex.I * θ) * ∑ j ∈ s, E j z‖ = ‖∑ j ∈ s, E j z‖ := by
    rw [norm_mul, Complex.norm_exp]
    have : (Complex.I * (θ : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [this, Real.exp_zero, one_mul]
  calc ‖star' (fun w => ∑ j ∈ s, E j w) z‖
      ≤ ∑ j ∈ s, ‖star' (E j) z‖ := step1
    _ < ∑ j ∈ s, (Complex.exp (Complex.I * θ) * E j z).re := step2
    _ = (Complex.exp (Complex.I * θ) * ∑ j ∈ s, E j z).re := step3
    _ ≤ ‖Complex.exp (Complex.I * θ) * ∑ j ∈ s, E j z‖ := step4
    _ = ‖∑ j ∈ s, E j z‖ := step5

/-- `star'` is `DeBranges.Estar` (same formula). -/
theorem star'_eq_estar (E : ℂ → ℂ) (z : ℂ) :
    star' E z = CriticalLinePhasor.DeBranges.Estar E z := rfl

/-- **The conditional master chain: winding coherence ⇒ the conjugation axis.**  If at
every point of the upper half-plane the bank is phase-aligned with margin — each term's
helix strand beats its own antihelix strand in some common direction — then the summed
fiber is Hermite–Biehler, and **every zero of its collapse wave `A = (E + E*)/2` is
real**: 3D-RH for the summed fiber, conditional on exactly ONE geometric hypothesis, the
carrier's winding coherence.  This is the whole remaining wall, welded into a single
implication: `hcoh` is where de Branges spent decades, and everything after it is
proven (`aligned_strict_sum_HB` + `DeBranges.Acomp_zero_im_eq_zero`).  The measurable
face of `hcoh`: the per-term alignment margin across the bank at upper-half-plane
sample points. -/
theorem coherence_implies_conj_axis {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (E : ι → ℂ → ℂ)
    (hcoh : ∀ z : ℂ, 0 < z.im → ∃ θ : ℝ, ∀ j ∈ s,
      ‖star' (E j) z‖ < (Complex.exp (Complex.I * θ) * E j z).re) :
    ∀ z : ℂ, CriticalLinePhasor.DeBranges.Acomp (fun w => ∑ j ∈ s, E j w) z = 0 →
      z.im = 0 := by
  have hHB : CriticalLinePhasor.DeBranges.IsHB (fun w => ∑ j ∈ s, E j w) := by
    intro z hz
    obtain ⟨θ, hθ⟩ := hcoh z hz
    exact aligned_strict_sum_HB s hs E z θ hθ
  intro z hz
  exact CriticalLinePhasor.DeBranges.Acomp_zero_im_eq_zero hHB hz

/-! ## No conspiracy on the double helix: the cup norm has no null space

Owner's principle, after the Part II obstruction (the re-welded scalar companion failed
strict HB in bands via phase cancellation): the "conspiracy" is a property of the 1D
READOUT, not the helix.  The rank-one readout `ℓ(v) = Σ vₙ` has an enormous null space
— that is where interference lives and where the bands were found.  The 3D object's own
metric — the cup norm, proven NONDEGENERATE (`ChiralCup.cup_nullspace_safe`) — admits no
interference at all: per-term strand dominance transfers to the summed cup norm
immediately, because sums of squares carry no phases.  There is no kernel null space
for a conspiracy to hide in.

Consequence for the wall: the scalar Hermite–Biehler route asks whether the
cup-dominant strand's SHADOW under `ℓ` can dip below the other strand's shadow — a
question about the readout's kernel, i.e. a 1D-chart question, as doctrine requires.
The 3D-native reformulation this suggests: the TWO-STRAND (ℂ²-valued) structure
function, where the star swaps strands and scalar HB is replaced by matrix
J-contractivity (de Branges–Rovnyak / Potapov, J = diag(1,−1)) — the det-1 strand
pairing is then built into the object rather than projected away.  Proposed as the next
formalization target; not claimed. -/

/-- **No conspiracy in the cup norm**: strict per-term dominance transfers to the summed
cup norm — sums of squares admit no interference, so no phase configuration can flip
the comparison.  (Contrast: the scalar readout `‖Σ·‖` CAN flip it — measured, Part II.) -/
theorem cup_dominance_no_conspiracy {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f g : ι → ℂ) (h : ∀ j ∈ s, ‖f j‖ < ‖g j‖) :
    ∑ j ∈ s, ‖f j‖ ^ 2 < ∑ j ∈ s, ‖g j‖ ^ 2 := by
  refine Finset.sum_lt_sum_of_nonempty hs fun j hj => ?_
  have hj2 := h j hj
  have h0 : (0 : ℝ) ≤ ‖f j‖ := norm_nonneg _
  nlinarith [norm_nonneg (g j)]

end CriticalLinePhasor.SummedFiberHB
