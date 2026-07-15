import RequestProject.EpsteinZetaGaussian

/-!
# The general lattice theta: the bank at every point of the upper half plane

Brick (iii-a) of the Eisenstein chain.  For `z ∈ ℍ` the Gram form of the lattice `ℤ·z + ℤ`,
normalized to determinant one, is `gram z (m,n) = |mz+n|²/im z`; the lattice theta
`latticeTheta z t = ∑ exp(-πt·gram z p)` is the carrier bank at `z`, whose heights are the
Gram values.  This file compiles the structural layer: the determinant-one **trace bound**
(`gram_ge` — the two-squares identity `tr·Q − |v|² = (am+bn)² + (bm+cn)²`, so positive
definiteness is exact algebra, not an estimate), summability of the bank at every `z` and
`t > 0` by comparison with the product Gaussian, and the weld to the compiled Gaussian point
(`latticeTheta_I`: at `z = i` the bank is the compiled `thetaSq`).  The transformation law for
general `z` (via the two-variable theta) and the resulting `E(z,s)` continuation are the next
slices.  No RH/GRH.
-/

open Complex UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.EpsteinTheta

/-- The determinant-one Gram form of the lattice `ℤ·z + ℤ`. -/
noncomputable def gram (z : ℍ) (p : ℤ × ℤ) : ℝ :=
  ((p.1 * z.re + p.2) ^ 2 + p.1 ^ 2 * z.im ^ 2) / z.im

/-- **The two-squares identity**: for the determinant-one Gram form, trace times form minus the
Euclidean norm is exactly a sum of two squares. -/
lemma gram_key (r y m n : ℝ) :
    (r ^ 2 + y ^ 2 + 1) * ((m * r + n) ^ 2 + m ^ 2 * y ^ 2) - (m ^ 2 + n ^ 2) * y ^ 2 =
      ((r ^ 2 + y ^ 2) * m + r * n) ^ 2 + (r * m + n) ^ 2 := by
  ring

/-- **The trace bound**: the Gram form dominates the Euclidean form over the trace. -/
lemma gram_ge (z : ℍ) (p : ℤ × ℤ) :
    ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * z.im / (z.re ^ 2 + z.im ^ 2 + 1) ≤ gram z p := by
  set r := z.re
  set y := z.im
  set m := (p.1 : ℝ)
  set n := (p.2 : ℝ)
  have hy : 0 < y := z.im_pos
  have htr : 0 < r ^ 2 + y ^ 2 + 1 := by positivity
  rw [gram, div_le_div_iff₀ htr hy]
  have hkey := gram_key r y m n
  nlinarith [sq_nonneg ((r ^ 2 + y ^ 2) * m + r * n), sq_nonneg (r * m + n)]

/-- The one-dimensional real Gaussian family is summable. -/
lemma summable_gaussian_real {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(π * c * (n : ℝ) ^ 2)) := by
  refine (summable_norm_term hc).congr fun n => ?_
  rw [term_eq_real, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]

set_option maxHeartbeats 1000000 in
/-- **Summability of the bank** at every point and every positive height. -/
lemma summable_latticeTheta_term (z : ℍ) {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ => Real.exp (-(π * t) * gram z p) := by
  set c : ℝ := t * z.im / (z.re ^ 2 + z.im ^ 2 + 1) with hc
  have hy : 0 < z.im := z.im_pos
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have hg : Summable fun n : ℤ => Real.exp (-(π * c) * (n : ℝ) ^ 2) :=
    (summable_gaussian_real hcpos).congr fun n => by congr 1; ring
  have hgn : Summable fun n : ℤ => ‖Real.exp (-(π * c) * (n : ℝ) ^ 2)‖ :=
    hg.congr fun n => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hmaj : Summable fun p : ℤ × ℤ =>
      Real.exp (-(π * c) * (p.1 : ℝ) ^ 2) * Real.exp (-(π * c) * (p.2 : ℝ) ^ 2) :=
    summable_mul_of_summable_norm' hgn hg hgn hg
  apply Summable.of_nonneg_of_le (fun p => (Real.exp_pos _).le) ?_ hmaj
  intro p
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hge := gram_ge z p
  have htr : 0 < z.re ^ 2 + z.im ^ 2 + 1 := by positivity
  have hcg : c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ t * gram z p := by
    rw [hc]
    calc t * z.im / (z.re ^ 2 + z.im ^ 2 + 1) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
        = t * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * z.im / (z.re ^ 2 + z.im ^ 2 + 1)) := by
          ring
      _ ≤ t * gram z p := by
          apply mul_le_mul_of_nonneg_left hge ht.le
  have hmul : π * (c * (((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2)) ≤ π * (t * gram z p) :=
    mul_le_mul_of_nonneg_left hcg Real.pi_pos.le
  ring_nf
  ring_nf at hmul
  linarith

/-- The carrier bank at `z`: the lattice theta. -/
noncomputable def latticeTheta (z : ℍ) (t : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, Real.exp (-(π * t) * gram z p)

/-- **The weld to the compiled point**: at `z = i` the general bank is the compiled Gaussian
theta. -/
theorem latticeTheta_I {t : ℝ} (ht : 0 < t) :
    (latticeTheta ⟨Complex.I, by simp⟩ t : ℂ) = thetaSq t := by
  rw [latticeTheta, Complex.ofReal_tsum, thetaSq_eq_double ht]
  apply tsum_congr
  intro p
  have hexp : (π : ℂ) * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) * ((t : ℂ) * Complex.I)
      = ((-(π * t) * (((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2) : ℝ) : ℂ) := by
    push_cast
    linear_combination (π * (t : ℂ) * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2)) * Complex.I_sq
  rw [hexp, ← Complex.ofReal_exp]
  congr 1
  have hre : (⟨Complex.I, by simp⟩ : ℍ).re = 0 := by
    simp [UpperHalfPlane.re]
  have him : (⟨Complex.I, by simp⟩ : ℍ).im = 1 := by
    simp [UpperHalfPlane.im]
  rw [gram, hre, him]
  push_cast
  ring


end CriticalLinePhasor.EpsteinTheta

#print axioms CriticalLinePhasor.EpsteinTheta.gram_ge
#print axioms CriticalLinePhasor.EpsteinTheta.summable_latticeTheta_term
#print axioms CriticalLinePhasor.EpsteinTheta.latticeTheta_I
