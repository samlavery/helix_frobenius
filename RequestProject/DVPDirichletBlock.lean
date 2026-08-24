import RequestProject.DVPRationalEnclosure
import RequestProject.DVPTruncatedZeta

/-!
# E6: the Dirichlet-block evaluator

Per-term enclosures for `n^{−s}`: the cpow split into `n^{−σ}·cos/sin(t·log n)`,
the kernel-arithmetic `n^{−1/2}` enclosure, and the σ = ½ term enclosure that
plugs the E4/E5 certificates into the truncated representation
(`truncated_zeta_pos_re`).
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **E6a: the cpow split.**  For `n ≥ 1` the term `n^{−(σ+it)}` has real
part `n^{−σ}·cos(t·log n)` and imaginary part `−n^{−σ}·sin(t·log n)`. -/
theorem nat_cpow_neg_split {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    (((n : ℝ) : ℂ) ^ (-(↑σ + ↑t * I))).re
        = (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)
      ∧ (((n : ℝ) : ℂ) ^ (-(↑σ + ↑t * I))).im
        = -((n : ℝ) ^ (-σ) * Real.sin (t * Real.log n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hn0.ne'
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log ((n : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) :=
    (Complex.ofReal_log hn0.le).symm
  rw [hlog]
  have hzre : (((Real.log n : ℝ) : ℂ) * -(↑σ + ↑t * I)).re
      = -(σ * Real.log n) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hzim : (((Real.log n : ℝ) : ℂ) * -(↑σ + ↑t * I)).im
      = -(t * Real.log n) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hrpow : Real.exp (-(σ * Real.log n)) = (n : ℝ) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    ring
  constructor
  · rw [Complex.exp_re, hzre, hzim, hrpow, Real.cos_neg]
  · rw [Complex.exp_im, hzre, hzim, hrpow, Real.sin_neg]
    ring

/-- **E6b: the `n^{−1/2}` enclosure — pure kernel arithmetic.**
`a ≤ n^{−1/2} ≤ b` from the rational comparisons `a²n ≤ 1 ≤ b²n`. -/
theorem inv_sqrt_enclosure {n : ℕ} {a b : ℚ} (hn : 1 ≤ n)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : (a : ℚ) ^ 2 * n ≤ 1) (hb : 1 ≤ (b : ℚ) ^ 2 * n) :
    (a : ℝ) ≤ (n : ℝ) ^ (-(1/2 : ℝ)) ∧ (n : ℝ) ^ (-(1/2 : ℝ)) ≤ (b : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := (n : ℝ) ^ (-(1/2 : ℝ)) with hxdef
  have hpos : (0 : ℝ) < x := Real.rpow_pos_of_pos hn0 _
  have hsq : x ^ 2 = (n : ℝ)⁻¹ := by
    rw [hxdef, ← Real.rpow_natCast ((n : ℝ) ^ (-(1/2 : ℝ))) 2,
      ← Real.rpow_mul hn0.le]
    norm_num [Real.rpow_neg_one]
  have ha0' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
  have haR : (a : ℝ) ^ 2 * n ≤ 1 := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ (b : ℝ) ^ 2 * n := by exact_mod_cast hb
  constructor
  · have h2 : (a : ℝ) ^ 2 ≤ x ^ 2 := by
      rw [hsq, inv_eq_one_div, le_div_iff₀ hn0]
      linarith
    by_contra hc
    push_neg at hc
    have : x ^ 2 < (a : ℝ) ^ 2 := by nlinarith [hpos]
    linarith
  · have hb0' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb0
    have h2 : x ^ 2 ≤ (b : ℝ) ^ 2 := by
      rw [hsq, inv_eq_one_div, div_le_iff₀ hn0]
      linarith
    by_contra hc
    push_neg at hc
    have : (b : ℝ) ^ 2 < x ^ 2 := by nlinarith [hb0']
    linarith

/-- **E6c: the product enclosure.**  An interval factor `X ∈ [a,b]` (as in
E6b) times a certified bounded factor `Y` (as in E4) encloses the product:
`|XY − bC| ≤ (b−a) + b·ε`.  This is the per-term pipeline for
`n^{−1/2}·cos/sin(t·log n)`. -/
theorem product_enclosure {X Y : ℝ} {a b C ε : ℚ}
    (ha0 : (0:ℝ) ≤ (a : ℝ)) (hXa : (a : ℝ) ≤ X) (hXb : X ≤ (b : ℝ))
    (hY : |Y| ≤ 1) (hYC : |Y - (C : ℝ)| ≤ (ε : ℝ)) :
    |X * Y - ((b * C : ℚ) : ℝ)| ≤ (((b - a) + b * ε : ℚ) : ℝ) := by
  have hb0 : (0:ℝ) ≤ (b : ℝ) := le_trans (le_trans ha0 hXa) hXb
  calc |X * Y - ((b * C : ℚ) : ℝ)|
      = |(X - (b : ℝ)) * Y + (b : ℝ) * (Y - (C : ℝ))| := by
        push_cast
        ring_nf
    _ ≤ |(X - (b : ℝ)) * Y| + |(b : ℝ) * (Y - (C : ℝ))| := abs_add_le _ _
    _ = |X - (b : ℝ)| * |Y| + |(b : ℝ)| * |Y - (C : ℝ)| := by
        rw [abs_mul, abs_mul]
    _ ≤ ((b : ℝ) - a) * 1 + (b : ℝ) * ε := by
        have h1 : |X - (b : ℝ)| ≤ (b : ℝ) - a := by
          rw [abs_le]
          constructor <;> linarith
        have h2 : |(b : ℝ)| = (b : ℝ) := abs_of_nonneg hb0
        rw [h2]
        exact add_le_add
          (mul_le_mul h1 hY (abs_nonneg _) (by linarith))
          (mul_le_mul_of_nonneg_left hYC hb0)
    _ = (((b - a) + b * ε : ℚ) : ℝ) := by
        push_cast
        ring

/-- One real product against certified factors: `|AU − au| ≤ (Ma+1)εu + Mu·εa`. -/
theorem mul_diff_bound {A U : ℝ} {a u εa εu Ma Mu : ℚ}
    (hA : |A - (a : ℝ)| ≤ (εa : ℝ)) (hU : |U - (u : ℝ)| ≤ (εu : ℝ))
    (hMa : |a| ≤ Ma) (hMu : |u| ≤ Mu) (hεa : εa ≤ 1) :
    |A * U - ((a * u : ℚ) : ℝ)| ≤ (((Ma + 1) * εu + Mu * εa : ℚ) : ℝ) := by
  have hMa' : |(a : ℝ)| ≤ (Ma : ℝ) := by exact_mod_cast hMa
  have hMu' : |(u : ℝ)| ≤ (Mu : ℝ) := by exact_mod_cast hMu
  have hεa' : (εa : ℝ) ≤ 1 := by exact_mod_cast hεa
  have hεu0 : (0:ℝ) ≤ (εu : ℝ) := le_trans (abs_nonneg _) hU
  have hεa0 : (0:ℝ) ≤ (εa : ℝ) := le_trans (abs_nonneg _) hA
  have hAbound : |A| ≤ (Ma : ℝ) + 1 := by
    calc |A| = |(A - (a : ℝ)) + (a : ℝ)| := by ring_nf
      _ ≤ |A - (a : ℝ)| + |(a : ℝ)| := abs_add_le _ _
      _ ≤ (Ma : ℝ) + 1 := by linarith
  have hkey : A * U - ((a * u : ℚ) : ℝ)
      = A * (U - (u : ℝ)) + (u : ℝ) * (A - (a : ℝ)) := by
    push_cast
    ring
  rw [hkey]
  calc |A * (U - (u : ℝ)) + (u : ℝ) * (A - (a : ℝ))|
      ≤ |A * (U - (u : ℝ))| + |(u : ℝ) * (A - (a : ℝ))| := abs_add_le _ _
    _ = |A| * |U - (u : ℝ)| + |(u : ℝ)| * |A - (a : ℝ)| := by
        rw [abs_mul, abs_mul]
    _ ≤ ((Ma : ℝ) + 1) * (εu : ℝ) + (Mu : ℝ) * (εa : ℝ) := by
        exact add_le_add
          (mul_le_mul hAbound hU (abs_nonneg _) (by linarith [hMa'.trans' (abs_nonneg (a:ℝ))]))
          (mul_le_mul hMu' hA (abs_nonneg _) (le_trans (abs_nonneg _) hMu'))
    _ = (((Ma + 1) * εu + Mu * εa : ℚ) : ℝ) := by
        push_cast
        ring

/-- **E6e: the complex product enclosure.**  Re/Im of `z·w` from
componentwise certificates — the composition node for station values. -/
theorem complex_mul_enclosure {z w : ℂ} {x y u v εz εw Mz Mw : ℚ}
    (hx : |z.re - (x : ℝ)| ≤ (εz : ℝ)) (hy : |z.im - (y : ℝ)| ≤ (εz : ℝ))
    (hu : |w.re - (u : ℝ)| ≤ (εw : ℝ)) (hv : |w.im - (v : ℝ)| ≤ (εw : ℝ))
    (hMx : |x| ≤ Mz) (hMy : |y| ≤ Mz) (hMu : |u| ≤ Mw) (hMv : |v| ≤ Mw)
    (hεz1 : εz ≤ 1) :
    |(z * w).re - ((x * u - y * v : ℚ) : ℝ)|
        ≤ ((2 * ((Mz + 1) * εw + Mw * εz) : ℚ) : ℝ)
      ∧ |(z * w).im - ((x * v + y * u : ℚ) : ℝ)|
        ≤ ((2 * ((Mz + 1) * εw + Mw * εz) : ℚ) : ℝ) := by
  have h1 := mul_diff_bound hx hu hMx hMu hεz1
  have h2 := mul_diff_bound hy hv hMy hMv hεz1
  have h3 := mul_diff_bound hx hv hMx hMv hεz1
  have h4 := mul_diff_bound hy hu hMy hMu hεz1
  constructor
  · have hre : (z * w).re - ((x * u - y * v : ℚ) : ℝ)
        = (z.re * w.re - ((x * u : ℚ) : ℝ))
          - (z.im * w.im - ((y * v : ℚ) : ℝ)) := by
      rw [Complex.mul_re]
      push_cast
      ring
    rw [hre]
    calc |(z.re * w.re - ((x * u : ℚ) : ℝ))
          - (z.im * w.im - ((y * v : ℚ) : ℝ))|
        ≤ |z.re * w.re - ((x * u : ℚ) : ℝ)|
          + |z.im * w.im - ((y * v : ℚ) : ℝ)| := abs_sub _ _
      _ ≤ (((Mz + 1) * εw + Mw * εz : ℚ) : ℝ)
          + (((Mz + 1) * εw + Mw * εz : ℚ) : ℝ) := add_le_add h1 h2
      _ = ((2 * ((Mz + 1) * εw + Mw * εz) : ℚ) : ℝ) := by
          push_cast
          ring
  · have him : (z * w).im - ((x * v + y * u : ℚ) : ℝ)
        = (z.re * w.im - ((x * v : ℚ) : ℝ))
          + (z.im * w.re - ((y * u : ℚ) : ℝ)) := by
      rw [Complex.mul_im]
      push_cast
      ring
    rw [him]
    calc |(z.re * w.im - ((x * v : ℚ) : ℝ))
          + (z.im * w.re - ((y * u : ℚ) : ℝ))|
        ≤ |z.re * w.im - ((x * v : ℚ) : ℝ)|
          + |z.im * w.re - ((y * u : ℚ) : ℝ)| := abs_add_le _ _
      _ ≤ (((Mz + 1) * εw + Mw * εz : ℚ) : ℝ)
          + (((Mz + 1) * εw + Mw * εz : ℚ) : ℝ) := add_le_add h3 h4
      _ = ((2 * ((Mz + 1) * εw + Mw * εz) : ℚ) : ℝ) := by
          push_cast
          ring

/-- **E6d: the sum enclosure.**  Per-term certificates aggregate over any
finite index set by the triangle inequality. -/
theorem sum_enclosure {ι : Type*} (s : Finset ι) (f : ι → ℝ) (v ε : ι → ℚ)
    (h : ∀ i ∈ s, |f i - (v i : ℝ)| ≤ (ε i : ℝ)) :
    |(∑ i ∈ s, f i) - ((∑ i ∈ s, v i : ℚ) : ℝ)|
      ≤ ((∑ i ∈ s, ε i : ℚ) : ℝ) := by
  rw [Rat.cast_sum, Rat.cast_sum, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ s, (f i - (v i : ℝ))|
      ≤ ∑ i ∈ s, |f i - (v i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (ε i : ℝ) := Finset.sum_le_sum h

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.nat_cpow_neg_split
#print axioms CriticalLinePhasor.DVP.inv_sqrt_enclosure
#print axioms CriticalLinePhasor.DVP.product_enclosure
#print axioms CriticalLinePhasor.DVP.sum_enclosure
#print axioms CriticalLinePhasor.DVP.mul_diff_bound
#print axioms CriticalLinePhasor.DVP.complex_mul_enclosure
end AxiomAudit
