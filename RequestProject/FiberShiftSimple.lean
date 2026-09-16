import RequestProject.StripShiftClass

/-!
# "Fibers can't cancel in two places at once": the shift of a real-rooted polynomial has SIMPLE zeros

Ledger 848 (Sam): the vanishing happens on the **warped fiber**, not on the scaled carrier, and *a
fiber cannot cancel in two places at once*.  This is the polynomial core of that statement, which is
the step the flow's real-rootedness is built from (`StripShiftClass`, `DeBruijnStripStep`).

**The mechanism.**  Let `p` be a real polynomial with only real zeros and let `h > 0`.  For real `x`,
`p(x − ih) = conj p(x + ih)` because `p` has real coefficients, so the shift restricted to the axis is
```
    (S_h p)(x) = p(x + ih) + p(x − ih) = 2 Re p(x + ih),
    (S_h p)'(x) = 2 Re p'(x + ih).
```
A double zero at `x` would make BOTH `p(w)` and `p'(w)` purely imaginary at `w = x + ih`, hence
`conj(p(w)) · p'(w)` real.  But in the upper half-plane that product has strictly negative imaginary
part (`im_conj_mul_deriv_neg`), because
```
    conj(p(w))·p'(w) = |p(w)|² · Σ_k 1/(w − r_k),   Im (1/(w − r_k)) = −h/|w − r_k|² < 0 .
```
So the cancellation is transversal: **the fiber crosses, it never grazes.**

The sum over roots is not formalized here; instead `im_conj_mul_deriv_nonpos` runs an induction that
peels one real root at a time, which is where the strict sign is produced:
`Im = −|q(w)|²·Im w + |w − r|²·Im(conj q(w)·q'(w))`, first term strictly negative, second `≤ 0` by
induction.

**Scope.**  This is the polynomial step, landed on the compiled `shiftPoly` (`shiftPoly_zero_simple`,
via `shiftPoly_derivative`: the shift commutes with differentiation).  It does NOT give simplicity of
the flow stages `Ξ_λ`: Hurwitz transports real-rootedness to a locally uniform limit but NOT
simplicity, so the passage from here to `flowStage` needs a zero-gap bound uniform in the approximating
index.  That bound is genuinely unavailable at this level — the approximants have degree `→ ∞` and
their own minimum gap degrades (the heat flow on `zⁿ` gives Hermite roots spread over `√n`), so it must
come from the limit's own zero density, not from the polynomials.  That step is not taken here.
-/

open Polynomial Complex

namespace CriticalLinePhasor.DeBruijn

/-- A real polynomial with only real complex roots and positive degree factors as `(X − r) * q` with
`r` real and `q` again real-rooted of smaller degree. -/
theorem exists_real_root_factor {p : ℝ[X]} (hdeg : 0 < p.natDegree)
    (hreal : ∀ v : ℂ, aeval v p = 0 → v.im = 0) :
    ∃ (r : ℝ) (q : ℝ[X]), p = (X - C r) * q ∧ q ≠ 0 ∧ q.natDegree < p.natDegree ∧
      ∀ v : ℂ, aeval v q = 0 → v.im = 0 := by
  have hpne : p ≠ 0 := fun h => by simp [h] at hdeg
  -- a complex root exists, and it is real
  have hmapne : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    simpa using (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hpne
  have hmapdeg : 0 < (p.map (algebraMap ℝ ℂ)).degree := by
    rw [Polynomial.degree_map]
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
  obtain ⟨z, hz⟩ := Complex.exists_root hmapdeg
  have hz' : aeval z p = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hz
  have hzim : z.im = 0 := hreal z hz'
  set r : ℝ := z.re with hr
  have hzr : z = (r : ℂ) := by
    apply Complex.ext <;> simp [hr, hzim]
  -- `r` is a root over `ℝ`
  have hroot : p.IsRoot r := by
    have h2 : aeval ((r : ℂ)) p = 0 := by rw [← hzr]; exact hz'
    have hbridge : ((p.eval r : ℝ) : ℂ) = aeval ((r : ℂ)) p := by
      exact Polynomial.ofReal_eval p r
    have hc : ((p.eval r : ℝ) : ℂ) = 0 := by rw [hbridge]; exact h2
    exact_mod_cast hc
  obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot.mpr hroot)
  refine ⟨r, q, hq, ?_, ?_, ?_⟩
  · intro h; rw [h, mul_zero] at hq; exact hpne hq
  · have hqne : q ≠ 0 := by intro h; rw [h, mul_zero] at hq; exact hpne hq
    have : p.natDegree = 1 + q.natDegree := by
      rw [hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hqne,
        Polynomial.natDegree_X_sub_C]
    omega
  · intro v hv
    refine hreal v ?_
    rw [hq, map_mul, hv, mul_zero]

/-- **The sign, non-strict.**  For a real polynomial with only real roots,
`Im (conj p(w) · p'(w)) ≤ 0` whenever `Im w > 0`. -/
theorem im_conj_mul_deriv_nonpos :
    ∀ (n : ℕ) (p : ℝ[X]), p.natDegree = n → (∀ v : ℂ, aeval v p = 0 → v.im = 0) →
      ∀ w : ℂ, 0 < w.im →
        ((starRingEnd ℂ) (aeval w p) * aeval w (derivative p)).im ≤ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hdeg hreal w hw
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- constant: the derivative vanishes
      subst hn
      have hp : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      rw [hp]
      simp
    · obtain ⟨r, q, hpq, hqne, hqdeg, hqreal⟩ :=
        exists_real_root_factor (by omega) hreal
      have hIH : ((starRingEnd ℂ) (aeval w q) * aeval w (derivative q)).im ≤ 0 :=
        ih q.natDegree (by omega) q rfl hqreal w hw
      -- expand `p = (X - C r) * q`
      set A : ℂ := aeval w q with hA
      set B : ℂ := aeval w (derivative q) with hB
      set d : ℂ := w - (r : ℂ) with hd
      have hpw : aeval w p = d * A := by rw [hpq]; simp [hd, hA]
      have hdp : aeval w (derivative p) = A + d * B := by
        rw [hpq, Polynomial.derivative_mul]
        simp [hd, hA, hB]
      have hkey :
          ((starRingEnd ℂ) (aeval w p) * aeval w (derivative p)).im
            = -(Complex.normSq A) * w.im
              + (Complex.normSq d) * ((starRingEnd ℂ) A * B).im := by
        rw [hpw, hdp]
        simp only [map_mul, Complex.normSq_apply, Complex.mul_im, Complex.mul_re,
          Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hd]
        ring
      rw [hkey]
      have h1 : -(Complex.normSq A) * w.im ≤ 0 := by
        have := Complex.normSq_nonneg A
        nlinarith
      have h2 : (Complex.normSq d) * ((starRingEnd ℂ) A * B).im ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg d) hIH
      linarith

/-- **The sign, strict.**  Positive degree makes it `< 0`: the peeled factor contributes
`−|q(w)|²·Im w < 0`, since a real-rooted `q` cannot vanish off the real axis. -/
theorem im_conj_mul_deriv_neg {p : ℝ[X]} (hdeg : 0 < p.natDegree)
    (hreal : ∀ v : ℂ, aeval v p = 0 → v.im = 0) {w : ℂ} (hw : 0 < w.im) :
    ((starRingEnd ℂ) (aeval w p) * aeval w (derivative p)).im < 0 := by
  obtain ⟨r, q, hpq, hqne, hqdeg, hqreal⟩ := exists_real_root_factor hdeg hreal
  have hIH : ((starRingEnd ℂ) (aeval w q) * aeval w (derivative q)).im ≤ 0 :=
    im_conj_mul_deriv_nonpos q.natDegree q rfl hqreal w hw
  set A : ℂ := aeval w q with hA
  set B : ℂ := aeval w (derivative q) with hB
  set d : ℂ := w - (r : ℂ) with hd
  have hAne : A ≠ 0 := by
    intro h
    have := hqreal w (by rw [← hA]; exact h)
    linarith
  have hpw : aeval w p = d * A := by rw [hpq]; simp [hd, hA]
  have hdp : aeval w (derivative p) = A + d * B := by
    rw [hpq, Polynomial.derivative_mul]
    simp [hd, hA, hB]
  have hkey :
      ((starRingEnd ℂ) (aeval w p) * aeval w (derivative p)).im
        = -(Complex.normSq A) * w.im
          + (Complex.normSq d) * ((starRingEnd ℂ) A * B).im := by
    rw [hpw, hdp]
    simp only [map_mul, Complex.normSq_apply, Complex.mul_im, Complex.mul_re,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hd]
    ring
  rw [hkey]
  have hApos : 0 < Complex.normSq A := Complex.normSq_pos.mpr hAne
  have h2 : (Complex.normSq d) * ((starRingEnd ℂ) A * B).im ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg d) hIH
  nlinarith

/-! ### The shift crosses transversally -/

/-- **A fiber cannot cancel in two places at once.**  If `p` is a real polynomial of positive degree
with only real zeros and `h > 0`, then at every real zero of the shift `S_h p` the shift's derivative
is nonzero: the zero is SIMPLE. -/
theorem shift_zero_simple {p : ℝ[X]} (hdeg : 0 < p.natDegree)
    (hreal : ∀ v : ℂ, aeval v p = 0 → v.im = 0) {h : ℝ} (hh : 0 < h) {x : ℝ}
    (hz : aeval ((x : ℂ) + I * h) p + aeval ((x : ℂ) - I * h) p = 0) :
    aeval ((x : ℂ) + I * h) (derivative p) + aeval ((x : ℂ) - I * h) (derivative p) ≠ 0 := by
  set w : ℂ := (x : ℂ) + I * h with hw
  have hwim : w.im = h := by simp [hw]
  have hwpos : 0 < w.im := by rw [hwim]; exact hh
  have hconj : (starRingEnd ℂ) w = (x : ℂ) - I * h := by
    apply Complex.ext <;> simp [hw]
  -- the two shifted values are conjugate, so the hypotheses are statements about real parts
  have hp2 : aeval ((x : ℂ) - I * h) p = (starRingEnd ℂ) (aeval w p) := by
    rw [← hconj, Polynomial.aeval_conj]
  have hd2 : aeval ((x : ℂ) - I * h) (derivative p) = (starRingEnd ℂ) (aeval w (derivative p)) := by
    rw [← hconj, Polynomial.aeval_conj]
  rw [hp2] at hz
  have hre : (aeval w p).re = 0 := by
    have := congrArg Complex.re hz
    simp [Complex.add_re, Complex.conj_re] at this
    linarith
  intro hcontra
  rw [hd2] at hcontra
  have hre' : (aeval w (derivative p)).re = 0 := by
    have := congrArg Complex.re hcontra
    simp [Complex.add_re, Complex.conj_re] at this
    linarith
  -- both purely imaginary ⟹ the product is real ⟹ contradiction with the strict sign
  have hprod : ((starRingEnd ℂ) (aeval w p) * aeval w (derivative p)).im = 0 := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, hre, hre']
    ring
  have := im_conj_mul_deriv_neg hdeg hreal hwpos
  linarith [hprod]


/-! ### Landing it on the compiled `shiftPoly` -/

/-- The shift commutes with differentiation: `d/dz [p(z+ih) + p(z−ih)] = p'(z+ih) + p'(z−ih)`. -/
theorem shiftPolyC_derivative (h : ℝ) (p : ℝ[X]) :
    derivative (shiftPolyC h p) = shiftPolyC h (derivative p) := by
  unfold shiftPolyC
  rw [derivative_add, derivative_comp, derivative_comp]
  simp [Polynomial.derivative_map]

theorem shiftPoly_derivative (h : ℝ) (p : ℝ[X]) :
    derivative (shiftPoly h p) = shiftPoly h (derivative p) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  rw [← Polynomial.derivative_map, shiftPoly_map, shiftPoly_map, shiftPolyC_derivative]

/-- **The statement on the compiled shift polynomial**: every real zero of `shiftPoly h p` is simple,
for `p` real-rooted of positive degree and `h > 0`. -/
theorem shiftPoly_zero_simple {p : ℝ[X]} (hdeg : 0 < p.natDegree)
    (hreal : ∀ v : ℂ, aeval v p = 0 → v.im = 0) {h : ℝ} (hh : 0 < h) {x : ℝ}
    (hz : aeval ((x : ℂ)) (shiftPoly h p) = 0) :
    aeval ((x : ℂ)) (derivative (shiftPoly h p)) ≠ 0 := by
  rw [aeval_shiftPoly] at hz
  rw [shiftPoly_derivative, aeval_shiftPoly]
  exact shift_zero_simple hdeg hreal hh hz

end CriticalLinePhasor.DeBruijn

#print axioms CriticalLinePhasor.DeBruijn.im_conj_mul_deriv_neg
#print axioms CriticalLinePhasor.DeBruijn.shift_zero_simple
#print axioms CriticalLinePhasor.DeBruijn.shiftPoly_zero_simple
