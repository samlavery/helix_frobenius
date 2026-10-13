import RequestProject.AreaDilation

/-!
# Every zero gives a covariant functional: exhaustive at the algebraic level (ledger 1222)

* `mellin_dilW`: for EVERY `s` (no condition on `Re s`) and every `f`, the Mellin transform intertwines the
  area-measure dilation with the scalar `e^{t(½ − s)}`: `𝓜(V_t f)(s) = e^{t(½ − s)}·𝓜f(s)`.
* `mellin_dilationSum`: at a finite head `N`, the integer-dilation sum `P f = Σ_{n ≤ N} w(n)·f(n·)` becomes
  multiplication by the Dirichlet polynomial `S_N(s) = Σ w(n) n^{−s}` (for Mellin-convergent `f`).
* `annihilates_iff`: the Mellin functional at `s` kills the range of `P` iff `S_N(s) = 0`, given one
  convergent `f` with `𝓜f(s) ≠ 0`. This holds for EVERY zero of `S_N`, on or off any line.

So every zero is represented by a covariant functional, with no assumption on its location. The HP step
(`DilationEigen.covariant_functional_re`, `SymPair.re_eq_half_of_symmetric`) then needs that functional
to be continuous on a dilation-tempered space (equivalently, an eigenvector in a symmetric realization).
At a finite head that FAILS for zeros of `S_N` off the line (e.g. `S_2 = 1 − 2^{−s}`, zeros at `Re s = 0`).
Exhaustiveness alone is therefore not the missing step; continuity (symmetry) on the exhaustive object is.
-/

open Complex MeasureTheory Set Finset

noncomputable section

namespace CriticalLinePhasor.Exhaustive

open CriticalLinePhasor.AreaDilation

/-- **The Mellin transform intertwines the native dilation at every `s`.** -/
theorem mellin_dilW (f : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    mellin (dilW (1 / 2) t f) s = Complex.exp ((t : ℂ) * (1 / 2 - s)) * mellin f s := by
  have hex : 0 < Real.exp t := Real.exp_pos t
  unfold dilW
  rw [show (fun x => ((Real.exp (1 / 2 * t) : ℝ) : ℂ) * f (Real.exp t * x)) =
      fun x => ((Real.exp (1 / 2 * t) : ℝ) : ℂ) • (fun y => f (Real.exp t * y)) x from rfl,
    mellin_const_smul, mellin_comp_mul_left _ _ hex, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  congr 1
  have hlog : Complex.log ((Real.exp t : ℝ) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_log hex.le, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (show ((Real.exp t : ℝ) : ℂ) ≠ 0 by exact_mod_cast hex.ne'),
    hlog, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The integer-dilation sum up to the head `N`. -/
def dilationSum (w : ℕ → ℂ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, w n * f (n * x)

/-- **At a finite head the integer-dilation sum becomes multiplication by the Dirichlet polynomial.** -/
theorem mellin_dilationSum (w : ℕ → ℂ) (N : ℕ) (f : ℝ → ℂ) (s : ℂ) (hf : MellinConvergent f s) :
    mellin (dilationSum w N f) s = (∑ n ∈ Finset.Icc 1 N, w n * (n : ℂ) ^ (-s)) * mellin f s := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, MellinConvergent (fun x => w n * f (n * x)) s := by
    intro n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    simpa [smul_eq_mul] using ((MellinConvergent.comp_mul_left hn0).mpr hf).const_smul (w n)
  unfold dilationSum mellin
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun n hn => hterm n hn), Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  have h := mellin_comp_mul_left f s hn0
  have h2 := mellin_const_smul (fun x => f (n * x)) s (w n)
  unfold mellin at h h2
  simp only [smul_eq_mul] at h h2 ⊢
  rw [show (fun t : ℝ => (t : ℂ) ^ (s - 1) * (w n * f (n * t))) =
      fun t : ℝ => w n * ((t : ℂ) ^ (s - 1) * f (n * t)) by funext t; ring]
  rw [integral_const_mul, h, Complex.ofReal_natCast]
  ring

/-- **Every zero of the head polynomial gives an annihilating functional, wherever it lies.** -/
theorem annihilates_iff (w : ℕ → ℂ) (N : ℕ) (s : ℂ) {f₀ : ℝ → ℂ} (hf₀ : MellinConvergent f₀ s)
    (hne : mellin f₀ s ≠ 0) :
    (∀ f : ℝ → ℂ, MellinConvergent f s → mellin (dilationSum w N f) s = 0) ↔
      ∑ n ∈ Finset.Icc 1 N, w n * (n : ℂ) ^ (-s) = 0 := by
  constructor
  · intro h
    have := h f₀ hf₀
    rw [mellin_dilationSum w N f₀ s hf₀] at this
    exact (mul_eq_zero.mp this).resolve_right hne
  · intro h f hf
    rw [mellin_dilationSum w N f s hf, h, zero_mul]

end CriticalLinePhasor.Exhaustive

end

#print axioms CriticalLinePhasor.Exhaustive.mellin_dilW
#print axioms CriticalLinePhasor.Exhaustive.mellin_dilationSum
#print axioms CriticalLinePhasor.Exhaustive.annihilates_iff
