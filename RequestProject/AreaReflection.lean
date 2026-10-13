import Mathlib

/-!
# The reflection `s ↦ 1 − conj s` from the area measure's duality (ledger 1223)

On the area measure (Lebesgue on `(0, ∞)`) the dilations `V_t f = e^{t/2} f(e^t ·)` are unitary with
`V_t* = V_{−t}`. The duality that implements this is `g ↦ g̃`, `g̃(x) = conj(g(1/x)) / x`.

* `mellin_conj`: `𝓜(conj ∘ f)(s) = conj(𝓜f(conj s))`.
* `mellin_areaDual`: `𝓜(g̃)(s) = conj(𝓜g(1 − conj s))`.

So the reflection `s ↦ 1 − conj s` that pairs zeros in any symmetric realization
(`SymPair.inner_eq_zero_unless_reflect`) is the Mellin image of the area measure's own duality. It is not
put in through the functional equation.
-/

open Complex MeasureTheory Set

noncomputable section

namespace CriticalLinePhasor.AreaReflection

/-- Conjugation commutes with the Mellin transform up to conjugating `s`. -/
theorem mellin_conj (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun t => (starRingEnd ℂ) (f t)) s = (starRingEnd ℂ) (mellin f ((starRingEnd ℂ) s)) := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_pos.ne
  simp only [smul_eq_mul, map_mul]
  congr 1
  rw [show (starRingEnd ℂ) s - 1 = (starRingEnd ℂ) (s - 1) by simp, Complex.cpow_conj _ _ harg,
    Complex.conj_ofReal, Complex.conj_conj]

/-- The area-measure dual `g̃(x) = conj(g(1/x)) / x`. -/
def areaDual (g : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (-1 : ℂ) * (starRingEnd ℂ) (g x⁻¹)

/-- **The reflection from the area measure's duality.** -/
theorem mellin_areaDual (g : ℝ → ℂ) (s : ℂ) :
    mellin (areaDual g) s = (starRingEnd ℂ) (mellin g (1 - (starRingEnd ℂ) s)) := by
  have h1 : mellin (areaDual g) s = mellin (fun x => (starRingEnd ℂ) (g x⁻¹)) (s + (-1)) := by
    rw [← mellin_cpow_smul]
    rfl
  rw [h1, mellin_comp_inv (fun x => (starRingEnd ℂ) (g x)), mellin_conj]
  congr 2
  simp [map_add, map_neg]
  ring

end CriticalLinePhasor.AreaReflection

end

#print axioms CriticalLinePhasor.AreaReflection.mellin_conj
#print axioms CriticalLinePhasor.AreaReflection.mellin_areaDual
