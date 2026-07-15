import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuation of a completed reflection from the weld axis

Two entire completed readouts that obey the desired reflection on the full weld axis obey it on
the whole plane.  The accumulation sequence is explicit: `κ / 2 + i / (n + 1)`.
-/

open Complex Set Filter Topology

namespace CriticalLinePhasor

/-- Equality of an entire readout and its reflected dual on the weld axis propagates globally. -/
theorem entire_reflection_of_axis
    (f g : ℂ → ℂ) (κ : ℝ) (ε : ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (haxis : ∀ t : ℝ,
      f (((κ / 2 : ℝ) : ℂ) + I * (t : ℂ)) =
        ε * g ((κ : ℂ) - (((κ / 2 : ℝ) : ℂ) + I * (t : ℂ)))) :
    ∀ s : ℂ, f s = ε * g ((κ : ℂ) - s) := by
  let rhs : ℂ → ℂ := fun s => ε * g ((κ : ℂ) - s)
  let c : ℂ := ((κ / 2 : ℝ) : ℂ)
  have hrhs : Differentiable ℂ rhs := by
    dsimp [rhs]
    fun_prop
  have hseq : Tendsto
      (fun n : ℕ => c + I * (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) atTop (𝓝 c) := by
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have htc : Tendsto (fun n : ℕ => (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp ht
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul htc)
  have hmem : ∀ n : ℕ,
      c + I * (((1 : ℝ) / (n + 1) : ℝ) : ℂ) ∈
        {z | f z = rhs z} \ {c} := by
    intro n
    constructor
    · change f (c + I * (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) =
        ε * g ((κ : ℂ) - (c + I * (((1 : ℝ) / (n + 1) : ℝ) : ℂ)))
      simpa [c] using haxis ((1 : ℝ) / (n + 1))
    · simp only [mem_singleton_iff]
      intro heq
      have hzero : I * (((1 : ℝ) / (n + 1) : ℝ) : ℂ) = 0 := by
        have := congrArg (fun z : ℂ => z - c) heq
        simpa using this
      have hrealzero : (1 : ℝ) / (n + 1) = 0 := by
        have hcoezero : (((1 : ℝ) / (n + 1) : ℝ) : ℂ) = 0 :=
          (mul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero
        exact_mod_cast hcoezero
      have hpos : 0 < (1 : ℝ) / (n + 1) := by positivity
      exact hpos.ne' hrealzero
  have hclosure : c ∈ closure ({z | f z = rhs z} \ {c}) :=
    mem_closure_iff_seq_limit.mpr ⟨
      (fun n : ℕ => c + I * (((1 : ℝ) / (n + 1) : ℝ) : ℂ)), hmem, hseq⟩
  have heq : EqOn f rhs (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable.mpr hf).eqOn_of_preconnected_of_mem_closure
      (analyticOnNhd_univ_iff_differentiable.mpr hrhs) isPreconnected_univ
      (Set.mem_univ c) hclosure
  intro s
  exact heq (Set.mem_univ s)

end CriticalLinePhasor

#print axioms CriticalLinePhasor.entire_reflection_of_axis
