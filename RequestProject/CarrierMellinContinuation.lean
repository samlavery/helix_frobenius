import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import RequestProject.CommonRepresentation
import RequestProject.TrivialChannelPole

/-!
# Carrier DC cancellation to entire Mellin continuation

Mathlib's `WeakFEPair` is the Riemann--Hecke theta interface: it records local integrability,
reflection, rapid decay up to two constant modes, and their values.  This file connects the project's
proved harmonic-bank DC cancellation to those constant modes.  Once both modes vanish, the unchanged
theta pair is a `StrongFEPair`; Mathlib then supplies an entire Mellin transform and its functional
equation.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace CriticalLinePhasor.CarrierMellinContinuation

/-- A weak Riemann--Hecke pair whose two constant modes vanish is already a strong pair, without
modifying either theta function. -/
def strongFEPairOfZeroConstants (P : WeakFEPair ℂ)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) : StrongFEPair ℂ :=
  StrongFEPair.mk P hf₀ hg₀

/-- Zero constant modes give an entire completed Mellin transform and the global functional equation. -/
theorem zeroConstants_entire_functionalEquation (P : WeakFEPair ℂ)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) :
    Differentiable ℂ (mellin P.f) ∧
      ∀ s : ℂ, mellin P.f (P.k - s) = P.ε * mellin P.g s := by
  let Q : StrongFEPair ℂ := strongFEPairOfZeroConstants P hf₀ hg₀
  refine ⟨?_, fun s => ?_⟩
  · exact Q.differentiable_Λ
  · have hQf : Q.f = P.f := rfl
    have hQg : Q.symm.f = P.g := rfl
    have hQk : Q.k = P.k := rfl
    have hQε : Q.ε = P.ε := rfl
    simpa only [StrongFEPair.Λ, hQf, hQg, hQk, hQε, smul_eq_mul] using
      Q.functional_equation s

/-- The Mellin transform of a strong Riemann--Hecke pair is uniformly bounded on every closed
vertical strip.  The dominating integral is the sum of the Mellin norm integrands at the two strip
endpoints; its value is independent of the imaginary part. -/
theorem strongFEPair_boundedOn_verticalStrip
    (P : StrongFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ s‖ ≤ C := by
  let bound : ℝ → ℝ := fun t =>
    ‖(t : ℂ) ^ ((a : ℂ) - 1) • P.f t‖ +
      ‖(t : ℂ) ^ ((b : ℂ) - 1) • P.f t‖
  have ha_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖(t : ℂ) ^ ((a : ℂ) - 1) • P.f t‖) (Ioi 0) :=
    (P.hasMellin (a : ℂ)).1.norm
  have hb_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖(t : ℂ) ^ ((b : ℂ) - 1) • P.f t‖) (Ioi 0) :=
    (P.hasMellin (b : ℂ)).1.norm
  have hbound_int : MeasureTheory.IntegrableOn bound (Ioi 0) := ha_int.add hb_int
  refine ⟨∫ t in Ioi (0 : ℝ), bound t, fun s has hsb => ?_⟩
  calc
    ‖P.Λ s‖ = ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • P.f t‖ := rfl
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f t‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), bound t := by
      apply MeasureTheory.integral_mono_ae (P.hasMellin s).1.norm hbound_int
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [bound, norm_smul, norm_cpow_eq_rpow_re_of_pos ht,
        sub_re, one_re, ofReal_re]
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg (P.f t))
      by_cases ht1 : 1 ≤ t
      · apply le_add_of_nonneg_of_le (Real.rpow_nonneg ht.le _)
        exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      · apply le_add_of_le_of_nonneg
        · exact Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge ht1) (by linarith)
        · exact Real.rpow_nonneg ht.le _

/-- The exact analytic payload consumed by a converse theorem: the primal and dual completed Mellin
transforms are entire, each is bounded on every closed vertical strip, and they satisfy the global
functional equation. -/
theorem zeroConstants_twistedNiceness (P : WeakFEPair ℂ)
    (hf₀ : P.f₀ = 0) (hg₀ : P.g₀ = 0) :
    Differentiable ℂ (mellin P.f) ∧
    Differentiable ℂ (mellin P.g) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖mellin P.f s‖ ≤ C) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖mellin P.g s‖ ≤ C) ∧
    (∀ s : ℂ, mellin P.f (P.k - s) = P.ε * mellin P.g s) := by
  let Q : StrongFEPair ℂ := strongFEPairOfZeroConstants P hf₀ hg₀
  have hQf : Q.f = P.f := rfl
  have hQg : Q.symm.f = P.g := rfl
  have hentire := zeroConstants_entire_functionalEquation P hf₀ hg₀
  refine ⟨hentire.1, ?_, ?_, ?_, hentire.2⟩
  · simpa only [StrongFEPair.Λ, hQg] using Q.symm.differentiable_Λ
  · intro a b
    simpa only [StrongFEPair.Λ, hQf] using strongFEPair_boundedOn_verticalStrip Q a b
  · intro a b
    simpa only [StrongFEPair.Λ, hQg] using strongFEPair_boundedOn_verticalStrip Q.symm a b

/-- A complete harmonic bank kills the `f`-side constant mode of a weak theta pair. -/
theorem fConstant_zero_of_completeBank
    (P : WeakFEPair ℂ)
    {G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J]
    (c : J → ℂ) (χ : J → AddChar G ℂ)
    (hχ : ∀ j, ∃ t, (χ j) t ≠ 1)
    (hf₀ : P.f₀ = ∑ g, ∑ j, c j * (χ j) g) :
    P.f₀ = 0 := by
  rw [hf₀]
  exact CriticalLinePhasor.CommonRepresentation.complete_bank_dc_zero c χ hχ

/-- A complete harmonic dual bank kills the `g`-side constant mode of a weak theta pair. -/
theorem gConstant_zero_of_completeBank
    (P : WeakFEPair ℂ)
    {G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J]
    (c : J → ℂ) (χ : J → AddChar G ℂ)
    (hχ : ∀ j, ∃ t, (χ j) t ≠ 1)
    (hg₀ : P.g₀ = ∑ g, ∑ j, c j * (χ j) g) :
    P.g₀ = 0 := by
  rw [hg₀]
  exact CriticalLinePhasor.CommonRepresentation.complete_bank_dc_zero c χ hχ

/-- End-to-end Riemann--Hecke continuation for a reflected rapid theta pair whose two constant
modes are complete harmonic banks.  The conclusion contains no residual hypothesis: both residuals
are discharged by character orthogonality. -/
theorem completeHarmonicPair_entire_functionalEquation
    (P : WeakFEPair ℂ)
    {Gf Jf Gg Jg : Type*}
    [AddCommGroup Gf] [Fintype Gf] [Fintype Jf]
    [AddCommGroup Gg] [Fintype Gg] [Fintype Jg]
    (cf : Jf → ℂ) (χf : Jf → AddChar Gf ℂ)
    (hχf : ∀ j, ∃ t, (χf j) t ≠ 1)
    (cg : Jg → ℂ) (χg : Jg → AddChar Gg ℂ)
    (hχg : ∀ j, ∃ t, (χg j) t ≠ 1)
    (hf₀ : P.f₀ = ∑ g, ∑ j, cf j * (χf j) g)
    (hg₀ : P.g₀ = ∑ g, ∑ j, cg j * (χg j) g) :
    Differentiable ℂ (mellin P.f) ∧
      ∀ s : ℂ, mellin P.f (P.k - s) = P.ε * mellin P.g s := by
  exact zeroConstants_entire_functionalEquation P
    (fConstant_zero_of_completeBank P cf χf hχf hf₀)
    (gConstant_zero_of_completeBank P cg χg hχg hg₀)

/-- A constant mode factoring linearly through `Hom(W,V)` vanishes when `V` is simple and the
carrier twist has strictly smaller dimension. -/
theorem rankGapConstant_zero
    {A W V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    (hV : IsSimpleModule A V) (hdim : Module.finrank ℂ W < Module.finrank ℂ V)
    (residue : W →ₗ[A] V) (readout : (W →ₗ[A] V) →ₗ[ℂ] ℂ) :
    readout residue = 0 := by
  have hresidue : residue = 0 :=
    CriticalLinePhasor.TrivialChannel.no_nonzero_hom_of_finrank_lt
      (k := ℂ) (A := A) hV hdim residue
  calc
    readout residue = readout 0 := congrArg readout hresidue
    _ = 0 := map_zero readout

/-- End-to-end Riemann--Hecke continuation for a reflected rapid theta pair whose two constant
modes factor through representation-theoretic trivial channels.  A strict rank gap into a simple
target kills both channels, so the completed Mellin transform is entire and obeys its global
functional equation. -/
theorem rankGapPair_entire_functionalEquation
    (P : WeakFEPair ℂ)
    {A W V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    (hV : IsSimpleModule A V) (hdim : Module.finrank ℂ W < Module.finrank ℂ V)
    (residueF residueG : W →ₗ[A] V)
    (readoutF readoutG : (W →ₗ[A] V) →ₗ[ℂ] ℂ)
    (hf₀ : P.f₀ = readoutF residueF)
    (hg₀ : P.g₀ = readoutG residueG) :
    Differentiable ℂ (mellin P.f) ∧
      ∀ s : ℂ, mellin P.f (P.k - s) = P.ε * mellin P.g s := by
  apply zeroConstants_entire_functionalEquation P
  · rw [hf₀]
    exact rankGapConstant_zero hV hdim residueF readoutF
  · rw [hg₀]
    exact rankGapConstant_zero hV hdim residueG readoutG

/-- The full primal/dual niceness package for the rank-gap branch. -/
theorem rankGapPair_twistedNiceness
    (P : WeakFEPair ℂ)
    {A W V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    (hV : IsSimpleModule A V) (hdim : Module.finrank ℂ W < Module.finrank ℂ V)
    (residueF residueG : W →ₗ[A] V)
    (readoutF readoutG : (W →ₗ[A] V) →ₗ[ℂ] ℂ)
    (hf₀ : P.f₀ = readoutF residueF)
    (hg₀ : P.g₀ = readoutG residueG) :
    Differentiable ℂ (mellin P.f) ∧
    Differentiable ℂ (mellin P.g) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖mellin P.f s‖ ≤ C) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖mellin P.g s‖ ≤ C) ∧
    (∀ s : ℂ, mellin P.f (P.k - s) = P.ε * mellin P.g s) := by
  apply zeroConstants_twistedNiceness P
  · rw [hf₀]
    exact rankGapConstant_zero hV hdim residueF readoutF
  · rw [hg₀]
    exact rankGapConstant_zero hV hdim residueG readoutG

end CriticalLinePhasor.CarrierMellinContinuation

#print axioms CriticalLinePhasor.CarrierMellinContinuation.zeroConstants_entire_functionalEquation
#print axioms CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
#print axioms CriticalLinePhasor.CarrierMellinContinuation.zeroConstants_twistedNiceness
#print axioms CriticalLinePhasor.CarrierMellinContinuation.fConstant_zero_of_completeBank
#print axioms CriticalLinePhasor.CarrierMellinContinuation.gConstant_zero_of_completeBank
#print axioms CriticalLinePhasor.CarrierMellinContinuation.completeHarmonicPair_entire_functionalEquation
#print axioms CriticalLinePhasor.CarrierMellinContinuation.rankGapConstant_zero
#print axioms CriticalLinePhasor.CarrierMellinContinuation.rankGapPair_entire_functionalEquation
#print axioms CriticalLinePhasor.CarrierMellinContinuation.rankGapPair_twistedNiceness
