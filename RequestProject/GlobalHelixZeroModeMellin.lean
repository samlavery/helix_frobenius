import RequestProject.GlobalHelixZeroModeGaussian

/-!
# Mellin projection of zero-mode-free 3D banks

The Mellin transform of a finite indexed 3D bank factors into its finite Dirichlet/Euler readout
and the Mellin transform of the fixed zero-mode-free Gaussian kernel.
-/

open Real Complex Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- Dirichlet readout of a finite indexed coefficient-height bank. -/
noncomputable def finiteIndexedDirichletReadout
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (s : ℂ) : ℂ :=
  ∑ i, a i * (H i : ℂ) ^ (-s)

/-- Mellin scaling for one arbitrary positive-height coefficient fiber. -/
theorem indexedKernelTerm_hasMellin
    {I : Type*} (a : I → ℂ) (H : I → ℝ) (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s) (i : I) (hH : 0 < H i) :
    HasMellin (fun x : ℝ => a i * g (H i * x)) s
      (a i * ((H i : ℂ) ^ (-s) * mellin g s)) := by
  have hconv : MellinConvergent (fun x : ℝ => g (H i * x)) s :=
    (MellinConvergent.comp_mul_left hH).2 hg
  have h := hasMellin_const_smul hconv (a i)
  refine ⟨h.1, ?_⟩
  calc
    mellin (fun x : ℝ => a i * g (H i * x)) s =
        a i * mellin (fun x : ℝ => g (H i * x)) s := by
      simpa [smul_eq_mul] using h.2
    _ = a i * ((H i : ℂ) ^ (-s) * mellin g s) := by
      rw [mellin_comp_mul_left g s hH]
      simp [smul_eq_mul]

/-- Mellin factorization for an arbitrary finite subset of coefficient fibers. -/
theorem finsetIndexedKernel_hasMellin
    {I : Type*} (S : Finset I) (a : I → ℂ) (H : I → ℝ) (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s) (hH : ∀ i ∈ S, 0 < H i) :
    HasMellin (fun x : ℝ => ∑ i ∈ S, a i * g (H i * x)) s
      ((∑ i ∈ S, a i * (H i : ℂ) ^ (-s)) * mellin g s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [HasMellin, MellinConvergent, mellin]
  | @insert i S hi ih =>
      have ht := indexedKernelTerm_hasMellin a H g hg i (hH i (Finset.mem_insert_self i S))
      have ih' := ih (fun j hj => hH j (Finset.mem_insert_of_mem hj))
      have hadd := hasMellin_add ht.1 ih'.1
      have hfun : (fun x : ℝ => ∑ j ∈ insert i S, a j * g (H j * x)) =
          (fun x : ℝ => a i * g (H i * x) + ∑ j ∈ S, a j * g (H j * x)) := by
        funext x
        rw [Finset.sum_insert hi]
      refine ⟨?_, ?_⟩
      · rw [hfun]
        exact hadd.1
      · rw [hfun]
        rw [hadd.2, ht.2, ih'.2, Finset.sum_insert hi]
        ring

/-- The one-fiber strong pair whose primal projection is exactly the zero-mode-free kernel. -/
noncomputable def zeroModeGaussianStrongFEPair (c : ℝ) (hc : 0 < c) : StrongFEPair ℂ :=
  finiteZeroModeGaussianStrongFEPair
    (I := Unit) (fun _ => (1 : ℂ)) (fun _ => (1 : ℝ)) (Equiv.refl Unit)
    (fun _ => zero_lt_one) (fun _ => by norm_num) c hc

theorem zeroModeGaussianStrongFEPair_f (c : ℝ) (hc : 0 < c) :
    (zeroModeGaussianStrongFEPair c hc).f = zeroModeGaussianKernel c := by
  funext x
  simp [zeroModeGaussianStrongFEPair, finiteZeroModeGaussianStrongFEPair,
    indexedZeroModeGaussianTheta, indexedTheta]

/-- The zero-mode-free kernel has a Mellin transform at every complex parameter. -/
theorem zeroModeGaussianKernel_mellinConvergent (c : ℝ) (hc : 0 < c) (s : ℂ) :
    MellinConvergent (zeroModeGaussianKernel c) s := by
  have h := (zeroModeGaussianStrongFEPair c hc).hasMellin s |>.1
  simpa [zeroModeGaussianStrongFEPair_f c hc] using h

/-- Exact Mellin factorization of the finite indexed zero-mode Gaussian projection. -/
theorem indexedZeroModeGaussianTheta_hasMellin
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ)
    (hH : ∀ i, 0 < H i) (c : ℝ) (hc : 0 < c) (s : ℂ) :
    HasMellin (indexedZeroModeGaussianTheta a H c) s
      (finiteIndexedDirichletReadout a H s * mellin (zeroModeGaussianKernel c) s) := by
  unfold indexedZeroModeGaussianTheta indexedTheta finiteIndexedDirichletReadout
  simp only [tsum_fintype]
  exact finsetIndexedKernel_hasMellin Finset.univ a H (zeroModeGaussianKernel c)
    (zeroModeGaussianKernel_mellinConvergent c hc s) (fun i _ => hH i)

/-- The entire transform of the 3D bank is its finite Dirichlet readout times the fixed completion
multiplier. -/
theorem finiteZeroModeGaussian_initialIdentification
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    (c : ℝ) (hc : 0 < c) (s : ℂ) :
    let P := finiteZeroModeGaussianStrongFEPair a H dual hH hrecip c hc
    P.Λ s = finiteIndexedDirichletReadout a H s * mellin (zeroModeGaussianKernel c) s := by
  dsimp only
  exact (indexedZeroModeGaussianTheta_hasMellin a H hH c hc s).2

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.indexedKernelTerm_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.finsetIndexedKernel_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.zeroModeGaussianKernel_mellinConvergent
#print axioms CriticalLinePhasor.GlobalHelix.indexedZeroModeGaussianTheta_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.finiteZeroModeGaussian_initialIdentification
