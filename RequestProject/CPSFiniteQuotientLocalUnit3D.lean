import RequestProject.CPSUnitTransvection3D
import RequestProject.CPSMellinBasicIdentity

/-!
# Finite winding quotients detect local unit transvections

A finite additive winding cell may index transvections over a different local field.  Fourier
separation needs no compatibility of the representative map with addition: evaluating the
separated cell identity at zero uses only that zero and one have their standard representatives.
-/

open Complex MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

/-- A completed Mellin identity on a finite winding quotient forces the unit transvection law
over the local carrier field. -/
theorem local_unit_transvection_invariant_of_finiteQuotientMellin
    {n K L X : Type*} [Fintype n] [DecidableEq n]
    [Field K] [Finite K] [Field L]
    [MulAction (Matrix.GeneralLinearGroup n L) X]
    (readout : X → ℂ) (lift : K → L)
    (hlift_zero : lift 0 = 0) (hlift_one : lift 1 = 1)
    (k sigma height : ℝ) (ε : ℂ) (hheight : 0 < height)
    (primal dual : ∀ (i j : n), i ≠ j → X → AddChar K ℂ → ℝ → ℂ)
    (hFE : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ) (s : ℂ),
      mellin (primal i j hij x character) (k - s) =
        ε • mellin (dual i j hij x character) s)
    (hInversion : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      MellinConvergent (primal i j hij x character) (sigma : ℂ) ∧
      MellinConvergent
        (reflectedTheta k ε (dual i j hij x character)) (sigma : ℂ) ∧
      VerticalIntegrable (mellin (primal i j hij x character)) sigma volume ∧
      VerticalIntegrable
        (mellin (reflectedTheta k ε (dual i j hij x character))) sigma volume ∧
      ContinuousAt (primal i j hij x character) height ∧
      ContinuousAt (reflectedTheta k ε (dual i j hij x character)) height)
    (hPrimalReadout : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      primal i j hij x character height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (lift (c + 1)) • x)) character)
    (hDualReadout : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      reflectedTheta k ε (dual i j hij x character) height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (lift c) • x)) character) :
    ∀ (i j : n) (hij : i ≠ j) (x : X),
      readout (transvectionGL i j hij (1 : L) • x) = readout x := by
  intro i j hij x
  have htwist : ∀ character : AddChar K ℂ,
      finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (lift (c + 1)) • x)) character =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (lift c) • x)) character := by
    intro character
    rcases hInversion i j hij x character with
      ⟨hfConv, hrefConv, hfVert, hrefVert, hfCont, hrefCont⟩
    have hreflection := theta_reflection_of_mellin_functionalEquation
      k sigma ε
      (primal i j hij x character)
      (dual i j hij x character)
      (hFE i j hij x character)
      hfConv hrefConv hfVert hrefVert
      height hheight hfCont hrefCont
    rw [hPrimalReadout i j hij x character,
      hDualReadout i j hij x character] at hreflection
    exact hreflection
  have hcell :
      (fun c => readout (transvectionGL i j hij (lift (c + 1)) • x)) =
        (fun c => readout (transvectionGL i j hij (lift c) • x)) :=
    finiteAbelianCell_eq_of_all_twists_eq htwist
  have hzero := congrFun hcell 0
  simpa [hlift_zero, hlift_one, transvectionGL_zero] using hzero

/-- **Finite-quotient local 3D CPS converse.** Finite-cell Mellin identities and local diagonal
clocks imply invariance under the full local general linear group. -/
theorem cpsLocal3D_invariant_of_finiteQuotientMellin
    {n K L X : Type*} [Fintype n] [DecidableEq n]
    [Field K] [Finite K] [Field L]
    [MulAction (Matrix.GeneralLinearGroup n L) X]
    (readout : X → ℂ) (lift : K → L)
    (hlift_zero : lift 0 = 0) (hlift_one : lift 1 = 1)
    (k sigma height : ℝ) (ε : ℂ) (hheight : 0 < height)
    (primal dual : ∀ (i j : n), i ≠ j → X → AddChar K ℂ → ℝ → ℂ)
    (hdiag : ∀ (D : n → L) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (hFE : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ) (s : ℂ),
      mellin (primal i j hij x character) (k - s) =
        ε • mellin (dual i j hij x character) s)
    (hInversion : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      MellinConvergent (primal i j hij x character) (sigma : ℂ) ∧
      MellinConvergent
        (reflectedTheta k ε (dual i j hij x character)) (sigma : ℂ) ∧
      VerticalIntegrable (mellin (primal i j hij x character)) sigma volume ∧
      VerticalIntegrable
        (mellin (reflectedTheta k ε (dual i j hij x character))) sigma volume ∧
      ContinuousAt (primal i j hij x character) height ∧
      ContinuousAt (reflectedTheta k ε (dual i j hij x character)) height)
    (hPrimalReadout : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      primal i j hij x character height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (lift (c + 1)) • x)) character)
    (hDualReadout : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      reflectedTheta k ε (dual i j hij x character) height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (lift c) • x)) character)
    (g : Matrix.GeneralLinearGroup n L) (x : X) :
    readout (g • x) = readout x := by
  apply cps3D_readout_invariant_of_unit readout hdiag
  exact local_unit_transvection_invariant_of_finiteQuotientMellin
    readout lift hlift_zero hlift_one k sigma height ε hheight primal dual
      hFE hInversion hPrimalReadout hDualReadout

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.local_unit_transvection_invariant_of_finiteQuotientMellin
#print axioms CriticalLinePhasor.ThreeDConverse.cpsLocal3D_invariant_of_finiteQuotientMellin
