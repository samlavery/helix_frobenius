import RequestProject.CPSUnitTransvection3D
import RequestProject.CPSMellinBasicIdentity

/-!
# Unit-winding Mellin converse in three dimensions

Only the translated unit winding cell is needed.  Mellin inversion converts its completed
functional equations into equality of every additive-character coordinate.  Finite Fourier
separation supplies unit-winding invariance, and coordinate dilations then supply all winding
parameters.
-/

open Complex MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

/-- Mellin identities for the single shift `c ↦ c + 1` force invariance under the unit
transvection in every off-diagonal direction. -/
theorem unit_transvection_readout_invariant_of_mellinFunctionalEquations
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ)
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
          (fun c => readout (transvectionGL i j hij (c + 1) • x)) character)
    (hDualReadout : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      reflectedTheta k ε (dual i j hij x character) height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij c • x)) character) :
    ∀ (i j : n) (hij : i ≠ j) (x : X),
      readout (transvectionGL i j hij (1 : K) • x) = readout x := by
  intro i j hij x
  apply transvection_readout_invariant_of_all_twists readout i j hij 1 x
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

/-- **Unit-Mellin 3D CPS converse.** Unit-shift Mellin identities and diagonal carrier clocks
imply readout invariance under all of `GL(n, K)`. -/
theorem cps3D_readout_invariant_of_unitMellinFunctionalEquations
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ)
    (k sigma height : ℝ) (ε : ℂ) (hheight : 0 < height)
    (primal dual : ∀ (i j : n), i ≠ j → X → AddChar K ℂ → ℝ → ℂ)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
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
          (fun c => readout (transvectionGL i j hij (c + 1) • x)) character)
    (hDualReadout : ∀ (i j : n) (hij : i ≠ j) (x : X)
        (character : AddChar K ℂ),
      reflectedTheta k ε (dual i j hij x character) height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij c • x)) character)
    (g : Matrix.GeneralLinearGroup n K) (x : X) :
    readout (g • x) = readout x := by
  apply cps3D_readout_invariant_of_unit readout hdiag
  exact unit_transvection_readout_invariant_of_mellinFunctionalEquations
    readout k sigma height ε hheight primal dual hFE hInversion
      hPrimalReadout hDualReadout

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.unit_transvection_readout_invariant_of_mellinFunctionalEquations
#print axioms CriticalLinePhasor.ThreeDConverse.cps3D_readout_invariant_of_unitMellinFunctionalEquations
