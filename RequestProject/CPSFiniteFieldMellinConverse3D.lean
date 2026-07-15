import RequestProject.CPSMellinBasicIdentity

/-!
# End-to-end finite-field Mellin-to-3D CPS converse

For every one-parameter transvection and every additive character, a completed Mellin functional
equation is inverted to a pointwise theta reflection.  The theta readout identifications turn this
into equality of all twisted winding-cell coordinates.  Fourier separation gives transvection
invariance, and diagonal/transvection generation gives full `GL(n)` invariance.
-/

open Complex MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

/-- **Finite-field Mellin-to-3D CPS converse.** The full analytic twist family, identified with the
finite character readouts of translated transvection cells, forces full rank-n invariance. -/
theorem cpsFiniteField3D_of_mellinFunctionalEquations
    {n K X : Type*} [Fintype n] [DecidableEq n] [Field K] [Finite K]
    [MulAction (Matrix.GeneralLinearGroup n K) X]
    (readout : X → ℂ)
    (k sigma height : ℝ) (ε : ℂ) (hheight : 0 < height)
    (primal dual : ∀ (i j : n), i ≠ j → K → X → AddChar K ℂ → ℝ → ℂ)
    (hdiag : ∀ (D : n → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) =
        readout x)
    (hFE : ∀ (i j : n) (hij : i ≠ j) (d : K) (x : X)
        (character : AddChar K ℂ) (s : ℂ),
      mellin (primal i j hij d x character) (k - s) =
        ε • mellin (dual i j hij d x character) s)
    (hInversion : ∀ (i j : n) (hij : i ≠ j) (d : K) (x : X)
        (character : AddChar K ℂ),
      MellinConvergent (primal i j hij d x character) (sigma : ℂ) ∧
      MellinConvergent
        (reflectedTheta k ε (dual i j hij d x character)) (sigma : ℂ) ∧
      VerticalIntegrable (mellin (primal i j hij d x character)) sigma volume ∧
      VerticalIntegrable
        (mellin (reflectedTheta k ε (dual i j hij d x character))) sigma volume ∧
      ContinuousAt (primal i j hij d x character) height ∧
      ContinuousAt (reflectedTheta k ε (dual i j hij d x character)) height)
    (hPrimalReadout : ∀ (i j : n) (hij : i ≠ j) (d : K) (x : X)
        (character : AddChar K ℂ),
      primal i j hij d x character height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij (c + d) • x)) character)
    (hDualReadout : ∀ (i j : n) (hij : i ≠ j) (d : K) (x : X)
        (character : AddChar K ℂ),
      reflectedTheta k ε (dual i j hij d x character) height =
        finiteAbelianTwistReadout K
          (fun c => readout (transvectionGL i j hij c • x)) character)
    (g : Matrix.GeneralLinearGroup n K) (x : X) :
    readout (g • x) = readout x := by
  apply cpsFiniteField3D_readout_invariant readout hdiag
  intro i j hij d x character
  rcases hInversion i j hij d x character with
    ⟨hfConv, hrefConv, hfVert, hrefVert, hfCont, hrefCont⟩
  have hreflection := theta_reflection_of_mellin_functionalEquation
    k sigma ε
    (primal i j hij d x character)
    (dual i j hij d x character)
    (hFE i j hij d x character)
    hfConv hrefConv hfVert hrefVert
    height hheight hfCont hrefCont
  rw [hPrimalReadout i j hij d x character,
    hDualReadout i j hij d x character] at hreflection
  exact hreflection

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.cpsFiniteField3D_of_mellinFunctionalEquations
