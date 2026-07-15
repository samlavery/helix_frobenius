import RequestProject.CPSMellinBasicIdentity

/-!
# Archimedean Mellin converse in three dimensions

Completed Mellin identities identify the primal archimedean move readout with its reflected dual
identity readout at a positive carrier height.  Mellin inversion therefore gives invariance under
every archimedean move.
-/

open Complex MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

/-- **Archimedean Mellin 3D converse.** Pointwise completed Mellin identities whose primal and
reflected-dual kernels read an archimedean orbit and its basepoint force invariance of the readout
under every archimedean move. -/
theorem archimedean_readout_invariant_of_mellinFunctionalEquations
    {G X : Type*} [Group G] [MulAction G X]
    (readout : X → ℂ)
    (k sigma height : ℝ) (ε : ℂ) (hheight : 0 < height)
    (primal dual : G → X → ℝ → ℂ)
    (hFE : ∀ (a : G) (x : X) (s : ℂ),
      mellin (primal a x) (k - s) = ε • mellin (dual a x) s)
    (hInversion : ∀ (a : G) (x : X),
      MellinConvergent (primal a x) (sigma : ℂ) ∧
      MellinConvergent (reflectedTheta k ε (dual a x)) (sigma : ℂ) ∧
      VerticalIntegrable (mellin (primal a x)) sigma volume ∧
      VerticalIntegrable (mellin (reflectedTheta k ε (dual a x))) sigma volume ∧
      ContinuousAt (primal a x) height ∧
      ContinuousAt (reflectedTheta k ε (dual a x)) height)
    (hPrimalReadout : ∀ (a : G) (x : X), primal a x height = readout (a • x))
    (hDualReadout : ∀ (a : G) (x : X),
      reflectedTheta k ε (dual a x) height = readout x) :
    ∀ (a : G) (x : X), readout (a • x) = readout x := by
  intro a x
  rcases hInversion a x with
    ⟨hfConv, hrefConv, hfVert, hrefVert, hfCont, hrefCont⟩
  have hreflection := theta_reflection_of_mellin_functionalEquation
    k sigma ε (primal a x) (dual a x) (hFE a x)
      hfConv hrefConv hfVert hrefVert height hheight hfCont hrefCont
  rw [hPrimalReadout a x, hDualReadout a x] at hreflection
  exact hreflection

/-- The archimedean Mellin converse in the left factor of an adelic product action. -/
theorem adelic_archimedean_readout_invariant_of_mellinFunctionalEquations
    {Gfinite Garch X : Type*} [Group Gfinite] [Group Garch]
    [MulAction (Garch × Gfinite) X]
    (readout : X → ℂ)
    (k sigma height : ℝ) (ε : ℂ) (hheight : 0 < height)
    (primal dual : Garch → X → ℝ → ℂ)
    (hFE : ∀ (a : Garch) (x : X) (s : ℂ),
      mellin (primal a x) (k - s) = ε • mellin (dual a x) s)
    (hInversion : ∀ (a : Garch) (x : X),
      MellinConvergent (primal a x) (sigma : ℂ) ∧
      MellinConvergent (reflectedTheta k ε (dual a x)) (sigma : ℂ) ∧
      VerticalIntegrable (mellin (primal a x)) sigma volume ∧
      VerticalIntegrable (mellin (reflectedTheta k ε (dual a x))) sigma volume ∧
      ContinuousAt (primal a x) height ∧
      ContinuousAt (reflectedTheta k ε (dual a x)) height)
    (hPrimalReadout : ∀ (a : Garch) (x : X),
      primal a x height = readout ((a, (1 : Gfinite)) • x))
    (hDualReadout : ∀ (a : Garch) (x : X),
      reflectedTheta k ε (dual a x) height = readout x) :
    ∀ (a : Garch) (x : X),
      readout ((a, (1 : Gfinite)) • x) = readout x := by
  let archEmbedding : Garch →* Garch × Gfinite := MonoidHom.inl Garch Gfinite
  letI archAction : MulAction Garch X := MulAction.compHom X archEmbedding
  apply archimedean_readout_invariant_of_mellinFunctionalEquations
    readout k sigma height ε hheight primal dual hFE hInversion
  · intro a x
    simpa [archAction, archEmbedding, MulAction.compHom_smul_def] using hPrimalReadout a x
  · exact hDualReadout

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.archimedean_readout_invariant_of_mellinFunctionalEquations
#print axioms CriticalLinePhasor.ThreeDConverse.adelic_archimedean_readout_invariant_of_mellinFunctionalEquations
