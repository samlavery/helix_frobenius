import RequestProject.XiStructureNativeSeat

/-!
# The radial amplitude identity: the native seat is `∂σ|ξ|²` signed

Step 1 of the supply-consumption pass (adjudicator directive): the exact
elementary identity

  `∂/∂σ |ξ(σ+it)|² = 2·Re(ξ(σ+it)·conj(ξ′(σ+it)))`,

compiled as a `HasDerivAt` and its `deriv` form.  With it the native-seat
target reads: the radial amplitude `|ξ|²` is strictly increasing in the
distance from the carrier projection, along every horizontal, on the
native domain.  An identity, not a door.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.XiStructure

/-- The horizontal path derivative of ξ. -/
theorem xi_horizontal_hasDerivAt (t σ : ℝ) :
    HasDerivAt (fun x : ℝ => ZD.riemannXi (↑x + ↑t * Complex.I))
      (deriv ZD.riemannXi (↑σ + ↑t * Complex.I)) σ := by
  have hin : HasDerivAt (fun w : ℂ => w + ↑t * Complex.I) 1 (σ : ℂ) := by
    simpa using (hasDerivAt_id (σ : ℂ)).add_const ((t : ℂ) * Complex.I)
  have hξ : HasDerivAt ZD.riemannXi
      (deriv ZD.riemannXi (↑σ + ↑t * Complex.I)) ((σ : ℂ) + ↑t * Complex.I) :=
    (ZD.riemannXi_differentiable _).hasDerivAt
  have hG := HasDerivAt.comp (σ : ℂ) hξ hin
  have := hG.comp_ofReal
  simpa [Function.comp] using this

/-- **The radial amplitude identity**: `∂σ |ξ(σ+it)|² = 2·Re(ξ·conj ξ′)`. -/
theorem radial_amplitude_hasDerivAt (t σ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.normSq (ZD.riemannXi (↑x + ↑t * Complex.I)))
      (2 * (ZD.riemannXi (↑σ + ↑t * Complex.I)
        * conj (deriv ZD.riemannXi (↑σ + ↑t * Complex.I))).re) σ := by
  have hf := xi_horizontal_hasDerivAt t σ
  have hre : HasDerivAt
      (fun x : ℝ => (ZD.riemannXi (↑x + ↑t * Complex.I)).re)
      ((deriv ZD.riemannXi (↑σ + ↑t * Complex.I)).re) σ :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt σ hf
  have him : HasDerivAt
      (fun x : ℝ => (ZD.riemannXi (↑x + ↑t * Complex.I)).im)
      ((deriv ZD.riemannXi (↑σ + ↑t * Complex.I)).im) σ :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt σ hf
  have hprod := (hre.mul hre).add (him.mul him)
  have heq : (fun x : ℝ =>
      Complex.normSq (ZD.riemannXi (↑x + ↑t * Complex.I)))
      = fun x : ℝ => (ZD.riemannXi (↑x + ↑t * Complex.I)).re
          * (ZD.riemannXi (↑x + ↑t * Complex.I)).re
        + (ZD.riemannXi (↑x + ↑t * Complex.I)).im
          * (ZD.riemannXi (↑x + ↑t * Complex.I)).im :=
    funext fun x => Complex.normSq_apply _
  rw [heq]
  have hval : (deriv ZD.riemannXi (↑σ + ↑t * Complex.I)).re
        * (ZD.riemannXi (↑σ + ↑t * Complex.I)).re
      + (ZD.riemannXi (↑σ + ↑t * Complex.I)).re
        * (deriv ZD.riemannXi (↑σ + ↑t * Complex.I)).re
      + ((deriv ZD.riemannXi (↑σ + ↑t * Complex.I)).im
          * (ZD.riemannXi (↑σ + ↑t * Complex.I)).im
        + (ZD.riemannXi (↑σ + ↑t * Complex.I)).im
          * (deriv ZD.riemannXi (↑σ + ↑t * Complex.I)).im)
      = 2 * (ZD.riemannXi (↑σ + ↑t * Complex.I)
          * conj (deriv ZD.riemannXi (↑σ + ↑t * Complex.I))).re := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  exact hval ▸ hprod

/-- The `deriv` form of the radial identity. -/
theorem radial_amplitude_deriv (t σ : ℝ) :
    deriv (fun x : ℝ => Complex.normSq (ZD.riemannXi (↑x + ↑t * Complex.I))) σ
      = 2 * (ZD.riemannXi (↑σ + ↑t * Complex.I)
          * conj (deriv ZD.riemannXi (↑σ + ↑t * Complex.I))).re :=
  (radial_amplitude_hasDerivAt t σ).deriv

end CriticalLinePhasor.XiStructure

#print axioms CriticalLinePhasor.XiStructure.radial_amplitude_hasDerivAt
#print axioms CriticalLinePhasor.XiStructure.radial_amplitude_deriv
