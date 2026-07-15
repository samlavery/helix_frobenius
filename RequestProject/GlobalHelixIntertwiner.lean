import RequestProject.GeometricReadout
import RequestProject.RoundTrip

/-!
# The global 3D double-helix involution and its readout

The source-independent carrier symmetry is defined first in 3D cylindrical coordinates.  It keeps
the radial ledger and exchanges helix with anti-helix by negating phase and signed height.  The
Cayley projection intertwines this with conjugation on the unit circle.  Only afterwards does the
positive-height encoding followed by logarithm produce the analytic ordinate; the resulting strip
coordinate is sent to both complex conjugation and `s ↦ 1 - s`.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection CriticalLinePhasor.Readout

/-- The global symmetry of the 3D double carrier: radius is retained in the ledger while phase and
signed height are reversed. -/
def globalHelixInvolution (f : Fiber) : Fiber :=
  (radial f, -phase f, -height f)

/-- The helix/anti-helix exchange is a genuine global involution. -/
theorem globalHelixInvolution_involutive :
    Function.Involutive globalHelixInvolution := by
  intro f
  rcases f with ⟨r, θ, h⟩
  simp [globalHelixInvolution, radial, phase, height]

/-- The 3D symmetry retains radius. -/
@[simp] theorem radial_globalHelixInvolution (f : Fiber) :
    radial (globalHelixInvolution f) = radial f := by
  rfl

/-- The 3D symmetry reverses phase. -/
@[simp] theorem phase_globalHelixInvolution (f : Fiber) :
    phase (globalHelixInvolution f) = -phase f := by
  rfl

/-- The 3D symmetry reverses signed height. -/
@[simp] theorem height_globalHelixInvolution (f : Fiber) :
    height (globalHelixInvolution f) = -height f := by
  rfl

/-- Cartesian realization makes the global symmetry literal: `(x,y,z) ↦ (x,-y,-z)`. -/
theorem realize_globalHelixInvolution (f : Fiber) :
    realize (globalHelixInvolution f) =
      ((realize f).1, -(realize f).2.1, -(realize f).2.2) := by
  rcases f with ⟨r, θ, h⟩
  simp [globalHelixInvolution, realize, atom, radial, phase, height, Real.cos_neg,
    Real.sin_neg]

/-- The loss-ledger record still reconstructs the exact 3D anti-helix point. -/
theorem reconstruct_record_globalHelixInvolution (f : Fiber) :
    reconstruct (record (globalHelixInvolution f)) = globalHelixInvolution f :=
  reconstruct_record _

/-- The 2D Cayley readout of the retained signed height. -/
noncomputable def circleReadout (f : Fiber) : ℂ :=
  cayley ((height f : ℝ) : ℂ)

/-- The 2D Cayley projection intertwines the global 3D involution with complex conjugation. -/
theorem circleReadout_globalHelixInvolution (f : Fiber) :
    circleReadout (globalHelixInvolution f) =
      (starRingEnd ℂ) (circleReadout f) := by
  rcases f with ⟨r, θ, h⟩
  unfold circleReadout cayley globalHelixInvolution height
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq]

/-- Every 2D Cayley readout lies on the unit circle. -/
theorem circleReadout_norm_one (f : Fiber) : ‖circleReadout f‖ = 1 := by
  exact cayley_real_norm_one (height f)

/-- The positive multiplicative carrier height, formed from the signed 3D height. -/
noncomputable def multiplicativeHeight (f : Fiber) : ℝ :=
  heightEncode (height f)

/-- Multiplicative carrier height is strictly positive. -/
theorem multiplicativeHeight_pos (f : Fiber) : 0 < multiplicativeHeight f := by
  exact Real.exp_pos _

/-- The global 3D helix/anti-helix exchange becomes reciprocal multiplicative height. -/
theorem multiplicativeHeight_globalHelixInvolution (f : Fiber) :
    multiplicativeHeight (globalHelixInvolution f) = 1 / multiplicativeHeight f := by
  unfold multiplicativeHeight heightEncode
  rw [height_globalHelixInvolution, Real.exp_neg]
  simp [one_div]

/-- The 2D→1D step: encode signed height positively and only then take its logarithm. -/
noncomputable def analyticOrdinate (f : Fiber) : ℝ :=
  lineProj (heightEncode (height f))

/-- The logarithmic readout recovers the retained signed height exactly. -/
theorem analyticOrdinate_eq_height (f : Fiber) : analyticOrdinate f = height f := by
  exact log_recovers_height (height f)

/-- The global 3D involution reverses the final analytic ordinate. -/
theorem analyticOrdinate_globalHelixInvolution (f : Fiber) :
    analyticOrdinate (globalHelixInvolution f) = -analyticOrdinate f := by
  rw [analyticOrdinate_eq_height, height_globalHelixInvolution,
    analyticOrdinate_eq_height]

/-- The normalized analytic strip coordinate, formed only after the 3D and 2D stages. -/
noncomputable def stripReadout (f : Fiber) : ℂ :=
  (1 / 2 : ℂ) + I * (analyticOrdinate f : ℂ)

/-- The full 3D→2D→1D chain sends the global involution to complex conjugation. -/
theorem stripReadout_globalHelixInvolution_conj (f : Fiber) :
    stripReadout (globalHelixInvolution f) =
      (starRingEnd ℂ) (stripReadout f) := by
  apply Complex.ext <;>
    simp [stripReadout, analyticOrdinate_globalHelixInvolution,
      Complex.mul_re, Complex.mul_im] <;> norm_num

/-- The same full chain sends the global involution to the completed reflection `s ↦ 1 - s`. -/
theorem stripReadout_globalHelixInvolution_one_sub (f : Fiber) :
    stripReadout (globalHelixInvolution f) = 1 - stripReadout f := by
  apply Complex.ext <;>
    simp [stripReadout, analyticOrdinate_globalHelixInvolution,
      Complex.mul_re, Complex.mul_im] <;> norm_num

/-- The unique fixed ordinate of the readout involution is the half-unit. -/
theorem stripReadout_fixed_iff_half (f : Fiber) :
    stripReadout (globalHelixInvolution f) = stripReadout f ↔
      stripReadout f = (1 / 2 : ℂ) := by
  rw [stripReadout_globalHelixInvolution_one_sub]
  constructor <;> intro h
  · calc
      stripReadout f = ((1 - stripReadout f) + stripReadout f) / 2 := by rw [h]; ring
      _ = (1 / 2 : ℂ) := by ring
  · rw [h]
    ring

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.globalHelixInvolution_involutive
#print axioms CriticalLinePhasor.GlobalHelix.realize_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.reconstruct_record_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.circleReadout_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.circleReadout_norm_one
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.analyticOrdinate_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.stripReadout_globalHelixInvolution_conj
#print axioms CriticalLinePhasor.GlobalHelix.stripReadout_globalHelixInvolution_one_sub
#print axioms CriticalLinePhasor.GlobalHelix.stripReadout_fixed_iff_half
