import RequestProject.GlobalHelixIntertwiner
import RequestProject.CancellationEquivalence
import RequestProject.TwoEndedGrownState
import RequestProject.TwoEndedJState

/-!
Unfolded target: v_n(s) has length n^(-Re s). For a cylindrical state f=(r,θ,h),
J f=(r,-θ,-h) realizes as (x,-y,-z). If v_n(s) and v_n(1-s) are these actual
Cartesian realizations, their lengths agree; injectivity of x ↦ n^x gives Re s=1/2.
The chart readout `stripReadout f` is definitionally 1/2+i*height(f), independent of r.
It is not used to identify an arbitrary parameter s.

Expectation-free next step: compare the two concrete Cartesian triples.
Strategy A: `have h := hJ.symm.trans (realize_globalHelixInvolution f)`.
Strategy B: `apply (Real.rpow_right_inj hn0 hn1).mp` after the two magnitude formulas.
The local pair hypothesis below is full state identification, not an assumed amplitude equality.
-/
noncomputable section
open Complex ConeProjection
namespace CriticalLinePhasor.GlobalHelix
open Phasor3D SpectralFiber

/-- Ordinary polar coordinates realize any phasor, without using a zero premise. -/
theorem realize_phasor_polar (v : Vec3) :
    realize (‖v.1‖, Complex.arg v.1, v.2) = (v.1.re, v.1.im, v.2) := by
  simp [realize, atom, radial, phase, height, Complex.norm_mul_cos_arg,
    Complex.norm_mul_sin_arg]

/-- The physical J-image of that same phasor has conjugated plane and negated mass. -/
theorem realize_j_phasor_polar (v : Vec3) :
    realize (globalHelixInvolution (‖v.1‖, Complex.arg v.1, v.2)) =
      (((starRingEnd ℂ) v.1).re, ((starRingEnd ℂ) v.1).im, -v.2) := by
  rw [realize_globalHelixInvolution, realize_phasor_polar]
  simp

/-- At a charged real-character site, the physical J-image has chart parameter `conj s`.
The abscissa and its Mellin amplitude are retained in this exact coordinate computation. -/
theorem spectralFiber_conj_charged (χ : ℕ → ℂ) (s : ℂ) (n : ℕ)
    (hcharged : χ n = 1 ∨ χ n = -1) :
    spectralFiber χ ((starRingEnd ℂ) s) n =
      ((starRingEnd ℂ) (spectralFiber χ s n).1, -(spectralFiber χ s n).2) := by
  unfold spectralFiber phasor3D
  simp only [Complex.conj_re, Complex.conj_im]
  apply Prod.ext
  · unfold LFunctionPhasor.phasorTerm
    split_ifs with hn
    · simp
    · rw [map_mul, map_mul, Complex.conj_ofReal, TwoEndedJState.conj_mellinSpin]
      rcases hcharged with h | h <;> simp [h]
  · rcases hcharged with h | h <;> simp [h]

/-- The global physical involution preserves the full 3D phasor magnitude. -/
theorem mag3_eq_of_realize_j_pair {v w : Vec3} {f : Fiber}
    (hH : realize f = (v.1.re, v.1.im, v.2))
    (hJ : realize (globalHelixInvolution f) = (w.1.re, w.1.im, w.2)) :
    mag3 v = mag3 w := by
  have h := hJ.symm.trans (realize_globalHelixInvolution f)
  rw [hH] at h
  have hx := congrArg (fun t : ℝ × ℝ × ℝ => t.1) h
  have hy := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) h
  have hz := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) h
  have hw : w = ((starRingEnd ℂ) v.1, -v.2) := by
    apply Prod.ext
    · apply Complex.ext
      · simpa using hx
      · simpa using hy
    · exact hz
  rw [hw]
  simp [mag3]

/-- Amplitude balance follows from a physical J-pair of the two actual spectral terms. -/
theorem j_pair_amplitude_balance {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) (s : ℂ) (n : ℕ) (hn : 1 < n)
    (hpair : ∃ f : Fiber,
      realize f = ((spectralFiber (fun k => χ k) s n).1.re,
        (spectralFiber (fun k => χ k) s n).1.im, (spectralFiber (fun k => χ k) s n).2) ∧
      realize (globalHelixInvolution f) = ((spectralFiber (fun k => χ k) (1 - s) n).1.re,
        (spectralFiber (fun k => χ k) (1 - s) n).1.im,
        (spectralFiber (fun k => χ k) (1 - s) n).2)) :
    (n : ℝ) ^ (-s.re) = (n : ℝ) ^ (-(1 - s.re)) := by
  obtain ⟨f, hH, hJ⟩ := hpair
  have hmag := mag3_eq_of_realize_j_pair hH hJ
  change mag3 (phasor3D (fun k => χ k) s.re s.im n) =
    mag3 (phasor3D (fun k => χ k) (1 - s).re (1 - s).im n) at hmag
  rw [phasor3D_mag3 χ hq _ _ n (by omega),
    phasor3D_mag3 χ hq _ _ n (by omega)] at hmag
  simpa using hmag

/-- The physical J-pair implies the midpoint, by injectivity of real exponentiation. -/
theorem j_pair_forces_midpoint {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) (s : ℂ) (n : ℕ) (hn : 1 < n)
    (hpair : ∃ f : Fiber,
      realize f = ((spectralFiber (fun k => χ k) s n).1.re,
        (spectralFiber (fun k => χ k) s n).1.im, (spectralFiber (fun k => χ k) s n).2) ∧
      realize (globalHelixInvolution f) = ((spectralFiber (fun k => χ k) (1 - s) n).1.re,
        (spectralFiber (fun k => χ k) (1 - s) n).1.im,
        (spectralFiber (fun k => χ k) (1 - s) n).2)) :
    s.re = 1 / 2 := by
  have hmag := j_pair_amplitude_balance χ hq s n hn hpair
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have h := (Real.rpow_right_inj (by linarith : (0 : ℝ) < n) (ne_of_gt hn')).mp hmag
  linarith

/-- The already compiled ratio, in the requested original/reflected orientation. -/
theorem inputPhasor_original_reflected_ratio (s : ℂ) (k : ℕ) :
    ‖GrownFiberEvolution.inputPhasor s k‖ /
        ‖GrownFiberEvolution.inputPhasor (1 - s) k‖ =
      ((k : ℝ) + 1) ^ (1 - 2 * s.re) := by
  rw [TwoEndedGrownState.end_scale_ratio]
  rw [GrownFiberEvolution.norm_inputPhasor]
  have hb : 0 < (k : ℝ) + 1 := by positivity
  have hpos := Real.rpow_pos_of_pos hb (-s.re)
  rw [div_mul_eq_div_div, div_right_comm, div_self hpos.ne', one_div,
    ← Real.rpow_neg hb.le]
  congr 1
  ring

/-- A cancellation at -2 checks the unrestricted final implication's scope. -/
theorem spectralCancellation_neg_two :
    SpectralCancellation (1 : DirichletCharacter ℂ 1) (-2) := by
  apply L_cancellation_realized_spectrally
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (-2) = 0
  rw [DirichletCharacter.LFunction_modOne_eq]
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

theorem unrestricted_spectralCancellation_midpoint_false :
    ¬ (∀ s : ℂ, SpectralCancellation (1 : DirichletCharacter ℂ 1) s → s.re = 1 / 2) := by
  intro h
  have hn := h (-2) spectralCancellation_neg_two
  norm_num at hn

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.realize_j_phasor_polar
#print axioms CriticalLinePhasor.GlobalHelix.spectralFiber_conj_charged
#print axioms CriticalLinePhasor.GlobalHelix.j_pair_amplitude_balance
#print axioms CriticalLinePhasor.GlobalHelix.j_pair_forces_midpoint
#print axioms CriticalLinePhasor.GlobalHelix.inputPhasor_original_reflected_ratio
#print axioms CriticalLinePhasor.GlobalHelix.unrestricted_spectralCancellation_midpoint_false
