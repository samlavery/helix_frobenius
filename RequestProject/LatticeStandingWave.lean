import RequestProject.CarrierLatticePair
import RequestProject.SchwarzAxisReality
import RequestProject.CarrierTargetIdentification

/-!
# The standing wave of the lattice family: gate 2 inhabited at every rank

Certifier (a) of the standing wave, fifth brick — the weak-side pipeline closed.  The
rank-`r` matrix bank's completed transform (the compiled `matrixLatticePair`, with its
arithmetic chart `Λ_r(s) = π^{-s}Γ(s)·L(r_{(r+1)²}, s)` from `LatticeLatticeUnfolding`)
satisfies **gate 2's shape at every rank**:

* `mellin_ofReal_conj` — the Mellin transform of any real profile is Schwarz-real;
* `matrixLattice_schwarz` — global Schwarz reality `Λ(s̄) = conj Λ(s)` of the completed
  transform, by the identity theorem through the entire part
  (`matrixLattice_entirePart_schwarz`, `lambda_decomp`);
* `matrixLatticePair_symm_eq` / `matrixLattice_FE` — the pair is its own reflection, so the
  completed functional equation is self-dual: `Λ((r+1)²/2 − s) = Λ(s)`;
* `matrixLattice_standingWave` — **the standing wave**: `Λ = conj Λ` on the central axis
  `Re s = (r+1)²/4`, root number `1` — exactly the FE-on-axis shape of
  `RankUniformReduction.RungData.standingWave`, at every rank, with
  `matrixLattice_axis_im_zero` (the transform is real on the axis) and the entire-part
  version `matrixLattice_standingWave₀`;
* `lattice_weak_rung` — the capstone conjunction.

**Register.**  This closes the weak-side pipeline of certifier (a): geometric Poisson identity ⟹
completed FE ⟹ standing wave, executed end-to-end on the genuine arithmetic family of
the carrier lattice, uniformly in the rank.  The cuspidal gate (`TransferGate`) demands
sub-axis primitive cancellation `θ < κ/2`, which the DC-mode family cannot supply — its
partial sums grow at the full abscissa (the poles are the measured exception).  The
remaining wall of certifier (a) is therefore exactly the **amplitude exchange**: replace
the representation-number amplitude by a rung profile with the cancellation gate while
keeping the lattice transformation law — one condition per rung, now located between two compiled endpoints.
No `axiom`, no `sorry`.
-/

open Complex ComplexConjugate MeasureTheory Set Filter

namespace CriticalLinePhasor.LatticeStandingWave

open CriticalLinePhasor.CarrierLatticePoisson CriticalLinePhasor.CarrierLatticePair
open CriticalLinePhasor.AxisReality

/-- Conjugation exchanges complex powers of a nonnegative real base across reflection. -/
lemma conj_ofReal_cpow {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    conj (((t : ℝ) : ℂ) ^ w) = ((t : ℝ) : ℂ) ^ (conj w) := by
  have harg : ((t : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (((t : ℝ) : ℂ)) (conj w) harg
  rw [Complex.conj_conj] at h
  rw [show conj (((t : ℝ) : ℂ)) = ((t : ℝ) : ℂ) from Complex.conj_ofReal t] at h
  rw [h, Complex.conj_conj]

/-- The Mellin transform of a real-valued profile is Schwarz-real. -/
theorem mellin_ofReal_conj (g : ℝ → ℝ) (s : ℂ) :
    mellin (fun t => ((g t : ℝ) : ℂ)) (conj s)
      = conj (mellin (fun t => ((g t : ℝ) : ℂ)) s) := by
  unfold mellin
  rw [← integral_conj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal,
    show conj ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (conj s - 1) by
      rw [show conj ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (conj (s - 1)) from
        conj_ofReal_cpow (le_of_lt (Set.mem_Ioi.mp ht)) (s - 1) ▸ rfl]
      rw [map_sub, map_one]]

theorem hreal_pair (r : ℕ) :
    (fun t => (matrixLatticePair r).f t - (matrixLatticePair r).f₀)
      = fun t : ℝ => ((matrixTheta r t - 1 : ℝ) : ℂ) := by
  funext t
  show matrixThetaC r t - 1 = _
  unfold matrixThetaC
  push_cast
  ring

/-- Schwarz reality of the completed transformation law transform on the convergence half-plane. -/
theorem matrixLattice_schwarz_halfPlane (r : ℕ) {s : ℂ}
    (hs : (matrixLatticePair r).k < s.re) :
    (matrixLatticePair r).Λ (conj s) = conj ((matrixLatticePair r).Λ s) := by
  have hs' : (matrixLatticePair r).k < (conj s).re := by
    rwa [Complex.conj_re]
  have h1 := ((matrixLatticePair r).hasMellin hs).2
  have h2 := ((matrixLatticePair r).hasMellin hs').2
  rw [← h1, ← h2, hreal_pair r]
  exact mellin_ofReal_conj _ s

/-- The completed transform decomposes over its entire part and its two booked poles. -/
theorem lambda_decomp (r : ℕ) (w : ℂ) :
    (matrixLatticePair r).Λ₀ w
      = (matrixLatticePair r).Λ w + (1 / w)
        + (1 / ((((matrixLatticePair r).k : ℝ) : ℂ) - w)) := by
  simp only [WeakFEPair.Λ, matrixLatticePair_ε, matrixLatticePair_f₀, matrixLatticePair_g₀,
    smul_eq_mul, mul_one, one_div]
  ring

/-- Global Schwarz reality of the entire part, by the identity theorem. -/
theorem matrixLattice_entirePart_schwarz (r : ℕ) (s : ℂ) :
    (matrixLatticePair r).Λ₀ (conj s) = conj ((matrixLatticePair r).Λ₀ s) := by
  have hglob : (fun z => conj ((matrixLatticePair r).Λ₀ (conj z)))
      = (matrixLatticePair r).Λ₀ := by
    refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
      (differentiable_conj_conj (matrixLatticePair r).differentiable_Λ₀)
      (matrixLatticePair r).differentiable_Λ₀
      (U := {z : ℂ | (matrixLatticePair r).k < z.re})
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
      (z₀ := (((matrixLatticePair r).k + 1 : ℝ) : ℂ))
      (by
        simp only [Set.mem_setOf_eq, Complex.ofReal_re]
        linarith)
      ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    have hz' : (matrixLatticePair r).k < (conj z).re := by rwa [Complex.conj_re]
    dsimp only
    rw [lambda_decomp r (conj z), lambda_decomp r z,
      matrixLattice_schwarz_halfPlane r hz]
    rw [map_add, map_add, map_div₀, map_div₀, map_one, map_sub, Complex.conj_conj,
      Complex.conj_conj, Complex.conj_ofReal]
  have h := congrFun hglob s
  calc (matrixLatticePair r).Λ₀ (conj s)
      = conj (conj ((matrixLatticePair r).Λ₀ (conj s))) := (Complex.conj_conj _).symm
    _ = conj ((matrixLatticePair r).Λ₀ s) := by rw [h]

/-- **Global Schwarz reality of the completed transformation law transform, at every rank.** -/
theorem matrixLattice_schwarz (r : ℕ) (s : ℂ) :
    (matrixLatticePair r).Λ (conj s) = conj ((matrixLatticePair r).Λ s) := by
  have hd := lambda_decomp r s
  have hd' := lambda_decomp r (conj s)
  have hΛ : (matrixLatticePair r).Λ (conj s)
      = (matrixLatticePair r).Λ₀ (conj s) - (1 / conj s)
        - (1 / ((((matrixLatticePair r).k : ℝ) : ℂ) - conj s)) := by
    rw [hd']
    ring
  rw [hΛ, matrixLattice_entirePart_schwarz r s]
  rw [show (matrixLatticePair r).Λ₀ s
      = (matrixLatticePair r).Λ s + (1 / s)
        + (1 / ((((matrixLatticePair r).k : ℝ) : ℂ) - s)) from hd]
  rw [map_add, map_add, map_div₀, map_div₀, map_one, map_sub, Complex.conj_ofReal]
  ring

/-- The lattice FE-pair is its own reflection. -/
theorem matrixLatticePair_symm_eq (r : ℕ) : (matrixLatticePair r).symm = matrixLatticePair r := by
  unfold WeakFEPair.symm matrixLatticePair
  simp only [inv_one]

/-- The self-dual completed functional equation, in weight-coordinate form. -/
theorem matrixLattice_FE (r : ℕ) (s : ℂ) :
    (matrixLatticePair r).Λ ((((matrixLatticePair r).k : ℝ) : ℂ) - s)
      = (matrixLatticePair r).Λ s := by
  have h := (matrixLatticePair r).functional_equation s
  rw [matrixLatticePair_symm_eq, matrixLatticePair_ε, one_smul] at h
  exact h

/-- **The standing wave of the lattice family, at every rank**: the completed transform
equals its own conjugate on the central axis `Re s = (r+1)²/4` — gate 2's shape, with root
number `1`.  Functional equation plus Schwarz reality; no new analytic input. -/
theorem matrixLattice_standingWave (r : ℕ) (t : ℝ) :
    (matrixLatticePair r).Λ ((((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I)
      = conj ((matrixLatticePair r).Λ
          ((((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I)) := by
  set s : ℂ := (((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I with hsdef
  have hconj : conj s = (((matrixLatticePair r).k : ℝ) : ℂ) - s := by
    rw [hsdef, map_add, map_mul, Complex.conj_I, map_div₀, Complex.conj_ofReal,
      map_ofNat, Complex.conj_ofReal]
    ring
  rw [show conj ((matrixLatticePair r).Λ s) = (matrixLatticePair r).Λ (conj s) from
    (matrixLattice_schwarz r s).symm, hconj, matrixLattice_FE]

/-- Axis reality: the completed transformation law transform is real on the central axis, every rank. -/
theorem matrixLattice_axis_im_zero (r : ℕ) (t : ℝ) :
    ((matrixLatticePair r).Λ
      ((((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I)).im = 0 :=
  Complex.conj_eq_iff_im.mp (matrixLattice_standingWave r t).symm

/-- The entire part carries the same standing wave: the pole terms are conjugation-
symmetric on the axis. -/
theorem matrixLattice_standingWave₀ (r : ℕ) (t : ℝ) :
    (matrixLatticePair r).Λ₀ ((((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I)
      = conj ((matrixLatticePair r).Λ₀
          ((((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I)) := by
  set s : ℂ := (((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I with hsdef
  have hconj : conj s = (((matrixLatticePair r).k : ℝ) : ℂ) - s := by
    rw [hsdef, map_add, map_mul, Complex.conj_I, map_div₀, Complex.conj_ofReal,
      map_ofNat, Complex.conj_ofReal]
    ring
  rw [lambda_decomp r s, map_add, map_add, map_div₀, map_div₀, map_one, map_sub,
    Complex.conj_ofReal, ← matrixLattice_standingWave r t]
  rw [show conj s = (((matrixLatticePair r).k : ℝ) : ℂ) - s from hconj]
  ring

/-- **Certifier (a)'s weak-side pipeline, closed at every rank**: the entire part, the
self-dual completed functional equation, global Schwarz reality, and the standing wave
hold simultaneously for the matrix-lattice family — one quantified conclusion, uniform in
the rank. -/
theorem lattice_weak_rung (r : ℕ) :
    Differentiable ℂ (matrixLatticePair r).Λ₀ ∧
    (∀ s : ℂ, (matrixLatticePair r).Λ ((((matrixLatticePair r).k : ℝ) : ℂ) - s)
      = (matrixLatticePair r).Λ s) ∧
    (∀ s : ℂ, (matrixLatticePair r).Λ (conj s) = conj ((matrixLatticePair r).Λ s)) ∧
    (∀ t : ℝ, (matrixLatticePair r).Λ
        ((((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I)
      = conj ((matrixLatticePair r).Λ
          ((((matrixLatticePair r).k : ℝ) : ℂ) / 2 + (t : ℂ) * I))) :=
  ⟨(matrixLatticePair r).differentiable_Λ₀,
   matrixLattice_FE r,
   matrixLattice_schwarz r,
   matrixLattice_standingWave r⟩

end CriticalLinePhasor.LatticeStandingWave

#print axioms CriticalLinePhasor.LatticeStandingWave.mellin_ofReal_conj
#print axioms CriticalLinePhasor.LatticeStandingWave.matrixLattice_schwarz
#print axioms CriticalLinePhasor.LatticeStandingWave.matrixLatticePair_symm_eq
#print axioms CriticalLinePhasor.LatticeStandingWave.matrixLattice_FE
#print axioms CriticalLinePhasor.LatticeStandingWave.matrixLattice_standingWave
#print axioms CriticalLinePhasor.LatticeStandingWave.matrixLattice_axis_im_zero
#print axioms CriticalLinePhasor.LatticeStandingWave.matrixLattice_standingWave₀
#print axioms CriticalLinePhasor.LatticeStandingWave.lattice_weak_rung
