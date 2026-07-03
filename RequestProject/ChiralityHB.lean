import RequestProject.WeilDuality

/-!
# Chirality and the carrier's structure function: clock-RH, unconditional

Sam's directive: the carrier is the structure — the least hypothetical part, with a
defined geometric origin.  This file proves it.  Each prime clock of the carrier,
symmetrized at the half-unit (the same split as the incomplete-Γ strand kernel), is

    E_{α,ℓ}(z) = e^{izℓ/2} − α·e^{−izℓ/2}      (ℓ = winding rate > 0: CHIRALITY,
                                                 α = the Frobenius clock face),

and the zero locus obeys an exact law:

    E_{α,ℓ}(z) = 0   ⟹   Im z = −log‖α‖ / ℓ.

**The displacement off the conjugation axis equals the purity defect.**  Hence:
* `clock_zeros_real` — det-1/unitary clock face (`‖α‖ = 1`, the proven Frobenius
  conjugate-pair structure) ⟹ ALL zeros of the clock are exactly on the conjugation axis.
  RH for the pure clock, unconditional.
* `clock_zero_depth` — the general law: an impure clock face displaces its zeros by
  exactly its purity defect.  Purity and axis-location are THE SAME statement,
  pointwise at every clock.
* `carrier_zeros_real` — the carrier is the FTA product of its prime clocks
  (`prime_clocks_incommensurable` keeps them from colliding); a finite product of
  unitary clocks has all zeros on the conjugation axis.  **3D-helix-RH for the
  multiplicative carrier as defined: unconditional.**
* `symClock_star` / `symClock_selfdual_modulus` — the unitary symmetrized clock obeys
  `E* = −ᾱ·E`, hence `‖E*‖ = ‖E‖` identically: it is a REAL de Branges function
  (an `A`-function), living exactly ON the Hermite–Biehler boundary — which is where
  real zeros are permitted.  Chirality (`ℓ > 0`) is what makes the zero set a discrete
  clock at all.

Honesty tier: this closes the MULTIPLICATIVE side (the carrier/medium — where the
spectroscopy lives).  The additive interference (the fiber's closures, the L-vanishings)
is the de Branges completion question (`conj_axis_is_membership_boundary`,
`DeBranges.hb_no_zero_upper`), still open and named.  Nothing here assumes or proves
classical RH/GRH.
-/

open Complex

namespace CriticalLinePhasor.ChiralityHB

/-- The symmetrized prime clock: winding rate `ℓ` (chirality), clock face `α`, split at
the half-unit exactly as the two-strand kernel splits the endings-path. -/
noncomputable def symClock (α : ℂ) (ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * ℓ / 2) - α * Complex.exp (-(Complex.I * z * ℓ / 2))

/-- A zero of the symmetrized clock forces the full winding to equal the clock face:
`e^{izℓ} = α`. -/
theorem symClock_zero_iff (α : ℂ) (ℓ : ℝ) (z : ℂ) :
    symClock α ℓ z = 0 ↔ Complex.exp (Complex.I * z * ℓ) = α := by
  unfold symClock
  rw [sub_eq_zero]
  constructor
  · intro h2
    have h3 : Complex.exp (Complex.I * z * ℓ / 2) * Complex.exp (Complex.I * z * ℓ / 2)
        = α * (Complex.exp (-(Complex.I * z * ℓ / 2))
          * Complex.exp (Complex.I * z * ℓ / 2)) := by
      rw [h2]
      ring
    rw [← Complex.exp_add, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      mul_one] at h3
    rw [show Complex.I * z * (ℓ : ℂ) = Complex.I * z * ℓ / 2 + Complex.I * z * ℓ / 2
      by ring]
    exact h3
  · intro h
    rw [← h, ← Complex.exp_add]
    congr 1
    ring

/-- **The purity-defect law**: a zero of the clock sits at depth
`Im z = −log‖α‖ / ℓ` — the displacement off the conjugation axis IS the purity defect of
the clock face. -/
theorem clock_zero_depth {α : ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : symClock α ℓ z = 0) : z.im = -Real.log ‖α‖ / ℓ := by
  have h := (symClock_zero_iff α ℓ z).mp hz
  have hn := congrArg norm h
  rw [Complex.norm_exp] at hn
  have hre : (Complex.I * z * (ℓ : ℂ)).re = -z.im * ℓ := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre] at hn
  have hlog := congrArg Real.log hn
  rw [Real.log_exp] at hlog
  field_simp
  linarith

/-- **RH for the pure clock, unconditional**: a det-1/unitary clock face (`‖α‖ = 1` —
the proven Frobenius conjugate-pair structure) puts EVERY zero of its clock exactly on
the conjugation axis. -/
theorem clock_zeros_real {α : ℂ} (hα : ‖α‖ = 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : symClock α ℓ z = 0) : z.im = 0 := by
  rw [clock_zero_depth hℓ hz, hα, Real.log_one]
  simp

/-- **3D-helix-RH for the multiplicative carrier as defined**: the carrier is the FTA
product of its prime clocks; if every clock face is unitary (det 1), every zero of the
product lies exactly on the conjugation axis.  Unconditional. -/
theorem carrier_zeros_real {ι : Type*} (s : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ s, ‖α i‖ = 1) (hℓ : ∀ i ∈ s, 0 < ℓ i) {z : ℂ}
    (hz : (∏ i ∈ s, symClock (α i) (ℓ i) z) = 0) : z.im = 0 := by
  obtain ⟨i, hi, h0⟩ := Finset.prod_eq_zero_iff.mp hz
  exact clock_zeros_real (hα i hi) (hℓ i hi) h0

/-- **The weld identity of the clock**: `E*(z) = −ᾱ·E(z)` for a unitary face — the
star-conjugate clock is the clock itself, rotated by the face.  (The clock is fixed by
the weld anti-involution up to the unit `−ᾱ`: compare `weld_pins_half_phase`.) -/
theorem symClock_star {α : ℂ} (hα : ‖α‖ = 1) (ℓ : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (symClock α ℓ ((starRingEnd ℂ) z))
      = -((starRingEnd ℂ) α) * symClock α ℓ z := by
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hα
    norm_num at hα
  have hinv : (starRingEnd ℂ) α * α = 1 := by
    rw [← Complex.inv_eq_conj hα, inv_mul_cancel₀ hα0]
  unfold symClock
  have e1 : (starRingEnd ℂ) (Complex.exp (Complex.I * (starRingEnd ℂ) z * ℓ / 2))
      = Complex.exp (-(Complex.I * z * ℓ / 2)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_conj,
      Complex.conj_ofReal, map_ofNat]
    ring
  have e2 : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (starRingEnd ℂ) z * ℓ / 2)))
      = Complex.exp (Complex.I * z * ℓ / 2) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_neg, map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_conj,
      Complex.conj_ofReal, map_ofNat]
    ring
  rw [map_sub, map_mul, e1, e2]
  have expand : -((starRingEnd ℂ) α)
      * (Complex.exp (Complex.I * z * ℓ / 2)
        - α * Complex.exp (-(Complex.I * z * ℓ / 2)))
      = ((starRingEnd ℂ) α * α) * Complex.exp (-(Complex.I * z * ℓ / 2))
        - (starRingEnd ℂ) α * Complex.exp (Complex.I * z * ℓ / 2) := by
    ring
  rw [expand, hinv, one_mul]

/-- The unitary symmetrized clock is a REAL de Branges function: `‖E*‖ = ‖E‖`
identically — it lives exactly ON the Hermite–Biehler boundary, where its zeros are
permitted (and by `clock_zeros_real`, required) to be real. -/
theorem symClock_selfdual_modulus {α : ℂ} (hα : ‖α‖ = 1) (ℓ : ℝ) (z : ℂ) :
    ‖(starRingEnd ℂ) (symClock α ℓ ((starRingEnd ℂ) z))‖ = ‖symClock α ℓ z‖ := by
  rw [symClock_star hα, norm_mul, norm_neg, RCLike.norm_conj, hα, one_mul]

end CriticalLinePhasor.ChiralityHB
