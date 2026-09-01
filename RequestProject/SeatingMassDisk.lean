import RequestProject.SeatingMassLedger

/-!
# The depth-disk law: the mass of any mirror pair, in closed form

The exact law behind the ledger (pencil + probe `tmp/att549`, boundary
exact): for ANY zero position `ρ = β + iγ`, the FE-mirror pair
`{ρ, 1−ρ̄}` (same height, reflected depth) contributes the floor

  `Re[(s−ρ)⁻¹ + (s−(1−ρ̄))⁻¹]
     = 2(σ−½)·[(σ−½)² + (t−γ)² − (β−½)²] / (|s−ρ|²·|s−(1−ρ̄)|²)`

— odd prefactor times an even mass whose sign is EXACTLY the position of
`s` relative to the **depth-disk**: the disk about `½+iγ` of radius equal
to the zero's depth `|β−½|`.  Corollaries: the pair's mass is nonnegative
at every point outside the closed depth-disk (no hypothesis on `β`); an
on-line pair (`β = ½`, degenerate disk) never obstructs anywhere.  The
mass hypothesis's failure set is exactly the union of the open depth-disks
of the off-line zeros it forbids.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- normSq of a shifted point, in real coordinates. -/
theorem normSq_shift (β γ : ℝ) (s : ℂ) :
    Complex.normSq (s - (β + γ * I)) = (s.re - β)^2 + (s.im - γ)^2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **The depth-disk law**: the mirror pair's floor in closed form. -/
theorem mirror_pair_floor_law (β γ : ℝ) {s : ℂ}
    (h1 : s ≠ β + γ * I) (h2 : s ≠ (1 - β) + γ * I) :
    ((s - (β + γ * I))⁻¹ + (s - ((1 - β) + γ * I))⁻¹).re
      = 2 * (s.re - 1/2) *
          ((s.re - 1/2)^2 + (s.im - γ)^2 - (β - 1/2)^2)
        / (((s.re - β)^2 + (s.im - γ)^2)
            * ((s.re - (1 - β))^2 + (s.im - γ)^2)) := by
  have hn1 : (s.re - β)^2 + (s.im - γ)^2 ≠ 0 := by
    rw [← normSq_shift]
    intro h
    exact sub_ne_zero.mpr h1 (Complex.normSq_eq_zero.mp h)
  have hn2 : (s.re - (1 - β))^2 + (s.im - γ)^2 ≠ 0 := by
    have hns := normSq_shift (1 - β) γ s
    rw [← hns]
    intro h
    exact sub_ne_zero.mpr (show s ≠ ((1 - β : ℝ) : ℂ) + γ * I by
      exact_mod_cast h2) (Complex.normSq_eq_zero.mp h)
  rw [Complex.add_re, point_floor_re, point_floor_re]
  have e1 : ((β:ℂ) + γ * I).re = β := by simp
  have e2 : (((1:ℂ) - β) + γ * I).re = 1 - β := by
    simp
  rw [normSq_shift]
  have f2 : Complex.normSq (s - ((1 - β) + γ * I))
      = (s.re - (1 - β))^2 + (s.im - γ)^2 := by
    have := normSq_shift (1 - β) γ s
    exact_mod_cast this
  rw [f2, e1]
  rw [show (((1:ℂ) - ↑β) + ↑γ * I).re = 1 - β from e2]
  field_simp
  ring

/-- **Mass nonnegativity outside the depth-disk** — for EVERY pair, on-line
or off: at any point outside the closed depth-disk, the pair's even factor
is nonnegative. -/
theorem mirror_pair_mass_nonneg_outside (β γ : ℝ) {s : ℂ}
    (hdisk : (β - 1/2)^2 ≤ (s.re - 1/2)^2 + (s.im - γ)^2)
    (h1 : s ≠ β + γ * I) (h2 : s ≠ (1 - β) + γ * I) :
    0 ≤ ((s - (β + γ * I))⁻¹ + (s - ((1 - β) + γ * I))⁻¹).re
        / (s.re - 1/2) := by
  rw [mirror_pair_floor_law β γ h1 h2]
  have hD : (0:ℝ) ≤ (s.re - 1/2)^2 + (s.im - γ)^2 - (β - 1/2)^2 := by
    linarith
  have hnn : (0:ℝ) ≤ ((s.re - β)^2 + (s.im - γ)^2)
      * ((s.re - (1 - β))^2 + (s.im - γ)^2) := by positivity
  rcases lt_trichotomy (s.re - 1/2) 0 with hc | hc | hc
  · apply div_nonneg_iff.mpr
    refine Or.inr ⟨?_, hc.le⟩
    apply div_nonpos_of_nonpos_of_nonneg _ hnn
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hD
  · rw [hc]
    simp
  · apply div_nonneg _ hc.le
    apply div_nonneg _ hnn
    exact mul_nonneg (by linarith) hD


/-- **Only zeros at nearby height can obstruct the mass.**  Unconditionally
(using just `0 < β < 1`, the strip): every FE-mirror pair whose ordinate is
at least `1/2` away from the point's height contributes NONNEGATIVELY to
the seat mass — its depth-disk has radius `< 1/2` and cannot reach.
So `seatMass ≥ 0` is not a global condition: at each height only the
`O(log t)` zeros within half a unit can possibly obstruct, and every other
pair in the ledger is already on the right side.  Multiplicity is
irrelevant throughout (it enters as a positive weight). -/
theorem far_height_pair_mass_nonneg (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    {s : ℂ} (hfar : 1/2 ≤ |s.im - γ|) :
    0 ≤ ((s - (β + γ * I))⁻¹ + (s - ((1 - β) + γ * I))⁻¹).re
        / (s.re - 1/2) := by
  have him : (((β : ℂ) + γ * I)).im = γ := by simp
  have him2 : ((((1 : ℂ) - β) + γ * I)).im = γ := by simp
  have hne : s.im ≠ γ := by
    intro h
    rw [h] at hfar
    simp at hfar
    linarith
  have h1 : s ≠ (β : ℂ) + γ * I := by
    intro h
    apply hne
    rw [h, him]
  have h2 : s ≠ ((1 : ℂ) - β) + γ * I := by
    intro h
    apply hne
    rw [h, him2]
  apply mirror_pair_mass_nonneg_outside β γ _ h1 h2
  have hb : (β - 1/2) ^ 2 < 1/4 := by nlinarith
  have hg : (1:ℝ)/4 ≤ (s.im - γ) ^ 2 := by
    have := sq_abs (s.im - γ)
    nlinarith [abs_nonneg (s.im - γ), hfar]
  nlinarith [sq_nonneg (s.re - 1/2)]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.mirror_pair_floor_law
#print axioms CriticalLinePhasor.SeatingLedger.mirror_pair_mass_nonneg_outside
#print axioms CriticalLinePhasor.SeatingLedger.far_height_pair_mass_nonneg
