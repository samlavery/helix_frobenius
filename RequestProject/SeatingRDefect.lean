import RequestProject.SeatingFlipConservation
import RequestProject.ResidueJump

/-!
# The R-branch defect ledger: the same integer `D`, from residues

The count register (`SeatingFlipConservation`) produced the defect
`D(box) = strip census − flip supply` from chain counting.  This file makes
the SAME integer appear independently on the R-normal-form branch, as residue
bookkeeping of `R = −Ξ′/Ξ − (detector sum)`:

* the analytic mass at each census zero is its ξ-order — the `ξ′/ξ` residue
  (`xi_logDeriv_residue`, via the compiled `logDeriv_residue_eq_order`);
* the detector books `1` at a zero exactly when the readout changes sign
  there, and that happens exactly at ODD ξ-order
  (`sign_change_window_iff_odd` — `odd_mult_flips` gives odd ⟹ flip, the new
  `even_mult_no_flip` gives even ⟹ no flip; `flipIndicator_eq_one_iff`);
* the difference is the per-zero R-residue weight `m − [detected]`, realized
  analytically by the z-chart packet residues (`packet_residue`: every
  compiled packet `c·2z/(γ²−z²)` has residue `−c` at `γ`; `c = m−1` for a
  detected odd zero — vanishing at `m = 1` — and `c = m` for the invisible
  classes).

The ledger: `rBoxLedger (box) = Σ_census (xiOrderNat − flipIndicator)`, with
the exact mass partition `Σ xiOrderNat = rBoxLedger + Σ flipIndicator`
(`census_mass_partition`) — total analytic mass = detector supply + defect.
`rBoxLedger = 0` forces every box zero on-line and SIMPLE
(`rDefectWeight_eq_zero_iff`), so the R-branch door closes through the
seating door, independently of the flip-chain door:
`rh_of_high_R_defect` — R-defect vanishing above the ladder ⟹ RH.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **Register bridge**: off the real axis the Zeta23 ζ-multiplicity IS the
ξ-order — the count-register weight and the R-branch weight are one number. -/
theorem zeroMult_eq_xiOrderNat {z : ℂ} (hz : z.im ≠ 0) :
    Zeta23.zeroMult z = ZD.xiOrderNat z := by
  unfold Zeta23.zeroMult ZD.xiOrderNat analyticOrderNatAt
  rw [CriticalLinePhasor.DVP.xi_order_eq_zeta_order hz]

/-- **The detector-pole characterization**: an on-line zero produces sign
changes of the readout in all small symmetric windows IFF its ξ-order is odd.
Forward is the new even-repulsion; backward is the compiled odd-flip. -/
theorem sign_change_window_iff_odd {γ : ℝ} (hγ : γ ≠ 0)
    (hmem : linePt γ ∈ ZD.NontrivialZeros) :
    (∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
        XiLine (γ - δ) * XiLine (γ + δ) < 0)
      ↔ Odd (ZD.xiOrderNat (linePt γ)) := by
  have him : (linePt γ).im ≠ 0 := by
    rw [linePt_im]
    exact hγ
  rw [← zeroMult_eq_xiOrderNat him]
  constructor
  · rintro ⟨ε, hε, hflip⟩
    by_contra hodd
    have heven : Even (Zeta23.zeroMult (linePt γ)) :=
      (Nat.even_or_odd _).resolve_right hodd
    obtain ⟨ε', hε', hprop⟩ := even_mult_no_flip hγ hmem heven
    have hmin : 0 < min ε ε' := lt_min hε hε'
    have hδ0 : 0 < min ε ε' / 2 := by linarith
    have hδε : min ε ε' / 2 < ε := by
      have h := min_le_left ε ε'
      linarith
    have hδε' : min ε ε' / 2 < ε' := by
      have h := min_le_right ε ε'
      linarith
    have h1 := hflip (min ε ε' / 2) hδ0 hδε
    have h2 := (hprop (min ε ε' / 2) hδ0 hδε').1
    linarith
  · exact fun hodd => odd_mult_flips hγ hmem hodd

/-- **The analytic mass at a zero**: `ξ′/ξ` has residue exactly the ξ-order —
the `Σ m` side of the ledger, per pole. -/
theorem xi_logDeriv_residue {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    Tendsto (fun s => (s - ρ) * logDeriv ZD.riemannXi s) (𝓝[≠] ρ)
      (𝓝 ((ZD.xiOrderNat ρ : ℂ))) := by
  have hA : AnalyticAt ℂ ZD.riemannXi ρ :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ ρ (Set.mem_univ _)
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere ρ
  have hm : analyticOrderAt ZD.riemannXi ρ = (ZD.xiOrderNat ρ : ℕ∞) := by
    unfold ZD.xiOrderNat analyticOrderNatAt
    exact (ENat.coe_toNat hne).symm
  exact ResidueJump.logDeriv_residue_eq_order hA hm

/-- **The two-point packet kernel has residue `−1`** at its real pole: the
z-chart normal-form packets are `c·(2z/(γ²−z²))`, so every packet books `−c`
at `γ`. -/
theorem two_point_kernel_residue {γ : ℝ} (hγ : γ ≠ 0) :
    Tendsto (fun z : ℂ => (z - (γ:ℂ)) * (2 * z / ((γ:ℂ)^2 - z^2)))
      (𝓝[≠] ((γ:ℂ))) (𝓝 (-1)) := by
  have hγc : ((γ:ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  have h2γ : ((γ:ℂ)) + γ ≠ 0 := by
    intro h
    apply hγc
    have h2 : (2:ℂ) * γ = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h2' | h0
    · exact absurd h2' two_ne_zero
    · exact h0
  have hnegne : ((γ:ℂ)) ≠ -(γ:ℂ) := by
    intro h
    apply h2γ
    linear_combination h
  have hev : (fun z : ℂ => -(2 * z) / (z + γ))
      =ᶠ[𝓝[≠] ((γ:ℂ))]
        (fun z : ℂ => (z - (γ:ℂ)) * (2 * z / ((γ:ℂ)^2 - z^2))) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hnegne),
      self_mem_nhdsWithin] with z hz1 hz2
    have hzγ : z - (γ:ℂ) ≠ 0 := sub_ne_zero.mpr hz2
    have hzpγ : z + (γ:ℂ) ≠ 0 := fun h => hz1 (eq_neg_of_add_eq_zero_left h)
    have hd : ((γ:ℂ))^2 - z^2 ≠ 0 := by
      have hfac : ((γ:ℂ))^2 - z^2 = -((z - γ) * (z + γ)) := by ring
      rw [hfac]
      exact neg_ne_zero.mpr (mul_ne_zero hzγ hzpγ)
    field_simp
    ring
  have hval : -(2 * ((γ:ℂ))) / ((γ:ℂ) + γ) = -1 := by
    rw [div_eq_iff h2γ]
    ring
  have hc : ContinuousAt (fun z : ℂ => -(2 * z) / (z + γ)) ((γ:ℂ)) := by
    apply ContinuousAt.div
    · exact (continuous_const.mul continuous_id).neg.continuousAt
    · exact continuousAt_id.add continuousAt_const
    · exact h2γ
  have hlim : Tendsto (fun z : ℂ => -(2 * z) / (z + γ))
      (𝓝[≠] ((γ:ℂ))) (𝓝 (-1)) := by
    have h : Tendsto (fun z : ℂ => -(2 * z) / (z + γ)) (𝓝[≠] ((γ:ℂ)))
        (𝓝 (-(2 * ((γ:ℂ))) / ((γ:ℂ) + γ))) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hval] at h
  exact Filter.Tendsto.congr' hev hlim

/-- **Packet residue**: the compiled normal-form packet `c·2z/(γ²−z²)` has
residue `−c` at `γ`.  With `c = m − 1` (detected odd zero) the residue
vanishes iff `m = 1`; with `c = m` (even-order or off-line mirror trace) it
never does — the per-pole appearance of the defect weight. -/
theorem packet_residue (c : ℂ) {γ : ℝ} (hγ : γ ≠ 0) :
    Tendsto (fun z : ℂ => (z - (γ:ℂ)) * (c * (2 * z / ((γ:ℂ)^2 - z^2))))
      (𝓝[≠] ((γ:ℂ))) (𝓝 (-c)) := by
  have h := (two_point_kernel_residue hγ).const_mul c
  have hfun : (fun z : ℂ => c * ((z - (γ:ℂ)) * (2 * z / ((γ:ℂ)^2 - z^2))))
      = fun z : ℂ => (z - (γ:ℂ)) * (c * (2 * z / ((γ:ℂ)^2 - z^2))) := by
    funext z
    ring
  rw [hfun] at h
  have hcm : c * (-1) = -c := by ring
  rwa [hcm] at h

open Classical in
/-- The detector's booking at a point: `1` on an on-line zero of odd ξ-order,
`0` otherwise. -/
def flipIndicator (ρ : ℂ) : ℕ :=
  if ρ.re = 1/2 ∧ Odd (ZD.xiOrderNat ρ) then 1 else 0

/-- **The indicator IS the detector pole**: for an on-line zero, the ledger's
booking is `1` exactly when the readout genuinely changes sign there. -/
theorem flipIndicator_eq_one_iff {γ : ℝ} (hγ : γ ≠ 0)
    (hmem : linePt γ ∈ ZD.NontrivialZeros) :
    flipIndicator (linePt γ) = 1
      ↔ ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
          XiLine (γ - δ) * XiLine (γ + δ) < 0 := by
  unfold flipIndicator
  by_cases hodd : Odd (ZD.xiOrderNat (linePt γ))
  · rw [if_pos ⟨linePt_re γ, hodd⟩]
    constructor
    · intro _
      exact (sign_change_window_iff_odd hγ hmem).mpr hodd
    · intro _
      rfl
  · rw [if_neg (fun hc => hodd hc.2)]
    constructor
    · intro h
      exact absurd h (by omega)
    · intro hflip
      exact absurd ((sign_change_window_iff_odd hγ hmem).mp hflip) hodd

/-- The per-zero R-defect weight: analytic mass minus detector booking. -/
def rDefectWeight (ρ : ℂ) : ℕ := ZD.xiOrderNat ρ - flipIndicator ρ

/-- The R-branch defect ledger of a box: the residue bookkeeping of the
normal form `R = −Ξ′/Ξ − (detector sum)`, summed over the strip census. -/
def rBoxLedger (T₁ T₂ : ℝ) : ℕ :=
  ∑ ρ ∈ (stripBox_finite T₁ T₂).toFinset, rDefectWeight ρ

/-- **The weight vanishes exactly on the invisible-free class**: a census
zero has zero R-defect iff it is ON-LINE and SIMPLE. -/
theorem rDefectWeight_eq_zero_iff {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    rDefectWeight ρ = 0 ↔ ρ.re = 1/2 ∧ ZD.xiOrderNat ρ = 1 := by
  have hpos := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ
  unfold rDefectWeight flipIndicator
  by_cases hc : ρ.re = 1/2 ∧ Odd (ZD.xiOrderNat ρ)
  · rw [if_pos hc]
    constructor
    · intro h
      exact ⟨hc.1, by omega⟩
    · intro h
      omega
  · rw [if_neg hc]
    constructor
    · intro h
      exact absurd h (by omega)
    · rintro ⟨h1, h2⟩
      exact absurd ⟨h1, by rw [h2]; exact odd_one⟩ hc

/-- **The mass partition** — T★ in the R register, per box, exact:
total analytic mass (`Σ` ξ-orders = `Σ` residues of `ξ′/ξ`) splits into the
detector supply plus the R-defect.  Nothing estimated. -/
theorem census_mass_partition (T₁ T₂ : ℝ) :
    ∑ ρ ∈ (stripBox_finite T₁ T₂).toFinset, ZD.xiOrderNat ρ
      = rBoxLedger T₁ T₂
        + ∑ ρ ∈ (stripBox_finite T₁ T₂).toFinset, flipIndicator ρ := by
  unfold rBoxLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hmem : ρ ∈ stripBox T₁ T₂ := (stripBox_finite T₁ T₂).mem_toFinset.mp hρ
  have hpos := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hmem.1
  unfold rDefectWeight flipIndicator
  by_cases hc : ρ.re = 1/2 ∧ Odd (ZD.xiOrderNat ρ)
  · rw [if_pos hc]
    omega
  · rw [if_neg hc]
    omega

/-- **A vanishing ledger empties the off-line class**: `rBoxLedger = 0`
forces the box's strip census onto the line (and simple, though only
on-line-ness is consumed here). -/
theorem strip_eq_onLine_of_rBoxLedger_zero {T₁ T₂ : ℝ}
    (h : rBoxLedger T₁ T₂ = 0) : stripBox T₁ T₂ = onLineBox T₁ T₂ := by
  apply Set.Subset.antisymm
  · intro ρ hρ
    have hmem : ρ ∈ (stripBox_finite T₁ T₂).toFinset :=
      (stripBox_finite T₁ T₂).mem_toFinset.mpr hρ
    have hzero : rDefectWeight ρ = 0 := by
      unfold rBoxLedger at h
      exact (Finset.sum_eq_zero_iff.mp h) ρ hmem
    exact ⟨hρ, ((rDefectWeight_eq_zero_iff hρ.1).mp hzero).1⟩
  · exact fun ρ hρ => hρ.1

/-- **RH from the R-branch defect**: the residue ledger vanishing in every
box above the compiled ladder forces every nontrivial zero onto the critical
line — through the seating door, independently of the flip-chain door. -/
theorem rh_of_high_R_defect
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ → rBoxLedger T₁ T₂ = 0) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  apply rh_of_high_seating
  intro T₁ T₂ hT₁ hT
  rw [strip_eq_onLine_of_rBoxLedger_zero (h T₁ T₂ hT₁ hT)]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.zeroMult_eq_xiOrderNat
#print axioms CriticalLinePhasor.SeatingLedger.sign_change_window_iff_odd
#print axioms CriticalLinePhasor.SeatingLedger.xi_logDeriv_residue
#print axioms CriticalLinePhasor.SeatingLedger.two_point_kernel_residue
#print axioms CriticalLinePhasor.SeatingLedger.packet_residue
#print axioms CriticalLinePhasor.SeatingLedger.flipIndicator_eq_one_iff
#print axioms CriticalLinePhasor.SeatingLedger.rDefectWeight_eq_zero_iff
#print axioms CriticalLinePhasor.SeatingLedger.census_mass_partition
#print axioms CriticalLinePhasor.SeatingLedger.strip_eq_onLine_of_rBoxLedger_zero
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_R_defect
