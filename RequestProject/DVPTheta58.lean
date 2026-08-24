import RequestProject.DVPTheta30Head

/-!
# θ(58): the count-height clock value

`θ(58) = θ(30) + [M(58) − M(30)] ± 14/87` (the γ-free increment 371), with
`M(58) − M(30) = (58·log 29 − 30·log 15 − 28·log π − 28)/2` — two fresh log
certificates. Result: `θ(58) + 7.5π = 58.636 ± 0.272`, giving the census
window `N(58) ∈ (11.58, 12.76)` once `|S(58)| < ½`.
-/

open CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `3.3672 ≤ log 29 ≤ 3.3674` (order-9 exp certs, shift 3). -/
theorem log_29_enclosure :
    ((33672/10000 : ℚ) : ℝ) ≤ Real.log 29
      ∧ Real.log 29 ≤ ((33674/10000 : ℚ) : ℝ) := by
  constructor
  · rw [show ((29:ℝ)) = (((29:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 29) (by norm_num) ?_
      (le_of_lt (by
        calc (((29:ℕ)):ℝ) = 29 := by norm_num
          _ < Real.exp 29 := by nlinarith [Real.add_one_le_exp (29:ℝ)]))).1
    have henc := exp_enclosure (x := (3672/10000 : ℚ))
      (by norm_num) (n := 9) (by norm_num)
    have hτ : |Real.exp ((3672/10000 : ℚ) : ℝ)
        - ((expTaylor (3672/10000) 9 : ℚ) : ℝ)| ≤ ((1/10^7 : ℚ) : ℝ) := by
      have hb : |((3672/10000 : ℚ) : ℝ)| ^ 9
          * (((9 : ℕ).succ : ℝ) / (((9 : ℕ).factorial : ℝ) * 9))
          ≤ ((1/10^7 : ℚ) : ℝ) := by
        rw [show |((3672/10000 : ℚ) : ℝ)| = ((3672/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_upper_shift (x := (33672/10000 : ℚ)) 3
      (by
        have hx : ((33672/10000 : ℚ) - (3 : ℕ) : ℚ) = 3672/10000 := by
          norm_num
        rw [hx]
        exact hτ)
    refine le_trans hshift ?_
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
  · rw [show ((29:ℝ)) = (((29:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 29) (by norm_num)
      (by
        calc Real.exp ((0:ℚ) : ℝ) = 1 := by norm_num [Real.exp_zero]
          _ ≤ (((29:ℕ)):ℝ) := by norm_num) ?_).2
    have henc := exp_enclosure (x := (3674/10000 : ℚ))
      (by norm_num) (n := 9) (by norm_num)
    have hτ : |Real.exp ((3674/10000 : ℚ) : ℝ)
        - ((expTaylor (3674/10000) 9 : ℚ) : ℝ)| ≤ ((1/10^7 : ℚ) : ℝ) := by
      have hb : |((3674/10000 : ℚ) : ℝ)| ^ 9
          * (((9 : ℕ).succ : ℝ) / (((9 : ℕ).factorial : ℝ) * 9))
          ≤ ((1/10^7 : ℚ) : ℝ) := by
        rw [show |((3674/10000 : ℚ) : ℝ)| = ((3674/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_lower_shift (x := (33674/10000 : ℚ)) 3
      (by
        have hx : ((33674/10000 : ℚ) - (3 : ℕ) : ℚ) = 3674/10000 := by
          norm_num
        rw [hx]
        exact hτ)
      (by norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial])
    refine le_trans ?_ hshift
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

/-- `2.7080 ≤ log 15 ≤ 2.7082` (order-9 exp certs, shift 2). -/
theorem log_15_enclosure :
    ((27080/10000 : ℚ) : ℝ) ≤ Real.log 15
      ∧ Real.log 15 ≤ ((27082/10000 : ℚ) : ℝ) := by
  constructor
  · rw [show ((15:ℝ)) = (((15:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 15) (by norm_num) ?_
      (le_of_lt (by
        calc (((15:ℕ)):ℝ) = 15 := by norm_num
          _ < Real.exp 15 := by nlinarith [Real.add_one_le_exp (15:ℝ)]))).1
    have henc := exp_enclosure (x := (7080/10000 : ℚ))
      (by norm_num) (n := 9) (by norm_num)
    have hτ : |Real.exp ((7080/10000 : ℚ) : ℝ)
        - ((expTaylor (7080/10000) 9 : ℚ) : ℝ)| ≤ ((1/10^6 : ℚ) : ℝ) := by
      have hb : |((7080/10000 : ℚ) : ℝ)| ^ 9
          * (((9 : ℕ).succ : ℝ) / (((9 : ℕ).factorial : ℝ) * 9))
          ≤ ((1/10^6 : ℚ) : ℝ) := by
        rw [show |((7080/10000 : ℚ) : ℝ)| = ((7080/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_upper_shift (x := (27080/10000 : ℚ)) 2
      (by
        have hx : ((27080/10000 : ℚ) - (2 : ℕ) : ℚ) = 7080/10000 := by
          norm_num
        rw [hx]
        exact hτ)
    refine le_trans hshift ?_
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]
  · rw [show ((15:ℝ)) = (((15:ℕ)):ℝ) by norm_num]
    refine (log_enclosure_nat (m := 15) (by norm_num)
      (by
        calc Real.exp ((0:ℚ) : ℝ) = 1 := by norm_num [Real.exp_zero]
          _ ≤ (((15:ℕ)):ℝ) := by norm_num) ?_).2
    have henc := exp_enclosure (x := (7082/10000 : ℚ))
      (by norm_num) (n := 9) (by norm_num)
    have hτ : |Real.exp ((7082/10000 : ℚ) : ℝ)
        - ((expTaylor (7082/10000) 9 : ℚ) : ℝ)| ≤ ((1/10^6 : ℚ) : ℝ) := by
      have hb : |((7082/10000 : ℚ) : ℝ)| ^ 9
          * (((9 : ℕ).succ : ℝ) / (((9 : ℕ).factorial : ℝ) * 9))
          ≤ ((1/10^6 : ℚ) : ℝ) := by
        rw [show |((7082/10000 : ℚ) : ℝ)| = ((7082/10000 : ℚ) : ℝ) from
          abs_of_pos (by norm_num)]
        push_cast
        norm_num [Nat.factorial]
      exact le_trans henc hb
    have hshift := exp_lower_shift (x := (27082/10000 : ℚ)) 2
      (by
        have hx : ((27082/10000 : ℚ) - (2 : ℕ) : ℚ) = 7082/10000 := by
          norm_num
        rw [hx]
        exact hτ)
      (by norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial])
    refine le_trans ?_ hshift
    push_cast
    norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

/-- **THE θ(58) ENCLOSURE**: `|θ(58) + (15/2)π − 58.636| ≤ 0.272`. -/
theorem theta58_enclosure :
    |theta 58 + (15/2) * Real.pi - 58636/1000| ≤ 272/1000 := by
  have hπ := Real.pi_pos
  have hinc := theta_increment_enclosure_from
    (T₁ := (30:ℝ)) (T := (58:ℝ)) (by norm_num) (by norm_num)
  have h30 := theta30_enclosure
  have h29 := log_29_enclosure
  have h15 := log_15_enclosure
  have hlp := log_pi_enclosure
  push_cast at h29 h15 hlp
  -- the M-difference in log form
  have hM58 : thetaMain 58 = (58 * (Real.log 29 - Real.log Real.pi) - 58)/2 := by
    rw [thetaMain]
    have harg : (58:ℝ)/(2*Real.pi) = 29/Real.pi := by
      field_simp
      ring
    rw [harg, Real.log_div (by norm_num) hπ.ne']
  have hM30 : thetaMain 30 = (30 * (Real.log 15 - Real.log Real.pi) - 30)/2 := by
    rw [thetaMain]
    have harg : (30:ℝ)/(2*Real.pi) = 15/Real.pi := by
      field_simp
      ring
    rw [harg, Real.log_div (by norm_num) hπ.ne']
  rw [hM58, hM30] at hinc
  obtain ⟨hincl, hincu⟩ := abs_le.mp hinc
  obtain ⟨h30l, h30u⟩ := abs_le.mp h30
  obtain ⟨h29l, h29u⟩ := h29
  obtain ⟨h15l, h15u⟩ := h15
  obtain ⟨hlpl, hlpu⟩ := hlp
  rw [abs_le]
  constructor
  · nlinarith [hincl, h30l, h29l, h15u, hlpu]
  · nlinarith [hincu, h30u, h29u, h15l, hlpl]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_29_enclosure
#print axioms CriticalLinePhasor.DVP.log_15_enclosure
#print axioms CriticalLinePhasor.DVP.theta58_enclosure
end AxiomAudit
