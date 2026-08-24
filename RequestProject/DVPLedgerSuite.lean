import RequestProject.DVPClockLedger
import RequestProject.DVPSeatSupply
import RequestProject.DVPCellMass

/-!
# The 2026-08-20 ledger suite — one entry point

The day's headline theorems (ledgers 392–422), re-exported with a single
axiom audit.  Everything below is UNCONDITIONAL and compiled from
`{propext, Classical.choice, Quot.sound}`.

* Littlewood 1924, `N_all`-form: `|∫₀ᵀ S_all| ≤ C(1+log(1+T))`.
* Riemann–von Mangoldt: `|N_all(T) − θ(T)/π − 1| ≤ 20 log T + 3`.
* Textbook RvM: `|N_all(T) − ((T/2π)log(T/2π) − T/2π) − 1| ≤ 20 log T + C`.
* θ asymptotic: `|θ(T) − ((T/2)log(T/2π) − T/2)| ≤ C`.
* Unit-window density: `N(T+1) − N(T) ≤ 41·log(T+2) + 6`.
* The o(T) registration input, and the two-residual reduction.
* The clock-measure ledger: `|∫ S_all·θ'/π| ≤ C(1+log(1+T))²`.
* The seat channel's K-supply: deep-window mass `≤ 41·log(Re w+3/2) + 6`.
-/

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

namespace CriticalLinePhasor.DVP

theorem suite_littlewood : LittlewoodBound := littlewoodBound_holds

theorem suite_rvm {T : ℝ} (h6 : Real.exp 6 ≤ T) (hT : GoodHeight T) :
    |(stripZeroCountMult T : ℝ) - theta T / Real.pi - 1|
      ≤ 20 * Real.log T + 3 := riemann_von_mangoldt h6 hT

theorem suite_rvm_classical :
    ∃ C : ℝ, ∀ T : ℝ, Real.exp 6 ≤ T → ∀ hT : GoodHeight T,
      |(stripZeroCountMult T : ℝ)
        - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi)) - 1|
      ≤ 20 * Real.log T + C := riemann_von_mangoldt_classical

theorem suite_theta_asymptotic :
    ∃ C : ℝ, ∀ T : ℝ, 10 ≤ T →
      |theta T - ((T/2) * Real.log (T/(2*Real.pi)) - T/2)| ≤ C :=
  theta_asymptotic

theorem suite_unit_window_density {T : ℝ} (hT : Real.exp 6 + 1 ≤ T) :
    (stripZeroCountMult (T + 1) : ℝ) - stripZeroCountMult T
      ≤ 41 * Real.log (T + 2) + 6 := zero_count_unit_window hT

theorem suite_o_input :
    (fun T => ∫ t in (0:ℝ)..T,
        (CriticalLinePhasor.ResidueJump.Smult t
          + (offLineStripZeroCountMult t : ℝ)))
      =o[Filter.atTop] fun T : ℝ => T := littlewood_o_input_holds

theorem suite_two_residuals (hOff : OffLineMassLog) :
    ∃ c : ℕ → ℝ, c 0 = 10 ∧ Monotone c
      ∧ (∀ n, theta (c (n + 1)) - theta (c n) = Real.pi)
      ∧ (CriticalLinePhasor.ContourArgument.ClockCellMassBounded c →
          ∀ (T : ℝ) (hT : GoodHeight T),
            classicalSContour hT = CriticalLinePhasor.ResidueJump.Smult T) :=
  gram_registration_two_residuals hOff

theorem suite_clock_ledger :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 6 + 1 ≤ T →
      |∫ t in (10:ℝ)..T, SAll t * (clockRate t / Real.pi)|
        ≤ C * (1 + Real.log (1 + T))^2 := sall_clock_weighted_bound

theorem suite_seat_K_supply {w : ℂ} (hre : Real.exp 6 + 3/2 ≤ w.re) :
    Summable (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|} =>
      (ZD.xiOrderNat x.val.val : ℝ))
    ∧ (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|},
      (ZD.xiOrderNat x.val.val : ℝ))
      ≤ 41 * Real.log (w.re + 3/2) + 6 := deep_window_mass_bound hre

theorem suite_offline_iff :
    OffLineMassLog ↔ ∀ T : ℝ, offLineStripZeroCountMult T = 0 :=
  offLineMassLog_iff_offLine_zero

theorem suite_cell_mass {a b : ℝ}
    (ha : Real.exp 6 + 1 ≤ a) (hab : a ≤ b)
    (hθ : theta b - theta a = Real.pi) :
    ∫ t in a..b, |SAll t| ≤ 240 :=
  cell_sall_abs_mass_bound ha hab hθ

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.suite_offline_iff
#print axioms CriticalLinePhasor.DVP.suite_cell_mass
#print axioms CriticalLinePhasor.DVP.suite_littlewood
#print axioms CriticalLinePhasor.DVP.suite_rvm
#print axioms CriticalLinePhasor.DVP.suite_rvm_classical
#print axioms CriticalLinePhasor.DVP.suite_theta_asymptotic
#print axioms CriticalLinePhasor.DVP.suite_unit_window_density
#print axioms CriticalLinePhasor.DVP.suite_o_input
#print axioms CriticalLinePhasor.DVP.suite_two_residuals
#print axioms CriticalLinePhasor.DVP.suite_clock_ledger
#print axioms CriticalLinePhasor.DVP.suite_seat_K_supply
end AxiomAudit
