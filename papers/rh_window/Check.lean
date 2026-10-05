import RequestProject.DVPLadder
import RequestProject.DVPLadder1269o2
import RequestProject.PNTWindowBridge
import RequestProject.OneAssumptionRH
import RequestProject.FiberZeroMidpointWindow

/-!
# Check file for "The Riemann hypothesis up to height 634.5, checked by the Lean kernel"

Run from the repository root (loads the full window: ~6 GB, ~5 min on an M2 Max):

    env LEAN_NUM_THREADS=2 nice -n 10 lake env lean papers/rh_window/Check.lean

Every `#print axioms` line must read `[propext, Classical.choice, Quot.sound]`.
-/

-- Theorem 1 (the window) and the fast slice
#check @CriticalLinePhasor.DVP.online_below_1269o2
#print axioms CriticalLinePhasor.DVP.online_below_1269o2
#check @CriticalLinePhasor.DVP.online_below_58
#print axioms CriticalLinePhasor.DVP.online_below_58

-- Theorem 2 (the census)
#check @CriticalLinePhasor.DVP.stripZeroCountMult_1269o2
#print axioms CriticalLinePhasor.DVP.stripZeroCountMult_1269o2

-- Theorem 3 (simplicity) and Theorem 4 (PNT+'s predicate)
#check @VerifiedWindow.xiOrder_eq_one_below_1269o2
#print axioms VerifiedWindow.xiOrder_eq_one_below_1269o2
#check @VerifiedWindow.pnt_RH_up_to_1269o2
#print axioms VerifiedWindow.pnt_RH_up_to_1269o2

-- The one-hypothesis interface (Section 4)
#check @OneAssumptionRH.riemannHypothesis_of_oneAssumption
#print axioms OneAssumptionRH.riemannHypothesis_of_oneAssumption
#check @CarrierReadout.oneVanishingPerHeight3D_below
#print axioms CarrierReadout.oneVanishingPerHeight3D_below
