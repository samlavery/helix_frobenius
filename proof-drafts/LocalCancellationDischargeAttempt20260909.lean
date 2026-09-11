import RequestProject.WarpNoResidue

open Complex Filter Topology
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.WarpNoResidue

#print axioms CriticalLinePhasor.WarpNoResidue.warpedSeat_no_residue

-- Strategy B's local step: test whether the cancelled full-seat residue kills a
-- multiplicity belonging to the off-line correction sum.
example (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) (hoff : ρ.re ≠ 1 / 2) :
    ZD.xiOrderNat ρ = 0 := by
  have hlocal := (warpedSeat_no_residue (L := 1) (by norm_num) hρ).limUnder_eq
  have horder : (ZD.xiOrderNat ρ : ℂ) = 0 := by
    exact hlocal
  exact_mod_cast horder
