import RequestProject.NiceClosure

/-!
# The symmetric cube from one identity: the theta-wall derivation

Rung 4, upgraded past the package finish: the classical input is no longer the completed
analytic package but **one pointwise identity between two explicit theta functions** —
the §sym5 self-duality of the prescribed `Sym³` readouts — and the entire analytic
superstructure is machine-derived from it.

* `sym3Shifts` — the `Sym³` Deligne shifts `(n−½, 3(n−½))` of a weight-`2n` seed (odd
  rank: a pure `Γℂ`-pair, exactly the prescribed kernel's chart);
* `symrPair_dual_eq_primal` — the dual bank of the clock pair is the primal bank at
  every rank: the inverse multiset is the clock reversal;
* `sym3Source` — from the single reflection, the complete strong pair: every other field
  (local integrability, rapid decay at both ends) is compiled, none is hypothesized;
* `sym3_symmLambda_eq` — the constructed pair is its own contragredient: the completed
  identifications agree on the open half-plane, entirety globalizes;
* `sym3_package_of_theta` — **the derivation**: continuation, entirety, the functional
  equation `Λ(1−s) = ε·Λ(s)`, and the prescribed chart
  `Λ(s) = Γℂ(s+n−½)·Γℂ(s+3(n−½))·L(Sym³, s)` — all from the one identity;
* `tensor23_nice_of_theta` — rung 4 end to end: the degree-6 tensor object fully nice
  from the single identity, the seed factor discharged by the compiled anchor.

The even rank `Sym⁴` carries a `Γℝ`-factor in its classical chart, outside this file's
pure-`Γℂ` kernel; its one-identity finish at the mixed chart is
`ThetaMechanism.sym4_package_of_theta` (via `mechanismR` and the real clock), with
`sym4_wall_collapse` the product-level tie.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups LSeries.notation

namespace CriticalLinePhasor.Sym3ThetaWall

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.SymrBank
open CriticalLinePhasor.SymCubeQuartic CriticalLinePhasor.UniformTransport
open CriticalLinePhasor.SeedStandardRung CriticalLinePhasor.GenuineGL2Carrier
open CriticalLinePhasor.NiceClosure CriticalLinePhasor.CarrierTheta

variable {n : ℕ} {f : CuspForm 𝒮ℒ (2 * n : ℤ)}



/-- The `Sym³` Deligne shifts of a weight-`2n` seed: `(n−½, 3(n−½))`. -/
noncomputable def sym3Shifts (n : ℕ) : List ℂ :=
  [((standardShiftR n : ℝ) : ℂ), ((3 * standardShiftR n : ℝ) : ℂ)]

theorem sym3Shifts_ne (n : ℕ) : sym3Shifts n ≠ [] := by simp [sym3Shifts]

/-- **The dual bank of the clock pair is the primal bank, at every rank**: the inverse
weight multiset is the reversal of the clock. -/
theorem symrPair_dual_eq_primal (H : HeckeEigenData f) (r : ℕ) (j : ℕ) :
    cpsPolynomialDualCoeff (symrSatakePair H r) j
      = cpsPolynomialPrimalCoeff (symrSatakePair H r) j := by
  unfold CriticalLinePhasor.GlobalHelix.cpsPolynomialDualCoeff
    CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimalCoeff
  have hswap : (symrSatakePair H r).dual
      = fun p => (symrSatakePair H r).primal p ∘ (Fin.revPerm : Equiv.Perm (Fin (r + 1))) := by
    funext p i
    show (symClockWeight r (H.satake p.2) (i : ℕ))⁻¹
      = symClockWeight r (H.satake p.2) ((Fin.rev i : Fin (r + 1)) : ℕ)
    unfold symClockWeight
    rw [← zpow_neg]
    congr 1
    have : ((Fin.rev i : Fin (r + 1)) : ℕ) = r - (i : ℕ) := by
      simp [Fin.rev]
    rw [this]
    have hle : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.2
    push_cast [Nat.cast_sub hle]
    ring
  rw [hswap]
  exact CriticalLinePhasor.GenuineGL2Carrier.radialGlobalSatakeCoeff_comp_equiv
    (Fin.revPerm) (symrSatakePair H r).primal j



/-- **The `Sym³` source from one pointwise identity**: given the single theta reflection
of the prescribed readouts — the §sym5 self-duality — the complete strong pair assembles,
every other field compiled. -/
noncomputable def sym3Source (H : HeckeEigenData f) (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (symrSatakePair H 3) 1 (sym3Shifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (symrSatakePair H 3) 1 (sym3Shifts n)
            (1 / x)) :
    PolynomialBankReflectedThetaSource (symrSatakePair H 3) 1 (sym3Shifts n) where
  pair := {
    toWeakFEPair := {
      f := cpsPolynomialFullPrimal3DBankReadout (symrSatakePair H 3) 1 (sym3Shifts n)
      g := fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout (symrSatakePair H 3) 1 (sym3Shifts n)
          (1 / x)
      k := 1
      ε := ε
      f₀ := 0
      g₀ := 0
      hf_int := cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn _ 1 one_pos
        (sym3Shifts n) (sym3Shifts_ne n)
      hg_int := cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn _ 1 one_pos
        (sym3Shifts n) (sym3Shifts_ne n)
      hk := one_pos
      hε := hε
      h_feq := fun x hx => hrefl x hx
      hf_top := fun q => by
        simpa using cpsPolynomialFullPrimal3DBankReadout_rapid _ 1 one_pos
          (sym3Shifts n) q
      hg_top := fun q => by
        simpa using cpsPolynomialFullDual3DReflectedReadout_rapid _ 1 one_pos
          (sym3Shifts n) q
    }
    hf₀ := rfl
    hg₀ := rfl
  }
  primal_source := rfl
  dual_source := rfl

/-- The `Sym³` completion clock. -/
noncomputable def sym3Clock (n : ℕ) : CPSCompletionClock where
  conductor := 1
  conductor_pos := one_pos
  shifts := sym3Shifts n
  shifts_nonempty := sym3Shifts_ne n

/-- The `Sym³` threshold. -/
noncomputable def sym3B (H : HeckeEigenData f) : ℝ :=
  ((Fintype.card (Fin (3 + 1)) + (symrSatakePair H 3).primalExponent : ℕ) : ℝ) + 1

/-- A point of the open half-plane, for the `Sym³` clock. -/
noncomputable def sym3Point (hn : 0 < n) (H : HeckeEigenData f) {s : ℂ}
    (hs : sym3B H < s.re) :
    CPSCompletionPoint (symrSatakePair H 3) (sym3Clock n) where
  s := s
  shifts_pos := by
    intro μ hμ
    have hshift : (0 : ℝ) ≤ standardShiftR n := by
      unfold standardShiftR
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hB0 : (0 : ℝ) ≤ sym3B H := by
      unfold sym3B
      positivity
    simp only [sym3Clock, sym3Shifts, List.mem_cons, List.not_mem_nil, or_false] at hμ
    rcases hμ with rfl | rfl <;>
      simp only [Complex.add_re, Complex.ofReal_re] <;>
      linarith
  primal_dirichlet := by
    unfold sym3B at hs
    simpa using hs
  dual_dirichlet := by
    unfold sym3B at hs
    have hdual : (symrSatakePair H 3).dualExponent
        = (symrSatakePair H 3).primalExponent := rfl
    rw [show (Fintype.card (Fin (3 + 1)) + (symrSatakePair H 3).dualExponent : ℕ)
        = (Fintype.card (Fin (3 + 1)) + (symrSatakePair H 3).primalExponent : ℕ) by
      simp [hdual]]
    exact hs

/-- **Self-duality of the constructed pair**: the two completed transforms agree on the
hence everywhere by entirety and the identity theorem. -/
theorem sym3_symmLambda_eq (hn : 0 < n) (H : HeckeEigenData f) (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (symrSatakePair H 3) 1 (sym3Shifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (symrSatakePair H 3) 1 (sym3Shifts n)
            (1 / x)) :
    (sym3Source H ε hε hrefl).pair.symm.Λ = (sym3Source H ε hε hrefl).pair.Λ := by
  refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
    (sym3Source H ε hε hrefl).pair.symm.differentiable_Λ
    (sym3Source H ε hε hrefl).pair.differentiable_Λ
    (U := {s : ℂ | sym3B H < s.re})
    (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
    (z₀ := ((sym3B H + 1 : ℝ) : ℂ))
    (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
    ?_
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  have hid := cpsPolynomialFullCompletion3D_identification (symrSatakePair H 3)
    (sym3Clock n) (sym3Point hn H hs)
  have hdual : CriticalLinePhasor.CarrierTheta.dirichlet
      (cpsPolynomialDualCoeff (symrSatakePair H 3)) s
      = CriticalLinePhasor.CarrierTheta.dirichlet
        (cpsPolynomialPrimalCoeff (symrSatakePair H 3)) s := by
    unfold CriticalLinePhasor.CarrierTheta.dirichlet
    exact tsum_congr fun m => by rw [symrPair_dual_eq_primal H 3 m]
  refine (hid.2.trans ?_).trans hid.1.symm
  unfold cpsPolynomialFullDualCompletedReadout cpsPolynomialFullPrimalCompletedReadout
  rw [show (sym3Point hn H hs).s = s from rfl, hdual]



/-- **The `Sym³` package, derived from one pointwise identity**: continuation, entirety,
functional equation, and the prescribed chart — the entire analytic superstructure of the
symmetric cube, machine-derived from the single §sym5 theta self-duality of the explicit
prescribed readouts. -/
noncomputable def sym3_package_of_theta (hn : 0 < n) (H : HeckeEigenData f)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (symrSatakePair H 3) 1 (sym3Shifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (symrSatakePair H 3) 1 (sym3Shifts n)
            (1 / x)) :
    NicePackage (symrBank H 3) (sym3Shifts n) (sym3B H) ε where
  lam := (sym3Source H ε hε hrefl).pair.Λ
  entire := (sym3Source H ε hε hrefl).pair.differentiable_Λ
  FE := by
    intro s
    have h := (sym3Source H ε hε hrefl).pair.functional_equation s
    rw [sym3_symmLambda_eq hn H ε hε hrefl] at h
    rw [show ((sym3Source H ε hε hrefl).pair.k : ℂ) = 1 from by
      show (((1 : ℝ)) : ℂ) = 1
      norm_num] at h
    rw [show (sym3Source H ε hε hrefl).pair.ε = ε from rfl] at h
    simpa using h
  chart := by
    intro s hs
    have hid := (cpsPolynomialFullCompletion3D_identification (symrSatakePair H 3)
      (sym3Clock n) (sym3Point hn H hs)).1
    refine hid.trans ?_
    show ((1 : ℝ) : ℂ) ^ s *
        ((sym3Shifts n).map fun μ => Complex.Gammaℂ (s + μ)).prod *
        CriticalLinePhasor.CarrierTheta.dirichlet
          (cpsPolynomialPrimalCoeff (symrSatakePair H 3)) s = _
    have hcoeff : cpsPolynomialPrimalCoeff (symrSatakePair H 3)
        = fun j => symrBank H 3 (j + 1) := by
      funext j
      exact CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H 3 j
    have hs3 : ((symrBound H 3 : ℕ) : ℝ) + 1 < s.re := by
      unfold sym3B at hs
      have hEq : (symrBound H 3 : ℕ)
          = (Fintype.card (Fin (3 + 1)) + (symrSatakePair H 3).primalExponent : ℕ) := by
        simp [symrBound, symrSatakePair]
      rw [hEq]
      exact hs
    rw [hcoeff, dirichlet_shift_eq_LSeries (symrBank H 3)
      (symrBank_LSeriesSummable H 3 hs3)]
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]

/-- **Rung 4, from one identity**: the degree-6 tensor object is fully nice given only
the single pointwise theta reflection of the `Sym³` prescribed readouts — the seed factor
compiled, the analytic superstructure derived. -/
noncomputable def tensor23_nice_of_theta (hn : 0 < n) (H : HeckeEigenData f)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (symrSatakePair H 3) 1 (sym3Shifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (symrSatakePair H 3) 1 (sym3Shifts n)
            (1 / x)) :
    NicePackage (symrBank H 3 * symrBank H 1) (sym3Shifts n ++ [standardShift n])
      (max (sym3B H) (seedPackageBound H)) (ε * (-1 : ℂ) ^ n) :=
  tensor23_nice hn H (sym3_package_of_theta hn H ε hε hrefl)
    (by
      unfold sym3B
      have hEq : (symrBound H 3 : ℕ)
          = (Fintype.card (Fin (3 + 1)) + (symrSatakePair H 3).primalExponent : ℕ) := by
        simp [symrBound, symrSatakePair]
      rw [hEq])

end CriticalLinePhasor.Sym3ThetaWall

#print axioms CriticalLinePhasor.Sym3ThetaWall.symrPair_dual_eq_primal
#print axioms CriticalLinePhasor.Sym3ThetaWall.sym3Source
#print axioms CriticalLinePhasor.Sym3ThetaWall.sym3_symmLambda_eq
#print axioms CriticalLinePhasor.Sym3ThetaWall.sym3_package_of_theta
#print axioms CriticalLinePhasor.Sym3ThetaWall.tensor23_nice_of_theta
