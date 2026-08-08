import RequestProject.WeilIdentification

/-!
# The amplitude-exchange instrument at `Sym^r`

The campaign's residual wall (route B) was the amplitude exchange: convert between
the one-sided theta identity of a `Sym^r` bank and its analytic package.  Both
arrows are now compiled — `mechanismK` (identity ⟹ package) and
`weil_converse_of_BV_reflection` (package + boundedness ⟹ identity) — so the wall
is an interface, not missing machinery.  This file types it at the `Sym^r` surface
of an arbitrary seed:

* `PolynomialSatakeDualPair.surface` — every fixed-rank pair is a coefficient
  surface (so every compiled bank feeds both arrows);
* `symrSurface` / `symrSurface_dual_eq` — the `Sym^r` bank of any seed as a
  self-dual surface;
* `symr_package_of_reflection` — **arrow one**: the theta identity of the `Sym^r`
  bank at any packaged chart kernel yields the complete package (`mechanismK`
  instance);
* `symr_reflection_of_package` — **arrow two**: an entire package with the
  functional equation, chart identification, kernel line data, and one boundedness
  constant forces the theta identity (`weil_converse_of_BV_reflection` instance).

**The exchange register, terminal.**  The per-rung analytic obligation on either
side is now exactly one classical datum: the completed package with bounded
vertical strips — the precise output shape of the classical symmetric-power
results (Kim–Shahidi for `r ≤ 4`, Newton–Thorne all `r`, level one; cited, not
formalized).  Feeding such a package to arrow two produces the pointwise identity
compiled; feeding an identity to arrow one produces the package compiled.  The
rank-varying (level-`N`) banks carry the same two arrows through
`RamifiedWeightFamily.surface`.  No `axiom`, no `sorry`.
-/

open Real Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.ExchangeInstrument

open CriticalLinePhasor.CarrierTheta CriticalLinePhasor.RamifiedMechanism
open CriticalLinePhasor.WeilConverse CriticalLinePhasor.PhragmenBV
open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.GeneralSeed

/-! ## Every fixed-rank pair is a coefficient surface -/

/-- The coefficient surface of a polynomial Satake dual pair: both banks, one
polynomial bound at the common exponent. -/
noncomputable def _root_.CriticalLinePhasor.GlobalHelix.PolynomialSatakeDualPair.surface
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) : CoefficientSurface where
  a := cpsPolynomialPrimalCoeff W
  adual := cpsPolynomialDualCoeff W
  A := Fintype.card ι + max W.primalExponent W.dualExponent
  a_bound := fun n => by
    have h := cpsPolynomialPrimalCoeff_norm_le W n
    have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    refine le_trans h (pow_le_pow_right₀ hbase ?_)
    have := le_max_left W.primalExponent W.dualExponent
    omega
  adual_bound := fun n => by
    have h := cpsPolynomialDualCoeff_norm_le W n
    have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    refine le_trans h (pow_le_pow_right₀ hbase ?_)
    have := le_max_right W.primalExponent W.dualExponent
    omega

/-- The `Sym^r` bank of any seed as a coefficient surface. -/
noncomputable def symrSurface (S : SatakeSeed) (r : ℕ) : CoefficientSurface :=
  (symrSatakePairOf S r).surface

/-- The `Sym^r` surface is self-dual — the clock reversal, seed-free. -/
theorem symrSurface_dual_eq (S : SatakeSeed) (r : ℕ) :
    ∀ n : ℕ, (symrSurface S r).adual n = (symrSurface S r).a n :=
  fun n => symrPairOf_dual_eq_primal S r n

/-! ## The two arrows of the exchange -/

/-- **Arrow one — identity to package**: the theta identity of the `Sym^r` bank at
any packaged chart kernel yields the complete analytic package. -/
noncomputable def symr_package_of_reflection (S : SatakeSeed) (r : ℕ)
    (κ : MellinKernel) (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout (symrSurface S r).a κ.K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout (symrSurface S r).adual κ.K (1 / x)) :
    KNicePackage (coefficientArithmetic (symrSurface S r).a) κ.G
      (max κ.B0 (((symrSurface S r).A : ℝ) + 1)) ε :=
  mechanismK (symrSurface S r) (symrSurface_dual_eq S r) κ ε hε hrefl

/-- **Arrow two — package to identity**: an entire package with the functional
equation, chart identification, kernel line data, and one boundedness constant
forces the pointwise theta identity of the `Sym^r` bank.  The hypotheses are the
exact output shape of the classical symmetric-power automorphy results. -/
theorem symr_reflection_of_package (S : SatakeSeed) (r : ℕ)
    (κ : MellinKernel) (hKc : ContinuousOn κ.K (Set.Ioi 0)) (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic (symrSurface S r).a) κ.G
      (max κ.B0 (((symrSurface S r).A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 (((symrSurface S r).A : ℝ) + 1) < σ)
    (hG_int : Integrable (fun t : ℝ => κ.G ((σ : ℂ) + t * I)))
    (A k : ℝ) (hApos : 0 < A) (hk : 0 < k)
    (hGexp : ∀ t : ℝ, ‖κ.G ((σ : ℂ) + t * I)‖ ≤ A * Real.exp (-k * |t|))
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta (symrSurface S r).a κ.K y
        = ε * ((y : ℂ)⁻¹ *
            CriticalLinePhasor.CarrierTheta.theta (symrSurface S r).adual κ.K
              (1 / y)) :=
  weil_converse_of_BV_reflection (symrSurface S r) (symrSurface_dual_eq S r) κ hKc
    ε pkg σ hσ hG_int A k hApos hk hGexp C hBV

end CriticalLinePhasor.ExchangeInstrument

#print axioms CriticalLinePhasor.GlobalHelix.PolynomialSatakeDualPair.surface
#print axioms CriticalLinePhasor.ExchangeInstrument.symrSurface_dual_eq
#print axioms CriticalLinePhasor.ExchangeInstrument.symr_package_of_reflection
#print axioms CriticalLinePhasor.ExchangeInstrument.symr_reflection_of_package
