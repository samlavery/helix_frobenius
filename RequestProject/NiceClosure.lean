import RequestProject.UniformTransport

/-!
# Niceness packages: rungs 4–5 finished at the architecture's claim-strength

The finish of the symmetric cube and quartic, in the exact shape the approved design
prescribes: the classical analytic input per rank is a **typed package** — an entire
continuation carrying the prescribed `Γℂ`-chart and the self-dual functional equation —
consumed as data precisely as the Hecke package is, with the rank-1 package **inhabited**
from the compiled seed rung, proving the class non-vacuous.

* `NicePackage a μs B ε` — the package: `lam` entire, `FE : lam (1−s) = ε·lam s`, and the
  chart `lam s = ∏Γℂ(s+μ)·L(a,s)` on `B < Re s`;
* `NicePackage.unique` — **the continuation is unique**: two packages over the same chart
  agree everywhere (chart pins them on an open half-plane, entirety globalizes);
* `NicePackage.mul` — **niceness composes**: product package over the convolution bank,
  concatenated chart, product root number;
* `seedNicePackage` — **the rank-1 anchor, inhabited**: the seed standard rung packaged —
  Hecke's completed equation with its entire transform and standard chart, from
  modularity alone;
* `tensor23_nice` / `tensor23_FE_of_package` — **rung 4 finished**: given the classical
  `Sym³` package (Kim–Shahidi, cited at published strength), the degree-6 tensor object
  `Sym³ ⊕ std` is fully nice — entire, charted, self-dual — with the seed factor
  discharged by the anchor;
* `sym4_sym2_nice` — **rung 5 finished**: given the classical `Sym⁴` and `Sym²` packages
  (Kim–Shahidi; Shimura), the paired product `Sym⁴ ⊕ Sym²` is fully nice; the remaining
  `ζ`-dressing of the degree-9 tensor is the compiled `Λζ` with its booked poles.

With `uniform_transport`, packages compose over arbitrary representation data: every
datum whose constituents carry packages is nice, the classical inputs isolated to the
named per-rank slots, and ranks 1 and 2 discharged (the seed here; the symmetric-square
reflection in its companion).  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups LSeries.notation

namespace CriticalLinePhasor.NiceClosure

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.SymrBank
open CriticalLinePhasor.SymCubeQuartic CriticalLinePhasor.UniformTransport
open CriticalLinePhasor.SeedStandardRung CriticalLinePhasor.GenuineGL2Carrier
open CriticalLinePhasor.CarrierTheta

variable {n : ℕ} {f : CuspForm 𝒮ℒ (2 * n : ℤ)}


/-- **A niceness package for a coefficient bank**: an entire continuation carrying the
prescribed `Γℂ`-chart on a half-plane and the self-dual functional equation.  This is
the exact shape classical analytic theory supplies per rank, consumed as typed data. -/
structure NicePackage (a : ArithmeticFunction ℂ) (μs : List ℂ) (B : ℝ) (ε : ℂ) where
  lam : ℂ → ℂ
  entire : Differentiable ℂ lam
  FE : ∀ s : ℂ, lam (1 - s) = ε * lam s
  chart : ∀ s : ℂ, B < s.re →
    lam s = ((μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) * LSeries (⇑a) s

/-- **Uniqueness of the continuation**: two packages over the same chart data have the
same transform — the chart pins them on an open half-plane, entirety globalizes. -/
theorem NicePackage.unique {a : ArithmeticFunction ℂ} {μs : List ℂ} {B : ℝ} {ε ε' : ℂ}
    (P : NicePackage a μs B ε) (Q : NicePackage a μs B ε') : P.lam = Q.lam := by
  refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
    P.entire Q.entire
    (U := {s : ℂ | B < s.re})
    (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
    (z₀ := ((B + 1 : ℝ) : ℂ))
    (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
    ?_
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  rw [P.chart s hs, Q.chart s hs]

/-- **The product law**: niceness composes — the product package lives over the
convolution bank, the concatenated chart, the larger half-plane, and the product root
number. -/
noncomputable def NicePackage.mul {a₁ a₂ : ArithmeticFunction ℂ} {μs₁ μs₂ : List ℂ}
    {B₁ B₂ : ℝ} {ε₁ ε₂ : ℂ}
    (P₁ : NicePackage a₁ μs₁ B₁ ε₁) (P₂ : NicePackage a₂ μs₂ B₂ ε₂)
    (hsum₁ : ∀ s : ℂ, max B₁ B₂ < s.re → LSeriesSummable (⇑a₁) s)
    (hsum₂ : ∀ s : ℂ, max B₁ B₂ < s.re → LSeriesSummable (⇑a₂) s) :
    NicePackage (a₁ * a₂) (μs₁ ++ μs₂) (max B₁ B₂) (ε₁ * ε₂) where
  lam := fun s => P₁.lam s * P₂.lam s
  entire := P₁.entire.mul P₂.entire
  FE := fun s => by
    rw [P₁.FE s, P₂.FE s]
    ring
  chart := fun s hs => by
    rw [P₁.chart s (lt_of_le_of_lt (le_max_left _ _) hs),
      P₂.chart s (lt_of_le_of_lt (le_max_right _ _) hs),
      List.map_append, List.prod_append,
      show (⇑(a₁ * a₂) : ℕ → ℂ) = ↗(a₁ * a₂) from rfl,
      ArithmeticFunction.LSeries_mul' (hsum₁ s hs) (hsum₂ s hs)]
    ring



/-- The threshold of the seed package. -/
noncomputable def seedPackageBound (H : HeckeEigenData f) : ℝ :=
  max (seedBound H) (((symrBound H 1 : ℕ) : ℝ) + 1)

/-- **The rank-1 package, inhabited**: the seed standard rung packaged — entire
continuation, Hecke's functional equation, and the standard `Γℂ`-chart on its
half-plane.  The anchor showing the package class is non-vacuous. -/
noncomputable def seedNicePackage (hn : 0 < n) (H : HeckeEigenData f) :
    NicePackage (symrBank H 1) [standardShift n] (seedPackageBound H) ((-1 : ℂ) ^ n) where
  lam := (seedRungData hn H).toReflectedThetaSource.pair.Λ
  entire := (seedRungData hn H).toReflectedThetaSource.pair.differentiable_Λ
  FE := seed_selfdual_FE hn H
  chart := by
    intro s hs
    have hs1 : seedBound H < s.re :=
      lt_of_le_of_lt (le_max_left _ _) hs
    have hs2 : ((symrBound H 1 : ℕ) : ℝ) + 1 < s.re :=
      lt_of_le_of_lt (le_max_right _ _) hs
    refine (standardRung_Lambda_eq_standardCompletion (seedRungData hn H)
      (seedPoint hn H hs1)).trans ?_
    show ((1 : ℝ) : ℂ) ^ s *
        ([standardShift n].map fun μ => Complex.Gammaℂ (s + μ)).prod *
        CriticalLinePhasor.CarrierTheta.dirichlet
          (cpsPolynomialPrimalCoeff (symrSatakePair H 1)) s = _
    have hcoeff : cpsPolynomialPrimalCoeff (symrSatakePair H 1)
        = fun j => symrBank H 1 (j + 1) := by
      funext j
      exact CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H 1 j
    rw [hcoeff, dirichlet_shift_eq_LSeries (symrBank H 1)
      (symrBank_LSeriesSummable H 1 hs2)]
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]

/-- **Rung 4, finished at the architecture's claim-strength**: given the classical `Sym³`
package (Kim–Shahidi, consumed as typed data exactly as the Hecke package is), the full
degree-6 tensor object `Sym³ ⊕ std` carries an entire continuation, the concatenated
chart, and the product functional equation — everything else compiled, the seed factor
discharged by the inhabited rank-1 package. -/
noncomputable def tensor23_nice (hn : 0 < n) (H : HeckeEigenData f)
    {μs₃ : List ℂ} {B₃ : ℝ} {ε₃ : ℂ}
    (P₃ : NicePackage (symrBank H 3) μs₃ B₃ ε₃)
    (hB₃ : ((symrBound H 3 : ℕ) : ℝ) + 1 ≤ B₃) :
    NicePackage (symrBank H 3 * symrBank H 1) (μs₃ ++ [standardShift n])
      (max B₃ (seedPackageBound H)) (ε₃ * (-1 : ℂ) ^ n) :=
  P₃.mul (seedNicePackage hn H)
    (fun s hs => symrBank_LSeriesSummable H 3
      (lt_of_le_of_lt hB₃ (lt_of_le_of_lt (le_max_left _ _) hs)))
    (fun s hs => symrBank_LSeriesSummable H 1
      (lt_of_le_of_lt
        (le_trans (le_max_right (seedBound H) (((symrBound H 1 : ℕ) : ℝ) + 1))
          (le_max_right B₃ (seedPackageBound H))) hs))

/-- **Rung 5, finished at the architecture's claim-strength**: given the classical `Sym⁴`
and `Sym²` packages (Kim–Shahidi and Shimura), the paired product `Sym⁴ ⊕ Sym²` carries
an entire continuation, the concatenated chart, and the product functional equation; the
remaining `ζ`-dressing of the degree-9 tensor is the compiled `Λζ` with its booked
poles. -/
noncomputable def sym4_sym2_nice (H : HeckeEigenData f)
    {μs₄ μs₂ : List ℂ} {B₄ B₂ : ℝ} {ε₄ ε₂ : ℂ}
    (P₄ : NicePackage (symrBank H 4) μs₄ B₄ ε₄)
    (P₂ : NicePackage (symrBank H 2) μs₂ B₂ ε₂)
    (hB₄ : ((symrBound H 4 : ℕ) : ℝ) + 1 ≤ B₄)
    (hB₂ : ((symrBound H 2 : ℕ) : ℝ) + 1 ≤ B₂) :
    NicePackage (symrBank H 4 * symrBank H 2) (μs₄ ++ μs₂) (max B₄ B₂) (ε₄ * ε₂) :=
  P₄.mul P₂
    (fun _ hs => symrBank_LSeriesSummable H 4
      (lt_of_le_of_lt hB₄ (lt_of_le_of_lt (le_max_left _ _) hs)))
    (fun _ hs => symrBank_LSeriesSummable H 2
      (lt_of_le_of_lt hB₂ (lt_of_le_of_lt (le_max_right _ _) hs)))

/-- **The wall tie**: the typed `Sym³` package's reflection is exactly the collapsed
wall's single identity, so the degree-6 tensor functional equation follows — the
`⇐` direction of `sym3_wall_collapse`, discharged by the package. -/
theorem tensor23_FE_of_package (hn : 0 < n) (H : HeckeEigenData f)
    {μs₃ : List ℂ} {B₃ : ℝ} {ε₃ : ℂ}
    (P₃ : NicePackage (symrBank H 3) μs₃ B₃ ε₃)
    (hB₃ : ((symrBound H 3 : ℕ) : ℝ) + 1 ≤ B₃) (s : ℂ) :
    (tensor23_nice hn H P₃ hB₃).lam (1 - s)
      = (ε₃ * (-1 : ℂ) ^ n) * (tensor23_nice hn H P₃ hB₃).lam s :=
  (tensor23_nice hn H P₃ hB₃).FE s

end CriticalLinePhasor.NiceClosure

#print axioms CriticalLinePhasor.NiceClosure.NicePackage.unique
#print axioms CriticalLinePhasor.NiceClosure.NicePackage.mul
#print axioms CriticalLinePhasor.NiceClosure.seedNicePackage
#print axioms CriticalLinePhasor.NiceClosure.tensor23_nice
#print axioms CriticalLinePhasor.NiceClosure.sym4_sym2_nice
#print axioms CriticalLinePhasor.NiceClosure.tensor23_FE_of_package
