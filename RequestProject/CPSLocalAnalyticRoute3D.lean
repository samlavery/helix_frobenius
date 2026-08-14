import RequestProject.CPSStandardBoundaryAssembly3D
import RequestProject.CPSEdgeLocalEngine3D

/-!
# The consumer chain never needed `h_feq`

`h_feq` is the arithmetic theta reflection `θ_a(1/x) = ε·x^k·θ_{a∨}(x)`.  In the CPS tower it has
exactly one job: it supplies the `StrongFEPair` whose Mellin transform is **entire**, and entirety
is what every downstream consumer was asking for.  By Mellin inversion `h_feq` is equivalent to
the completed functional equation of `L(s, Sym^r)`, so demanding it is demanding automorphy of
`Sym^r` — the open problem.

This file replaces that demand.  The Wiener--Ikehara boundary datum is rebuilt from a purely
**local** analytic input:

* `C` differentiable on some open `U ⊇ {Re s ≥ 1}` — holomorphy on a neighbourhood of the closed
  readout half-plane, nothing about the rest of the plane;
* `C` agreeing with the bank Dirichlet series on `{Re s > 1}`;
* `C` nonvanishing on `{Re s ≥ 1}`.

No functional equation, no reflection, no continuation to `ℂ`.  Together with
`CPSEdgeLocalEngine3D` (which showed the edge test needs differentiability at the single point
under test) this locates the genuine analytic requirement of the whole consumer chain.

**What this does and does not do.**  It does not prove the local input; holomorphy and
nonvanishing of `L(s, Sym^r)` on a neighbourhood of `Re s ≥ 1` is still unproven here, and for a
Maass form it is not known.  What it does is replace *automorphy of `Sym^r`* by something strictly
weaker as the thing to be supplied — the tower's global reflection was sufficient for the chain,
never necessary.
-/

open Complex Filter

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

variable {M : GenuineMaassCuspForm3D} {r : ℕ} {D : ArithmeticCPSCompletionData r 1}

/-- **The boundary datum from local holomorphy alone.**  The source `L` enters only as coefficient
bookkeeping — its `arithmeticCoefficient` and `logarithmicCoefficient` are functions of the Satake
bank, not of any analytic data — while every analytic hypothesis is local to a neighbourhood of
the closed readout half-plane. -/
noncomputable def boundaryOfLocalHolomorphy
    (hC : MaassTowerCeiling M.eigenData)
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D)
    (C : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U) (hUsub : {s : ℂ | 1 ≤ s.re} ⊆ U)
    (hCdiff : DifferentiableOn ℂ C U)
    (hCeq : Set.EqOn C (LSeries (⇑L.arithmeticCoefficient)) {s : ℂ | 1 < s.re})
    (hne : ∀ s : ℂ, 1 ≤ s.re → C s ≠ 0) :
    ContinuousLSeriesBoundary3D (fun n => (L.logarithmicCoefficient n).re) where
  continuation := fun s => -logDeriv C s
  continuousOn := by
    intro s hs
    have hsU : s ∈ U := hUsub hs
    have hderivOn : DifferentiableOn ℂ (deriv C) U := hCdiff.deriv hUopen
    have hCat : DifferentiableAt ℂ C s := hCdiff.differentiableAt (hUopen.mem_nhds hsU)
    have hdat : DifferentiableAt ℂ (deriv C) s :=
      hderivOn.differentiableAt (hUopen.mem_nhds hsU)
    refine ContinuousAt.continuousWithinAt ?_
    simp only [logDeriv_apply]
    exact ((hdat.continuousAt).div (hCat.continuousAt) (hne s hs)).neg
  eqOn := by
    intro s hs
    have hs' : 1 < s.re := hs
    have htemp := standard_twist_tempered hC r
    have hopen : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hev : C =ᶠ[nhds s] LSeries (⇑L.arithmeticCoefficient) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hs) hCeq
    have hderiv : deriv C s = deriv (LSeries (⇑L.arithmeticCoefficient)) s := hev.deriv_eq
    have hneA : LSeries (⇑L.arithmeticCoefficient) s ≠ 0 := by
      rw [← hCeq hs]
      exact hne s (le_of_lt hs')
    have hlog :=
      ConventionalCompletedRankinSelbergSource3D.LSeries_logarithmicCoefficient_eq_neg_logDeriv_of_tempered
        L htemp hs' hneA
    have hreal : LSeries (fun n => (((L.logarithmicCoefficient n).re : ℝ) : ℂ)) s =
        LSeries (⇑L.logarithmicCoefficient) s :=
      LSeries_congr (fun _ => standard_ofReal_re_logarithmicCoefficient hC L _) s
    show -logDeriv C s =
      LSeries (fun n => (((L.logarithmicCoefficient n).re : ℝ) : ℂ)) s
    rw [hreal, hlog, logDeriv_apply, logDeriv_apply, hderiv, hCeq hs]
  summable := by
    intro sigma hsigma
    have hsum := (ConventionalCompletedRankinSelbergSource3D.logarithmicCoefficient_LSeriesSummable_of_tempered
      L (standard_twist_tempered hC r) (s := (sigma : ℂ)) (by simpa using hsigma)).norm
    have hfun : (fun n : ℕ => (((L.logarithmicCoefficient n).re : ℝ) : ℂ)) =
        ⇑L.logarithmicCoefficient := by
      funext m
      exact standard_ofReal_re_logarithmicCoefficient hC L m
    rw [hfun]
    simpa only [← nterm_eq_norm_term] using hsum

/-- **The local input suffices for the Wiener--Ikehara conclusion.**  From holomorphy on a
neighbourhood of the closed readout half-plane, the Dirichlet identification, and nonvanishing,
the generalized von Mangoldt coefficients have `o(N)` summatory function — with no functional
equation anywhere in the derivation. -/
theorem cumsum_isLittleO_of_localHolomorphy
    (hC : MaassTowerCeiling M.eigenData)
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D)
    (C : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U) (hUsub : {s : ℂ | 1 ≤ s.re} ⊆ U)
    (hCdiff : DifferentiableOn ℂ C U)
    (hCeq : Set.EqOn C (LSeries (⇑L.arithmeticCoefficient)) {s : ℂ | 1 < s.re})
    (hne : ∀ s : ℂ, 1 ≤ s.re → C s ≠ 0) :
    (fun N : ℕ ↦ cumsum (fun n => (L.logarithmicCoefficient n).re) N) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  refine boundedByVonMangoldt_cumsum_isLittleO
    (d := (Fintype.card (CPSTensorIndex r 1) : ℝ)) (by positivity) ?_
    (boundaryOfLocalHolomorphy hC L C U hUopen hUsub hCdiff hCeq hne)
  intro n
  have h := ConventionalCompletedRankinSelbergSource3D.norm_logarithmicCoefficient_le_vonMangoldt
    L (standard_twist_tempered hC r) n
  calc
    |(L.logarithmicCoefficient n).re| ≤ ‖L.logarithmicCoefficient n‖ :=
      Complex.abs_re_le_norm _
    _ ≤ (Fintype.card (CPSTensorIndex r 1) : ℝ) * ArithmeticFunction.vonMangoldt n := h

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.boundaryOfLocalHolomorphy
#print axioms CriticalLinePhasor.ThreeDConverse.cumsum_isLittleO_of_localHolomorphy
