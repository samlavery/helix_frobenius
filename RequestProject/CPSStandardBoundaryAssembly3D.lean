import RequestProject.CPSPairReadoutPole3D
import RequestProject.CPSLogCoefficientReality3D
import RequestProject.CPSWienerIkeharaBridge3D

/-!
# Assembling the Wiener--Ikehara boundary datum

Everything the boundary structure needs is now compiled except one point.  Collecting:

* the continuation is `-C'/C` with `C` the tower's entire rank-`r` continuation;
* `C ≠ 0` on `Re s > 1` — the Euler product is an exponential (`CPSStandardEulerIdentification3D`);
* `C ≠ 0` at `1 + iy` for `y ≠ 0` — the pole-tolerant edge argument with the Clebsch--Gordan
  companion (`CPSPairReadoutPole3D`);
* `LSeries (log coefficients) = -C'/C` on `Re s > 1` (`CPSTemperedLogDerivative3D` plus the
  descent), and those coefficients are real (`CPSLogCoefficientReality3D`);
* absolute convergence from the von Mangoldt majorant.

**The one point not proven anywhere in this development is `C 1 ≠ 0`**, the `y = 0` end of the
edge.  It is taken here as an explicit named hypothesis `hone`, never as a structure field of some
larger object, so that the obligation stays visible.  See the module note in
`CPSEdgePoleTolerantEngine3D`: the `2/1/4/1` combination provably cannot reach `y = 0` — with the
companion's simple pole the order count there is `4` against a zero order `4m`, so `m = 1`
survives.
-/

open Complex Filter

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

variable {M : GenuineMaassCuspForm3D} {r : ℕ} {D : ArithmeticCPSCompletionData r 1}

/-- Temperedness of the standard twist, from the tower ceiling. -/
theorem standard_twist_tempered (hC : MaassTowerCeiling M.eigenData) (r : ℕ) :
    ∀ (p : Nat.Primes) (i : CPSTensorIndex r 1),
      ‖(arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
        trivialPolynomialSatakePair3D).primal p i‖ = 1 := by
  intro p i
  rw [show (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D).primal p i =
      arithmeticSymmetricPowerRoot r (maassCPSBase M) p i.1 from
    arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D r (maassCPSBase M) p i]
  exact (maass_symmetricPowerRoot_unit_and_real M hC r).1 p i.1

/-- **Nonvanishing on the closed readout half-plane, modulo the single point `s = 1`.** -/
theorem standard_ne_zero_of_one_le_re
    (hC : MaassTowerCeiling M.eigenData)
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D)
    (block : ℕ → ℂ → ℂ)
    (hblock_entire : ∀ j, Differentiable ℂ (block j))
    (hblock_eq : ∀ j, Set.EqOn (block j)
      (bankEulerReadout (arithmeticSymmetricPowerRoot (2 * (j + 1)) (maassCPSBase M)))
      {s : ℂ | 1 < s.re})
    (hone : L.uncompletedContinuation 1 ≠ 0)
    {s : ℂ} (hs : 1 ≤ s.re) :
    L.uncompletedContinuation s ≠ 0 := by
  rcases lt_or_eq_of_le hs with hlt | heq
  · exact ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_ne_zero_of_one_lt_re
      L one_pos (standard_twist_tempered hC r) hlt
  · have hsplit : s = 1 + (s.im : ℂ) * I := by
      apply Complex.ext
      · simp [← heq]
      · simp
    rcases eq_or_ne s.im 0 with him | him
    · rw [hsplit, him]
      simpa using hone
    · rw [hsplit]
      exact standard_edge_nonvanishing_of_blocks hC L block hblock_entire hblock_eq him

/-- **The Wiener--Ikehara boundary datum for the standard Maass rung.**  Every field is compiled
from the tower ceiling; the single named hypothesis is `hone : C 1 ≠ 0`. -/
noncomputable def standardContinuousLSeriesBoundary
    (hC : MaassTowerCeiling M.eigenData)
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D)
    (block : ℕ → ℂ → ℂ)
    (hblock_entire : ∀ j, Differentiable ℂ (block j))
    (hblock_eq : ∀ j, Set.EqOn (block j)
      (bankEulerReadout (arithmeticSymmetricPowerRoot (2 * (j + 1)) (maassCPSBase M)))
      {s : ℂ | 1 < s.re})
    (hone : L.uncompletedContinuation 1 ≠ 0) :
    ContinuousLSeriesBoundary3D
      (fun n => (L.logarithmicCoefficient n).re) where
  continuation := fun s => -logDeriv L.uncompletedContinuation s
  continuousOn := by
    intro s hs
    have hne := standard_ne_zero_of_one_le_re hC L block hblock_entire hblock_eq hone
      (show 1 ≤ s.re from hs)
    refine ContinuousAt.continuousWithinAt ?_
    simp only [logDeriv_apply]
    exact (((L.uncompletedContinuation_entire.deriv).continuous.continuousAt).div
      (L.uncompletedContinuation_entire.continuous.continuousAt) hne).neg
  eqOn := by
    intro s hs
    have hs' : 1 < s.re := hs
    have htemp := standard_twist_tempered hC r
    have hCA : Set.EqOn L.uncompletedContinuation
        (LSeries (⇑L.arithmeticCoefficient)) {s : ℂ | 1 < s.re} :=
      ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_eqOn_LSeries
        L one_pos htemp
    have hopen : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hev : L.uncompletedContinuation =ᶠ[nhds s] LSeries (⇑L.arithmeticCoefficient) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hs) hCA
    have hderiv : deriv L.uncompletedContinuation s =
        deriv (LSeries (⇑L.arithmeticCoefficient)) s := hev.deriv_eq
    have hne : LSeries (⇑L.arithmeticCoefficient) s ≠ 0 := by
      rw [← hCA hs]
      exact ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_ne_zero_of_one_lt_re
        L one_pos htemp hs'
    have hlog :=
      ConventionalCompletedRankinSelbergSource3D.LSeries_logarithmicCoefficient_eq_neg_logDeriv_of_tempered
        L htemp hs' hne
    have hreal : LSeries (fun n => (((L.logarithmicCoefficient n).re : ℝ) : ℂ)) s =
        LSeries (⇑L.logarithmicCoefficient) s :=
      LSeries_congr (fun _ => standard_ofReal_re_logarithmicCoefficient hC L _) s
    show -logDeriv L.uncompletedContinuation s =
      LSeries (fun n => (((L.logarithmicCoefficient n).re : ℝ) : ℂ)) s
    rw [hreal, hlog, logDeriv_apply, logDeriv_apply, hderiv, hCA hs]
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

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.standard_twist_tempered
#print axioms CriticalLinePhasor.ThreeDConverse.standard_ne_zero_of_one_le_re
#print axioms CriticalLinePhasor.ThreeDConverse.standardContinuousLSeriesBoundary
