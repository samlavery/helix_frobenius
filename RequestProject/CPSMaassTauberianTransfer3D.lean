import RequestProject.CPSGeneralizedVonMangoldtSupport3D
import RequestProject.CPSMaassCompletedRankinSelbergTower3D
import RequestProject.CPSMaassSatoTate3D
import Mathlib.NumberTheory.Chebyshev
import PrimeNumberTheoremAnd.Consequences

/-!
# Tauberian transfer for the Maass CPS coefficients

This file turns the exact standard Rankin--Selberg logarithmic coefficients into the bounded
prime-power coefficients needed by the automorphic prime theorem.  The first layer is pointwise:
the real generalized von Mangoldt coefficient is dominated by the ordinary von Mangoldt function
times the degree of the symmetric-power representation.
-/

open Filter Topology Asymptotics
open Finset Nat
open scoped ArithmeticFunction

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate CriticalLinePhasor.SatoTateCarrier3D

/-- Every positive power sum of the rank-`r` Maass symmetric-power roots has real part bounded by
the degree `r+1`. -/
theorem abs_sum_arithmeticSymmetricPowerRoot_pow_maass_re_le
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r k : ℕ) (p : Nat.Primes) :
    |(∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r (maassCPSBase M) p j ^ k).re| ≤
      r + 1 := by
  calc
    |(∑ j : Fin (r + 1),
        arithmeticSymmetricPowerRoot r (maassCPSBase M) p j ^ k).re| ≤
        ‖∑ j : Fin (r + 1),
          arithmeticSymmetricPowerRoot r (maassCPSBase M) p j ^ k‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ j : Fin (r + 1),
        ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j ^ k‖ := norm_sum_le _ _
    _ = r + 1 := by
      simp [norm_pow, norm_arithmeticSymmetricPowerRoot_maass M hC]

/-- The real standard logarithmic coefficient is bounded pointwise by the ordinary von Mangoldt
function times the degree.  Off prime powers both sides vanish; at `p^k` this is the exact local
power-sum identity and temperedness. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.abs_standard_logarithmicCoefficient_re_le
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    |((T.sources.standardSource r hr).logarithmicCoefficient n).re| ≤
      ArithmeticFunction.vonMangoldt n * (r + 1) := by
  by_cases hn : IsPrimePow n
  · rcases hn with ⟨p, k, hp, hk, rfl⟩
    rw [T.standard_logarithmicCoefficient_eq_sum r hr hp.nat_prime hk,
      ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp.nat_prime]
    rw [← Complex.natCast_log]
    norm_cast
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg (mod_cast hp.nat_prime.one_le))]
    gcongr
    simpa only [Nat.cast_add, Nat.cast_one] using
      (abs_sum_arithmeticSymmetricPowerRoot_pow_maass_re_le M T.toCeiling r k
        ⟨p, hp.nat_prime⟩)
  · rw [(T.sources.standardSource r hr).logarithmicCoefficient_eq_zero_of_not_isPrimePow hn,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    simp

/-- The contribution of composite prime powers up to `x` is bounded by the classical
`psi(x)-theta(x)` error times the symmetric-power degree. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.abs_standard_compositePrimePowerSum_le
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime,
        ((T.sources.standardSource r hr).logarithmicCoefficient n).re| ≤
      (r + 1 : ℝ) * (Chebyshev.psi x - Chebyshev.theta x) := by
  calc
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime,
        ((T.sources.standardSource r hr).logarithmicCoefficient n).re| ≤
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime,
          |((T.sources.standardSource r hr).logarithmicCoefficient n).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime,
          ArithmeticFunction.vonMangoldt n * (r + 1) := by
      gcongr with n hn
      exact T.abs_standard_logarithmicCoefficient_re_le r hr n
    _ = (r + 1 : ℝ) * (Chebyshev.psi x - Chebyshev.theta x) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- The square-root prime-power remainder is negligible compared with the main linear scale. -/
theorem sqrt_isLittleO_id_atTop3D :
    Real.sqrt =o[atTop] (fun x : ℝ ↦ x) := by
  have hsqrtlog : Real.sqrt =O[atTop] (fun x : ℝ ↦ x.sqrt * x.log) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : 0 ≤ x := le_trans (Real.exp_pos 1).le hx
    have hlog : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
        (lt_of_lt_of_le (Real.exp_pos 1) hx) hx
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (le_trans zero_le_one hlog))]
    exact le_mul_of_one_le_right (Real.sqrt_nonneg x) hlog
  exact hsqrtlog.trans_isLittleO isLittleO_sqrt_mul_log

/-- The composite-prime-power part of the standard logarithmic coefficient summatory function. -/
noncomputable def GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardCompositePrimePowerSum
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime,
    ((T.sources.standardSource r hr).logarithmicCoefficient n).re

/-- Composite prime powers contribute `o(x)` to the standard logarithmic coefficient sum. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardCompositePrimePowerSum_isLittleO
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) :
    T.standardCompositePrimePowerSum r hr =o[atTop] (fun x : ℝ ↦ x) := by
  have htail : T.standardCompositePrimePowerSum r hr =O[atTop]
      (Chebyshev.psi - Chebyshev.theta) := by
    apply IsBigO.of_bound (r + 1)
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.sub_apply,
      abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
    simpa [GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardCompositePrimePowerSum,
      Nat.cast_add, Nat.cast_one] using T.abs_standard_compositePrimePowerSum_le r hr hx
  exact (htail.trans Chebyshev.isBigO_psi_sub_theta_sqrt).trans_isLittleO
    sqrt_isLittleO_id_atTop3D

/-- The prime part of the standard logarithmic coefficient summatory function. -/
noncomputable def GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardPrimeLogarithmicSum
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime,
    ((T.sources.standardSource r hr).logarithmicCoefficient p).re

/-- Exact prime/composite-prime-power decomposition of the inclusive standard coefficient sum. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_cumsum_eq_prime_add_composite
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) (N : ℕ) :
    cumsum (fun n ↦ ((T.sources.standardSource r hr).logarithmicCoefficient n).re) (N + 1) =
      T.standardPrimeLogarithmicSum r hr N + T.standardCompositePrimePowerSum r hr N := by
  rw [cumsum]
  have hrange : Finset.range (N + 1) = Finset.Icc 0 N := by
    ext n
    simp
  rw [hrange, Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons]
  have hzero : ((T.sources.standardSource r hr).logarithmicCoefficient 0).re = 0 := by simp
  rw [hzero, zero_add, ← Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc 0 N) Nat.Prime]
  simp only [GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardPrimeLogarithmicSum,
    GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardCompositePrimePowerSum,
    Nat.floor_natCast]

/-- A Wiener--Ikehara `o(N)` estimate for the full logarithmic coefficient sum transfers to the
prime-only logarithmically weighted sum; the discarded prime powers are already `o(N)`. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardPrimeLogarithmicSum_nat_isLittleO_of_cumsum
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r)
    (htotal : (fun N : ℕ ↦ cumsum
      (fun n ↦ ((T.sources.standardSource r hr).logarithmicCoefficient n).re) N) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ))) :
    (fun N : ℕ ↦ T.standardPrimeLogarithmicSum r hr N) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  have hshift0 := htotal.comp_tendsto (tendsto_add_atTop_nat 1)
  have hconst : (fun _N : ℕ ↦ (1 : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) :=
    (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop
  have heq : (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) ~[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
    have hrefl : (fun N : ℕ ↦ (N : ℝ)) ~[atTop] (fun N : ℕ ↦ (N : ℝ)) :=
      IsEquivalent.refl
    have hadd := hrefl.add_isLittleO hconst
    exact hadd.congr (fun N ↦ by simp [Pi.add_apply]) (fun _ ↦ rfl)
  have hshift : (fun N : ℕ ↦ cumsum
      (fun n ↦ ((T.sources.standardSource r hr).logarithmicCoefficient n).re) (N + 1)) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ)) := hshift0.trans_isEquivalent heq
  have htail : (fun N : ℕ ↦ T.standardCompositePrimePowerSum r hr N) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) :=
    (T.standardCompositePrimePowerSum_isLittleO r hr).comp_tendsto
      tendsto_natCast_atTop_atTop
  apply (hshift.sub htail).congr_left
  intro N
  rw [T.standard_cumsum_eq_prime_add_composite r hr N]
  ring

/-- The primes up to the `n`-th prime are exactly the image of `0,...,n` under `nthPrime`. -/
theorem primesLE_nthPrime_eq_image_range3D (n : ℕ) :
    Nat.primesLE (nth_prime n) = (Finset.range (n + 1)).image nth_prime := by
  have hinj : Function.Injective nth_prime :=
    (nth_strictMono infinite_setOf_prime).injective
  have hsub : (Finset.range (n + 1)).image nth_prime ⊆ Nat.primesLE (nth_prime n) := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨i, hi, rfl⟩
    rw [Nat.mem_primesLE]
    exact ⟨(nth_strictMono infinite_setOf_prime).monotone (by simpa using hi),
      prime_nth_prime i⟩
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Nat.primesLE_card_eq_primeCounting, pi_nth_prime,
    Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- The logarithmically weighted first-prime summatory function for the literal CPS trace. -/
noncomputable def maassCPSLocalWeightedPrimeSummatory
    (M : GenuineMaassCuspForm3D) (r n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), Real.log (nthPrime i) *
    (∑ j : Fin (r + 1),
      arithmeticSymmetricPowerRoot r (maassCPSBase M) (nthPrime i) j).re

/-- The literal real symmetric-power trace at the `i`-th prime. -/
noncomputable def maassCPSLocalTrace
    (M : GenuineMaassCuspForm3D) (r i : ℕ) : ℝ :=
  (∑ j : Fin (r + 1),
    arithmeticSymmetricPowerRoot r (maassCPSBase M) (nthPrime i) j).re

/-- The same trace with the elementary slowly varying weight `log(i+2)`. -/
noncomputable def maassCPSLocalShiftedLogPrimeSummatory
    (M : GenuineMaassCuspForm3D) (r n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), Real.log (i + 2) * maassCPSLocalTrace M r i

/-- The shifted natural logarithm is asymptotic to the logarithm. -/
theorem log_nat_add_two_isEquivalent_log_nat3D :
    (fun n : ℕ ↦ Real.log (n + 2)) ~[atTop] (fun n : ℕ ↦ Real.log n) := by
  have hconst : (fun _n : ℕ ↦ (2 : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
    (isLittleO_const_id_atTop (2 : ℝ)).natCast_atTop
  have hrefl : (fun n : ℕ ↦ (n : ℝ)) ~[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
    IsEquivalent.refl
  have hadd : (fun n : ℕ ↦ (n : ℝ) + 2) ~[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    exact (hrefl.add_isLittleO hconst).congr (fun n ↦ by simp [Pi.add_apply]) (fun _ ↦ rfl)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hadd.log tendsto_natCast_atTop_atTop

/-- The finite difference of `1 / log(n+2)` has the order needed for Abel de-weighting. -/
theorem shiftedLogReciprocalNabla_isBigO3D :
    nabla (fun n : ℕ => (Real.log (n + 2))⁻¹) =O[atTop]
      (fun n : ℕ => ((n + 1 : ℝ) * Real.log (n + 1))⁻¹) := by
  apply IsBigO.of_bound (Real.log 2)⁻¹
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hn3 : (0 : ℝ) < n + 3 := by positivity
  have hl1 : 0 < Real.log (n + 1) := Real.log_pos (by norm_cast; omega)
  have hl2 : 0 < Real.log (n + 2) := Real.log_pos (by norm_cast; omega)
  have hl3 : 0 < Real.log (n + 3) := Real.log_pos (by norm_cast; omega)
  have hmono : Real.log (n + 2) ≤ Real.log (n + 3) :=
    Real.log_le_log hn2 (by norm_cast; omega)
  have hdiff : Real.log (n + 3) - Real.log (n + 2) ≤ ((n + 2 : ℝ))⁻¹ := by
    calc
      Real.log (n + 3) - Real.log (n + 2) = nabla Real.log (n + 2 : ℝ) := by
        simp [nabla]
        ring
      _ ≤ ((n + 2 : ℝ))⁻¹ := log_add_one_sub_log_le hn2
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [nabla]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ) + 1 + 2 = n + 3 by ring]
  rw [abs_of_nonpos]
  · rw [neg_sub, abs_inv, inv_sub_inv hl2.ne' hl3.ne']
    rw [abs_of_nonneg (mul_nonneg (by positivity) hl1.le)]
    have hnum : 0 ≤ Real.log (n + 3) - Real.log (n + 2) := sub_nonneg.mpr hmono
    calc
      _ ≤ (n + 2 : ℝ)⁻¹ / (Real.log (n + 2) * Real.log (n + 3)) :=
        div_le_div_of_nonneg_right hdiff (mul_nonneg hl2.le hl3.le)
      _ ≤ (Real.log 2)⁻¹ / ((n + 1 : ℝ) * Real.log (n + 1)) := by
        rw [div_le_div_iff₀ (mul_pos hl2 hl3) (mul_pos hn1 hl1)]
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hratio : (n + 2 : ℝ)⁻¹ * (n + 1) ≤ 1 := by
          rw [inv_mul_eq_div, div_le_one hn2]
          norm_num
        have hleft :
            (n + 2 : ℝ)⁻¹ * ((n + 1) * Real.log (n + 1)) ≤
              Real.log (n + 1) := by
          calc
            _ = ((n + 2 : ℝ)⁻¹ * (n + 1)) * Real.log (n + 1) := by ring
            _ ≤ 1 * Real.log (n + 1) := mul_le_mul_of_nonneg_right hratio hl1.le
            _ = _ := one_mul _
        have hlog13 : Real.log (n + 1) ≤ Real.log (n + 3) :=
          Real.log_le_log hn1 (by norm_num)
        have hlog22 : Real.log 2 ≤ Real.log (n + 2) :=
          Real.log_le_log (by norm_num) (by norm_cast; omega)
        have hfactor : 1 ≤ (Real.log 2)⁻¹ * Real.log (n + 2) := by
          rw [inv_mul_eq_div, le_div_iff₀ hlog2]
          simpa using hlog22
        calc
          _ ≤ Real.log (n + 1) := hleft
          _ ≤ Real.log (n + 3) := hlog13
          _ = 1 * Real.log (n + 3) := by ring
          _ ≤ ((Real.log 2)⁻¹ * Real.log (n + 2)) * Real.log (n + 3) :=
            mul_le_mul_of_nonneg_right hfactor hl3.le
          _ = _ := by ring
  · apply sub_nonpos.mpr
    exact inv_anti₀ hl2 hmono

/-- Replacing `log p_i` by `log(i+2)` changes the bounded trace summatory function by
`o(n log n)`. -/
theorem maassCPSLocalWeighted_sub_shiftedLog_isLittleO
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ) :
    (fun n : ℕ ↦ maassCPSLocalWeightedPrimeSummatory M r n -
      maassCPSLocalShiftedLogPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n) := by
  have hlogs : (fun n : ℕ ↦ Real.log (nth_prime n)) ~[atTop]
      (fun n : ℕ ↦ Real.log (n + 2)) :=
    log_nth_prime_asymp.trans log_nat_add_two_isEquivalent_log_nat3D.symm
  have htrace : (fun i : ℕ ↦ maassCPSLocalTrace M r i) =O[atTop]
      (fun _i : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound (r + 1)
    filter_upwards with i
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one]
    exact abs_sum_arithmeticSymmetricPowerRoot_maass_re_le M hC r (nthPrime i)
  have hterm : (fun i : ℕ ↦
      (Real.log (nth_prime i) - Real.log (i + 2)) * maassCPSLocalTrace M r i) =o[atTop]
      (fun i : ℕ ↦ Real.log (i + 2)) := by
    simpa only [Pi.sub_apply, Pi.mul_apply, mul_one] using
      hlogs.isLittleO.mul_isBigO htrace
  have hg_nonneg : 0 ≤ fun i : ℕ ↦ Real.log (i + 2) := by
    intro i
    exact Real.log_nonneg (by norm_cast; omega)
  have hg_top : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, Real.log (i + 2))
      atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n ↦ ?_)
    · exact (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    · calc
        Real.log 2 * (n : ℝ) = ∑ _i ∈ Finset.range n, Real.log 2 := by simp [mul_comm]
        _ ≤ ∑ i ∈ Finset.range n, Real.log (i + 2) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Real.log_le_log (by norm_num) (by norm_cast; omega)
  have hsum := hterm.sum_range hg_nonneg hg_top
  have hsumO : (fun n : ℕ ↦ ∑ i ∈ Finset.range n, Real.log (i + 2)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by norm_cast; omega)
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range n, Real.log (i + 2) :=
      Finset.sum_nonneg (fun i _ ↦ hg_nonneg i)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hlogn)]
    calc
      ∑ i ∈ Finset.range n, Real.log (i + 2) ≤
          ∑ _i ∈ Finset.range n, Real.log (n + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.log_le_log (by norm_cast; omega)
        norm_cast
        simp only [Finset.mem_range] at hi
        omega
      _ = (n : ℝ) * Real.log (n + 1) := by simp
      _ ≤ 2 * ((n : ℝ) * Real.log n) := by
        have hn_sq : (n + 1 : ℕ) ≤ n ^ 2 := by
          calc
            n + 1 ≤ n + n := by omega
            _ = n * 2 := by omega
            _ ≤ n * n := Nat.mul_le_mul_left n hn
            _ = n ^ 2 := by ring
        have hn_sq_real : (n + 1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hn_sq
        have hlog : Real.log (n + 1) ≤ 2 * Real.log n := by
          calc
            Real.log (n + 1) ≤ Real.log ((n : ℝ) ^ 2) :=
              Real.log_le_log (by positivity) hn_sq_real
            _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
        calc
          (n : ℝ) * Real.log (n + 1) ≤ (n : ℝ) * (2 * Real.log n) :=
            mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
          _ = 2 * ((n : ℝ) * Real.log n) := by ring
  have hsumShift := (hsum.trans_isBigO hsumO).comp_tendsto (tendsto_add_atTop_nat 1)
  have hconst : (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
    (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop
  have hcast : (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) ~[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    have hrefl : (fun n : ℕ ↦ (n : ℝ)) ~[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
      IsEquivalent.refl
    exact (hrefl.add_isLittleO hconst).congr (fun n ↦ by simp [Pi.add_apply]) (fun _ ↦ rfl)
  have hlog : (fun n : ℕ ↦ Real.log (n + 1)) ~[atTop] (fun n : ℕ ↦ Real.log n) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcast.log tendsto_natCast_atTop_atTop
  have hscale : (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * Real.log (n + 1)) ~[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n) := hcast.mul hlog
  have hscaleComp : ((fun n : ℕ ↦ (n : ℝ) * Real.log n) ∘ fun a ↦ a + 1) ~[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n) := by
    exact hscale.congr (fun n ↦ by simp [Function.comp_apply]) (fun _ ↦ rfl)
  apply (hsumShift.trans_isEquivalent hscaleComp).congr_left
  intro n
  unfold maassCPSLocalWeightedPrimeSummatory maassCPSLocalShiftedLogPrimeSummatory
  rw [Function.comp_apply, Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp [hi, nthPrime, maassCPSLocalTrace]
  ring

/-- At a prime, the retained standard logarithmic coefficient is exactly `log p` times the
literal symmetric-power Satake trace. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_logarithmicCoefficient_prime_re
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) :
    ((T.sources.standardSource r hr).logarithmicCoefficient p).re =
      Real.log p *
        (∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r (maassCPSBase M)
          (show Nat.Primes from ⟨p, hp⟩) j).re := by
  have h := congrArg Complex.re
    (T.standard_logarithmicCoefficient_eq_sum r hr hp (by omega : 0 < 1))
  simp only [pow_one] at h
  rw [← Complex.natCast_log] at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

/-- Reading the prime-only coefficient sum at `p_n` gives the exact weighted first-prime trace. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardPrimeLogarithmicSum_nthPrime
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    T.standardPrimeLogarithmicSum r hr (nthPrime n).1 =
      maassCPSLocalWeightedPrimeSummatory M r n := by
  change T.standardPrimeLogarithmicSum r hr (nth_prime n) =
    maassCPSLocalWeightedPrimeSummatory M r n
  rw [GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardPrimeLogarithmicSum,
    Nat.floor_natCast, ← Nat.primesLE_eq_filter_Ioc_zero,
    primesLE_nthPrime_eq_image_range3D]
  rw [Finset.sum_image]
  · unfold maassCPSLocalWeightedPrimeSummatory
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [T.standard_logarithmicCoefficient_prime_re r hr (prime_nth_prime i)]
    simp only [Finset.mem_range] at hi
    simp [hi, nthPrime]
  · exact (nth_strictMono infinite_setOf_prime).injective.injOn

/-- The cited Wiener--Ikehara estimate for the standard logarithmic coefficients yields
`o(n log n)` for the logarithmically weighted first-prime symmetric-power trace. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.maassCPSLocalWeightedPrimeSummatory_isLittleO_of_cumsum
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r)
    (htotal : (fun N : ℕ ↦ cumsum
      (fun n ↦ ((T.sources.standardSource r hr).logarithmicCoefficient n).re) N) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ))) :
    (fun n : ℕ ↦ maassCPSLocalWeightedPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n) := by
  have hprime := T.standardPrimeLogarithmicSum_nat_isLittleO_of_cumsum r hr htotal
  have hcomp := hprime.comp_tendsto tendsto_nth_prime_atTop
  have hweighted : (fun n : ℕ ↦ maassCPSLocalWeightedPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ (nth_prime n : ℝ)) := by
    apply hcomp.congr_left
    intro n
    exact T.standardPrimeLogarithmicSum_nthPrime r hr n
  exact hweighted.trans_isEquivalent nth_prime_asymp

/-- Passing from the actual prime logarithms to `log(i+2)` preserves the Tauberian
`o(n log n)` estimate. -/
theorem maassCPSLocalShiftedLogPrimeSummatory_isLittleO
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    (hweighted : (fun n : ℕ ↦ maassCPSLocalWeightedPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n)) :
    (fun n : ℕ ↦ maassCPSLocalShiftedLogPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n) := by
  have hdiff := maassCPSLocalWeighted_sub_shiftedLog_isLittleO M hC r
  apply (hweighted.sub hdiff).congr_left
  intro n
  ring

/-- Finite Abel summation removes the positive weight `log(i+2)` from the literal CPS trace. -/
theorem maassCPSLocalPrimeSummatory_isLittleO_of_shiftedLog
    (M : GenuineMaassCuspForm3D) (r : ℕ)
    (hshifted : (fun n : ℕ ↦ maassCPSLocalShiftedLogPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log n)) :
    (fun n : ℕ ↦ maassCPSLocalPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) := by
  let b : ℕ → ℝ := fun n ↦ (Real.log (n + 2))⁻¹
  have hb : b =O[atTop] b := isBigO_refl _ _
  have hboundary0 := hshifted.mul_isBigO hb
  have hboundaryScale :
      (fun n : ℕ ↦ ((n : ℝ) * Real.log n) * b n) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hln2 : 0 < Real.log (n + 2) := Real.log_pos (by norm_cast; omega)
    have hlog : Real.log n ≤ Real.log (n + 2) :=
      Real.log_le_log (by positivity) (by norm_cast; omega)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    simp only [b]
    rw [abs_of_nonneg hn0]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hn0 hln.le) (inv_nonneg.mpr hln2.le))]
    calc
      (n : ℝ) * Real.log n * (Real.log (n + 2))⁻¹ ≤
          (n : ℝ) * Real.log (n + 2) * (Real.log (n + 2))⁻¹ := by
        gcongr
      _ = (n : ℝ) := by field_simp
  have hboundary :
      (fun n : ℕ ↦ maassCPSLocalShiftedLogPrimeSummatory M r n * b n) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) :=
    hboundary0.trans_isBigO hboundaryScale
  have hterm0 := hshifted.mul_isBigO shiftedLogReciprocalNabla_isBigO3D
  have htermScale :
      (fun n : ℕ ↦ ((n : ℝ) * Real.log n) *
        (((n + 1 : ℝ) * Real.log (n + 1))⁻¹)) =O[atTop]
          (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hln1 : 0 < Real.log (n + 1) := Real.log_pos (by norm_cast; omega)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, one_mul]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hn0 hln.le)
      (inv_nonneg.mpr (mul_nonneg hn1.le hln1.le)))]
    rw [← div_eq_mul_inv, div_le_one (mul_pos hn1 hln1)]
    exact mul_le_mul (by norm_num) (Real.log_le_log (by positivity) (by norm_num))
      hln.le hn1.le
  have hterm :
      (fun n : ℕ ↦ maassCPSLocalShiftedLogPrimeSummatory M r n * nabla b n) =o[atTop]
        (fun _n : ℕ ↦ (1 : ℝ)) :=
    hterm0.trans_isBigO htermScale
  have htermTendsto : Tendsto
      (fun n : ℕ ↦ maassCPSLocalShiftedLogPrimeSummatory M r n * nabla b n)
      atTop (nhds 0) := (isLittleO_one_iff ℝ).mp hterm
  have hcorrection :
      (fun n : ℕ ↦ cumsum
        (fun i ↦ maassCPSLocalShiftedLogPrimeSummatory M r i * nabla b i) n) =o[atTop]
          (fun n : ℕ ↦ (n : ℝ)) := by
    simpa only [cumsum] using
      Asymptotics.isLittleO_sum_range_of_tendsto_zero htermTendsto
  have hmain := hboundary.sub hcorrection
  have hunweighted :
      (fun n : ℕ ↦ maassCPSLocalPrimeSummatory M r n) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) := by
    apply hmain.congr_left
    intro n
    let a : ℕ → ℝ := fun i ↦ Real.log (i + 2) * maassCPSLocalTrace M r i
    have hparts := @summation_by_parts' ℝ _ a b n
    have hab : a * b = fun i ↦ maassCPSLocalTrace M r i := by
      funext i
      simp only [Pi.mul_apply, a, b]
      have hlog : Real.log (i + 2) ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_cast; omega))
      field_simp
    have hcumsum_a (k : ℕ) :
        cumsum a (k + 1) = maassCPSLocalShiftedLogPrimeSummatory M r k := by
      unfold cumsum maassCPSLocalShiftedLogPrimeSummatory
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp [a, hi]
    have hshift_a : shift (cumsum a) =
        fun i ↦ maassCPSLocalShiftedLogPrimeSummatory M r i := by
      funext i
      exact hcumsum_a i
    calc
      _ = cumsum (a * b) (n + 1) := by
        rw [hcumsum_a n, hshift_a] at hparts
        simpa only [cumsum, Pi.mul_apply] using hparts.symm
      _ = cumsum (fun i ↦ maassCPSLocalTrace M r i) (n + 1) := by rw [hab]
      _ = _ := by
        unfold cumsum maassCPSLocalPrimeSummatory maassCPSLocalTrace
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [hi]
  have hconst : (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
    (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop
  have hscale : (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
    have hrefl : (fun n : ℕ ↦ (n : ℝ)) ~[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
      IsEquivalent.refl
    exact (hrefl.add_isLittleO hconst).congr (fun n ↦ by simp [Pi.add_apply]) (fun _ ↦ rfl)
  exact hunweighted.trans_isEquivalent hscale.symm

/-- The cited full logarithmic-coefficient estimate yields the exact unweighted prime
summatory conclusion expected by the Sato--Tate endpoint. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.maassCPSLocalPrimeSummatory_isLittleO_of_cumsum
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r)
    (htotal : (fun N : ℕ ↦ cumsum
      (fun n ↦ ((T.sources.standardSource r hr).logarithmicCoefficient n).re) N) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ))) :
    (fun n : ℕ ↦ maassCPSLocalPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) :=
  maassCPSLocalPrimeSummatory_isLittleO_of_shiftedLog M r
    (maassCPSLocalShiftedLogPrimeSummatory_isLittleO M T.toCeiling r
      (T.maassCPSLocalWeightedPrimeSummatory_isLittleO_of_cumsum r hr htotal))

#print axioms CriticalLinePhasor.ThreeDConverse.abs_sum_arithmeticSymmetricPowerRoot_pow_maass_re_le
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.abs_standard_logarithmicCoefficient_re_le
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.abs_standard_compositePrimePowerSum_le
#print axioms CriticalLinePhasor.ThreeDConverse.sqrt_isLittleO_id_atTop3D
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardCompositePrimePowerSum_isLittleO
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_cumsum_eq_prime_add_composite
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardPrimeLogarithmicSum_nat_isLittleO_of_cumsum
#print axioms CriticalLinePhasor.ThreeDConverse.primesLE_nthPrime_eq_image_range3D
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_logarithmicCoefficient_prime_re
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardPrimeLogarithmicSum_nthPrime
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.maassCPSLocalWeightedPrimeSummatory_isLittleO_of_cumsum
#print axioms CriticalLinePhasor.ThreeDConverse.log_nat_add_two_isEquivalent_log_nat3D
#print axioms CriticalLinePhasor.ThreeDConverse.shiftedLogReciprocalNabla_isBigO3D
#print axioms CriticalLinePhasor.ThreeDConverse.maassCPSLocalWeighted_sub_shiftedLog_isLittleO
#print axioms CriticalLinePhasor.ThreeDConverse.maassCPSLocalShiftedLogPrimeSummatory_isLittleO
#print axioms CriticalLinePhasor.ThreeDConverse.maassCPSLocalPrimeSummatory_isLittleO_of_shiftedLog
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.maassCPSLocalPrimeSummatory_isLittleO_of_cumsum

end CriticalLinePhasor.ThreeDConverse
