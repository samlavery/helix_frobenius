import RequestProject.CarrierThetaCoupling
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Dirichlet-inverse synthesis of carrier theta kernels

The dilation action in a coefficient theta bank is multiplicative in its positive integer height.
Consequently, Dirichlet convolution is composition of dilation banks.  This module proves that
identity by regrouping an absolutely summable double series along the divisor antidiagonals, then
uses Mathlib's computable Dirichlet inverse to synthesize a kernel whose coefficient theta is an
arbitrary specified carrier function.
-/

open Complex

namespace CriticalLinePhasor.CarrierTheta

open ArithmeticFunction

/-- The positive-integer-indexed form of a coefficient theta bank. -/
noncomputable def positiveTheta (a : ArithmeticFunction ℂ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ+, a n * h ((n : ℕ) * x)

/-- Shift a zero-indexed coefficient sequence to a positive arithmetic function. -/
def coefficientArithmetic (a : ℕ → ℂ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else a (n - 1)
  map_zero' := rfl

/-- The existing zero-indexed theta is exactly its positive arithmetic-function form. -/
theorem theta_eq_positiveTheta (a : ℕ → ℂ) (h : ℝ → ℂ) (x : ℝ) :
    theta a h x = positiveTheta (coefficientArithmetic a) h x := by
  unfold theta positiveTheta
  have hpnat : (∑' n : ℕ+, (coefficientArithmetic a) n * h ((n : ℕ) * x)) =
      ∑' n : ℕ, (coefficientArithmetic a) (n + 1) * h ((n + 1 : ℕ) * x) :=
    by simpa using (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => (coefficientArithmetic a) n * h (n * x)))
  rw [hpnat]
  apply tsum_congr
  intro n
  simp [coefficientArithmetic]

/-- Regroup an absolutely summable pair of positive dilation indices by their product. -/
theorem positiveTheta_iterated_eq_convolution
    (a b : ArithmeticFunction ℂ) (h : ℝ → ℂ) (x : ℝ)
    (hsum : Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * b p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x)) :
    (∑' m : ℕ+, ∑' d : ℕ+,
      a m * b d * h (((m : ℕ) * (d : ℕ)) * x)) = positiveTheta (a * b) h x := by
  let F : ℕ+ × ℕ+ → ℂ := fun p =>
    a p.1 * b p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x)
  have hsumF : Summable F := by simpa [F] using hsum
  have hsigma : Summable (fun q : (Σ n : ℕ+, (n : ℕ).divisorsAntidiagonal) =>
      F (sigmaAntidiagonalEquivProd q)) :=
    hsumF.comp_injective sigmaAntidiagonalEquivProd.injective
  calc
    (∑' m : ℕ+, ∑' d : ℕ+,
        a m * b d * h (((m : ℕ) * (d : ℕ)) * x)) = ∑' p : ℕ+ × ℕ+, F p := by
          rw [hsumF.tsum_prod]
    _ = ∑' q : (Σ n : ℕ+, (n : ℕ).divisorsAntidiagonal),
        F (sigmaAntidiagonalEquivProd q) :=
          (sigmaAntidiagonalEquivProd.tsum_eq F).symm
    _ = ∑' n : ℕ+, ∑' q : (n : ℕ).divisorsAntidiagonal,
        F (sigmaAntidiagonalEquivProd ⟨n, q⟩) := by
          rw [hsigma.tsum_sigma]
    _ = ∑' n : ℕ+, ∑ q ∈ (n : ℕ).divisorsAntidiagonal,
        a q.1 * b q.2 * h ((n : ℕ) * x) := by
          apply tsum_congr
          intro n
          rw [tsum_fintype]
          simp only [Finset.univ_eq_attach]
          calc
            ∑ q ∈ (n : ℕ).divisorsAntidiagonal.attach,
                F (sigmaAntidiagonalEquivProd ⟨n, q⟩) =
                ∑ q ∈ (n : ℕ).divisorsAntidiagonal.attach,
                  a q.1.1 * b q.1.2 * h ((n : ℕ) * x) := by
                    apply Finset.sum_congr rfl
                    intro q _
                    simp only [F, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
                      divisorsAntidiagonalFactors, PNat.mk_coe]
                    have hprod : q.1.1 * q.1.2 = (n : ℕ) :=
                      (Nat.mem_divisorsAntidiagonal.mp q.2).1
                    have hprodR : (q.1.1 : ℝ) * (q.1.2 : ℝ) = ((n : ℕ) : ℝ) := by
                      exact_mod_cast hprod
                    rw [hprodR]
            _ = ∑ q ∈ (n : ℕ).divisorsAntidiagonal,
                  a q.1 * b q.2 * h ((n : ℕ) * x) := by
                    exact Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
                      (fun q => a q.1 * b q.2 * h ((n : ℕ) * x))
    _ = positiveTheta (a * b) h x := by
          unfold positiveTheta
          apply tsum_congr
          intro n
          rw [ArithmeticFunction.mul_apply, Finset.sum_mul]

/-- The kernel obtained by a second positive dilation bank. -/
noncomputable def dilationKernel (b : ArithmeticFunction ℂ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  positiveTheta b h x

/-- Composition of dilation banks is Dirichlet convolution of their coefficients. -/
theorem positiveTheta_dilationKernel
    (a b : ArithmeticFunction ℂ) (h : ℝ → ℂ) (x : ℝ)
    (hsum : Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * b p.2 * h (((p.1 : ℕ) * (p.2 : ℕ)) * x)) :
    positiveTheta a (dilationKernel b h) x = positiveTheta (a * b) h x := by
  unfold positiveTheta dilationKernel
  calc
    (∑' m : ℕ+, a m * ∑' d : ℕ+, b d * h ((d : ℕ) * ((m : ℕ) * x))) =
        ∑' m : ℕ+, ∑' d : ℕ+,
          a m * b d * h (((m : ℕ) * (d : ℕ)) * x) := by
            apply tsum_congr
            intro m
            calc
              a m * ∑' d : ℕ+, b d * h ((d : ℕ) * ((m : ℕ) * x)) =
                  ∑' d : ℕ+, a m * (b d * h ((d : ℕ) * ((m : ℕ) * x))) :=
                    tsum_mul_left.symm
              _ = ∑' d : ℕ+, a m * b d * h (((m : ℕ) * (d : ℕ)) * x) := by
                    apply tsum_congr
                    intro d
                    have hxscale : ((d : ℕ) : ℝ) * (((m : ℕ) : ℝ) * x) =
                        ((((m : ℕ) * (d : ℕ)) : ℕ) : ℝ) * x := by
                      push_cast
                      ring
                    rw [hxscale]
                    have hxscale' : ((((m : ℕ) * (d : ℕ)) : ℕ) : ℝ) * x =
                        x * ((m : ℕ) : ℝ) * ((d : ℕ) : ℝ) := by
                      push_cast
                      ring
                    rw [hxscale']
                    have harg : x * ((m : ℕ) : ℝ) * ((d : ℕ) : ℝ) =
                        ((m : ℕ) : ℝ) * ((d : ℕ) : ℝ) * x := by ring
                    rw [harg]
                    ring
    _ = positiveTheta (a * b) h x :=
      positiveTheta_iterated_eq_convolution a b h x hsum

/-- The unit arithmetic function acts as the identity dilation bank. -/
theorem positiveTheta_one (h : ℝ → ℂ) (x : ℝ) :
    positiveTheta (1 : ArithmeticFunction ℂ) h x = h x := by
  unfold positiveTheta
  rw [tsum_eq_single (1 : ℕ+)]
  · simp
  · intro n hn
    have hnNat : (n : ℕ) ≠ 1 := by exact_mod_cast hn
    simp [hnNat]

/-- Mathlib's Dirichlet inverse synthesizes a dilation kernel that recovers the carrier function. -/
theorem positiveTheta_dirichletInverse
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1)) (h : ℝ → ℂ) (x : ℝ)
    (hsum : Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * (dirichletInverse a ha) p.2 *
        h (((p.1 : ℕ) * (p.2 : ℕ)) * x)) :
    positiveTheta a (dilationKernel (dirichletInverse a ha) h) x = h x := by
  rw [positiveTheta_dilationKernel a (dirichletInverse a ha) h x hsum,
    self_mul_dirichletInverse, positiveTheta_one]

/-- Zero-indexed coefficient form of the exact Dirichlet-inverse carrier coupling. -/
theorem theta_dirichletInverse_coupling
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (h : ℝ → ℂ) (x : ℝ)
    (hsum : Summable fun p : ℕ+ × ℕ+ =>
      (coefficientArithmetic a) p.1 *
        (dirichletInverse (coefficientArithmetic a) ha) p.2 *
          h (((p.1 : ℕ) * (p.2 : ℕ)) * x)) :
    theta a (dilationKernel (dirichletInverse (coefficientArithmetic a) ha) h) x = h x := by
  rw [theta_eq_positiveTheta]
  exact positiveTheta_dirichletInverse (coefficientArithmetic a) ha h x hsum

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.theta_eq_positiveTheta
#print axioms CriticalLinePhasor.CarrierTheta.positiveTheta_iterated_eq_convolution
#print axioms CriticalLinePhasor.CarrierTheta.positiveTheta_dilationKernel
#print axioms CriticalLinePhasor.CarrierTheta.positiveTheta_dirichletInverse
#print axioms CriticalLinePhasor.CarrierTheta.theta_dirichletInverse_coupling
