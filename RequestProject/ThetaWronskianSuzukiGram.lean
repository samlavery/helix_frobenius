import Mathlib
import RequestProject.CarrierLatticePoisson

/-!
# Finite theta Wronskians and the Suzuki Gram defect

This file keeps the two finite hierarchies independent.

The unfolded finite theta statement is the following.  If `p j` is the degree-`j`
orthogonal polynomial for the even theta moment functional, form

`Wₙ(z) = det ((derivative^[i]) (p (j+1)))`.

The assertion at level `n` is that every complex zero of this real polynomial has
real part zero.  The first three levels use only positivity of the second moment;
their exact Wronskians are proved below.  The next level is the first one that also
sees a fourth-moment inequality.

The unfolded finite Suzuki statement is independent of the Wronskians.  For a
finite test family, let `W` be the matrix of the Weil Hermitian form and let `G` be
the Gram matrix of the Suzuki analysis vectors.  Then

`cᵀ G c ≤ cᵀ W c` for every coefficient vector `c`

is exactly positive semidefiniteness of the defect `W - G`.  This is proved below.
The notation `P̂` in Suzuki's paper denotes an integral transform, not an
orthogonal projection.  The projection theorem below is therefore used only for
Galerkin discretizations and is not substituted for the analytic Suzuki map.

Search record used before construction:

* repository: `rg -n -i "Wronskian|Dimitrov|Suzuki|Gram inequality|Fredholm|Galerkin|Toda"`
* Mathlib names: `rg -n "def wronskian|posSemidef_gram|orthogonalProjection.*norm"`
* semantic searches: "orthogonal projection ... does not increase norm" and
  "Gram matrix ... is positive semidefinite"
* Fredholm search: `‖x‖ < 1 → IsUnit (1 - x)`
* Xi-integrability search: `integrableOn.*pow.*exp`, `integrable.*tsum`,
  `logConcav.*moment`, and `Turan.*Xi` in both the repository and Mathlib
* Xi-integrability decompositions: (A) a summable global exponential majorant;
  (B) termwise integration followed by `integral_tsum`
-/

open Matrix Polynomial
open scoped BigOperators Polynomial Matrix.Norms.L2Operator

noncomputable section

namespace CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ## 0. The actual Riemann theta kernel and its moments -/

/-- The `n+1` summand in Riemann's positive cosine-transform kernel

`4 ∑ₙ (2π²n⁴e^(9u/2) - 3πn²e^(5u/2)) e^(-πn²e^(2u))`.

Indexing by `n : ℕ` avoids a separate positive-natural-number type. -/
def riemannXiKernelTerm (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  (2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) -
      3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u))

/-- Riemann's half-line theta kernel for the Xi cosine transform. -/
def riemannXiKernel (u : ℝ) : ℝ :=
  4 * ∑' n : ℕ, riemannXiKernelTerm n u

/-- The one-strand theta profile in logarithmic height. -/
def xiThetaProfile (u : ℝ) : ℝ :=
  CriticalLinePhasor.CarrierLatticePoisson.strandTheta (Real.exp (2 * u))

/-- Jacobi reflection in logarithmic height, obtained directly from the
compiled one-strand Poisson identity. -/
theorem xiThetaProfile_neg (u : ℝ) :
    xiThetaProfile (-u) = Real.exp u * xiThetaProfile u := by
  have hreflect :=
    CriticalLinePhasor.CarrierLatticePoisson.strandTheta_inv
      (t := Real.exp (2 * u)) (Real.exp_pos _)
  unfold xiThetaProfile
  rw [show Real.exp (2 * -u) = (Real.exp (2 * u))⁻¹ by
    rw [← Real.exp_neg]
    congr 1
    ring]
  rw [hreflect, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- The positive-index Gaussian term in logarithmic height. -/
def xiThetaSeriesTerm (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u))

/-- The Poisson theta profile split into its zero mode and positive modes. -/
theorem xiThetaProfile_eq_zero_add_positive (u : ℝ) :
    xiThetaProfile u = 1 + 2 * ∑' n : ℕ, xiThetaSeriesTerm n u := by
  have hsum := CriticalLinePhasor.CarrierLatticePoisson.summable_gaussInt
    (a := Real.exp (2 * u)) (Real.exp_pos _)
  have heven : Function.Even (fun n : ℤ =>
      Real.exp (-Real.pi * Real.exp (2 * u) * (n : ℝ) ^ 2)) := by
    intro n
    simp
  unfold xiThetaProfile CriticalLinePhasor.CarrierLatticePoisson.strandTheta
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum]
  norm_num
  have hpnat : (∑' n : ℕ+,
      Real.exp (-(Real.pi * Real.exp (2 * u) * ((n : ℕ) : ℝ) ^ 2))) =
      ∑' n : ℕ,
        Real.exp (-(Real.pi * Real.exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using (tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
      Real.exp (-(Real.pi * Real.exp (2 * u) * (n : ℝ) ^ 2))))
  rw [hpnat]
  congr 2
  funext n
  unfold xiThetaSeriesTerm
  dsimp only
  congr 1
  push_cast
  ring

/-- The half-line moments of Riemann's Xi kernel.  The common factor two needed
to pass to the even full-line kernel cancels in every normalized TW inequality. -/
def xiThetaMoment (k : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), u ^ k * riemannXiKernel u

/-- Every summand of Riemann's kernel is strictly positive on the physical
half-line. -/
theorem riemannXiKernelTerm_pos (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < riemannXiKernelTerm n u := by
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have her : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hp1 : Real.pi ≤ Real.pi * r ^ 2 :=
    le_mul_of_one_le_right Real.pi_pos.le hr2
  have hp2 : Real.pi * r ^ 2 ≤ Real.pi * r ^ 2 * Real.exp (2 * u) :=
    le_mul_of_one_le_right (mul_nonneg Real.pi_pos.le (sq_nonneg r)) her
  have hfactor : 0 < 2 * Real.pi * r ^ 2 * Real.exp (2 * u) - 3 := by
    nlinarith [Real.pi_gt_three]
  have hid :
      2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) -
          3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) =
        Real.pi * r ^ 2 * Real.exp (5 * u / 2) *
          (2 * Real.pi * r ^ 2 * Real.exp (2 * u) - 3) := by
    have hexp : Real.exp (9 * u / 2) =
        Real.exp (5 * u / 2) * Real.exp (2 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  unfold riemannXiKernelTerm
  dsimp only
  rw [hid]
  positivity

/-- The positive exponential coordinate in the `n`th kernel summand. -/
def xiKernelQ (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  Real.pi * r ^ 2 * Real.exp (2 * u)

/-- The positive theta term is the exponential of the negative kernel
coordinate. -/
theorem xiThetaSeriesTerm_eq_exp_neg_q (n : ℕ) (u : ℝ) :
    xiThetaSeriesTerm n u = Real.exp (-xiKernelQ n u) := by
  unfold xiThetaSeriesTerm xiKernelQ
  dsimp only
  congr 1
  ring

/-- Formal first height derivative of a positive theta-series term. -/
def xiThetaSeriesDeriv1 (n : ℕ) (u : ℝ) : ℝ :=
  -2 * xiKernelQ n u * Real.exp (-xiKernelQ n u)

/-- Formal second height derivative of a positive theta-series term. -/
def xiThetaSeriesDeriv2 (n : ℕ) (u : ℝ) : ℝ :=
  (4 * xiKernelQ n u ^ 2 - 4 * xiKernelQ n u) *
    Real.exp (-xiKernelQ n u)

/-- A separated index majorant for powers of the Gaussian coordinate on the
unit window centered at `a`. -/
def xiThetaLocalMajorantCoeff (m : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  let r : ℝ := n + 1
  let cUpper : ℝ := Real.pi * Real.exp (2 * (a + 1))
  let cLower : ℝ := Real.pi * Real.exp (2 * (a - 1))
  cUpper ^ m * r ^ (2 * m) * Real.exp (-cLower * r)

/-- The local Gaussian majorant is summable for every derivative order and
window center. -/
theorem xiThetaLocalMajorantCoeff_summable (m : ℕ) (a : ℝ) :
    Summable (xiThetaLocalMajorantCoeff m a) := by
  let cUpper : ℝ := Real.pi * Real.exp (2 * (a + 1))
  let cLower : ℝ := Real.pi * Real.exp (2 * (a - 1))
  have hcLower : 0 < cLower := by
    dsimp [cLower]
    positivity
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ (2 * m) * Real.exp (-cLower * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul (2 * m) hcLower
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (2 * m) *
        Real.exp (-cLower * (n + 1 : ℕ))) :=
    (summable_nat_add_iff 1).2 hbase
  have hscaled := hshift.mul_left (cUpper ^ m)
  rw [show xiThetaLocalMajorantCoeff m a = fun n : ℕ =>
      cUpper ^ m *
        (((n + 1 : ℕ) : ℝ) ^ (2 * m) *
          Real.exp (-cLower * (n + 1 : ℕ))) by
    funext n
    change cUpper ^ m * ((n : ℝ) + 1) ^ (2 * m) *
        Real.exp (-cLower * ((n : ℝ) + 1)) =
      cUpper ^ m *
        (((n + 1 : ℕ) : ℝ) ^ (2 * m) *
          Real.exp (-cLower * (n + 1 : ℕ)))
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring]
  exact hscaled

/-- Uniform domination of a coordinate power times its Gaussian on the unit
window centered at `a`. -/
theorem xiKernelQ_pow_mul_exp_neg_le_local
    (m n : ℕ) {a v : ℝ} (hv : v ∈ Set.Ioo (a - 1) (a + 1)) :
    xiKernelQ n v ^ m * Real.exp (-xiKernelQ n v) ≤
      xiThetaLocalMajorantCoeff m a n := by
  let r : ℝ := n + 1
  let cUpper : ℝ := Real.pi * Real.exp (2 * (a + 1))
  let cLower : ℝ := Real.pi * Real.exp (2 * (a - 1))
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr2 : r ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hcUpper : 0 ≤ cUpper := by
    dsimp [cUpper]
    positivity
  have hcLower : 0 ≤ cLower := by
    dsimp [cLower]
    positivity
  have heLower : Real.exp (2 * (a - 1)) ≤ Real.exp (2 * v) :=
    Real.exp_le_exp.mpr (by linarith [hv.1])
  have heUpper : Real.exp (2 * v) ≤ Real.exp (2 * (a + 1)) :=
    Real.exp_le_exp.mpr (by linarith [hv.2])
  have hqLower : cLower * r ^ 2 ≤ xiKernelQ n v := by
    have h := mul_le_mul_of_nonneg_left heLower
      (mul_nonneg Real.pi_pos.le (sq_nonneg r))
    simpa [cLower, xiKernelQ, r, mul_assoc, mul_left_comm, mul_comm] using h
  have hqUpper : xiKernelQ n v ≤ cUpper * r ^ 2 := by
    have h := mul_le_mul_of_nonneg_left heUpper
      (mul_nonneg Real.pi_pos.le (sq_nonneg r))
    simpa [cUpper, xiKernelQ, r, mul_assoc, mul_left_comm, mul_comm] using h
  have hq0 : 0 ≤ xiKernelQ n v := by
    unfold xiKernelQ
    positivity
  have hpow : xiKernelQ n v ^ m ≤ (cUpper * r ^ 2) ^ m :=
    pow_le_pow_left₀ hq0 hqUpper m
  have hexp : Real.exp (-xiKernelQ n v) ≤
      Real.exp (-cLower * r) := by
    apply Real.exp_le_exp.mpr
    have h1 : -xiKernelQ n v ≤ -(cLower * r ^ 2) := neg_le_neg hqLower
    have h2 : -(cLower * r ^ 2) ≤ -cLower * r := by
      calc
        -(cLower * r ^ 2) ≤ -(cLower * r) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hr2 hcLower)
        _ = -cLower * r := by ring
    exact h1.trans h2
  calc
    xiKernelQ n v ^ m * Real.exp (-xiKernelQ n v) ≤
        (cUpper * r ^ 2) ^ m * Real.exp (-cLower * r) :=
      mul_le_mul hpow hexp (Real.exp_pos _).le
        (pow_nonneg (mul_nonneg hcUpper (sq_nonneg r)) m)
    _ = xiThetaLocalMajorantCoeff m a n := by
      unfold xiThetaLocalMajorantCoeff
      dsimp only
      rw [mul_pow, pow_mul]

/-- Locally uniform summable bound for the first theta derivative. -/
theorem xiThetaSeriesDeriv1_norm_le_local
    (n : ℕ) {a v : ℝ} (hv : v ∈ Set.Ioo (a - 1) (a + 1)) :
    ‖xiThetaSeriesDeriv1 n v‖ ≤
      2 * xiThetaLocalMajorantCoeff 1 a n := by
  have hq0 : 0 ≤ xiKernelQ n v := by
    unfold xiKernelQ
    positivity
  have hmajor := xiKernelQ_pow_mul_exp_neg_le_local 1 n hv
  calc
    ‖xiThetaSeriesDeriv1 n v‖ =
        2 * (xiKernelQ n v ^ 1 * Real.exp (-xiKernelQ n v)) := by
      unfold xiThetaSeriesDeriv1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hq0,
        abs_of_pos (Real.exp_pos _), pow_one]
      norm_num
      ring
    _ ≤ 2 * xiThetaLocalMajorantCoeff 1 a n :=
      mul_le_mul_of_nonneg_left hmajor (by norm_num)

/-- Locally uniform summable bound for the second theta derivative. -/
theorem xiThetaSeriesDeriv2_norm_le_local
    (n : ℕ) {a v : ℝ} (hv : v ∈ Set.Ioo (a - 1) (a + 1)) :
    ‖xiThetaSeriesDeriv2 n v‖ ≤
      4 * xiThetaLocalMajorantCoeff 2 a n +
        4 * xiThetaLocalMajorantCoeff 1 a n := by
  have hq0 : 0 ≤ xiKernelQ n v := by
    unfold xiKernelQ
    positivity
  have h1 := xiKernelQ_pow_mul_exp_neg_le_local 1 n hv
  have h2 := xiKernelQ_pow_mul_exp_neg_le_local 2 n hv
  have habs : |4 * xiKernelQ n v ^ 2 - 4 * xiKernelQ n v| ≤
      4 * xiKernelQ n v ^ 2 + 4 * xiKernelQ n v := by
    calc
      |4 * xiKernelQ n v ^ 2 - 4 * xiKernelQ n v| ≤
          |4 * xiKernelQ n v ^ 2| + |4 * xiKernelQ n v| := abs_sub _ _
      _ = 4 * xiKernelQ n v ^ 2 + 4 * xiKernelQ n v := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc
    ‖xiThetaSeriesDeriv2 n v‖ =
        |4 * xiKernelQ n v ^ 2 - 4 * xiKernelQ n v| *
          Real.exp (-xiKernelQ n v) := by
      unfold xiThetaSeriesDeriv2
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (4 * xiKernelQ n v ^ 2 + 4 * xiKernelQ n v) *
        Real.exp (-xiKernelQ n v) :=
      mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ = 4 * (xiKernelQ n v ^ 2 * Real.exp (-xiKernelQ n v)) +
        4 * (xiKernelQ n v ^ 1 * Real.exp (-xiKernelQ n v)) := by
      rw [pow_one]
      ring
    _ ≤ 4 * xiThetaLocalMajorantCoeff 2 a n +
        4 * xiThetaLocalMajorantCoeff 1 a n :=
      add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
        (mul_le_mul_of_nonneg_left h1 (by norm_num))

/-- The formal theta operator appearing in Riemann's kernel. -/
def xiThetaProfileOperatorSeries (u : ℝ) : ℝ :=
  2 * (∑' n : ℕ, (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u))

/-- One Riemann-kernel summand is the completed theta operator applied to one
positive Gaussian mode. -/
theorem four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm
    (n : ℕ) (u : ℝ) :
    4 * riemannXiKernelTerm n u =
      Real.exp (u / 2) *
        (2 * (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u)) := by
  unfold riemannXiKernelTerm xiThetaSeriesDeriv1 xiThetaSeriesDeriv2 xiKernelQ
  dsimp only
  have h5 : Real.exp (5 * u / 2) =
      Real.exp (u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h9 : Real.exp (9 * u / 2) =
      Real.exp (u / 2) * Real.exp (2 * u) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [h5, h9]
  ring

/-- Exact algebraic identification of Riemann's kernel with the formal
completed theta operator series. -/
theorem riemannXiKernel_eq_profileOperatorSeries (u : ℝ) :
    riemannXiKernel u =
      Real.exp (u / 2) * xiThetaProfileOperatorSeries u := by
  unfold riemannXiKernel xiThetaProfileOperatorSeries
  calc
    4 * (∑' n : ℕ, riemannXiKernelTerm n u) =
        ∑' n : ℕ, 4 * riemannXiKernelTerm n u := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, Real.exp (u / 2) *
        (2 * (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u)) :=
      tsum_congr fun n =>
        four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm n u
    _ = (Real.exp (u / 2) * 2) *
        (∑' n : ℕ,
          (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u)) := by
      rw [show (fun n : ℕ => Real.exp (u / 2) *
          (2 * (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u))) =
          fun n : ℕ => (Real.exp (u / 2) * 2) *
            (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u) from
        funext fun n => by ring]
      rw [tsum_mul_left]
    _ = Real.exp (u / 2) *
        (2 * (∑' n : ℕ,
          (xiThetaSeriesDeriv2 n u + xiThetaSeriesDeriv1 n u))) := by ring

/-- The positive affine factor in the `n`th Riemann-kernel summand after its
common exponential factors are removed. -/
def xiKernelInner (n : ℕ) (u : ℝ) : ℝ :=
  2 * xiKernelQ n u - 3

/-- Exact positive-factor decomposition of one Riemann-kernel summand. -/
theorem riemannXiKernelTerm_factorized (n : ℕ) (u : ℝ) :
    riemannXiKernelTerm n u =
      let r : ℝ := n + 1
      Real.pi * r ^ 2 * Real.exp (5 * u / 2) * xiKernelInner n u *
        Real.exp (-xiKernelQ n u) := by
  let r : ℝ := n + 1
  have hexp : Real.exp (9 * u / 2) =
      Real.exp (5 * u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold riemannXiKernelTerm xiKernelInner xiKernelQ
  dsimp only
  rw [hexp]
  ring

/-- The inner factor is strictly positive throughout the physical half-line. -/
theorem xiKernelInner_pos (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < xiKernelInner n u := by
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have her : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hp1 : Real.pi ≤ Real.pi * r ^ 2 :=
    le_mul_of_one_le_right Real.pi_pos.le hr2
  have hp2 : Real.pi * r ^ 2 ≤ Real.pi * r ^ 2 * Real.exp (2 * u) :=
    le_mul_of_one_le_right (mul_nonneg Real.pi_pos.le (sq_nonneg r)) her
  unfold xiKernelInner xiKernelQ
  dsimp only
  nlinarith [Real.pi_gt_three]

/-- The explicit second logarithmic-derivative expression for one isolated
Riemann-kernel summand. -/
def xiKernelTermLogCurvature (n : ℕ) (u : ℝ) : ℝ :=
  (-24 * xiKernelQ n u / xiKernelInner n u ^ 2) - 4 * xiKernelQ n u

/-- The explicit first logarithmic-derivative expression for one isolated
Riemann-kernel summand. -/
def xiKernelTermLogSlope (n : ℕ) : ℝ → ℝ :=
  (fun _ => 5 / 2) + (fun u => 4 * xiKernelQ n u) / xiKernelInner n -
    fun u => 2 * xiKernelQ n u

/-- Derivative of the positive exponential coordinate. -/
theorem xiKernelQ_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiKernelQ n) (2 * xiKernelQ n u) u := by
  let r : ℝ := n + 1
  have h := ((hasDerivAt_id u).const_mul 2).exp.const_mul (Real.pi * r ^ 2)
  have heq : xiKernelQ n =ᶠ[nhds u]
      (fun y : ℝ => Real.pi * r ^ 2 * Real.exp (2 * id y)) := by
    filter_upwards [] with y
    simp only [xiKernelQ, id_eq, r]
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  simp only [xiKernelQ, id_eq, r]
  ring

/-- The formal first derivative is the actual derivative of one positive
theta-series mode. -/
theorem xiThetaSeriesTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiThetaSeriesTerm n) (xiThetaSeriesDeriv1 n u) u := by
  have hneg := (xiKernelQ_hasDerivAt n u).neg
  have hexp := (Real.hasDerivAt_exp (-xiKernelQ n u)).comp u hneg
  have heq : xiThetaSeriesTerm n =ᶠ[nhds u]
      (Real.exp ∘ (-xiKernelQ n)) := by
    filter_upwards [] with v
    simp only [Function.comp_apply, Pi.neg_apply]
    exact xiThetaSeriesTerm_eq_exp_neg_q n v
  have hterm := hexp.congr_of_eventuallyEq heq
  apply hterm.congr_deriv
  unfold xiThetaSeriesDeriv1
  ring

/-- The formal second derivative is the actual derivative of the first
theta-series derivative. -/
theorem xiThetaSeriesDeriv1_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiThetaSeriesDeriv1 n) (xiThetaSeriesDeriv2 n u) u := by
  have hq := xiKernelQ_hasDerivAt n u
  have hneg := hq.neg
  have hexp := (Real.hasDerivAt_exp (-xiKernelQ n u)).comp u hneg
  have h := (hq.const_mul (-2 : ℝ)).mul hexp
  have hfun : xiThetaSeriesDeriv1 n =
      (fun v => -2 * xiKernelQ n v) *
        (Real.exp ∘ (-xiKernelQ n)) := by
    unfold xiThetaSeriesDeriv1
    funext v
    simp only [Pi.mul_apply, Function.comp_apply, Pi.neg_apply]
  rw [hfun]
  have hval :
      -2 * (2 * xiKernelQ n u) * (Real.exp ∘ (-xiKernelQ n)) u +
          -2 * xiKernelQ n u *
            (Real.exp (-xiKernelQ n u) * -(2 * xiKernelQ n u)) =
        xiThetaSeriesDeriv2 n u := by
    simp only [Function.comp_apply, Pi.neg_apply]
    unfold xiThetaSeriesDeriv2
    ring
  rw [← hval]
  exact h

/-- The positive theta modes are summable at every logarithmic height. -/
theorem xiThetaSeriesTerm_summable (a : ℝ) :
    Summable (fun n : ℕ => xiThetaSeriesTerm n a) := by
  have ha : a ∈ Set.Ioo (a - 1) (a + 1) := by constructor <;> linarith
  apply Summable.of_norm_bounded (xiThetaLocalMajorantCoeff_summable 0 a)
  intro n
  have h := xiKernelQ_pow_mul_exp_neg_le_local 0 n ha
  rw [xiThetaSeriesTerm_eq_exp_neg_q, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa using h

/-- The first formal theta-derivative series is summable at every height. -/
theorem xiThetaSeriesDeriv1_summable (a : ℝ) :
    Summable (fun n : ℕ => xiThetaSeriesDeriv1 n a) := by
  have ha : a ∈ Set.Ioo (a - 1) (a + 1) := by constructor <;> linarith
  exact Summable.of_norm_bounded
    ((xiThetaLocalMajorantCoeff_summable 1 a).mul_left 2)
    (fun n => xiThetaSeriesDeriv1_norm_le_local n ha)

/-- The second formal theta-derivative series is summable at every height. -/
theorem xiThetaSeriesDeriv2_summable (a : ℝ) :
    Summable (fun n : ℕ => xiThetaSeriesDeriv2 n a) := by
  have ha : a ∈ Set.Ioo (a - 1) (a + 1) := by constructor <;> linarith
  have hmajor : Summable (fun n : ℕ =>
      4 * xiThetaLocalMajorantCoeff 2 a n +
        4 * xiThetaLocalMajorantCoeff 1 a n) :=
    (xiThetaLocalMajorantCoeff_summable 2 a).mul_left 4 |>.add
      ((xiThetaLocalMajorantCoeff_summable 1 a).mul_left 4)
  exact Summable.of_norm_bounded hmajor
    (fun n => xiThetaSeriesDeriv2_norm_le_local n ha)

/-- First derivative of the Poisson theta profile, obtained by locally
uniform termwise differentiation of its positive-mode expansion. -/
theorem xiThetaProfile_hasDerivAt (a : ℝ) :
    HasDerivAt xiThetaProfile
      (2 * ∑' n : ℕ, xiThetaSeriesDeriv1 n a) a := by
  have ha : a ∈ Set.Ioo (a - 1) (a + 1) := by constructor <;> linarith
  have hsum := hasDerivAt_tsum_of_isPreconnected
    ((xiThetaLocalMajorantCoeff_summable 1 a).mul_left 2)
    isOpen_Ioo isPreconnected_Ioo
    (fun n v hv => xiThetaSeriesTerm_hasDerivAt n v)
    (fun n v hv => xiThetaSeriesDeriv1_norm_le_local n hv)
    ha (xiThetaSeriesTerm_summable a) ha
  have hprofile := (hsum.const_mul (2 : ℝ)).const_add (1 : ℝ)
  have heq : xiThetaProfile =ᶠ[nhds a]
      (fun v => 1 + 2 * ∑' n : ℕ, xiThetaSeriesTerm n v) := by
    filter_upwards [] with v
    exact xiThetaProfile_eq_zero_add_positive v
  have hprofile' := hprofile.congr_of_eventuallyEq heq
  apply hprofile'.congr_deriv
  ring

/-- Second derivative of the Poisson theta profile, obtained by a second
locally uniform termwise differentiation. -/
theorem xiThetaProfile_deriv_hasDerivAt (a : ℝ) :
    HasDerivAt (deriv xiThetaProfile)
      (2 * ∑' n : ℕ, xiThetaSeriesDeriv2 n a) a := by
  have ha : a ∈ Set.Ioo (a - 1) (a + 1) := by constructor <;> linarith
  have hmajor : Summable (fun n : ℕ =>
      4 * xiThetaLocalMajorantCoeff 2 a n +
        4 * xiThetaLocalMajorantCoeff 1 a n) :=
    (xiThetaLocalMajorantCoeff_summable 2 a).mul_left 4 |>.add
      ((xiThetaLocalMajorantCoeff_summable 1 a).mul_left 4)
  have hsum := hasDerivAt_tsum_of_isPreconnected hmajor
    isOpen_Ioo isPreconnected_Ioo
    (fun n v hv => xiThetaSeriesDeriv1_hasDerivAt n v)
    (fun n v hv => xiThetaSeriesDeriv2_norm_le_local n hv)
    ha (xiThetaSeriesDeriv1_summable a) ha
  have hseries := hsum.const_mul (2 : ℝ)
  have heq : deriv xiThetaProfile =ᶠ[nhds a]
      (fun v => 2 * ∑' n : ℕ, xiThetaSeriesDeriv1 n v) := by
    filter_upwards [] with v
    exact (xiThetaProfile_hasDerivAt v).deriv
  exact hseries.congr_of_eventuallyEq heq

/-- The formal completed theta series is the literal differential operator
`D² + D` applied to the Poisson theta profile. -/
theorem xiThetaProfile_operatorSeries_eq (u : ℝ) :
    xiThetaProfileOperatorSeries u =
      deriv (deriv xiThetaProfile) u + deriv xiThetaProfile u := by
  rw [(xiThetaProfile_hasDerivAt u).deriv,
    (xiThetaProfile_deriv_hasDerivAt u).deriv]
  unfold xiThetaProfileOperatorSeries
  rw [(xiThetaSeriesDeriv2_summable u).tsum_add
    (xiThetaSeriesDeriv1_summable u)]
  ring

/-- Riemann's kernel is the completed differential theta profile. -/
theorem riemannXiKernel_eq_profile_operator (u : ℝ) :
    riemannXiKernel u =
      Real.exp (u / 2) *
        (deriv (deriv xiThetaProfile) u + deriv xiThetaProfile u) := by
  rw [riemannXiKernel_eq_profileOperatorSeries,
    xiThetaProfile_operatorSeries_eq]

/-- First differentiated Jacobi reflection identity. -/
theorem xiThetaProfile_deriv_reflection (u : ℝ) :
    -deriv xiThetaProfile (-u) =
      Real.exp u * (xiThetaProfile u + deriv xiThetaProfile u) := by
  have hleft : HasDerivAt (xiThetaProfile ∘ Neg.neg)
      (-deriv xiThetaProfile (-u)) u := by
    have h := (xiThetaProfile_hasDerivAt (-u)).comp u (hasDerivAt_neg u)
    rw [← (xiThetaProfile_hasDerivAt (-u)).deriv] at h
    apply h.congr_deriv
    ring
  have hprofile : HasDerivAt xiThetaProfile (deriv xiThetaProfile u) u := by
    apply (xiThetaProfile_hasDerivAt u).congr_deriv
    exact (xiThetaProfile_hasDerivAt u).deriv.symm
  have hright : HasDerivAt (fun v => Real.exp v * xiThetaProfile v)
      (Real.exp u * (xiThetaProfile u + deriv xiThetaProfile u)) u := by
    apply ((Real.hasDerivAt_exp u).mul hprofile).congr_deriv
    ring
  have heq : (xiThetaProfile ∘ Neg.neg) =ᶠ[nhds u]
      (fun v => Real.exp v * xiThetaProfile v) := by
    filter_upwards [] with v
    exact xiThetaProfile_neg v
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

/-- Second differentiated Jacobi reflection identity. -/
theorem xiThetaProfile_deriv2_reflection (u : ℝ) :
    deriv (deriv xiThetaProfile) (-u) =
      Real.exp u * (xiThetaProfile u + 2 * deriv xiThetaProfile u +
        deriv (deriv xiThetaProfile) u) := by
  have hsecondNeg : HasDerivAt (deriv xiThetaProfile)
      (deriv (deriv xiThetaProfile) (-u)) (-u) := by
    apply (xiThetaProfile_deriv_hasDerivAt (-u)).congr_deriv
    exact (xiThetaProfile_deriv_hasDerivAt (-u)).deriv.symm
  have hleft : HasDerivAt
      (fun v => -deriv xiThetaProfile (-v))
      (deriv (deriv xiThetaProfile) (-u)) u := by
    have h := (hsecondNeg.comp u (hasDerivAt_neg u)).neg
    apply h.congr_deriv
    ring
  have hprofile : HasDerivAt xiThetaProfile (deriv xiThetaProfile u) u := by
    apply (xiThetaProfile_hasDerivAt u).congr_deriv
    exact (xiThetaProfile_hasDerivAt u).deriv.symm
  have hsecond : HasDerivAt (deriv xiThetaProfile)
      (deriv (deriv xiThetaProfile) u) u := by
    apply (xiThetaProfile_deriv_hasDerivAt u).congr_deriv
    exact (xiThetaProfile_deriv_hasDerivAt u).deriv.symm
  have hright : HasDerivAt
      (fun v => Real.exp v *
        (xiThetaProfile v + deriv xiThetaProfile v))
      (Real.exp u * (xiThetaProfile u + 2 * deriv xiThetaProfile u +
        deriv (deriv xiThetaProfile) u)) u := by
    apply ((Real.hasDerivAt_exp u).mul (hprofile.add hsecond)).congr_deriv
    simp only [Pi.add_apply]
    ring
  have heq : (fun v => -deriv xiThetaProfile (-v)) =ᶠ[nhds u]
      (fun v => Real.exp v *
        (xiThetaProfile v + deriv xiThetaProfile v)) := by
    filter_upwards [] with v
    exact xiThetaProfile_deriv_reflection v
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

/-- The completed theta operator has weight one under Jacobi reflection. -/
theorem xiThetaProfile_operator_reflection (u : ℝ) :
    deriv (deriv xiThetaProfile) (-u) + deriv xiThetaProfile (-u) =
      Real.exp u *
        (deriv (deriv xiThetaProfile) u + deriv xiThetaProfile u) := by
  have hneg : deriv xiThetaProfile (-u) =
      -Real.exp u * (xiThetaProfile u + deriv xiThetaProfile u) := by
    linarith [xiThetaProfile_deriv_reflection u]
  rw [xiThetaProfile_deriv2_reflection, hneg]
  ring

/-- Evenness of Riemann's Xi kernel, obtained from the Jacobi reflection law
and the exact completed-profile identity. -/
theorem riemannXiKernel_neg (u : ℝ) :
    riemannXiKernel (-u) = riemannXiKernel u := by
  rw [riemannXiKernel_eq_profile_operator,
    riemannXiKernel_eq_profile_operator,
    xiThetaProfile_operator_reflection]
  calc
    Real.exp (-u / 2) *
        (Real.exp u *
          (deriv (deriv xiThetaProfile) u + deriv xiThetaProfile u)) =
        (Real.exp (-u / 2) * Real.exp u) *
          (deriv (deriv xiThetaProfile) u + deriv xiThetaProfile u) := by ring
    _ = Real.exp (-u / 2 + u) *
          (deriv (deriv xiThetaProfile) u + deriv xiThetaProfile u) := by
      rw [Real.exp_add]
    _ = Real.exp (u / 2) *
          (deriv (deriv xiThetaProfile) u + deriv xiThetaProfile u) := by
      congr 2
      ring

/-- The first origin jet vanishes.  This conclusion is valid directly for
Lean's total `deriv`: in the differentiable branch it follows from evenness,
and in the complementary branch `deriv` is definitionally zero. -/
theorem riemannXiKernel_deriv_zero : deriv riemannXiKernel 0 = 0 := by
  by_cases hdiff : DifferentiableAt ℝ riemannXiKernel 0
  · have hK : HasDerivAt riemannXiKernel (deriv riemannXiKernel 0) 0 :=
      hdiff.hasDerivAt
    have hKneg : HasDerivAt riemannXiKernel
        (deriv riemannXiKernel 0) (-0 : ℝ) := by simpa using hK
    have hneg := hKneg.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have heq : (riemannXiKernel ∘ Neg.neg) =ᶠ[nhds 0]
        riemannXiKernel := by
      filter_upwards [] with v
      exact riemannXiKernel_neg v
    have hslope := (hneg.congr_of_eventuallyEq heq.symm).unique hK
    norm_num [Function.comp_apply] at hslope
    linarith
  · exact deriv_zero_of_not_differentiableAt hdiff

/-- The even quartic Taylor jet with prescribed values `k₀`, `k₂`, `k₄`. -/
def xiEvenQuarticJet (k₀ k₂ k₄ u : ℝ) : ℝ :=
  k₀ + k₂ / 2 * u ^ 2 + k₄ / 24 * u ^ 4

/-- The literal first derivative polynomial of `xiEvenQuarticJet`. -/
def xiEvenQuarticJetDeriv1 (k₂ k₄ u : ℝ) : ℝ :=
  k₂ * u + k₄ / 6 * u ^ 3

/-- The literal second derivative polynomial of `xiEvenQuarticJet`. -/
def xiEvenQuarticJetDeriv2 (k₂ k₄ u : ℝ) : ℝ :=
  k₂ + k₄ / 2 * u ^ 2

/-- Exact radial numerator of the even quartic jet.  The leading coefficient
is the cubic cornerstone `k₂² - k₀ k₄ / 3`; the remaining terms are
displayed rather than hidden in asymptotic notation. -/
theorem xiEvenQuarticJet_radialNumerator (k₀ k₂ k₄ u : ℝ) :
    u * xiEvenQuarticJetDeriv1 k₂ k₄ u ^ 2 -
        u * xiEvenQuarticJet k₀ k₂ k₄ u *
          xiEvenQuarticJetDeriv2 k₂ k₄ u +
        xiEvenQuarticJet k₀ k₂ k₄ u *
          xiEvenQuarticJetDeriv1 k₂ k₄ u =
      (k₂ ^ 2 - k₀ * k₄ / 3) * u ^ 3 +
        (k₂ * k₄ / 6) * u ^ 5 +
        (k₄ ^ 2 / 72) * u ^ 7 := by
  unfold xiEvenQuarticJet xiEvenQuarticJetDeriv1 xiEvenQuarticJetDeriv2
  ring

/-- The finite theta-constant inequality is exactly positivity of the cubic
coefficient in the radial numerator jet. -/
theorem xiOriginCubicCoefficient_pos_iff (k₀ k₂ k₄ : ℝ) :
    0 < k₂ ^ 2 - k₀ * k₄ / 3 ↔ k₀ * k₄ < 3 * k₂ ^ 2 := by
  constructor <;> intro h <;> nlinarith

/-! ### Gaussian origin jets through order four -/

/-- Exponential coordinate for one Gaussian mode. -/
def xiGaussianQ (c u : ℝ) : ℝ := c * Real.exp (2 * u)

/-- One exponential-Gaussian mode `exp (a u - c exp(2u))`. -/
def xiGaussianMode (a c u : ℝ) : ℝ :=
  Real.exp (a * u - xiGaussianQ c u)

/-- Logarithmic slope of one exponential-Gaussian mode. -/
def xiGaussianSlope (a c u : ℝ) : ℝ := a - 2 * xiGaussianQ c u

def xiGaussianJet1 (a c u : ℝ) : ℝ :=
  xiGaussianSlope a c u * xiGaussianMode a c u

def xiGaussianJet2 (a c u : ℝ) : ℝ :=
  (xiGaussianSlope a c u ^ 2 - 4 * xiGaussianQ c u) *
    xiGaussianMode a c u

def xiGaussianJet3 (a c u : ℝ) : ℝ :=
  (xiGaussianSlope a c u ^ 3 -
      12 * (xiGaussianQ c u * xiGaussianSlope a c u) -
      8 * xiGaussianQ c u) * xiGaussianMode a c u

def xiGaussianJet4 (a c u : ℝ) : ℝ :=
  (xiGaussianSlope a c u ^ 4 -
      24 * xiGaussianQ c u * xiGaussianSlope a c u ^ 2 -
      32 * xiGaussianQ c u * xiGaussianSlope a c u +
      48 * xiGaussianQ c u ^ 2 - 16 * xiGaussianQ c u) *
    xiGaussianMode a c u

theorem xiGaussianQ_hasDerivAt (c u : ℝ) :
    HasDerivAt (xiGaussianQ c) (2 * xiGaussianQ c u) u := by
  change HasDerivAt (fun v : ℝ => c * Real.exp (2 * v))
    (2 * (c * Real.exp (2 * u))) u
  apply ((((hasDerivAt_id u).const_mul 2).exp).const_mul c).congr_deriv
  simp only [id_eq]
  ring

theorem xiGaussianSlope_hasDerivAt (a c u : ℝ) :
    HasDerivAt (xiGaussianSlope a c) (-4 * xiGaussianQ c u) u := by
  change HasDerivAt (fun v : ℝ => a - 2 * xiGaussianQ c v)
    (-4 * xiGaussianQ c u) u
  apply (((xiGaussianQ_hasDerivAt c u).const_mul 2).const_sub a).congr_deriv
  ring

theorem xiGaussianMode_hasDerivAt (a c u : ℝ) :
    HasDerivAt (xiGaussianMode a c) (xiGaussianJet1 a c u) u := by
  have hexponent : HasDerivAt (fun v => a * v - xiGaussianQ c v)
      (xiGaussianSlope a c u) u := by
    unfold xiGaussianSlope
    apply (((hasDerivAt_id u).const_mul a).sub
      (xiGaussianQ_hasDerivAt c u)).congr_deriv
    ring
  have h := (Real.hasDerivAt_exp
    (a * u - xiGaussianQ c u)).comp u hexponent
  have heq : xiGaussianMode a c =ᶠ[nhds u]
      (Real.exp ∘ fun v => a * v - xiGaussianQ c v) := by
    filter_upwards [] with v
    rfl
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  unfold xiGaussianJet1 xiGaussianMode
  ring

theorem xiGaussianJet1_hasDerivAt (a c u : ℝ) :
    HasDerivAt (xiGaussianJet1 a c) (xiGaussianJet2 a c u) u := by
  have h := (xiGaussianSlope_hasDerivAt a c u).mul
    (xiGaussianMode_hasDerivAt a c u)
  apply h.congr_deriv
  unfold xiGaussianJet1 xiGaussianJet2
  ring

theorem xiGaussianJet2_hasDerivAt (a c u : ℝ) :
    HasDerivAt (xiGaussianJet2 a c) (xiGaussianJet3 a c u) u := by
  have hpoly : HasDerivAt
      (fun v => xiGaussianSlope a c v ^ 2 - 4 * xiGaussianQ c v)
      (-8 * xiGaussianQ c u * xiGaussianSlope a c u -
        8 * xiGaussianQ c u) u := by
    apply (((xiGaussianSlope_hasDerivAt a c u).pow 2).sub
      ((xiGaussianQ_hasDerivAt c u).const_mul 4)).congr_deriv
    ring
  have h := hpoly.mul (xiGaussianMode_hasDerivAt a c u)
  apply h.congr_deriv
  unfold xiGaussianJet3 xiGaussianJet1
  ring

theorem xiGaussianJet3_hasDerivAt (a c u : ℝ) :
    HasDerivAt (xiGaussianJet3 a c) (xiGaussianJet4 a c u) u := by
  have hs := xiGaussianSlope_hasDerivAt a c u
  have hq := xiGaussianQ_hasDerivAt c u
  have hpoly : HasDerivAt
      (fun v => xiGaussianSlope a c v ^ 3 -
        12 * (xiGaussianQ c v * xiGaussianSlope a c v) -
        8 * xiGaussianQ c v)
      (-12 * xiGaussianQ c u * xiGaussianSlope a c u ^ 2 -
        24 * xiGaussianQ c u * xiGaussianSlope a c u +
        48 * xiGaussianQ c u ^ 2 - 16 * xiGaussianQ c u) u := by
    have hraw := ((hs.pow 3).sub ((hq.mul hs).const_mul 12)).sub
      (hq.const_mul 8)
    change HasDerivAt
      (fun v => xiGaussianSlope a c v ^ 3 -
        12 * (xiGaussianQ c v * xiGaussianSlope a c v) -
        8 * xiGaussianQ c v)
      _ u at hraw
    apply hraw.congr_deriv
    ring
  have h := hpoly.mul (xiGaussianMode_hasDerivAt a c u)
  apply h.congr_deriv
  unfold xiGaussianJet4 xiGaussianJet1
  ring

/-- Componentwise Gaussian representation of one Riemann-kernel summand. -/
def xiKernelGaussianJet0 (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  let c : ℝ := Real.pi * r ^ 2
  2 * Real.pi ^ 2 * r ^ 4 * xiGaussianMode (9 / 2) c u -
    3 * Real.pi * r ^ 2 * xiGaussianMode (5 / 2) c u

def xiKernelGaussianJet1 (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  let c : ℝ := Real.pi * r ^ 2
  2 * Real.pi ^ 2 * r ^ 4 * xiGaussianJet1 (9 / 2) c u -
    3 * Real.pi * r ^ 2 * xiGaussianJet1 (5 / 2) c u

def xiKernelGaussianJet2 (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  let c : ℝ := Real.pi * r ^ 2
  2 * Real.pi ^ 2 * r ^ 4 * xiGaussianJet2 (9 / 2) c u -
    3 * Real.pi * r ^ 2 * xiGaussianJet2 (5 / 2) c u

def xiKernelGaussianJet3 (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  let c : ℝ := Real.pi * r ^ 2
  2 * Real.pi ^ 2 * r ^ 4 * xiGaussianJet3 (9 / 2) c u -
    3 * Real.pi * r ^ 2 * xiGaussianJet3 (5 / 2) c u

def xiKernelGaussianJet4 (n : ℕ) (u : ℝ) : ℝ :=
  let r : ℝ := n + 1
  let c : ℝ := Real.pi * r ^ 2
  2 * Real.pi ^ 2 * r ^ 4 * xiGaussianJet4 (9 / 2) c u -
    3 * Real.pi * r ^ 2 * xiGaussianJet4 (5 / 2) c u

theorem riemannXiKernelTerm_eq_gaussianJet0 (n : ℕ) (u : ℝ) :
    riemannXiKernelTerm n u = xiKernelGaussianJet0 n u := by
  have h9 : Real.exp
      ((9 / 2 : ℝ) * u - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) =
      Real.exp (9 * u / 2) *
        Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5 : Real.exp
      ((5 / 2 : ℝ) * u - Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) =
      Real.exp (5 * u / 2) *
        Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold riemannXiKernelTerm xiKernelGaussianJet0 xiGaussianMode xiGaussianQ
  dsimp only
  rw [h9, h5]
  ring

theorem xiKernelGaussianJet0_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiKernelGaussianJet0 n) (xiKernelGaussianJet1 n u) u := by
  unfold xiKernelGaussianJet0 xiKernelGaussianJet1
  dsimp only
  exact ((xiGaussianMode_hasDerivAt (9 / 2)
    (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
      (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4)).sub
    ((xiGaussianMode_hasDerivAt (5 / 2)
      (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
        (3 * Real.pi * ((n : ℝ) + 1) ^ 2))

theorem xiKernelGaussianJet1_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiKernelGaussianJet1 n) (xiKernelGaussianJet2 n u) u := by
  unfold xiKernelGaussianJet1 xiKernelGaussianJet2
  dsimp only
  exact ((xiGaussianJet1_hasDerivAt (9 / 2)
    (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
      (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4)).sub
    ((xiGaussianJet1_hasDerivAt (5 / 2)
      (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
        (3 * Real.pi * ((n : ℝ) + 1) ^ 2))

theorem xiKernelGaussianJet2_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiKernelGaussianJet2 n) (xiKernelGaussianJet3 n u) u := by
  unfold xiKernelGaussianJet2 xiKernelGaussianJet3
  dsimp only
  exact ((xiGaussianJet2_hasDerivAt (9 / 2)
    (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
      (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4)).sub
    ((xiGaussianJet2_hasDerivAt (5 / 2)
      (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
        (3 * Real.pi * ((n : ℝ) + 1) ^ 2))

theorem xiKernelGaussianJet3_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiKernelGaussianJet3 n) (xiKernelGaussianJet4 n u) u := by
  unfold xiKernelGaussianJet3 xiKernelGaussianJet4
  dsimp only
  exact ((xiGaussianJet3_hasDerivAt (9 / 2)
    (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
      (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4)).sub
    ((xiGaussianJet3_hasDerivAt (5 / 2)
      (Real.pi * ((n : ℝ) + 1) ^ 2) u).const_mul
        (3 * Real.pi * ((n : ℝ) + 1) ^ 2))

/-- One kernel summand has the componentwise Gaussian first jet. -/
theorem riemannXiKernelTerm_hasDerivAt_gaussianJet1 (n : ℕ) (u : ℝ) :
    HasDerivAt (riemannXiKernelTerm n) (xiKernelGaussianJet1 n u) u := by
  have hfun : riemannXiKernelTerm n = xiKernelGaussianJet0 n := by
    funext v
    exact riemannXiKernelTerm_eq_gaussianJet0 n v
  rw [hfun]
  exact xiKernelGaussianJet0_hasDerivAt n u

theorem riemannXiKernelTerm_deriv_eq_gaussianJet1 (n : ℕ) (u : ℝ) :
    deriv (riemannXiKernelTerm n) u = xiKernelGaussianJet1 n u :=
  (riemannXiKernelTerm_hasDerivAt_gaussianJet1 n u).deriv

theorem riemannXiKernelTerm_deriv_hasDerivAt_gaussianJet2
    (n : ℕ) (u : ℝ) :
    HasDerivAt (deriv (riemannXiKernelTerm n))
      (xiKernelGaussianJet2 n u) u := by
  have hfun : deriv (riemannXiKernelTerm n) = xiKernelGaussianJet1 n := by
    funext v
    exact riemannXiKernelTerm_deriv_eq_gaussianJet1 n v
  rw [hfun]
  exact xiKernelGaussianJet1_hasDerivAt n u

theorem riemannXiKernelTerm_deriv2_eq_gaussianJet2 (n : ℕ) (u : ℝ) :
    deriv (deriv (riemannXiKernelTerm n)) u =
      xiKernelGaussianJet2 n u :=
  (riemannXiKernelTerm_deriv_hasDerivAt_gaussianJet2 n u).deriv

theorem riemannXiKernelTerm_deriv2_hasDerivAt_gaussianJet3
    (n : ℕ) (u : ℝ) :
    HasDerivAt (deriv (deriv (riemannXiKernelTerm n)))
      (xiKernelGaussianJet3 n u) u := by
  have hfun : deriv (deriv (riemannXiKernelTerm n)) =
      xiKernelGaussianJet2 n := by
    funext v
    exact riemannXiKernelTerm_deriv2_eq_gaussianJet2 n v
  rw [hfun]
  exact xiKernelGaussianJet2_hasDerivAt n u

theorem riemannXiKernelTerm_deriv3_eq_gaussianJet3 (n : ℕ) (u : ℝ) :
    deriv (deriv (deriv (riemannXiKernelTerm n))) u =
      xiKernelGaussianJet3 n u :=
  (riemannXiKernelTerm_deriv2_hasDerivAt_gaussianJet3 n u).deriv

theorem riemannXiKernelTerm_deriv3_hasDerivAt_gaussianJet4
    (n : ℕ) (u : ℝ) :
    HasDerivAt (deriv (deriv (deriv (riemannXiKernelTerm n))))
      (xiKernelGaussianJet4 n u) u := by
  have hfun : deriv (deriv (deriv (riemannXiKernelTerm n))) =
      xiKernelGaussianJet3 n := by
    funext v
    exact riemannXiKernelTerm_deriv3_eq_gaussianJet3 n v
  rw [hfun]
  exact xiKernelGaussianJet3_hasDerivAt n u

theorem riemannXiKernelTerm_deriv4_eq_gaussianJet4 (n : ℕ) (u : ℝ) :
    deriv (deriv (deriv (deriv (riemannXiKernelTerm n)))) u =
      xiKernelGaussianJet4 n u :=
  (riemannXiKernelTerm_deriv3_hasDerivAt_gaussianJet4 n u).deriv

/-! ### A locally uniform fourth-jet majorant at the origin -/

/-- Upper exponential-coordinate coefficient on the unit window about zero. -/
def xiKernelJet4LocalQUpper : ℝ := Real.pi * Real.exp 2

/-- Lower exponential-coordinate coefficient on the unit window about zero. -/
def xiKernelJet4LocalQLower : ℝ := Real.pi * Real.exp (-2)

/-- Uniform slope coefficient for both kernel components on the unit window. -/
def xiKernelJet4LocalSlope : ℝ := 5 + 2 * xiKernelJet4LocalQUpper

/-- The absolute fourth-jet polynomial after replacing `q` and the logarithmic
slope by their unit-window upper bounds. -/
def xiKernelJet4LocalPolynomial : ℝ :=
  xiKernelJet4LocalSlope ^ 4 +
    24 * xiKernelJet4LocalQUpper * xiKernelJet4LocalSlope ^ 2 +
    32 * xiKernelJet4LocalQUpper * xiKernelJet4LocalSlope +
    48 * xiKernelJet4LocalQUpper ^ 2 + 16 * xiKernelJet4LocalQUpper

/-- Constant multiplying the degree-twelve shifted exponential majorant. -/
def xiKernelJet4LocalConstant : ℝ :=
  (2 * Real.pi ^ 2 + 3 * Real.pi) * Real.exp (9 / 2) *
    xiKernelJet4LocalPolynomial

/-- Summable coefficient used for locally uniform fourth differentiation. -/
def xiKernelJet4LocalMajorantCoeff (n : ℕ) : ℝ :=
  let r : ℝ := n + 1
  xiKernelJet4LocalConstant * r ^ 12 *
    Real.exp (-xiKernelJet4LocalQLower * r)

theorem xiKernelJet4LocalQLower_pos : 0 < xiKernelJet4LocalQLower := by
  unfold xiKernelJet4LocalQLower
  positivity

theorem xiKernelJet4LocalConstant_nonneg :
    0 ≤ xiKernelJet4LocalConstant := by
  unfold xiKernelJet4LocalConstant xiKernelJet4LocalPolynomial
    xiKernelJet4LocalSlope xiKernelJet4LocalQUpper
  positivity

/-- The degree-twelve unit-window fourth-jet majorant is summable. -/
theorem xiKernelJet4LocalMajorantCoeff_summable :
    Summable xiKernelJet4LocalMajorantCoeff := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 12 * Real.exp (-xiKernelJet4LocalQLower * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 12 xiKernelJet4LocalQLower_pos
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ 12 *
        Real.exp (-xiKernelJet4LocalQLower * (n + 1 : ℕ))) := by
    simpa using (summable_nat_add_iff 1).2 hbase
  unfold xiKernelJet4LocalMajorantCoeff
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
    hshift.mul_left xiKernelJet4LocalConstant

theorem xiKernelJet4LocalQUpper_nonneg : 0 ≤ xiKernelJet4LocalQUpper := by
  unfold xiKernelJet4LocalQUpper
  positivity

theorem xiKernelJet4LocalSlope_nonneg : 0 ≤ xiKernelJet4LocalSlope := by
  unfold xiKernelJet4LocalSlope
  nlinarith [xiKernelJet4LocalQUpper_nonneg]

/-- Upper bound for the Gaussian coordinate on `(-1,1)`. -/
theorem xiGaussianQ_le_local_zero (n : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    xiGaussianQ (Real.pi * ((n : ℝ) + 1) ^ 2) v ≤
      xiKernelJet4LocalQUpper * ((n : ℝ) + 1) ^ 2 := by
  have hexp : Real.exp (2 * v) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    linarith [hv.2]
  unfold xiGaussianQ xiKernelJet4LocalQUpper
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hexp
      (mul_nonneg Real.pi_pos.le (sq_nonneg ((n : ℝ) + 1)))

/-- Lower bound for the Gaussian coordinate on `(-1,1)`. -/
theorem xiGaussianQ_ge_local_zero (n : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    xiKernelJet4LocalQLower * ((n : ℝ) + 1) ^ 2 ≤
      xiGaussianQ (Real.pi * ((n : ℝ) + 1) ^ 2) v := by
  have hexp : Real.exp (-2) ≤ Real.exp (2 * v) := by
    apply Real.exp_le_exp.mpr
    linarith [hv.1]
  unfold xiGaussianQ xiKernelJet4LocalQLower
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hexp
      (mul_nonneg Real.pi_pos.le (sq_nonneg ((n : ℝ) + 1)))

/-- Gaussian decay on the unit window, weakened from a quadratic to a shifted
linear exponent to match a standard summable sequence. -/
theorem xiGaussianMode_exp_le_local_zero (n : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.exp (-xiGaussianQ (Real.pi * ((n : ℝ) + 1) ^ 2) v) ≤
      Real.exp (-xiKernelJet4LocalQLower * ((n : ℝ) + 1)) := by
  let r : ℝ := (n : ℝ) + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr2 : r ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hq := xiGaussianQ_ge_local_zero n hv
  apply Real.exp_le_exp.mpr
  have hlower : xiKernelJet4LocalQLower * r ≤
      xiKernelJet4LocalQLower * r ^ 2 :=
    mul_le_mul_of_nonneg_left hr2 xiKernelJet4LocalQLower_pos.le
  change -xiGaussianQ (Real.pi * r ^ 2) v ≤
    -xiKernelJet4LocalQLower * r
  nlinarith

/-- Both exponential-Gaussian components have logarithmic slope bounded by a
quadratic shifted-index envelope on the unit window. -/
theorem xiGaussianSlope_abs_le_local_zero (n : ℕ) {a v : ℝ}
    (ha0 : 0 ≤ a) (ha5 : a ≤ 5) (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    |xiGaussianSlope a (Real.pi * ((n : ℝ) + 1) ^ 2) v| ≤
      xiKernelJet4LocalSlope * ((n : ℝ) + 1) ^ 2 := by
  let r : ℝ := (n : ℝ) + 1
  let q : ℝ := xiGaussianQ (Real.pi * r ^ 2) v
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    unfold xiGaussianQ
    positivity
  have hqUpper : q ≤ xiKernelJet4LocalQUpper * r ^ 2 := by
    simpa only [r, q] using xiGaussianQ_le_local_zero n hv
  have habs : |a - 2 * q| ≤ a + 2 * q := by
    rw [abs_le]
    constructor <;> nlinarith
  unfold xiGaussianSlope
  change |a - 2 * q| ≤ xiKernelJet4LocalSlope * r ^ 2
  calc
    |a - 2 * q| ≤ a + 2 * q := habs
    _ ≤ 5 + 2 * (xiKernelJet4LocalQUpper * r ^ 2) := by nlinarith
    _ ≤ (5 + 2 * xiKernelJet4LocalQUpper) * r ^ 2 := by
      nlinarith [xiKernelJet4LocalQUpper_nonneg]
    _ = xiKernelJet4LocalSlope * r ^ 2 := by
      unfold xiKernelJet4LocalSlope
      rfl

theorem abs_sub_sub_add_sub_le (x₁ x₂ x₃ x₄ x₅ : ℝ) :
    |x₁ - x₂ - x₃ + x₄ - x₅| ≤
      |x₁| + |x₂| + |x₃| + |x₄| + |x₅| := by
  have h₁ := abs_sub (((x₁ - x₂) - x₃) + x₄) x₅
  have h₂ := abs_add_le ((x₁ - x₂) - x₃) x₄
  have h₃ := abs_sub (x₁ - x₂) x₃
  have h₄ := abs_sub x₁ x₂
  linarith

/-- Uniform fourth-jet bound for either exponential-Gaussian component of one
kernel summand on the unit window. -/
theorem xiGaussianJet4_norm_le_component_local_zero
    (n : ℕ) {a v : ℝ} (ha0 : 0 ≤ a) (ha9 : a ≤ 9 / 2)
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiGaussianJet4 a (Real.pi * ((n : ℝ) + 1) ^ 2) v‖ ≤
      Real.exp (9 / 2) * xiKernelJet4LocalPolynomial *
        ((n : ℝ) + 1) ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * ((n : ℝ) + 1)) := by
  let r : ℝ := (n : ℝ) + 1
  let q : ℝ := xiGaussianQ (Real.pi * r ^ 2) v
  let s : ℝ := xiGaussianSlope a (Real.pi * r ^ 2) v
  let Q : ℝ := xiKernelJet4LocalQUpper
  let S : ℝ := xiKernelJet4LocalSlope
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    unfold xiGaussianQ
    positivity
  have hQ0 : 0 ≤ Q := by exact xiKernelJet4LocalQUpper_nonneg
  have hS0 : 0 ≤ S := by exact xiKernelJet4LocalSlope_nonneg
  have hq : q ≤ Q * r ^ 2 := by
    simpa only [q, Q, r] using xiGaussianQ_le_local_zero n hv
  have hs : |s| ≤ S * r ^ 2 := by
    apply xiGaussianSlope_abs_le_local_zero n ha0
    · linarith
    · exact hv
  have habs4 : |s| ^ 4 = s ^ 4 := by
    calc
      |s| ^ 4 = (|s| ^ 2) ^ 2 := by ring
      _ = (s ^ 2) ^ 2 := by rw [sq_abs]
      _ = s ^ 4 := by ring
  have hpolyAbs :
      |s ^ 4 - 24 * q * s ^ 2 - 32 * q * s + 48 * q ^ 2 - 16 * q| ≤
        s ^ 4 + 24 * q * s ^ 2 + 32 * q * |s| +
          48 * q ^ 2 + 16 * q := by
    have h := abs_sub_sub_add_sub_le
      (s ^ 4) (24 * q * s ^ 2) (32 * q * s) (48 * q ^ 2) (16 * q)
    simpa only [abs_pow, abs_mul, abs_of_nonneg hq0, abs_of_nonneg (by norm_num :
      (0 : ℝ) ≤ 16), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 48),
      abs_of_nonneg (sq_nonneg s), abs_of_nonneg (sq_nonneg q),
      habs4, mul_assoc] using h
  have hs2 : s ^ 2 ≤ (S * r ^ 2) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg s)
      (mul_nonneg hS0 (sq_nonneg r))).2 hs
    simpa only [sq_abs] using h
  have hs4 : s ^ 4 ≤ (S * r ^ 2) ^ 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg s) hs 4
    simpa only [abs_pow, habs4] using h
  have hq2 : q ^ 2 ≤ (Q * r ^ 2) ^ 2 := by
    nlinarith [sq_nonneg q, sq_nonneg (Q * r ^ 2 - q)]
  have hr2_8 : r ^ 2 ≤ r ^ 8 := pow_le_pow_right₀ hr (by omega)
  have hr4_8 : r ^ 4 ≤ r ^ 8 := pow_le_pow_right₀ hr (by omega)
  have hr6_8 : r ^ 6 ≤ r ^ 8 := pow_le_pow_right₀ hr (by omega)
  have hpoly :
      s ^ 4 + 24 * q * s ^ 2 + 32 * q * |s| +
          48 * q ^ 2 + 16 * q ≤
        xiKernelJet4LocalPolynomial * r ^ 8 := by
    calc
      s ^ 4 + 24 * q * s ^ 2 + 32 * q * |s| +
          48 * q ^ 2 + 16 * q ≤
          (S * r ^ 2) ^ 4 +
            24 * (Q * r ^ 2) * (S * r ^ 2) ^ 2 +
            32 * (Q * r ^ 2) * (S * r ^ 2) +
            48 * (Q * r ^ 2) ^ 2 + 16 * (Q * r ^ 2) := by
        gcongr
      _ ≤ (S ^ 4 + 24 * Q * S ^ 2 + 32 * Q * S +
          48 * Q ^ 2 + 16 * Q) * r ^ 8 := by
        ring_nf
        gcongr
      _ = xiKernelJet4LocalPolynomial * r ^ 8 := by
        unfold xiKernelJet4LocalPolynomial
        rfl
  have hexpa : Real.exp (a * v) ≤ Real.exp (9 / 2) := by
    apply Real.exp_le_exp.mpr
    have hav : a * v ≤ a := by nlinarith [hv.2]
    linarith
  have hdecay := xiGaussianMode_exp_le_local_zero n hv
  have hmode : xiGaussianMode a (Real.pi * r ^ 2) v ≤
      Real.exp (9 / 2) *
        Real.exp (-xiKernelJet4LocalQLower * r) := by
    unfold xiGaussianMode
    have hsplit : Real.exp (a * v - q) =
        Real.exp (a * v) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
    rw [hsplit]
    exact mul_le_mul hexpa (by simpa only [q, r] using hdecay)
      (Real.exp_pos _).le (Real.exp_pos _).le
  unfold xiGaussianJet4
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show
    0 < xiGaussianMode a (Real.pi * r ^ 2) v by
      unfold xiGaussianMode
      positivity)]
  calc
    |s ^ 4 - 24 * q * s ^ 2 - 32 * q * s + 48 * q ^ 2 - 16 * q| *
        xiGaussianMode a (Real.pi * r ^ 2) v ≤
      (xiKernelJet4LocalPolynomial * r ^ 8) *
        (Real.exp (9 / 2) *
          Real.exp (-xiKernelJet4LocalQLower * r)) :=
      mul_le_mul (hpolyAbs.trans hpoly) hmode
        (Real.exp_pos _).le
        (mul_nonneg (by
          unfold xiKernelJet4LocalPolynomial
          positivity) (pow_nonneg (le_trans zero_le_one hr) 8))
    _ = Real.exp (9 / 2) * xiKernelJet4LocalPolynomial * r ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * r) := by ring

/-- The complete fourth jet of one kernel summand is dominated by the common
degree-twelve local majorant. -/
theorem xiKernelGaussianJet4_norm_le_local_zero
    (n : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiKernelGaussianJet4 n v‖ ≤ xiKernelJet4LocalMajorantCoeff n := by
  let r : ℝ := (n : ℝ) + 1
  let E : ℝ := Real.exp (9 / 2) * xiKernelJet4LocalPolynomial * r ^ 8 *
    Real.exp (-xiKernelJet4LocalQLower * r)
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold xiKernelJet4LocalPolynomial xiKernelJet4LocalSlope
      xiKernelJet4LocalQUpper
    positivity
  have h9 : ‖xiGaussianJet4 (9 / 2)
      (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet4_norm_le_component_local_zero n (a := 9 / 2)
        (by norm_num) (by norm_num) hv
  have h5 : ‖xiGaussianJet4 (5 / 2)
      (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet4_norm_le_component_local_zero n (a := 5 / 2)
        (by norm_num) (by norm_num) hv
  have hr2_le_r4 : r ^ 2 ≤ r ^ 4 := pow_le_pow_right₀ hr (by omega)
  unfold xiKernelGaussianJet4
  dsimp only
  change ‖2 * Real.pi ^ 2 * r ^ 4 *
      xiGaussianJet4 (9 / 2) (Real.pi * r ^ 2) v -
      3 * Real.pi * r ^ 2 *
        xiGaussianJet4 (5 / 2) (Real.pi * r ^ 2) v‖ ≤ _
  calc
    ‖2 * Real.pi ^ 2 * r ^ 4 *
        xiGaussianJet4 (9 / 2) (Real.pi * r ^ 2) v -
        3 * Real.pi * r ^ 2 *
          xiGaussianJet4 (5 / 2) (Real.pi * r ^ 2) v‖ ≤
        ‖2 * Real.pi ^ 2 * r ^ 4 *
          xiGaussianJet4 (9 / 2) (Real.pi * r ^ 2) v‖ +
        ‖3 * Real.pi * r ^ 2 *
          xiGaussianJet4 (5 / 2) (Real.pi * r ^ 2) v‖ := norm_sub_le _ _
    _ ≤
        (2 * Real.pi ^ 2 * r ^ 4) * E +
          (3 * Real.pi * r ^ 2) * E := by
      apply add_le_add
      · rw [norm_mul]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h9 (by positivity)
      · rw [norm_mul]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ ((2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4) * E := by
      rw [show 2 * Real.pi ^ 2 * r ^ 4 * E + 3 * Real.pi * r ^ 2 * E =
        (2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 2) * E by ring]
      apply mul_le_mul_of_nonneg_right _ hE
      calc
        2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 2 ≤
            2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 4 := by
          gcongr
        _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4 := by ring
    _ = xiKernelJet4LocalMajorantCoeff n := by
      unfold xiKernelJet4LocalMajorantCoeff xiKernelJet4LocalConstant
      dsimp [r, E]
      ring

/-- A coarse polynomial envelope for the third Gaussian jet. -/
def xiKernelJet3LocalPolynomial : ℝ :=
  21 * (1 + xiKernelJet4LocalSlope + xiKernelJet4LocalQUpper) ^ 4

def xiKernelJet3LocalConstant : ℝ :=
  (2 * Real.pi ^ 2 + 3 * Real.pi) * Real.exp (9 / 2) *
    xiKernelJet3LocalPolynomial

def xiKernelJet3LocalMajorantCoeff (n : ℕ) : ℝ :=
  let r : ℝ := n + 1
  xiKernelJet3LocalConstant * r ^ 12 *
    Real.exp (-xiKernelJet4LocalQLower * r)

theorem xiKernelJet3LocalMajorantCoeff_summable :
    Summable xiKernelJet3LocalMajorantCoeff := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 12 * Real.exp (-xiKernelJet4LocalQLower * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 12 xiKernelJet4LocalQLower_pos
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ 12 *
        Real.exp (-xiKernelJet4LocalQLower * (n + 1 : ℕ))) := by
    simpa using (summable_nat_add_iff 1).2 hbase
  unfold xiKernelJet3LocalMajorantCoeff
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
    hshift.mul_left xiKernelJet3LocalConstant

-- Uniform third-jet bound for either Gaussian component.
set_option maxHeartbeats 800000 in
theorem xiGaussianJet3_norm_le_component_local_zero
    (n : ℕ) {a v : ℝ} (ha0 : 0 ≤ a) (ha9 : a ≤ 9 / 2)
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiGaussianJet3 a (Real.pi * ((n : ℝ) + 1) ^ 2) v‖ ≤
      Real.exp (9 / 2) * xiKernelJet3LocalPolynomial *
        ((n : ℝ) + 1) ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * ((n : ℝ) + 1)) := by
  let r : ℝ := (n : ℝ) + 1
  let q : ℝ := xiGaussianQ (Real.pi * r ^ 2) v
  let s : ℝ := xiGaussianSlope a (Real.pi * r ^ 2) v
  let Q : ℝ := xiKernelJet4LocalQUpper
  let S : ℝ := xiKernelJet4LocalSlope
  let M : ℝ := (1 + S + Q) * r ^ 2
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    unfold xiGaussianQ
    positivity
  have hQ0 : 0 ≤ Q := xiKernelJet4LocalQUpper_nonneg
  have hS0 : 0 ≤ S := xiKernelJet4LocalSlope_nonneg
  have hq : q ≤ Q * r ^ 2 := by
    simpa only [q, Q, r] using xiGaussianQ_le_local_zero n hv
  have hs : |s| ≤ S * r ^ 2 := by
    apply xiGaussianSlope_abs_le_local_zero n ha0
    · linarith
    · exact hv
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by
    dsimp [M]
    calc
      1 ≤ 1 * r ^ 2 := by simpa using hr2
      _ ≤ (1 + S + Q) * r ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)
  have hsM : |s| ≤ M := by
    dsimp [M]
    calc
      |s| ≤ S * r ^ 2 := hs
      _ ≤ (1 + S + Q) * r ^ 2 := by gcongr <;> linarith
  have hqM : q ≤ M := by
    dsimp [M]
    calc
      q ≤ Q * r ^ 2 := hq
      _ ≤ (1 + S + Q) * r ^ 2 := by gcongr <;> linarith
  have hs3 : |s| ^ 3 ≤ M ^ 4 := by
    calc
      |s| ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (abs_nonneg s) hsM 3
      _ ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by omega)
  have hqs : q * |s| ≤ M ^ 4 := by
    calc
      q * |s| ≤ M * M := mul_le_mul hqM hsM (abs_nonneg s) hM0
      _ = M ^ 2 := by ring
      _ ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by omega)
  have hq4 : q ≤ M ^ 4 := by
    calc
      q ≤ M := hqM
      _ ≤ M ^ 4 := by simpa only [pow_one] using
        (pow_le_pow_right₀ hM1 (show 1 ≤ 4 by omega))
  have hpolyAbs : |s ^ 3 - 12 * (q * s) - 8 * q| ≤
      |s| ^ 3 + 12 * (q * |s|) + 8 * q := by
    calc
      |s ^ 3 - 12 * (q * s) - 8 * q| ≤
          |s ^ 3 - 12 * (q * s)| + |8 * q| := abs_sub _ _
      _ ≤ (|s ^ 3| + |12 * (q * s)|) + |8 * q| := by
        gcongr
        exact abs_sub _ _
      _ = |s| ^ 3 + 12 * (q * |s|) + 8 * q := by
        simp only [abs_pow, abs_mul, abs_of_nonneg hq0,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
  have hpoly : |s ^ 3 - 12 * (q * s) - 8 * q| ≤
      xiKernelJet3LocalPolynomial * r ^ 8 := by
    calc
      |s ^ 3 - 12 * (q * s) - 8 * q| ≤
          |s| ^ 3 + 12 * (q * |s|) + 8 * q := hpolyAbs
      _ ≤ 21 * M ^ 4 := by nlinarith
      _ = xiKernelJet3LocalPolynomial * r ^ 8 := by
        unfold xiKernelJet3LocalPolynomial
        dsimp [M]
        ring
  have hexpa : Real.exp (a * v) ≤ Real.exp (9 / 2) := by
    apply Real.exp_le_exp.mpr
    have hav : a * v ≤ a := by nlinarith [hv.2]
    linarith
  have hdecay := xiGaussianMode_exp_le_local_zero n hv
  have hmode : xiGaussianMode a (Real.pi * r ^ 2) v ≤
      Real.exp (9 / 2) *
        Real.exp (-xiKernelJet4LocalQLower * r) := by
    unfold xiGaussianMode
    have hsplit : Real.exp (a * v - q) =
        Real.exp (a * v) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
    rw [hsplit]
    exact mul_le_mul hexpa (by simpa only [q, r] using hdecay)
      (Real.exp_pos _).le (Real.exp_pos _).le
  unfold xiGaussianJet3
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show
    0 < xiGaussianMode a (Real.pi * r ^ 2) v by
      unfold xiGaussianMode
      positivity)]
  calc
    |s ^ 3 - 12 * (q * s) - 8 * q| *
        xiGaussianMode a (Real.pi * r ^ 2) v ≤
      (xiKernelJet3LocalPolynomial * r ^ 8) *
        (Real.exp (9 / 2) *
          Real.exp (-xiKernelJet4LocalQLower * r)) :=
      mul_le_mul hpoly hmode (Real.exp_pos _).le (by
        unfold xiKernelJet3LocalPolynomial
        positivity)
    _ = Real.exp (9 / 2) * xiKernelJet3LocalPolynomial * r ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * r) := by ring

theorem xiKernelGaussianJet3_norm_le_local_zero
    (n : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiKernelGaussianJet3 n v‖ ≤ xiKernelJet3LocalMajorantCoeff n := by
  let r : ℝ := (n : ℝ) + 1
  let E : ℝ := Real.exp (9 / 2) * xiKernelJet3LocalPolynomial * r ^ 8 *
    Real.exp (-xiKernelJet4LocalQLower * r)
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold xiKernelJet3LocalPolynomial xiKernelJet4LocalSlope
      xiKernelJet4LocalQUpper
    positivity
  have h9 : ‖xiGaussianJet3 (9 / 2)
      (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet3_norm_le_component_local_zero n (a := 9 / 2)
        (by norm_num) (by norm_num) hv
  have h5 : ‖xiGaussianJet3 (5 / 2)
      (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet3_norm_le_component_local_zero n (a := 5 / 2)
        (by norm_num) (by norm_num) hv
  have hr2_le_r4 : r ^ 2 ≤ r ^ 4 := pow_le_pow_right₀ hr (by omega)
  unfold xiKernelGaussianJet3
  dsimp only
  change ‖2 * Real.pi ^ 2 * r ^ 4 *
      xiGaussianJet3 (9 / 2) (Real.pi * r ^ 2) v -
      3 * Real.pi * r ^ 2 *
        xiGaussianJet3 (5 / 2) (Real.pi * r ^ 2) v‖ ≤ _
  calc
    ‖2 * Real.pi ^ 2 * r ^ 4 *
        xiGaussianJet3 (9 / 2) (Real.pi * r ^ 2) v -
        3 * Real.pi * r ^ 2 *
          xiGaussianJet3 (5 / 2) (Real.pi * r ^ 2) v‖ ≤
        ‖2 * Real.pi ^ 2 * r ^ 4 *
          xiGaussianJet3 (9 / 2) (Real.pi * r ^ 2) v‖ +
        ‖3 * Real.pi * r ^ 2 *
          xiGaussianJet3 (5 / 2) (Real.pi * r ^ 2) v‖ := norm_sub_le _ _
    _ ≤ (2 * Real.pi ^ 2 * r ^ 4) * E +
          (3 * Real.pi * r ^ 2) * E := by
      apply add_le_add
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h9 (by positivity)
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ ((2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4) * E := by
      rw [show 2 * Real.pi ^ 2 * r ^ 4 * E + 3 * Real.pi * r ^ 2 * E =
        (2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 2) * E by ring]
      apply mul_le_mul_of_nonneg_right _ hE
      calc
        2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 2 ≤
            2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 4 := by
          gcongr
        _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4 := by ring
    _ = xiKernelJet3LocalMajorantCoeff n := by
      unfold xiKernelJet3LocalMajorantCoeff xiKernelJet3LocalConstant
      dsimp [r, E]
      ring

theorem xiKernelGaussianJet3_summable_zero :
    Summable (fun n : ℕ => xiKernelGaussianJet3 n 0) := by
  apply Summable.of_norm_bounded xiKernelJet3LocalMajorantCoeff_summable
  intro n
  exact xiKernelGaussianJet3_norm_le_local_zero n (by constructor <;> norm_num)

/-- The third-jet series differentiates at the origin to the summed fourth
jet. -/
theorem xiKernelGaussianJet3Series_hasDerivAt_zero :
    HasDerivAt (fun v => ∑' n : ℕ, xiKernelGaussianJet3 n v)
      (∑' n : ℕ, xiKernelGaussianJet4 n 0) 0 := by
  exact hasDerivAt_tsum_of_isPreconnected
    xiKernelJet4LocalMajorantCoeff_summable
    isOpen_Ioo isPreconnected_Ioo
    (fun n v _ => xiKernelGaussianJet3_hasDerivAt n v)
    (fun n v hv => xiKernelGaussianJet4_norm_le_local_zero n hv)
    (by constructor <;> norm_num)
    xiKernelGaussianJet3_summable_zero
    (by constructor <;> norm_num)

/-- The component mode itself has the common unit-window decay. -/
theorem xiGaussianMode_le_component_local_zero
    (n : ℕ) {a v : ℝ} (ha0 : 0 ≤ a) (ha9 : a ≤ 9 / 2)
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    xiGaussianMode a (Real.pi * ((n : ℝ) + 1) ^ 2) v ≤
      Real.exp (9 / 2) *
        Real.exp (-xiKernelJet4LocalQLower * ((n : ℝ) + 1)) := by
  let r : ℝ := (n : ℝ) + 1
  let q : ℝ := xiGaussianQ (Real.pi * r ^ 2) v
  have hexpa : Real.exp (a * v) ≤ Real.exp (9 / 2) := by
    apply Real.exp_le_exp.mpr
    have hav : a * v ≤ a := by nlinarith [hv.2]
    linarith
  have hdecay := xiGaussianMode_exp_le_local_zero n hv
  unfold xiGaussianMode
  have hsplit : Real.exp (a * v - q) =
      Real.exp (a * v) * Real.exp (-q) := by
    rw [← Real.exp_add]
    congr 1
  rw [hsplit]
  exact mul_le_mul hexpa (by simpa only [q, r] using hdecay)
    (Real.exp_pos _).le (Real.exp_pos _).le

/-- Assembly bound for the two Gaussian components of a kernel jet. -/
theorem xiKernelGaussianCombination_norm_le
    (n : ℕ) {x9 x5 E : ℝ} (hE : 0 ≤ E)
    (h9 : ‖x9‖ ≤ E) (h5 : ‖x5‖ ≤ E) :
    ‖2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * x9 -
        3 * Real.pi * ((n : ℝ) + 1) ^ 2 * x5‖ ≤
      ((2 * Real.pi ^ 2 + 3 * Real.pi) * ((n : ℝ) + 1) ^ 4) * E := by
  let r : ℝ := (n : ℝ) + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr2_le_r4 : r ^ 2 ≤ r ^ 4 := pow_le_pow_right₀ hr (by omega)
  change ‖2 * Real.pi ^ 2 * r ^ 4 * x9 -
      3 * Real.pi * r ^ 2 * x5‖ ≤ _
  calc
    ‖2 * Real.pi ^ 2 * r ^ 4 * x9 - 3 * Real.pi * r ^ 2 * x5‖ ≤
        ‖2 * Real.pi ^ 2 * r ^ 4 * x9‖ +
          ‖3 * Real.pi * r ^ 2 * x5‖ := norm_sub_le _ _
    _ ≤ (2 * Real.pi ^ 2 * r ^ 4) * E +
          (3 * Real.pi * r ^ 2) * E := by
      apply add_le_add
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h9 (by positivity)
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ ((2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4) * E := by
      rw [show 2 * Real.pi ^ 2 * r ^ 4 * E + 3 * Real.pi * r ^ 2 * E =
        (2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 2) * E by ring]
      apply mul_le_mul_of_nonneg_right _ hE
      calc
        2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 2 ≤
            2 * Real.pi ^ 2 * r ^ 4 + 3 * Real.pi * r ^ 4 := by
          gcongr
        _ = (2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4 := by ring

-- Uniform second-jet bound for either Gaussian component.
set_option maxHeartbeats 500000 in
theorem xiGaussianJet2_norm_le_component_local_zero
    (n : ℕ) {a v : ℝ} (ha0 : 0 ≤ a) (ha9 : a ≤ 9 / 2)
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiGaussianJet2 a (Real.pi * ((n : ℝ) + 1) ^ 2) v‖ ≤
      Real.exp (9 / 2) * xiKernelJet3LocalPolynomial *
        ((n : ℝ) + 1) ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * ((n : ℝ) + 1)) := by
  let r : ℝ := (n : ℝ) + 1
  let q : ℝ := xiGaussianQ (Real.pi * r ^ 2) v
  let s : ℝ := xiGaussianSlope a (Real.pi * r ^ 2) v
  let Q : ℝ := xiKernelJet4LocalQUpper
  let S : ℝ := xiKernelJet4LocalSlope
  let M : ℝ := (1 + S + Q) * r ^ 2
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    unfold xiGaussianQ
    positivity
  have hQ0 : 0 ≤ Q := xiKernelJet4LocalQUpper_nonneg
  have hS0 : 0 ≤ S := xiKernelJet4LocalSlope_nonneg
  have hq : q ≤ Q * r ^ 2 := by
    simpa only [q, Q, r] using xiGaussianQ_le_local_zero n hv
  have hs : |s| ≤ S * r ^ 2 := by
    apply xiGaussianSlope_abs_le_local_zero n ha0
    · linarith
    · exact hv
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by
    dsimp [M]
    calc
      1 ≤ 1 * r ^ 2 := by simpa using hr2
      _ ≤ (1 + S + Q) * r ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)
  have hsM : |s| ≤ M := by
    dsimp [M]
    calc
      |s| ≤ S * r ^ 2 := hs
      _ ≤ (1 + S + Q) * r ^ 2 := by gcongr <;> linarith
  have hqM : q ≤ M := by
    dsimp [M]
    calc
      q ≤ Q * r ^ 2 := hq
      _ ≤ (1 + S + Q) * r ^ 2 := by gcongr <;> linarith
  have hs2 : |s| ^ 2 ≤ M ^ 4 := by
    calc
      |s| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg s) hsM 2
      _ ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by omega)
  have hq4 : q ≤ M ^ 4 := by
    calc
      q ≤ M := hqM
      _ ≤ M ^ 4 := by simpa only [pow_one] using
        (pow_le_pow_right₀ hM1 (show 1 ≤ 4 by omega))
  have hpoly : |s ^ 2 - 4 * q| ≤
      xiKernelJet3LocalPolynomial * r ^ 8 := by
    calc
      |s ^ 2 - 4 * q| ≤ s ^ 2 + 4 * q := by
        calc
          |s ^ 2 - 4 * q| ≤ |s ^ 2| + |4 * q| := abs_sub _ _
          _ = s ^ 2 + 4 * q := by
            rw [abs_of_nonneg (sq_nonneg s), abs_of_nonneg (by positivity)]
      _ ≤ 5 * M ^ 4 := by
        have hsabs : s ^ 2 = |s| ^ 2 := by rw [sq_abs]
        nlinarith
      _ ≤ 21 * M ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hM0 4)
      _ = xiKernelJet3LocalPolynomial * r ^ 8 := by
        unfold xiKernelJet3LocalPolynomial
        dsimp [M]
        ring
  have hmode := xiGaussianMode_le_component_local_zero n ha0 ha9 hv
  change ‖(s ^ 2 - 4 * q) *
    xiGaussianMode a (Real.pi * r ^ 2) v‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show
    0 < xiGaussianMode a (Real.pi * r ^ 2) v by
      unfold xiGaussianMode
      positivity)]
  exact (mul_le_mul hpoly (by
      simpa only [xiGaussianMode, q, r] using hmode)
    (Real.exp_pos _).le (by
      unfold xiKernelJet3LocalPolynomial
      positivity)).trans_eq (by ring)

theorem xiKernelGaussianJet2_norm_le_local_zero
    (n : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiKernelGaussianJet2 n v‖ ≤ xiKernelJet3LocalMajorantCoeff n := by
  let r : ℝ := (n : ℝ) + 1
  let E : ℝ := Real.exp (9 / 2) * xiKernelJet3LocalPolynomial * r ^ 8 *
    Real.exp (-xiKernelJet4LocalQLower * r)
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold xiKernelJet3LocalPolynomial xiKernelJet4LocalSlope
      xiKernelJet4LocalQUpper
    positivity
  have h9 : ‖xiGaussianJet2 (9 / 2) (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet2_norm_le_component_local_zero n (a := 9 / 2)
        (by norm_num) (by norm_num) hv
  have h5 : ‖xiGaussianJet2 (5 / 2) (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet2_norm_le_component_local_zero n (a := 5 / 2)
        (by norm_num) (by norm_num) hv
  unfold xiKernelGaussianJet2
  dsimp only
  calc
    ‖2 * Real.pi ^ 2 * r ^ 4 * xiGaussianJet2 (9 / 2)
        (Real.pi * r ^ 2) v -
        3 * Real.pi * r ^ 2 * xiGaussianJet2 (5 / 2)
          (Real.pi * r ^ 2) v‖ ≤
      ((2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4) * E := by
        simpa only [r] using xiKernelGaussianCombination_norm_le n hE h9 h5
    _ = xiKernelJet3LocalMajorantCoeff n := by
      unfold xiKernelJet3LocalMajorantCoeff xiKernelJet3LocalConstant
      dsimp [r, E]
      ring

theorem xiKernelGaussianJet2_summable_zero :
    Summable (fun n : ℕ => xiKernelGaussianJet2 n 0) := by
  apply Summable.of_norm_bounded xiKernelJet3LocalMajorantCoeff_summable
  intro n
  exact xiKernelGaussianJet2_norm_le_local_zero n (by constructor <;> norm_num)

theorem xiKernelGaussianJet2Series_hasDerivAt_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun z => ∑' n : ℕ, xiKernelGaussianJet2 n z)
      (∑' n : ℕ, xiKernelGaussianJet3 n v) v := by
  exact hasDerivAt_tsum_of_isPreconnected
    xiKernelJet3LocalMajorantCoeff_summable
    isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => xiKernelGaussianJet2_hasDerivAt n z)
    (fun n z hz => xiKernelGaussianJet3_norm_le_local_zero n hz)
    (by constructor <;> norm_num)
    xiKernelGaussianJet2_summable_zero hv

theorem xiGaussianJet1_norm_le_component_local_zero
    (n : ℕ) {a v : ℝ} (ha0 : 0 ≤ a) (ha9 : a ≤ 9 / 2)
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiGaussianJet1 a (Real.pi * ((n : ℝ) + 1) ^ 2) v‖ ≤
      Real.exp (9 / 2) * xiKernelJet3LocalPolynomial *
        ((n : ℝ) + 1) ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * ((n : ℝ) + 1)) := by
  let r : ℝ := (n : ℝ) + 1
  let s : ℝ := xiGaussianSlope a (Real.pi * r ^ 2) v
  let Q : ℝ := xiKernelJet4LocalQUpper
  let S : ℝ := xiKernelJet4LocalSlope
  let M : ℝ := (1 + S + Q) * r ^ 2
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hQ0 : 0 ≤ Q := xiKernelJet4LocalQUpper_nonneg
  have hS0 : 0 ≤ S := xiKernelJet4LocalSlope_nonneg
  have hs : |s| ≤ S * r ^ 2 := by
    apply xiGaussianSlope_abs_le_local_zero n ha0
    · linarith
    · exact hv
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by
    dsimp [M]
    calc
      1 ≤ 1 * r ^ 2 := by simpa using hr2
      _ ≤ (1 + S + Q) * r ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)
  have hsM : |s| ≤ M := by
    dsimp [M]
    calc
      |s| ≤ S * r ^ 2 := hs
      _ ≤ (1 + S + Q) * r ^ 2 := by gcongr <;> linarith
  have hpoly : |s| ≤ xiKernelJet3LocalPolynomial * r ^ 8 := by
    calc
      |s| ≤ M := hsM
      _ ≤ M ^ 4 := by simpa only [pow_one] using
        (pow_le_pow_right₀ hM1 (show 1 ≤ 4 by omega))
      _ ≤ 21 * M ^ 4 := by
        have hM4 : 0 ≤ M ^ 4 := pow_nonneg hM0 4
        nlinarith
      _ = xiKernelJet3LocalPolynomial * r ^ 8 := by
        unfold xiKernelJet3LocalPolynomial
        dsimp [M]
        ring
  have hmode := xiGaussianMode_le_component_local_zero n ha0 ha9 hv
  change ‖s * xiGaussianMode a (Real.pi * r ^ 2) v‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show
    0 < xiGaussianMode a (Real.pi * r ^ 2) v by
      unfold xiGaussianMode
      positivity)]
  exact (mul_le_mul hpoly (by
      simpa only [xiGaussianMode, r] using hmode)
    (Real.exp_pos _).le (by
      unfold xiKernelJet3LocalPolynomial
      positivity)).trans_eq (by ring)

theorem xiKernelGaussianJet1_norm_le_local_zero
    (n : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiKernelGaussianJet1 n v‖ ≤ xiKernelJet3LocalMajorantCoeff n := by
  let r : ℝ := (n : ℝ) + 1
  let E : ℝ := Real.exp (9 / 2) * xiKernelJet3LocalPolynomial * r ^ 8 *
    Real.exp (-xiKernelJet4LocalQLower * r)
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold xiKernelJet3LocalPolynomial xiKernelJet4LocalSlope
      xiKernelJet4LocalQUpper
    positivity
  have h9 : ‖xiGaussianJet1 (9 / 2) (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet1_norm_le_component_local_zero n (a := 9 / 2)
        (by norm_num) (by norm_num) hv
  have h5 : ‖xiGaussianJet1 (5 / 2) (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianJet1_norm_le_component_local_zero n (a := 5 / 2)
        (by norm_num) (by norm_num) hv
  unfold xiKernelGaussianJet1
  dsimp only
  calc
    ‖2 * Real.pi ^ 2 * r ^ 4 * xiGaussianJet1 (9 / 2)
        (Real.pi * r ^ 2) v -
        3 * Real.pi * r ^ 2 * xiGaussianJet1 (5 / 2)
          (Real.pi * r ^ 2) v‖ ≤
      ((2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4) * E := by
        simpa only [r] using xiKernelGaussianCombination_norm_le n hE h9 h5
    _ = xiKernelJet3LocalMajorantCoeff n := by
      unfold xiKernelJet3LocalMajorantCoeff xiKernelJet3LocalConstant
      dsimp [r, E]
      ring

theorem xiKernelGaussianJet1_summable_zero :
    Summable (fun n : ℕ => xiKernelGaussianJet1 n 0) := by
  apply Summable.of_norm_bounded xiKernelJet3LocalMajorantCoeff_summable
  intro n
  exact xiKernelGaussianJet1_norm_le_local_zero n (by constructor <;> norm_num)

theorem xiKernelGaussianJet1Series_hasDerivAt_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun z => ∑' n : ℕ, xiKernelGaussianJet1 n z)
      (∑' n : ℕ, xiKernelGaussianJet2 n v) v := by
  exact hasDerivAt_tsum_of_isPreconnected
    xiKernelJet3LocalMajorantCoeff_summable
    isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => xiKernelGaussianJet1_hasDerivAt n z)
    (fun n z hz => xiKernelGaussianJet2_norm_le_local_zero n hz)
    (by constructor <;> norm_num)
    xiKernelGaussianJet1_summable_zero hv

theorem xiGaussianMode_norm_le_component_majorant_local_zero
    (n : ℕ) {a v : ℝ} (ha0 : 0 ≤ a) (ha9 : a ≤ 9 / 2)
    (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiGaussianMode a (Real.pi * ((n : ℝ) + 1) ^ 2) v‖ ≤
      Real.exp (9 / 2) * xiKernelJet3LocalPolynomial *
        ((n : ℝ) + 1) ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * ((n : ℝ) + 1)) := by
  let r : ℝ := (n : ℝ) + 1
  let Q : ℝ := xiKernelJet4LocalQUpper
  let S : ℝ := xiKernelJet4LocalSlope
  let C : ℝ := 1 + S + Q
  have hr : 1 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hQ0 : 0 ≤ Q := xiKernelJet4LocalQUpper_nonneg
  have hS0 : 0 ≤ S := xiKernelJet4LocalSlope_nonneg
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC4 : 1 ≤ C ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hC 4
  have hr8 : 1 ≤ r ^ 8 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hr 8
  have hpoly : 1 ≤ xiKernelJet3LocalPolynomial * r ^ 8 := by
    have hprod : 1 ≤ C ^ 4 * r ^ 8 := by
      simpa only [one_mul] using
        mul_le_mul hC4 hr8 zero_le_one (pow_nonneg (by linarith : 0 ≤ C) 4)
    calc
      1 ≤ C ^ 4 * r ^ 8 := hprod
      _ ≤ 21 * (C ^ 4 * r ^ 8) := by
        nlinarith
      _ = xiKernelJet3LocalPolynomial * r ^ 8 := by
        unfold xiKernelJet3LocalPolynomial
        dsimp [C, S, Q]
        ring
  have hmode := xiGaussianMode_le_component_local_zero n ha0 ha9 hv
  rw [Real.norm_eq_abs, abs_of_pos (show
    0 < xiGaussianMode a (Real.pi * r ^ 2) v by
      unfold xiGaussianMode
      positivity)]
  calc
    xiGaussianMode a (Real.pi * r ^ 2) v ≤
        Real.exp (9 / 2) *
          Real.exp (-xiKernelJet4LocalQLower * r) := by
      simpa only [r] using hmode
    _ ≤ (Real.exp (9 / 2) *
          Real.exp (-xiKernelJet4LocalQLower * r)) *
        (xiKernelJet3LocalPolynomial * r ^ 8) :=
      by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpoly
          (show 0 ≤ Real.exp (9 / 2) *
            Real.exp (-xiKernelJet4LocalQLower * r) by positivity)
    _ = Real.exp (9 / 2) * xiKernelJet3LocalPolynomial * r ^ 8 *
        Real.exp (-xiKernelJet4LocalQLower * r) := by ring

theorem xiKernelGaussianJet0_norm_le_local_zero
    (n : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖xiKernelGaussianJet0 n v‖ ≤ xiKernelJet3LocalMajorantCoeff n := by
  let r : ℝ := (n : ℝ) + 1
  let E : ℝ := Real.exp (9 / 2) * xiKernelJet3LocalPolynomial * r ^ 8 *
    Real.exp (-xiKernelJet4LocalQLower * r)
  have hE : 0 ≤ E := by
    dsimp [E]
    unfold xiKernelJet3LocalPolynomial xiKernelJet4LocalSlope
      xiKernelJet4LocalQUpper
    positivity
  have h9 : ‖xiGaussianMode (9 / 2) (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianMode_norm_le_component_majorant_local_zero n (a := 9 / 2)
        (by norm_num) (by norm_num) hv
  have h5 : ‖xiGaussianMode (5 / 2) (Real.pi * r ^ 2) v‖ ≤ E := by
    simpa only [r, E] using
      xiGaussianMode_norm_le_component_majorant_local_zero n (a := 5 / 2)
        (by norm_num) (by norm_num) hv
  unfold xiKernelGaussianJet0
  dsimp only
  calc
    ‖2 * Real.pi ^ 2 * r ^ 4 * xiGaussianMode (9 / 2)
        (Real.pi * r ^ 2) v -
        3 * Real.pi * r ^ 2 * xiGaussianMode (5 / 2)
          (Real.pi * r ^ 2) v‖ ≤
      ((2 * Real.pi ^ 2 + 3 * Real.pi) * r ^ 4) * E := by
        simpa only [r] using xiKernelGaussianCombination_norm_le n hE h9 h5
    _ = xiKernelJet3LocalMajorantCoeff n := by
      unfold xiKernelJet3LocalMajorantCoeff xiKernelJet3LocalConstant
      dsimp [r, E]
      ring

theorem xiKernelGaussianJet0_summable_zero :
    Summable (fun n : ℕ => xiKernelGaussianJet0 n 0) := by
  apply Summable.of_norm_bounded xiKernelJet3LocalMajorantCoeff_summable
  intro n
  exact xiKernelGaussianJet0_norm_le_local_zero n (by constructor <;> norm_num)

theorem xiKernelGaussianJet0Series_hasDerivAt_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun z => ∑' n : ℕ, xiKernelGaussianJet0 n z)
      (∑' n : ℕ, xiKernelGaussianJet1 n v) v := by
  exact hasDerivAt_tsum_of_isPreconnected
    xiKernelJet3LocalMajorantCoeff_summable
    isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => xiKernelGaussianJet0_hasDerivAt n z)
    (fun n z hz => xiKernelGaussianJet1_norm_le_local_zero n hz)
    (by constructor <;> norm_num)
    xiKernelGaussianJet0_summable_zero hv

theorem xiKernelGaussianJet3Series_hasDerivAt_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun z => ∑' n : ℕ, xiKernelGaussianJet3 n z)
      (∑' n : ℕ, xiKernelGaussianJet4 n v) v := by
  exact hasDerivAt_tsum_of_isPreconnected
    xiKernelJet4LocalMajorantCoeff_summable
    isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => xiKernelGaussianJet3_hasDerivAt n z)
    (fun n z hz => xiKernelGaussianJet4_norm_le_local_zero n hz)
    (by constructor <;> norm_num)
    xiKernelGaussianJet3_summable_zero hv

/-- The actual kernel is four times the zeroth Gaussian-jet series. -/
theorem riemannXiKernel_eq_gaussianJet0Series (v : ℝ) :
    riemannXiKernel v = 4 * ∑' n : ℕ, xiKernelGaussianJet0 n v := by
  unfold riemannXiKernel
  congr 1
  apply tsum_congr
  intro n
  exact riemannXiKernelTerm_eq_gaussianJet0 n v

theorem riemannXiKernel_hasDerivAt_gaussianJet1_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt riemannXiKernel
      (4 * ∑' n : ℕ, xiKernelGaussianJet1 n v) v := by
  have h := (xiKernelGaussianJet0Series_hasDerivAt_local_zero hv).const_mul
    (4 : ℝ)
  have heq : riemannXiKernel =
      (fun z => 4 * ∑' n : ℕ, xiKernelGaussianJet0 n z) := by
    funext z
    exact riemannXiKernel_eq_gaussianJet0Series z
  rw [heq]
  exact h

theorem riemannXiKernel_deriv_eq_gaussianJet1_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv riemannXiKernel v =
      4 * ∑' n : ℕ, xiKernelGaussianJet1 n v :=
  (riemannXiKernel_hasDerivAt_gaussianJet1_local_zero hv).deriv

theorem riemannXiKernel_deriv_hasDerivAt_gaussianJet2_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv riemannXiKernel)
      (4 * ∑' n : ℕ, xiKernelGaussianJet2 n v) v := by
  have h := (xiKernelGaussianJet1Series_hasDerivAt_local_zero hv).const_mul
    (4 : ℝ)
  have heq : deriv riemannXiKernel =ᶠ[nhds v]
      (fun z => 4 * ∑' n : ℕ, xiKernelGaussianJet1 n z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with z hz
    exact riemannXiKernel_deriv_eq_gaussianJet1_local_zero hz
  exact h.congr_of_eventuallyEq heq

theorem riemannXiKernel_deriv2_eq_gaussianJet2_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv riemannXiKernel) v =
      4 * ∑' n : ℕ, xiKernelGaussianJet2 n v :=
  (riemannXiKernel_deriv_hasDerivAt_gaussianJet2_local_zero hv).deriv

theorem riemannXiKernel_deriv2_hasDerivAt_gaussianJet3_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (deriv riemannXiKernel))
      (4 * ∑' n : ℕ, xiKernelGaussianJet3 n v) v := by
  have h := (xiKernelGaussianJet2Series_hasDerivAt_local_zero hv).const_mul
    (4 : ℝ)
  have heq : deriv (deriv riemannXiKernel) =ᶠ[nhds v]
      (fun z => 4 * ∑' n : ℕ, xiKernelGaussianJet2 n z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with z hz
    exact riemannXiKernel_deriv2_eq_gaussianJet2_local_zero hz
  exact h.congr_of_eventuallyEq heq

theorem riemannXiKernel_deriv3_eq_gaussianJet3_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv (deriv riemannXiKernel)) v =
      4 * ∑' n : ℕ, xiKernelGaussianJet3 n v :=
  (riemannXiKernel_deriv2_hasDerivAt_gaussianJet3_local_zero hv).deriv

theorem riemannXiKernel_deriv3_hasDerivAt_gaussianJet4_local_zero
    {v : ℝ} (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (deriv (deriv riemannXiKernel)))
      (4 * ∑' n : ℕ, xiKernelGaussianJet4 n v) v := by
  have h := (xiKernelGaussianJet3Series_hasDerivAt_local_zero hv).const_mul
    (4 : ℝ)
  have heq : deriv (deriv (deriv riemannXiKernel)) =ᶠ[nhds v]
      (fun z => 4 * ∑' n : ℕ, xiKernelGaussianJet3 n z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with z hz
    exact riemannXiKernel_deriv3_eq_gaussianJet3_local_zero hz
  exact h.congr_of_eventuallyEq heq

/-- Exact fourth derivative of the summed Riemann kernel at the origin. -/
theorem riemannXiKernel_deriv4_zero_eq :
    deriv^[4] riemannXiKernel 0 =
      4 * ∑' n : ℕ, xiKernelGaussianJet4 n 0 := by
  change deriv (deriv (deriv (deriv riemannXiKernel))) 0 = _
  exact (riemannXiKernel_deriv3_hasDerivAt_gaussianJet4_local_zero
    (by constructor <;> norm_num)).deriv

/-! ### Certified origin nome bounds -/

/-- A rational upper bound on `exp π`, used for lower bounds on the first
theta nome. -/
theorem exp_pi_lt_one_hundred_sixteen_div_five :
    Real.exp Real.pi < (116 : ℝ) / 5 := by
  let d : ℝ := Real.pi - 3
  have hd0 : 0 ≤ d := by
    dsimp [d]
    linarith [Real.pi_gt_three]
  have hd1 : d ≤ 177 / 1250 := by
    dsimp [d]
    linarith [Real.pi_lt_d4]
  have hed := Real.exp_bound' hd0 (hd1.trans (by norm_num))
    (show 0 < 4 by norm_num)
  have hd2 : d ^ 2 ≤ (177 / 1250 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hd0 hd1 2
  have hd3 : d ^ 3 ≤ (177 / 1250 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hd0 hd1 3
  have hd4 : d ^ 4 ≤ (177 / 1250 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hd0 hd1 4
  have hed' : Real.exp d ≤ 5761 / 5000 := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ,
      show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ,
      show (1 : ℕ) = 0 + 1 by norm_num, Finset.sum_range_succ] at hed
    norm_num [Nat.factorial] at hed
    nlinarith
  have he1 := Real.exp_one_lt_d9
  have he3 : Real.exp 3 < (27182818286 / 10000000000 : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num,
      Real.exp_add, Real.exp_add]
    calc
      Real.exp 1 * Real.exp 1 * Real.exp 1 = Real.exp 1 ^ 3 := by ring
      _ < (2.7182818286 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ (n := 3) he1 (Real.exp_pos 1).le (by norm_num)
      _ = (27182818286 / 10000000000 : ℝ) ^ 3 := by norm_num
  have hpi : Real.pi = 3 + d := by
    dsimp [d]
    ring
  rw [hpi, Real.exp_add]
  calc
    Real.exp 3 * Real.exp d <
        (27182818286 / 10000000000 : ℝ) ^ 3 * (5761 / 5000) :=
      mul_lt_mul he3 hed' (Real.exp_pos d) (by positivity)
    _ < (116 : ℝ) / 5 := by norm_num

/-- A rational lower bound on `exp π`, used for the corresponding upper
nome bound. -/
theorem twenty_three_lt_exp_pi : (23 : ℝ) < Real.exp Real.pi := by
  let d : ℝ := Real.pi - 3
  have hd0 : 0 ≤ d := by
    dsimp [d]
    linarith [Real.pi_gt_three]
  have hdLower : 7 / 50 < d := by
    dsimp [d]
    linarith [Real.pi_gt_d2]
  have hed := Real.sum_le_exp_of_nonneg hd0 3
  have hed' : 5749 / 5000 < Real.exp d := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Finset.sum_range_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ,
      show (1 : ℕ) = 0 + 1 by norm_num, Finset.sum_range_succ] at hed
    norm_num [Nat.factorial] at hed
    nlinarith [sq_nonneg (d - 7 / 50)]
  have he1 := Real.exp_one_gt_d9
  have he3 : (27182818283 / 10000000000 : ℝ) ^ 3 < Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num,
      Real.exp_add, Real.exp_add]
    calc
      (27182818283 / 10000000000 : ℝ) ^ 3 =
          (2.7182818283 : ℝ) ^ 3 := by norm_num
      _ < Real.exp 1 ^ 3 :=
        pow_lt_pow_left₀ (n := 3) he1 (by positivity) (by norm_num)
      _ = Real.exp 1 * Real.exp 1 * Real.exp 1 := by ring
  have hpi : Real.pi = 3 + d := by
    dsimp [d]
    ring
  rw [hpi, Real.exp_add]
  calc
    (23 : ℝ) < (27182818283 / 10000000000 : ℝ) ^ 3 *
        (5749 / 5000) := by norm_num
    _ < Real.exp 3 * Real.exp d :=
      mul_lt_mul he3 hed'.le (by positivity) (by positivity)

theorem five_div_one_hundred_sixteen_lt_exp_neg_pi :
    (5 : ℝ) / 116 < Real.exp (-Real.pi) := by
  rw [Real.exp_neg]
  rw [lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  norm_num
  exact exp_pi_lt_one_hundred_sixteen_div_five

theorem exp_neg_pi_lt_one_div_twenty_three :
    Real.exp (-Real.pi) < (1 : ℝ) / 23 := by
  rw [Real.exp_neg]
  rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num
  exact twenty_three_lt_exp_pi

theorem originIndexAddThree_le (n : ℕ) :
    ((n : ℝ) + 3) ≤ 3 * (2 : ℝ) ^ n := by
  norm_cast
  have hn : n + 1 ≤ 2 ^ n := Nat.succ_le_iff.mpr n.lt_two_pow_self
  omega

theorem originSevenStepExponent_le (n : ℕ) :
    (9 + 7 * n : ℕ) ≤ (n + 3) ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        9 + 7 * (n + 1) = (9 + 7 * n) + 7 := by omega
        _ ≤ (n + 3) ^ 2 + 7 := Nat.add_le_add_right ih 7
        _ ≤ (n + 1 + 3) ^ 2 := by nlinarith

theorem originNomePow12_pointwise_le (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 23) (n : ℕ) :
    ((n : ℝ) + 3) ^ 12 * t ^ (n + 3) ^ 2 ≤
      ((3 : ℝ) ^ 12 / 23 ^ 9) * ((4096 : ℝ) / 23 ^ 7) ^ n := by
  have hr := originIndexAddThree_le n
  have he := originSevenStepExponent_le n
  have htbase : t ^ (n + 3) ^ 2 ≤ (1 / 23 : ℝ) ^ (n + 3) ^ 2 :=
    pow_le_pow_left₀ ht0 ht1 _
  have htexp : (1 / 23 : ℝ) ^ (n + 3) ^ 2 ≤
      (1 / 23 : ℝ) ^ (9 + 7 * n) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) he
  calc
    ((n : ℝ) + 3) ^ 12 * t ^ (n + 3) ^ 2 ≤
        (3 * (2 : ℝ) ^ n) ^ 12 * (1 / 23 : ℝ) ^ (9 + 7 * n) := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hr 12)
        (htbase.trans htexp) (pow_nonneg ht0 _) (by positivity)
    _ = ((3 : ℝ) ^ 12 / 23 ^ 9) *
        ((4096 : ℝ) / 23 ^ 7) ^ n := by
      rw [pow_add, pow_mul]
      norm_num [mul_pow]
      rw [← pow_mul, mul_comm n 12, pow_mul]
      rw [show (531441 : ℝ) * (2 ^ 12) ^ n *
          (1 / 1801152661463 * (1 / 3404825447) ^ n) =
          (531441 / 1801152661463) *
            ((2 ^ 12) ^ n * (1 / 3404825447) ^ n) by ring]
      rw [← mul_pow]
      norm_num

theorem originNomePow12Tail_summable :
    Summable (fun n : ℕ => ((n : ℝ) + 3) ^ 12 *
      Real.exp (-Real.pi) ^ (n + 3) ^ 2) := by
  let t : ℝ := Real.exp (-Real.pi)
  let A : ℝ := 3 ^ 12 / 23 ^ 9
  let R : ℝ := 4096 / 23 ^ 7
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 23 := by
    dsimp [t]
    exact exp_neg_pi_lt_one_div_twenty_three.le
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by dsimp [R]; norm_num
  have hg : Summable (fun n : ℕ => A * R ^ n) :=
    (summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hR0]
      exact hR1)).mul_left A
  exact hg.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (pow_nonneg ht0 _))
    (fun n => originNomePow12_pointwise_le t ht0 ht1 n)

theorem tsum_originNomePow12_tail_lt :
    (∑' n : ℕ, ((n : ℝ) + 3) ^ 12 *
      Real.exp (-Real.pi) ^ (n + 3) ^ 2) < (1 : ℝ) / 3000000 := by
  let t : ℝ := Real.exp (-Real.pi)
  let A : ℝ := 3 ^ 12 / 23 ^ 9
  let R : ℝ := 4096 / 23 ^ 7
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 23 := by
    dsimp [t]
    exact exp_neg_pi_lt_one_div_twenty_three.le
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by dsimp [R]; norm_num
  have hg : Summable (fun n : ℕ => A * R ^ n) :=
    (summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hR0]
      exact hR1)).mul_left A
  have hf : Summable (fun n : ℕ =>
      ((n : ℝ) + 3) ^ 12 * t ^ (n + 3) ^ 2) :=
    hg.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (pow_nonneg ht0 _))
      (fun n => originNomePow12_pointwise_le t ht0 ht1 n)
  have hle := hf.tsum_le_tsum
    (fun n => originNomePow12_pointwise_le t ht0 ht1 n) hg
  change (∑' n : ℕ, ((n : ℝ) + 3) ^ 12 * t ^ (n + 3) ^ 2) < _
  calc
    (∑' n : ℕ, ((n : ℝ) + 3) ^ 12 * t ^ (n + 3) ^ 2) ≤
        ∑' n : ℕ, A * R ^ n := hle
    _ = A * (1 - R)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1]
    _ < (1 : ℝ) / 3000000 := by
      dsimp [A, R]
      norm_num

/-! ### Exact origin-jet polynomials -/

def xiOriginJet0Polynomial (q : ℝ) : ℝ :=
  q * (2 * q - 3)

def xiOriginJet2Polynomial (q : ℝ) : ℝ :=
  q * (32 * q ^ 3 - 224 * q ^ 2 + 330 * q - 75) / 4

def xiOriginJet4Polynomial (q : ℝ) : ℝ :=
  q * (512 * q ^ 5 - 8448 * q ^ 4 + 41408 * q ^ 3 -
    68096 * q ^ 2 + 30930 * q - 1875) / 16

theorem xiOriginJet0Polynomial_bounds {q : ℝ} (hq : 27 ≤ q) :
    0 ≤ xiOriginJet0Polynomial q ∧ xiOriginJet0Polynomial q ≤ 2 * q ^ 2 := by
  unfold xiOriginJet0Polynomial
  constructor <;> nlinarith

theorem xiOriginJet2Polynomial_bounds {q : ℝ} (hq : 27 ≤ q) :
    0 ≤ xiOriginJet2Polynomial q ∧ xiOriginJet2Polynomial q ≤ 9 * q ^ 4 := by
  have hq0 : 0 ≤ q := by linarith
  have hlead : 0 ≤ q ^ 2 * (32 * q - 224) :=
    mul_nonneg (sq_nonneg q) (by nlinarith)
  have hq2ge : 729 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 27)]
  have hq4ge : 729 * q ^ 2 ≤ q ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hq2ge (sq_nonneg q)]
  unfold xiOriginJet2Polynomial
  constructor <;> nlinarith

theorem xiOriginJet4Polynomial_bounds {q : ℝ} (hq : 27 ≤ q) :
    0 ≤ xiOriginJet4Polynomial q ∧ xiOriginJet4Polynomial q ≤ 36 * q ^ 6 := by
  have hq0 : 0 ≤ q := by linarith
  have hq2ge : 729 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 27)]
  have hq4ge : 729 * q ^ 2 ≤ q ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hq2ge (sq_nonneg q)]
  have hq6ge : 729 * q ^ 4 ≤ q ^ 6 := by
    nlinarith [mul_le_mul_of_nonneg_right hq2ge (sq_nonneg (q ^ 2))]
  have hq6ge' : 729 ^ 2 * q ^ 2 ≤ q ^ 6 := by nlinarith
  have hlead : 0 ≤ q ^ 4 * (512 * q - 8448) :=
    mul_nonneg (pow_nonneg hq0 4) (by nlinarith)
  unfold xiOriginJet4Polynomial
  constructor <;> nlinarith

set_option maxHeartbeats 500000 in
theorem xiOriginLeadingPolynomial_bounds :
    xiOriginJet0Polynomial Real.pi ≤ 258 / 25 ∧
    xiOriginJet0Polynomial (4 * Real.pi) ≤ 279 ∧
    xiOriginJet2Polynomial Real.pi ≤ -(201739 : ℝ) / 1000 ∧
    xiOriginJet2Polynomial (4 * Real.pi) ≤ 101160 ∧
    xiOriginJet4Polynomial Real.pi ≤ 8030 ∧
    xiOriginJet4Polynomial (4 * Real.pi) ≤ 16949700 := by
  let l : ℝ := 3.141592
  let u : ℝ := 3.141593
  have hl : l ≤ Real.pi := by
    dsimp [l]
    exact Real.pi_gt_d6.le
  have hu : Real.pi ≤ u := by
    dsimp [u]
    exact Real.pi_lt_d6.le
  have hl0 : 0 ≤ l := by dsimp [l]; norm_num
  have hp0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hpow (k : ℕ) : l ^ k ≤ Real.pi ^ k ∧ Real.pi ^ k ≤ u ^ k :=
    ⟨pow_le_pow_left₀ hl0 hl k, pow_le_pow_left₀ hp0 hu k⟩
  have hql : 4 * l ≤ 4 * Real.pi := mul_le_mul_of_nonneg_left hl (by norm_num)
  have hqu : 4 * Real.pi ≤ 4 * u := mul_le_mul_of_nonneg_left hu (by norm_num)
  have hql0 : 0 ≤ 4 * l := by positivity
  have hq0 : 0 ≤ 4 * Real.pi := by positivity
  have hqpow (k : ℕ) : (4 * l) ^ k ≤ (4 * Real.pi) ^ k ∧
      (4 * Real.pi) ^ k ≤ (4 * u) ^ k :=
    ⟨pow_le_pow_left₀ hql0 hql k, pow_le_pow_left₀ hq0 hqu k⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      xiOriginJet0Polynomial Real.pi =
          2 * Real.pi ^ 2 - 3 * Real.pi := by
            unfold xiOriginJet0Polynomial
            ring
      _ ≤ 2 * u ^ 2 - 3 * l := by nlinarith [(hpow 2).2]
      _ ≤ 258 / 25 := by norm_num [l, u]
  · calc
      xiOriginJet0Polynomial (4 * Real.pi) =
          2 * (4 * Real.pi) ^ 2 - 3 * (4 * Real.pi) := by
            unfold xiOriginJet0Polynomial
            ring
      _ ≤ 2 * (4 * u) ^ 2 - 3 * (4 * l) := by nlinarith [(hqpow 2).2]
      _ ≤ 279 := by norm_num [l, u]
  · calc
      xiOriginJet2Polynomial Real.pi =
          8 * Real.pi ^ 4 - 56 * Real.pi ^ 3 +
            (165 / 2) * Real.pi ^ 2 - (75 / 4) * Real.pi := by
              unfold xiOriginJet2Polynomial
              ring
      _ ≤ 8 * u ^ 4 - 56 * l ^ 3 + (165 / 2) * u ^ 2 - (75 / 4) * l := by
        gcongr
      _ ≤ -(201739 : ℝ) / 1000 := by norm_num [l, u]
  · calc
      xiOriginJet2Polynomial (4 * Real.pi) =
          8 * (4 * Real.pi) ^ 4 - 56 * (4 * Real.pi) ^ 3 +
            (165 / 2) * (4 * Real.pi) ^ 2 - (75 / 4) * (4 * Real.pi) := by
              unfold xiOriginJet2Polynomial
              ring
      _ ≤ 8 * (4 * u) ^ 4 - 56 * (4 * l) ^ 3 +
          (165 / 2) * (4 * u) ^ 2 - (75 / 4) * (4 * l) := by
        gcongr
      _ ≤ 101160 := by norm_num [l, u]
  · calc
      xiOriginJet4Polynomial Real.pi =
          32 * Real.pi ^ 6 - 528 * Real.pi ^ 5 + 2588 * Real.pi ^ 4 -
            4256 * Real.pi ^ 3 + (15465 / 8) * Real.pi ^ 2 -
            (1875 / 16) * Real.pi := by
              unfold xiOriginJet4Polynomial
              ring
      _ ≤ 32 * u ^ 6 - 528 * l ^ 5 + 2588 * u ^ 4 -
          4256 * l ^ 3 + (15465 / 8) * u ^ 2 - (1875 / 16) * l := by
        gcongr
      _ ≤ 8030 := by norm_num [l, u]
  · calc
      xiOriginJet4Polynomial (4 * Real.pi) =
          32 * (4 * Real.pi) ^ 6 - 528 * (4 * Real.pi) ^ 5 +
            2588 * (4 * Real.pi) ^ 4 - 4256 * (4 * Real.pi) ^ 3 +
            (15465 / 8) * (4 * Real.pi) ^ 2 - (1875 / 16) * (4 * Real.pi) := by
              unfold xiOriginJet4Polynomial
              ring
      _ ≤ 32 * (4 * u) ^ 6 - 528 * (4 * l) ^ 5 +
          2588 * (4 * u) ^ 4 - 4256 * (4 * l) ^ 3 +
          (15465 / 8) * (4 * u) ^ 2 - (1875 / 16) * (4 * l) := by
        gcongr
      _ ≤ 16949700 := by norm_num [l, u]

theorem xiKernelGaussianJet0_zero_formula (n : ℕ) :
    xiKernelGaussianJet0 n 0 =
      xiOriginJet0Polynomial (Real.pi * ((n : ℝ) + 1) ^ 2) *
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2)) := by
  simp [xiKernelGaussianJet0, xiOriginJet0Polynomial, xiGaussianMode,
    xiGaussianQ]
  ring

theorem xiKernelGaussianJet2_zero_formula (n : ℕ) :
    xiKernelGaussianJet2 n 0 =
      xiOriginJet2Polynomial (Real.pi * ((n : ℝ) + 1) ^ 2) *
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2)) := by
  simp [xiKernelGaussianJet2, xiOriginJet2Polynomial, xiGaussianJet2,
    xiGaussianSlope, xiGaussianMode, xiGaussianQ]
  ring

theorem xiKernelGaussianJet4_zero_formula (n : ℕ) :
    xiKernelGaussianJet4 n 0 =
      xiOriginJet4Polynomial (Real.pi * ((n : ℝ) + 1) ^ 2) *
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2)) := by
  simp [xiKernelGaussianJet4, xiOriginJet4Polynomial, xiGaussianJet4,
    xiGaussianSlope, xiGaussianMode, xiGaussianQ]
  ring

theorem exp_neg_pi_mul_index_sq_eq_nome_pow (n : ℕ) :
    Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2)) =
      Real.exp (-Real.pi) ^ (n + 1) ^ 2 := by
  calc
    Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2)) =
        Real.exp ((((n + 1) ^ 2 : ℕ) : ℝ) * (-Real.pi)) := by
      congr 1
      norm_num [Nat.cast_pow, Nat.cast_add]
      ring
    _ = Real.exp (-Real.pi) ^ (n + 1) ^ 2 := by
      rw [Real.exp_nat_mul]

theorem xiKernelGaussianJet0_shifted_abs_le (n : ℕ) :
    |xiKernelGaussianJet0 (n + 2) 0| ≤
      32 * ((n : ℝ) + 3) ^ 12 *
        Real.exp (-Real.pi) ^ (n + 3) ^ 2 := by
  let r : ℝ := (n : ℝ) + 3
  let q : ℝ := Real.pi * r ^ 2
  have hr : 3 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hqLower : 27 ≤ q := by
    dsimp [q]
    have hr2 : 9 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 3)]
    calc
      (27 : ℝ) = 3 * 9 := by norm_num
      _ ≤ Real.pi * r ^ 2 :=
        mul_le_mul Real.pi_gt_three.le hr2 (by norm_num) Real.pi_pos.le
  have hqUpper : q ≤ 4 * r ^ 2 := by
    dsimp [q]
    exact mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (sq_nonneg r)
  have hp := xiOriginJet0Polynomial_bounds hqLower
  have hpUpper : xiOriginJet0Polynomial q ≤ 32 * r ^ 12 := by
    have hq2 := pow_le_pow_left₀ (by positivity) hqUpper 2
    have hr4 : r ^ 4 ≤ r ^ 12 := pow_le_pow_right₀ (by linarith) (by omega)
    calc
      xiOriginJet0Polynomial q ≤ 2 * q ^ 2 := hp.2
      _ ≤ 2 * (4 * r ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hq2 (by norm_num)
      _ ≤ 32 * r ^ 12 := by nlinarith
  rw [xiKernelGaussianJet0_zero_formula,
    exp_neg_pi_mul_index_sq_eq_nome_pow]
  have hrEq : (((n + 2 : ℕ) : ℝ) + 1) = r := by
    dsimp [r]
    push_cast
    ring
  have hnEq : n + 2 + 1 = n + 3 := by omega
  rw [hrEq, hnEq]
  change |xiOriginJet0Polynomial q *
      Real.exp (-Real.pi) ^ (n + 3) ^ 2| ≤ _
  rw [abs_mul, abs_of_nonneg hp.1, abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact mul_le_mul_of_nonneg_right hpUpper (pow_nonneg (by positivity) _)

theorem xiKernelGaussianJet2_shifted_abs_le (n : ℕ) :
    |xiKernelGaussianJet2 (n + 2) 0| ≤
      2304 * ((n : ℝ) + 3) ^ 12 *
        Real.exp (-Real.pi) ^ (n + 3) ^ 2 := by
  let r : ℝ := (n : ℝ) + 3
  let q : ℝ := Real.pi * r ^ 2
  have hr : 3 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hqLower : 27 ≤ q := by
    dsimp [q]
    have hr2 : 9 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 3)]
    calc
      (27 : ℝ) = 3 * 9 := by norm_num
      _ ≤ Real.pi * r ^ 2 :=
        mul_le_mul Real.pi_gt_three.le hr2 (by norm_num) Real.pi_pos.le
  have hqUpper : q ≤ 4 * r ^ 2 := by
    dsimp [q]
    exact mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (sq_nonneg r)
  have hp := xiOriginJet2Polynomial_bounds hqLower
  have hpUpper : xiOriginJet2Polynomial q ≤ 2304 * r ^ 12 := by
    have hq4 := pow_le_pow_left₀ (by positivity) hqUpper 4
    have hr8 : r ^ 8 ≤ r ^ 12 := pow_le_pow_right₀ (by linarith) (by omega)
    calc
      xiOriginJet2Polynomial q ≤ 9 * q ^ 4 := hp.2
      _ ≤ 9 * (4 * r ^ 2) ^ 4 := mul_le_mul_of_nonneg_left hq4 (by norm_num)
      _ ≤ 2304 * r ^ 12 := by nlinarith
  rw [xiKernelGaussianJet2_zero_formula,
    exp_neg_pi_mul_index_sq_eq_nome_pow]
  have hrEq : (((n + 2 : ℕ) : ℝ) + 1) = r := by
    dsimp [r]
    push_cast
    ring
  have hnEq : n + 2 + 1 = n + 3 := by omega
  rw [hrEq, hnEq]
  change |xiOriginJet2Polynomial q *
      Real.exp (-Real.pi) ^ (n + 3) ^ 2| ≤ _
  rw [abs_mul, abs_of_nonneg hp.1, abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact mul_le_mul_of_nonneg_right hpUpper (pow_nonneg (by positivity) _)

theorem xiKernelGaussianJet4_shifted_abs_le (n : ℕ) :
    |xiKernelGaussianJet4 (n + 2) 0| ≤
      147456 * ((n : ℝ) + 3) ^ 12 *
        Real.exp (-Real.pi) ^ (n + 3) ^ 2 := by
  let r : ℝ := (n : ℝ) + 3
  let q : ℝ := Real.pi * r ^ 2
  have hr : 3 ≤ r := by
    dsimp [r]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hqLower : 27 ≤ q := by
    dsimp [q]
    have hr2 : 9 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 3)]
    calc
      (27 : ℝ) = 3 * 9 := by norm_num
      _ ≤ Real.pi * r ^ 2 :=
        mul_le_mul Real.pi_gt_three.le hr2 (by norm_num) Real.pi_pos.le
  have hqUpper : q ≤ 4 * r ^ 2 := by
    dsimp [q]
    exact mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (sq_nonneg r)
  have hp := xiOriginJet4Polynomial_bounds hqLower
  have hpUpper : xiOriginJet4Polynomial q ≤ 147456 * r ^ 12 := by
    have hq6 := pow_le_pow_left₀ (by positivity) hqUpper 6
    calc
      xiOriginJet4Polynomial q ≤ 36 * q ^ 6 := hp.2
      _ ≤ 36 * (4 * r ^ 2) ^ 6 := mul_le_mul_of_nonneg_left hq6 (by norm_num)
      _ = 147456 * r ^ 12 := by ring
  rw [xiKernelGaussianJet4_zero_formula,
    exp_neg_pi_mul_index_sq_eq_nome_pow]
  have hrEq : (((n + 2 : ℕ) : ℝ) + 1) = r := by
    dsimp [r]
    push_cast
    ring
  have hnEq : n + 2 + 1 = n + 3 := by omega
  rw [hrEq, hnEq]
  change |xiOriginJet4Polynomial q *
      Real.exp (-Real.pi) ^ (n + 3) ^ 2| ≤ _
  rw [abs_mul, abs_of_nonneg hp.1, abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact mul_le_mul_of_nonneg_right hpUpper (pow_nonneg (by positivity) _)

set_option maxHeartbeats 800000 in
theorem abs_tsum_xiKernelGaussianJet0_shifted_lt :
    |∑' n : ℕ, xiKernelGaussianJet0 (n + 2) 0| < (1 : ℝ) / 90000 := by
  let g : ℕ → ℝ := fun n => ((n : ℝ) + 3) ^ 12 *
    Real.exp (-Real.pi) ^ (n + 3) ^ 2
  have hf : Summable (fun n : ℕ => xiKernelGaussianJet0 (n + 2) 0) :=
    (summable_nat_add_iff 2).2 xiKernelGaussianJet0_summable_zero
  have hg : Summable g := by
    simpa only [g] using originNomePow12Tail_summable
  have hmajor : Summable (fun n : ℕ => 32 * g n) := hg.mul_left 32
  have hupper : (∑' n : ℕ, xiKernelGaussianJet0 (n + 2) 0) ≤
      ∑' n : ℕ, 32 * g n :=
    hf.tsum_le_tsum (fun n => (le_abs_self _).trans (by
      simpa only [g, mul_assoc] using xiKernelGaussianJet0_shifted_abs_le n))
      hmajor
  have hnegative : -(∑' n : ℕ, xiKernelGaussianJet0 (n + 2) 0) ≤
      ∑' n : ℕ, 32 * g n := by
    rw [← tsum_neg]
    exact hf.neg.tsum_le_tsum (fun n => (neg_le_abs _).trans (by
      simpa only [g, mul_assoc] using xiKernelGaussianJet0_shifted_abs_le n))
      hmajor
  have habs : |∑' n : ℕ, xiKernelGaussianJet0 (n + 2) 0| ≤
      ∑' n : ℕ, 32 * g n := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |∑' n : ℕ, xiKernelGaussianJet0 (n + 2) 0| ≤
        ∑' n : ℕ, 32 * g n := habs
    _ = 32 * ∑' n : ℕ, g n := tsum_mul_left
    _ < 32 * ((1 : ℝ) / 3000000) :=
      mul_lt_mul_of_pos_left (by simpa only [g] using tsum_originNomePow12_tail_lt)
        (by norm_num)
    _ < (1 : ℝ) / 90000 := by norm_num

set_option maxHeartbeats 800000 in
theorem abs_tsum_xiKernelGaussianJet2_shifted_lt :
    |∑' n : ℕ, xiKernelGaussianJet2 (n + 2) 0| < (1 : ℝ) / 1250 := by
  let g : ℕ → ℝ := fun n => ((n : ℝ) + 3) ^ 12 *
    Real.exp (-Real.pi) ^ (n + 3) ^ 2
  have hf : Summable (fun n : ℕ => xiKernelGaussianJet2 (n + 2) 0) :=
    (summable_nat_add_iff 2).2 xiKernelGaussianJet2_summable_zero
  have hg : Summable g := by
    simpa only [g] using originNomePow12Tail_summable
  have hmajor : Summable (fun n : ℕ => 2304 * g n) := hg.mul_left 2304
  have hupper : (∑' n : ℕ, xiKernelGaussianJet2 (n + 2) 0) ≤
      ∑' n : ℕ, 2304 * g n :=
    hf.tsum_le_tsum (fun n => (le_abs_self _).trans (by
      simpa only [g, mul_assoc] using xiKernelGaussianJet2_shifted_abs_le n))
      hmajor
  have hnegative : -(∑' n : ℕ, xiKernelGaussianJet2 (n + 2) 0) ≤
      ∑' n : ℕ, 2304 * g n := by
    rw [← tsum_neg]
    exact hf.neg.tsum_le_tsum (fun n => (neg_le_abs _).trans (by
      simpa only [g, mul_assoc] using xiKernelGaussianJet2_shifted_abs_le n))
      hmajor
  have habs : |∑' n : ℕ, xiKernelGaussianJet2 (n + 2) 0| ≤
      ∑' n : ℕ, 2304 * g n := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |∑' n : ℕ, xiKernelGaussianJet2 (n + 2) 0| ≤
        ∑' n : ℕ, 2304 * g n := habs
    _ = 2304 * ∑' n : ℕ, g n := tsum_mul_left
    _ < 2304 * ((1 : ℝ) / 3000000) :=
      mul_lt_mul_of_pos_left (by simpa only [g] using tsum_originNomePow12_tail_lt)
        (by norm_num)
    _ < (1 : ℝ) / 1250 := by norm_num

set_option maxHeartbeats 800000 in
theorem abs_tsum_xiKernelGaussianJet4_shifted_lt :
    |∑' n : ℕ, xiKernelGaussianJet4 (n + 2) 0| < (1 : ℝ) / 20 := by
  let g : ℕ → ℝ := fun n => ((n : ℝ) + 3) ^ 12 *
    Real.exp (-Real.pi) ^ (n + 3) ^ 2
  have hfull : Summable (fun n : ℕ => xiKernelGaussianJet4 n 0) := by
    apply Summable.of_norm_bounded xiKernelJet4LocalMajorantCoeff_summable
    intro n
    exact xiKernelGaussianJet4_norm_le_local_zero n
      (by constructor <;> norm_num)
  have hf : Summable (fun n : ℕ => xiKernelGaussianJet4 (n + 2) 0) :=
    (summable_nat_add_iff 2).2 hfull
  have hg : Summable g := by
    simpa only [g] using originNomePow12Tail_summable
  have hmajor : Summable (fun n : ℕ => 147456 * g n) := hg.mul_left 147456
  have hupper : (∑' n : ℕ, xiKernelGaussianJet4 (n + 2) 0) ≤
      ∑' n : ℕ, 147456 * g n :=
    hf.tsum_le_tsum (fun n => (le_abs_self _).trans (by
      simpa only [g, mul_assoc] using xiKernelGaussianJet4_shifted_abs_le n))
      hmajor
  have hnegative : -(∑' n : ℕ, xiKernelGaussianJet4 (n + 2) 0) ≤
      ∑' n : ℕ, 147456 * g n := by
    rw [← tsum_neg]
    exact hf.neg.tsum_le_tsum (fun n => (neg_le_abs _).trans (by
      simpa only [g, mul_assoc] using xiKernelGaussianJet4_shifted_abs_le n))
      hmajor
  have habs : |∑' n : ℕ, xiKernelGaussianJet4 (n + 2) 0| ≤
      ∑' n : ℕ, 147456 * g n := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |∑' n : ℕ, xiKernelGaussianJet4 (n + 2) 0| ≤
        ∑' n : ℕ, 147456 * g n := habs
    _ = 147456 * ∑' n : ℕ, g n := tsum_mul_left
    _ < 147456 * ((1 : ℝ) / 3000000) :=
      mul_lt_mul_of_pos_left (by simpa only [g] using tsum_originNomePow12_tail_lt)
        (by norm_num)
    _ < (1 : ℝ) / 20 := by norm_num

/-- The first two Gaussian modes, isolated from the certified tail, obey
the rational origin bounds needed for the quartic theta constant. -/
theorem xiOriginLeadingModes_bounds :
    xiKernelGaussianJet0 0 0 + xiKernelGaussianJet0 1 0 < (4497 : ℝ) / 10000 ∧
    xiKernelGaussianJet2 0 0 + xiKernelGaussianJet2 1 0 < -(8334 : ℝ) / 1000 ∧
    xiKernelGaussianJet4 0 0 + xiKernelGaussianJet4 1 0 < (4097 : ℝ) / 10 := by
  let t : ℝ := Real.exp (-Real.pi)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htLower : (5 : ℝ) / 116 ≤ t :=
    five_div_one_hundred_sixteen_lt_exp_neg_pi.le
  have htUpper : t ≤ (1 : ℝ) / 23 :=
    exp_neg_pi_lt_one_div_twenty_three.le
  have hpoly := xiOriginLeadingPolynomial_bounds
  have h00 : xiKernelGaussianJet0 0 0 =
      xiOriginJet0Polynomial Real.pi * t := by
    rw [xiKernelGaussianJet0_zero_formula,
      exp_neg_pi_mul_index_sq_eq_nome_pow]
    norm_num [t]
  have h01 : xiKernelGaussianJet0 1 0 =
      xiOriginJet0Polynomial (4 * Real.pi) * t ^ 4 := by
    rw [xiKernelGaussianJet0_zero_formula,
      exp_neg_pi_mul_index_sq_eq_nome_pow]
    norm_num [t]
    ring_nf
  have h20 : xiKernelGaussianJet2 0 0 =
      xiOriginJet2Polynomial Real.pi * t := by
    rw [xiKernelGaussianJet2_zero_formula,
      exp_neg_pi_mul_index_sq_eq_nome_pow]
    norm_num [t]
  have h21 : xiKernelGaussianJet2 1 0 =
      xiOriginJet2Polynomial (4 * Real.pi) * t ^ 4 := by
    rw [xiKernelGaussianJet2_zero_formula,
      exp_neg_pi_mul_index_sq_eq_nome_pow]
    norm_num [t]
    ring_nf
  have h40 : xiKernelGaussianJet4 0 0 =
      xiOriginJet4Polynomial Real.pi * t := by
    rw [xiKernelGaussianJet4_zero_formula,
      exp_neg_pi_mul_index_sq_eq_nome_pow]
    norm_num [t]
  have h41 : xiKernelGaussianJet4 1 0 =
      xiOriginJet4Polynomial (4 * Real.pi) * t ^ 4 := by
    rw [xiKernelGaussianJet4_zero_formula,
      exp_neg_pi_mul_index_sq_eq_nome_pow]
    norm_num [t]
    ring_nf
  have ht4Upper : t ^ 4 ≤ ((1 : ℝ) / 23) ^ 4 :=
    pow_le_pow_left₀ ht0 htUpper 4
  have hj00 : xiKernelGaussianJet0 0 0 ≤
      (258 / 25 : ℝ) * (1 / 23) := by
    rw [h00]
    calc
      xiOriginJet0Polynomial Real.pi * t ≤ (258 / 25 : ℝ) * t :=
        mul_le_mul_of_nonneg_right hpoly.1 ht0
      _ ≤ (258 / 25 : ℝ) * (1 / 23) :=
        mul_le_mul_of_nonneg_left htUpper (by norm_num)
  have hj01 : xiKernelGaussianJet0 1 0 ≤
      (279 : ℝ) * (1 / 23) ^ 4 := by
    rw [h01]
    calc
      xiOriginJet0Polynomial (4 * Real.pi) * t ^ 4 ≤ 279 * t ^ 4 :=
        mul_le_mul_of_nonneg_right hpoly.2.1 (pow_nonneg ht0 4)
      _ ≤ (279 : ℝ) * (1 / 23) ^ 4 :=
        mul_le_mul_of_nonneg_left ht4Upper (by norm_num)
  have hj20 : xiKernelGaussianJet2 0 0 ≤
      (-(201739 : ℝ) / 1000) * (5 / 116) := by
    rw [h20]
    calc
      xiOriginJet2Polynomial Real.pi * t ≤
          (-(201739 : ℝ) / 1000) * t :=
        mul_le_mul_of_nonneg_right hpoly.2.2.1 ht0
      _ ≤ (-(201739 : ℝ) / 1000) * (5 / 116) :=
        mul_le_mul_of_nonpos_left htLower (by norm_num)
  have hj21 : xiKernelGaussianJet2 1 0 ≤
      (101160 : ℝ) * (1 / 23) ^ 4 := by
    rw [h21]
    calc
      xiOriginJet2Polynomial (4 * Real.pi) * t ^ 4 ≤ 101160 * t ^ 4 :=
        mul_le_mul_of_nonneg_right hpoly.2.2.2.1 (pow_nonneg ht0 4)
      _ ≤ (101160 : ℝ) * (1 / 23) ^ 4 :=
        mul_le_mul_of_nonneg_left ht4Upper (by norm_num)
  have hj40 : xiKernelGaussianJet4 0 0 ≤ (8030 : ℝ) * (1 / 23) := by
    rw [h40]
    calc
      xiOriginJet4Polynomial Real.pi * t ≤ 8030 * t :=
        mul_le_mul_of_nonneg_right hpoly.2.2.2.2.1 ht0
      _ ≤ (8030 : ℝ) * (1 / 23) :=
        mul_le_mul_of_nonneg_left htUpper (by norm_num)
  have hj41 : xiKernelGaussianJet4 1 0 ≤
      (16949700 : ℝ) * (1 / 23) ^ 4 := by
    rw [h41]
    calc
      xiOriginJet4Polynomial (4 * Real.pi) * t ^ 4 ≤ 16949700 * t ^ 4 :=
        mul_le_mul_of_nonneg_right hpoly.2.2.2.2.2 (pow_nonneg ht0 4)
      _ ≤ (16949700 : ℝ) * (1 / 23) ^ 4 :=
        mul_le_mul_of_nonneg_left ht4Upper (by norm_num)
  constructor
  · calc
      xiKernelGaussianJet0 0 0 + xiKernelGaussianJet0 1 0 ≤
          (258 / 25 : ℝ) * (1 / 23) + 279 * (1 / 23) ^ 4 :=
        add_le_add hj00 hj01
      _ < (4497 : ℝ) / 10000 := by norm_num
  constructor
  · calc
      xiKernelGaussianJet2 0 0 + xiKernelGaussianJet2 1 0 ≤
          (-(201739 : ℝ) / 1000) * (5 / 116) +
            101160 * (1 / 23) ^ 4 := add_le_add hj20 hj21
      _ < -(8334 : ℝ) / 1000 := by norm_num
  · calc
      xiKernelGaussianJet4 0 0 + xiKernelGaussianJet4 1 0 ≤
          (8030 : ℝ) * (1 / 23) + 16949700 * (1 / 23) ^ 4 :=
        add_le_add hj40 hj41
      _ < (4097 : ℝ) / 10 := by norm_num

theorem xiKernelGaussianJet4_summable_zero :
    Summable (fun n : ℕ => xiKernelGaussianJet4 n 0) := by
  apply Summable.of_norm_bounded xiKernelJet4LocalMajorantCoeff_summable
  intro n
  exact xiKernelGaussianJet4_norm_le_local_zero n
    (by constructor <;> norm_num)

theorem tsum_eq_first_two_add_tail {f : ℕ → ℝ} (hf : Summable f) :
    ∑' n : ℕ, f n = f 0 + f 1 + ∑' n : ℕ, f (n + 2) := by
  rw [← hf.sum_add_tsum_nat_add 2]
  norm_num [Finset.sum_range_succ]

/-- Certified rational bounds on the complete zeroth, second, and fourth
Gaussian origin-jet series. -/
theorem xiOriginJetSeries_bounds :
    (∑' n : ℕ, xiKernelGaussianJet0 n 0) < (9 : ℝ) / 20 ∧
    (∑' n : ℕ, xiKernelGaussianJet2 n 0) < -(8333 : ℝ) / 1000 ∧
    (∑' n : ℕ, xiKernelGaussianJet4 n 0) < 410 := by
  have hlead := xiOriginLeadingModes_bounds
  have hsplit0 := tsum_eq_first_two_add_tail xiKernelGaussianJet0_summable_zero
  have hsplit2 := tsum_eq_first_two_add_tail xiKernelGaussianJet2_summable_zero
  have hsplit4 := tsum_eq_first_two_add_tail xiKernelGaussianJet4_summable_zero
  have htail0 : (∑' n : ℕ, xiKernelGaussianJet0 (n + 2) 0) < (1 : ℝ) / 90000 :=
    (le_abs_self _).trans_lt abs_tsum_xiKernelGaussianJet0_shifted_lt
  have htail2 : (∑' n : ℕ, xiKernelGaussianJet2 (n + 2) 0) < (1 : ℝ) / 1250 :=
    (le_abs_self _).trans_lt abs_tsum_xiKernelGaussianJet2_shifted_lt
  have htail4 : (∑' n : ℕ, xiKernelGaussianJet4 (n + 2) 0) < (1 : ℝ) / 20 :=
    (le_abs_self _).trans_lt abs_tsum_xiKernelGaussianJet4_shifted_lt
  constructor
  · rw [hsplit0]
    nlinarith
  constructor
  · rw [hsplit2]
    nlinarith
  · rw [hsplit4]
    nlinarith

theorem riemannXiKernel_zero_eq :
    riemannXiKernel 0 =
      4 * ∑' n : ℕ, xiKernelGaussianJet0 n 0 := by
  unfold riemannXiKernel
  congr 1
  apply tsum_congr
  intro n
  exact riemannXiKernelTerm_eq_gaussianJet0 n 0

theorem riemannXiKernel_deriv2_zero_eq :
    deriv^[2] riemannXiKernel 0 =
      4 * ∑' n : ℕ, xiKernelGaussianJet2 n 0 := by
  change deriv (deriv riemannXiKernel) 0 = _
  exact riemannXiKernel_deriv2_eq_gaussianJet2_local_zero
    (by constructor <;> norm_num)

/-- Derivative of the positive inner factor. -/
theorem xiKernelInner_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (xiKernelInner n)
      (2 * (2 * xiKernelQ n u)) u := by
  change HasDerivAt (fun y => 2 * xiKernelQ n y - 3)
    (2 * (2 * xiKernelQ n u)) u
  exact HasDerivAt.sub_const 3 ((xiKernelQ_hasDerivAt n u).const_mul 2)

/-- The derivative of the explicit log slope is exactly the explicit negative
curvature. -/
theorem xiKernelTermLogSlope_hasDerivAt (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (xiKernelTermLogSlope n) (xiKernelTermLogCurvature n u) u := by
  have hq := xiKernelQ_hasDerivAt n u
  have hinner : HasDerivAt (xiKernelInner n)
      (2 * (2 * xiKernelQ n u)) u := xiKernelInner_hasDerivAt n u
  have hinner_ne : xiKernelInner n u ≠ 0 :=
    ne_of_gt (xiKernelInner_pos n hu)
  have hquot := (hq.const_mul 4).div hinner hinner_ne
  have hslope :=
    ((hasDerivAt_const u (5 / 2 : ℝ)).add hquot).sub (hq.const_mul 2)
  have hder : xiKernelTermLogCurvature n u =
      0 +
        (4 * (2 * xiKernelQ n u) * xiKernelInner n u -
            4 * xiKernelQ n u * (2 * (2 * xiKernelQ n u))) /
          xiKernelInner n u ^ 2 -
        2 * (2 * xiKernelQ n u) := by
    simp only [xiKernelTermLogCurvature, xiKernelInner]
    field_simp [hinner_ne]
    ring
  rw [hder]
  exact hslope

/-- Every isolated summand has strictly negative explicit log curvature on the
physical half-line. -/
theorem xiKernelTermLogCurvature_neg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    xiKernelTermLogCurvature n u < 0 := by
  have hinner : 0 < xiKernelInner n u := xiKernelInner_pos n hu
  have hden : 0 < xiKernelInner n u ^ 2 := sq_pos_of_pos hinner
  have hq : 0 < xiKernelQ n u := by
    unfold xiKernelQ
    dsimp only
    positivity
  have hnum : 0 < 24 * xiKernelQ n u := by positivity
  have hneg : -24 * xiKernelQ n u < 0 := by nlinarith
  have hfirst :
      -24 * xiKernelQ n u / xiKernelInner n u ^ 2 < 0 :=
    div_neg_of_neg_of_pos hneg hden
  have hsecond : 0 < 4 * xiKernelQ n u := by positivity
  unfold xiKernelTermLogCurvature
  nlinarith

/-- Direct chain-rule form of the logarithmic derivative of one positive
kernel summand. -/
theorem riemannXiKernelTerm_log_hasDerivAt_deriv
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun v => Real.log (riemannXiKernelTerm n v))
      (deriv (riemannXiKernelTerm n) u / riemannXiKernelTerm n u) u := by
  apply HasDerivAt.log
  · exact (show DifferentiableAt ℝ (riemannXiKernelTerm n) u by
      unfold riemannXiKernelTerm
      dsimp only
      fun_prop).hasDerivAt
  · exact ne_of_gt (riemannXiKernelTerm_pos n hu)

/-- Derivative of the elementary factor `exp (5u/2)`. -/
theorem xiExpFiveHalves_hasDerivAt (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (5 * v / 2))
      ((5 / 2) * Real.exp (5 * u / 2)) u := by
  have h := ((hasDerivAt_id u).const_mul (5 / 2 : ℝ)).exp
  have heq : (fun v : ℝ => Real.exp (5 * v / 2)) =ᶠ[nhds u]
      (fun v : ℝ => Real.exp ((5 / 2 : ℝ) * id v)) := by
    filter_upwards [] with v
    simp only [id_eq]
    congr 1
    ring
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  simp only [id_eq]
  ring

/-- Product-rule form of the derivative of one kernel summand. -/
theorem riemannXiKernelTerm_hasDerivAt_logSlope_mul
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (riemannXiKernelTerm n)
      (xiKernelTermLogSlope n u * riemannXiKernelTerm n u) u := by
  let r : ℝ := n + 1
  let c : ℝ := Real.pi * r ^ 2
  have hq := xiKernelQ_hasDerivAt n u
  have hinner := xiKernelInner_hasDerivAt n u
  have hexpFive := xiExpFiveHalves_hasDerivAt u
  have hexpNegQ := hq.neg.exp
  have hfactor :=
    ((((hasDerivAt_const u c).mul hexpFive).mul hinner).mul hexpNegQ)
  have heq : riemannXiKernelTerm n =ᶠ[nhds u]
      (fun v : ℝ =>
        c * Real.exp (5 * v / 2) * xiKernelInner n v *
          Real.exp (-xiKernelQ n v)) := by
    filter_upwards [] with v
    simpa only [c, r] using riemannXiKernelTerm_factorized n v
  have hterm := hfactor.congr_of_eventuallyEq heq
  apply hterm.congr_deriv
  rw [heq.eq_of_nhds]
  simp only [xiKernelTermLogSlope, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
    Pi.mul_apply, Pi.neg_apply]
  have hinner_ne : xiKernelInner n u ≠ 0 :=
    ne_of_gt (xiKernelInner_pos n hu)
  field_simp [hinner_ne]
  ring

/-- The literal logarithmic derivative of one kernel summand is its explicit
log slope. -/
theorem riemannXiKernelTerm_log_hasDerivAt
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun v => Real.log (riemannXiKernelTerm n v))
      (xiKernelTermLogSlope n u) u := by
  have hne : riemannXiKernelTerm n u ≠ 0 :=
    ne_of_gt (riemannXiKernelTerm_pos n hu)
  have hlog := (riemannXiKernelTerm_hasDerivAt_logSlope_mul n hu).log hne
  apply hlog.congr_deriv
  field_simp [hne]

/-- The explicit logarithmic slope of each isolated kernel summand is strictly
decreasing on the physical half-line. -/
theorem xiKernelTermLogSlope_strictAntiOn (n : ℕ) :
    StrictAntiOn (xiKernelTermLogSlope n) (Set.Ici (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro u hu
    exact (xiKernelTermLogSlope_hasDerivAt n hu).continuousAt.continuousWithinAt
  · intro u hu
    have hu0 : 0 < u := by simpa using hu
    have hd := xiKernelTermLogSlope_hasDerivAt n hu0.le
    rw [hd.deriv]
    exact xiKernelTermLogCurvature_neg n hu0.le

/-- Each isolated theta-kernel summand is strictly log-concave on the physical
half-line.  This is the exact Phase-A wrapper around the explicit decreasing
logarithmic slope. -/
theorem riemannXiKernelTerm_log_strictConcaveOn (n : ℕ) :
    StrictConcaveOn ℝ (Set.Ici (0 : ℝ))
      (fun u => Real.log (riemannXiKernelTerm n u)) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
  · intro u hu
    have hu0 : 0 ≤ u := hu
    exact (riemannXiKernelTerm_log_hasDerivAt n hu0).continuousAt.continuousWithinAt
  · intro u hu v hv huv
    have hu0 : 0 ≤ u := le_of_lt (by simpa using hu)
    have hv0 : 0 ≤ v := le_of_lt (by simpa using hv)
    rw [(riemannXiKernelTerm_log_hasDerivAt n hu0).deriv,
      (riemannXiKernelTerm_log_hasDerivAt n hv0).deriv]
    exact xiKernelTermLogSlope_strictAntiOn n hu0 hv0 huv

/-- The defining theta series is absolutely summable at every real argument. -/
theorem riemannXiKernelTerm_summable (u : ℝ) :
    Summable (fun n : ℕ => riemannXiKernelTerm n u) := by
  let c : ℝ := Real.pi * Real.exp (2 * u)
  let A : ℝ :=
    2 * Real.pi ^ 2 * Real.exp (9 * u / 2) +
      3 * Real.pi * Real.exp (5 * u / 2)
  have hc : 0 < c := mul_pos Real.pi_pos (Real.exp_pos _)
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-c * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 4 hc
  have hshift : Summable
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-c * (n + 1 : ℕ))) := by
    exact (summable_nat_add_iff 1).2 hbase
  apply (hshift.mul_left A).of_norm_bounded
  intro n
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hr2 : r ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hr24 : r ^ 2 ≤ r ^ 4 := by nlinarith [sq_nonneg (r ^ 2 - 1)]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : Real.exp (-c * r ^ 2) ≤ Real.exp (-c * r) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hr2 (neg_nonpos.mpr hc.le)
  have hnonneg :
      0 ≤ (2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) +
        3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)) := by positivity
  have hcoeff :
      2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) +
          3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) ≤ A * r ^ 4 := by
    have hb : 0 ≤ 3 * Real.pi * Real.exp (5 * u / 2) := by positivity
    have hsecond :
        3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) ≤
          (3 * Real.pi * Real.exp (5 * u / 2)) * r ^ 4 := by
      calc
        3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) =
            (3 * Real.pi * Real.exp (5 * u / 2)) * r ^ 2 := by ring
        _ ≤ (3 * Real.pi * Real.exp (5 * u / 2)) * r ^ 4 :=
          mul_le_mul_of_nonneg_left hr24 hb
    calc
      2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) +
          3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) ≤
        2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) +
          (3 * Real.pi * Real.exp (5 * u / 2)) * r ^ 4 := by
            exact add_le_add_right hsecond _
      _ = A * r ^ 4 := by dsimp [A]; ring
  unfold riemannXiKernelTerm
  dsimp only
  norm_num only [Nat.cast_add, Nat.cast_one]
  change
    ‖(2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) -
        3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u))‖ ≤
      A * (r ^ 4 * Real.exp (-c * r))
  rw [show -Real.pi * r ^ 2 * Real.exp (2 * u) = -c * r ^ 2 by
    dsimp [c]; ring]
  calc
    ‖(2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) -
          3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)) *
        Real.exp (-c * r ^ 2)‖
        ≤ (2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) +
            3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)) *
          Real.exp (-c * r ^ 2) := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            have haTerm :
                0 ≤ 2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) := by
              positivity
            have hbTerm :
                0 ≤ 3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) := by
              positivity
            have habs :
                |2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) -
                    3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)| ≤
                  2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) +
                    3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) := by
              calc
                |2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) -
                    3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)| ≤
                    |2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2)| +
                      |3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)| :=
                  abs_sub
                  (2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2))
                  (3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2))
                _ = 2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) +
                    3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) := by
                  rw [abs_of_nonneg haTerm, abs_of_nonneg hbTerm]
            exact mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ ≤ (A * r ^ 4) * Real.exp (-c * r ^ 2) := by
          exact mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
    _ ≤ (A * r ^ 4) * Real.exp (-c * r) := by
          exact mul_le_mul_of_nonneg_left he (mul_nonneg hA (pow_nonneg hr0 4))
    _ = A * (r ^ 4 * Real.exp (-c * r)) := by ring

/-- Each summand is continuous in the height variable. -/
theorem riemannXiKernelTerm_continuous (n : ℕ) :
    Continuous (riemannXiKernelTerm n) := by
  unfold riemannXiKernelTerm
  dsimp only
  fun_prop

/-- The actual summed Riemann kernel is measurable. -/
theorem riemannXiKernel_measurable : Measurable riemannXiKernel := by
  unfold riemannXiKernel
  exact measurable_const.mul
    (Measurable.tsum fun n => (riemannXiKernelTerm_continuous n).measurable)

/-- A summable coefficient for a uniform half-line exponential majorant. -/
def xiKernelMajorantCoeff (n : ℕ) : ℝ :=
  let r : ℝ := n + 1
  2 * Real.pi ^ 2 * r ^ 4 * Real.exp (-3 * r)

/-- The finite constant in the global Xi-kernel majorant. -/
def xiKernelMajorantConstant : ℝ :=
  4 * ∑' n : ℕ, xiKernelMajorantCoeff n

set_option maxHeartbeats 800000 in
/-- The coefficient sequence of the global majorant is summable. -/
theorem xiKernelMajorantCoeff_summable : Summable xiKernelMajorantCoeff := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-3 * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 4 (by norm_num)
  have hshift : Summable
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-3 * (n + 1 : ℕ))) :=
    (summable_nat_add_iff 1).2 hbase
  have heq : xiKernelMajorantCoeff = fun n : ℕ =>
      (2 * Real.pi ^ 2) *
        (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-3 * (n + 1 : ℕ))) := by
    funext n
    unfold xiKernelMajorantCoeff
    dsimp only
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  rw [heq]
  exact hshift.mul_left (2 * Real.pi ^ 2)

/-- Every theta summand is dominated on `u ≥ 0` by a separated summable
coefficient times `exp (-3u/2)`. -/
theorem riemannXiKernelTerm_le_majorant (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    riemannXiKernelTerm n u ≤
      xiKernelMajorantCoeff n * Real.exp (-3 * u / 2) := by
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hexp : 1 + 2 * u ≤ Real.exp (2 * u) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * u)
  have hscale : 3 * r ^ 2 * (1 + 2 * u) ≤
      Real.pi * r ^ 2 * Real.exp (2 * u) := by
    have hpi : 3 * r ^ 2 ≤ Real.pi * r ^ 2 :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg r)
    calc
      3 * r ^ 2 * (1 + 2 * u) ≤ Real.pi * r ^ 2 * (1 + 2 * u) := by
        exact mul_le_mul_of_nonneg_right hpi (by nlinarith)
      _ ≤ Real.pi * r ^ 2 * Real.exp (2 * u) := by
        exact mul_le_mul_of_nonneg_left hexp
          (mul_nonneg Real.pi_pos.le (sq_nonneg r))
  have hru : 3 * r + 6 * u ≤ 3 * r ^ 2 * (1 + 2 * u) := by
    nlinarith [mul_nonneg hu (le_trans zero_le_one hr2)]
  have hexponent :
      9 * u / 2 - Real.pi * r ^ 2 * Real.exp (2 * u) ≤
        -3 * r - 3 * u / 2 := by
    nlinarith [hru.trans hscale]
  have hpow :
      Real.exp (9 * u / 2 - Real.pi * r ^ 2 * Real.exp (2 * u)) ≤
        Real.exp (-3 * r - 3 * u / 2) :=
    Real.exp_le_exp.mpr hexponent
  have hdrop :
      riemannXiKernelTerm n u ≤
        2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) *
          Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u)) := by
    unfold riemannXiKernelTerm
    dsimp only
    exact mul_le_mul_of_nonneg_right
      (sub_le_self _ (by positivity)) (Real.exp_pos _).le
  calc
    riemannXiKernelTerm n u ≤
        2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) *
          Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u)) := hdrop
    _ = 2 * Real.pi ^ 2 * r ^ 4 *
        Real.exp (9 * u / 2 - Real.pi * r ^ 2 * Real.exp (2 * u)) := by
          rw [show
            2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) *
                Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u)) =
              2 * Real.pi ^ 2 * r ^ 4 *
                (Real.exp (9 * u / 2) *
                  Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u))) by ring]
          rw [← Real.exp_add]
          congr 2
          ring
    _ ≤ 2 * Real.pi ^ 2 * r ^ 4 * Real.exp (-3 * r - 3 * u / 2) := by
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = xiKernelMajorantCoeff n * Real.exp (-3 * u / 2) := by
          rw [show -3 * r - 3 * u / 2 = (-3 * r) + (-3 * u / 2) by ring]
          rw [Real.exp_add]
          unfold xiKernelMajorantCoeff
          dsimp only
          change
            2 * Real.pi ^ 2 * r ^ 4 *
                (Real.exp (-3 * r) * Real.exp (-3 * u / 2)) =
              (2 * Real.pi ^ 2 * r ^ 4 * Real.exp (-3 * r)) *
                Real.exp (-3 * u / 2)
          ring

/-- The separated majorant coefficient is nonnegative. -/
theorem xiKernelMajorantCoeff_nonneg (n : ℕ) :
    0 ≤ xiKernelMajorantCoeff n := by
  unfold xiKernelMajorantCoeff
  dsimp only
  positivity

/-- The global majorant constant is nonnegative. -/
theorem xiKernelMajorantConstant_nonneg : 0 ≤ xiKernelMajorantConstant := by
  unfold xiKernelMajorantConstant
  exact mul_nonneg (by norm_num) (tsum_nonneg xiKernelMajorantCoeff_nonneg)

/-- The actual summed Xi kernel has a global exponential majorant on the
positive half-line. -/
theorem riemannXiKernel_le_majorant {u : ℝ} (hu : 0 ≤ u) :
    riemannXiKernel u ≤
      xiKernelMajorantConstant * Real.exp (-3 * u / 2) := by
  have hsum :
      (∑' n : ℕ, riemannXiKernelTerm n u) ≤
        ∑' n : ℕ, xiKernelMajorantCoeff n * Real.exp (-3 * u / 2) :=
    Summable.tsum_le_tsum
      (fun n => riemannXiKernelTerm_le_majorant n hu)
      (riemannXiKernelTerm_summable u)
      (xiKernelMajorantCoeff_summable.mul_right _)
  rw [xiKernelMajorantCoeff_summable.tsum_mul_right] at hsum
  unfold riemannXiKernel xiKernelMajorantConstant
  calc
    4 * ∑' n : ℕ, riemannXiKernelTerm n u ≤
        4 * ((∑' n : ℕ, xiKernelMajorantCoeff n) *
          Real.exp (-3 * u / 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (4 * ∑' n : ℕ, xiKernelMajorantCoeff n) *
        Real.exp (-3 * u / 2) := by ring

/-- The M-test majorant also gives continuity of the summed Xi kernel on its
physical half-line. -/
theorem riemannXiKernel_continuousOn :
    ContinuousOn riemannXiKernel (Set.Ici (0 : ℝ)) := by
  unfold riemannXiKernel
  apply continuousOn_const.mul
  apply continuousOn_tsum
  · intro n
    exact (riemannXiKernelTerm_continuous n).continuousOn
  · exact xiKernelMajorantCoeff_summable
  · intro n u hu
    have hu0 : 0 ≤ u := hu
    rw [Real.norm_eq_abs, abs_of_pos (riemannXiKernelTerm_pos n hu0)]
    calc
      riemannXiKernelTerm n u ≤
          xiKernelMajorantCoeff n * Real.exp (-3 * u / 2) :=
        riemannXiKernelTerm_le_majorant n hu0
      _ ≤ xiKernelMajorantCoeff n * 1 := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith))
          (xiKernelMajorantCoeff_nonneg n)
      _ = xiKernelMajorantCoeff n := mul_one _

/-- Pointwise nonnegativity of the actual Riemann Xi kernel on `u ≥ 0`. -/
theorem riemannXiKernel_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ riemannXiKernel u := by
  unfold riemannXiKernel
  exact mul_nonneg (by norm_num)
    (tsum_nonneg fun n => (riemannXiKernelTerm_pos n hu).le)

/-- The summed Riemann kernel is strictly positive on the physical half-line. -/
theorem riemannXiKernel_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < riemannXiKernel u := by
  have hsum := riemannXiKernelTerm_summable u
  have htsum : 0 < ∑' n : ℕ, riemannXiKernelTerm n u :=
    hsum.tsum_pos (fun n => (riemannXiKernelTerm_pos n hu).le) 0
      (riemannXiKernelTerm_pos 0 hu)
  unfold riemannXiKernel
  positivity

/-! ## Phase B: term-by-term differentiation of the theta series -/

/-- Lower bound for the exponential coordinate on the physical half-line. -/
theorem xiKernelQ_ge (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.pi * ((n : ℝ) + 1) ^ 2 ≤ xiKernelQ n u := by
  unfold xiKernelQ
  dsimp only
  have her : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  exact le_mul_of_one_le_right (by positivity) her

/-- The exponential coordinate is at least three on the physical half-line. -/
theorem xiKernelQ_ge_three (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    3 ≤ xiKernelQ n u := by
  have h := xiKernelQ_ge n hu
  have hr : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  nlinarith [Real.pi_gt_three]

/-- The exponential coordinate is strictly positive. -/
theorem xiKernelQ_pos (n : ℕ) (u : ℝ) : 0 < xiKernelQ n u := by
  unfold xiKernelQ
  dsimp only
  positivity

/-- Half the exponential coordinate dominates the summand index. -/
theorem xiKernelQ_half_ge (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ((n : ℝ) + 1) ≤ xiKernelQ n u / 2 := by
  have h := xiKernelQ_ge n hu
  have hr : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  nlinarith [Real.pi_gt_three, sq_nonneg ((n : ℝ) + 1 - 1)]

/-- The inner affine factor is at least three on the physical half-line. -/
theorem xiKernelInner_ge_three (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    3 ≤ xiKernelInner n u := by
  have hq := xiKernelQ_ge_three n hu
  unfold xiKernelInner
  linarith

/-- Uniform linear bound for the explicit log slope of one kernel summand. -/
theorem xiKernelTermLogSlope_abs_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |xiKernelTermLogSlope n u| ≤ 5 * xiKernelQ n u := by
  have hq3 := xiKernelQ_ge_three n hu
  have hq0 := xiKernelQ_pos n u
  have hinner3 := xiKernelInner_ge_three n hu
  have hinner0 : 0 < xiKernelInner n u := by linarith
  have hslope_eq : xiKernelTermLogSlope n u =
      5 / 2 + 4 * xiKernelQ n u / xiKernelInner n u - 2 * xiKernelQ n u := by
    simp only [xiKernelTermLogSlope, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  have hdiv_le : 4 * xiKernelQ n u / xiKernelInner n u ≤ 4 * xiKernelQ n u / 3 := by
    gcongr
  have hdiv_nonneg : 0 ≤ 4 * xiKernelQ n u / xiKernelInner n u := by positivity
  rw [hslope_eq, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Uniform linear bound for the explicit log curvature of one kernel summand. -/
theorem xiKernelTermLogCurvature_abs_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |xiKernelTermLogCurvature n u| ≤ 7 * xiKernelQ n u := by
  have hq3 := xiKernelQ_ge_three n hu
  have hq0 := xiKernelQ_pos n u
  have hinner3 := xiKernelInner_ge_three n hu
  have hinner_sq : 9 ≤ xiKernelInner n u ^ 2 := by nlinarith
  have hdiv_le : 24 * xiKernelQ n u / xiKernelInner n u ^ 2 ≤
      24 * xiKernelQ n u / 9 := by
    gcongr
  have hdiv_nonneg : 0 ≤ 24 * xiKernelQ n u / xiKernelInner n u ^ 2 := by positivity
  have hkey : xiKernelTermLogCurvature n u =
      -(24 * xiKernelQ n u / xiKernelInner n u ^ 2) - 4 * xiKernelQ n u := by
    unfold xiKernelTermLogCurvature
    ring
  rw [hkey, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Each kernel summand is dominated by a pure power of its exponential
coordinate times the Gaussian factor. -/
theorem riemannXiKernelTerm_le_qcube (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    riemannXiKernelTerm n u ≤
      xiKernelQ n u ^ 3 * Real.exp (-xiKernelQ n u) := by
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr2 : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hq0 := xiKernelQ_pos n u
  have hpir : (3 : ℝ) ≤ Real.pi * r ^ 2 := by nlinarith [Real.pi_gt_three]
  have hinner_le : xiKernelInner n u ≤ 2 * xiKernelQ n u := by
    unfold xiKernelInner
    linarith
  have hinner0 : 0 ≤ xiKernelInner n u := by
    have := xiKernelInner_ge_three n hu
    linarith
  have hexp54 : Real.exp (5 * u / 2) ≤ Real.exp (4 * u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hqsq : Real.pi * r ^ 2 * Real.exp (4 * u) =
      xiKernelQ n u ^ 2 / (Real.pi * r ^ 2) := by
    have h4 : Real.exp (4 * u) = Real.exp (2 * u) * Real.exp (2 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold xiKernelQ
    dsimp only
    rw [h4]
    have hne : Real.pi * r ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hfrac : xiKernelQ n u ^ 2 / (Real.pi * r ^ 2) ≤ xiKernelQ n u ^ 2 / 3 := by
    gcongr
  have hfact := riemannXiKernelTerm_factorized n u
  calc
    riemannXiKernelTerm n u =
        Real.pi * r ^ 2 * Real.exp (5 * u / 2) * xiKernelInner n u *
          Real.exp (-xiKernelQ n u) := by
      simpa only [r] using hfact
    _ ≤ Real.pi * r ^ 2 * Real.exp (4 * u) * (2 * xiKernelQ n u) *
          Real.exp (-xiKernelQ n u) := by
      have h1 : Real.pi * r ^ 2 * Real.exp (5 * u / 2) ≤
          Real.pi * r ^ 2 * Real.exp (4 * u) :=
        mul_le_mul_of_nonneg_left hexp54 (by positivity)
      have h2 : Real.pi * r ^ 2 * Real.exp (5 * u / 2) * xiKernelInner n u ≤
          Real.pi * r ^ 2 * Real.exp (4 * u) * (2 * xiKernelQ n u) := by
        apply mul_le_mul h1 hinner_le hinner0 (by positivity)
      exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = xiKernelQ n u ^ 2 / (Real.pi * r ^ 2) * (2 * xiKernelQ n u) *
          Real.exp (-xiKernelQ n u) := by rw [hqsq]
    _ ≤ xiKernelQ n u ^ 2 / 3 * (2 * xiKernelQ n u) *
          Real.exp (-xiKernelQ n u) := by
      have := mul_le_mul_of_nonneg_right hfrac (by positivity : (0:ℝ) ≤ 2 * xiKernelQ n u)
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ ≤ xiKernelQ n u ^ 3 * Real.exp (-xiKernelQ n u) := by
      have hcube : xiKernelQ n u ^ 2 / 3 * (2 * xiKernelQ n u) ≤ xiKernelQ n u ^ 3 := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hcube (Real.exp_pos _).le

/-- Polynomial-times-Gaussian tails: `x ^ m · e^{-x} ≤ 2^m m! e^{-x/2}` on the
nonnegative half-line. -/
theorem pow_mul_exp_neg_le_exp_neg_half (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m * Real.exp (-x) ≤
      2 ^ m * (m.factorial : ℝ) * Real.exp (-x / 2) := by
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have h := Real.pow_div_factorial_le_exp (x / 2) (by positivity) m
  have hhalf : (x / 2) ^ m ≤ (m.factorial : ℝ) * Real.exp (x / 2) := by
    have := mul_le_mul_of_nonneg_right h hfac.le
    calc
      (x / 2) ^ m = (x / 2) ^ m / (m.factorial : ℝ) * (m.factorial : ℝ) := by
        field_simp
      _ ≤ Real.exp (x / 2) * (m.factorial : ℝ) := this
      _ = (m.factorial : ℝ) * Real.exp (x / 2) := by ring
  have hxm : x ^ m ≤ 2 ^ m * (m.factorial : ℝ) * Real.exp (x / 2) := by
    have hx2 : x ^ m = 2 ^ m * (x / 2) ^ m := by
      rw [div_pow]
      field_simp
    rw [hx2]
    calc
      2 ^ m * (x / 2) ^ m ≤ 2 ^ m * ((m.factorial : ℝ) * Real.exp (x / 2)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = 2 ^ m * (m.factorial : ℝ) * Real.exp (x / 2) := by ring
  calc
    x ^ m * Real.exp (-x) ≤
        2 ^ m * (m.factorial : ℝ) * Real.exp (x / 2) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hxm (Real.exp_pos _).le
    _ = 2 ^ m * (m.factorial : ℝ) * (Real.exp (x / 2) * Real.exp (-x)) := by
      ring
    _ = 2 ^ m * (m.factorial : ℝ) * Real.exp (-x / 2) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Uniform half-line bound: any fixed power of the exponential coordinate
times one kernel summand is dominated by a summable index coefficient. -/
theorem xiKernelQ_pow_mul_term_le (m n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
      2 ^ (3 + m) * ((3 + m).factorial : ℝ) * Real.exp (-((n : ℝ) + 1)) := by
  have hq0 := xiKernelQ_pos n u
  have hterm := riemannXiKernelTerm_le_qcube n hu
  have h1 : xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
      xiKernelQ n u ^ (3 + m) * Real.exp (-xiKernelQ n u) := by
    calc
      xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
          xiKernelQ n u ^ m *
            (xiKernelQ n u ^ 3 * Real.exp (-xiKernelQ n u)) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = xiKernelQ n u ^ (3 + m) * Real.exp (-xiKernelQ n u) := by
        rw [pow_add]
        ring
  have h2 := pow_mul_exp_neg_le_exp_neg_half (3 + m) hq0.le
  have h3 : Real.exp (-xiKernelQ n u / 2) ≤ Real.exp (-((n : ℝ) + 1)) := by
    apply Real.exp_le_exp.mpr
    have := xiKernelQ_half_ge n hu
    linarith
  calc
    xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
        xiKernelQ n u ^ (3 + m) * Real.exp (-xiKernelQ n u) := h1
    _ ≤ 2 ^ (3 + m) * ((3 + m).factorial : ℝ) *
          Real.exp (-xiKernelQ n u / 2) := h2
    _ ≤ 2 ^ (3 + m) * ((3 + m).factorial : ℝ) *
          Real.exp (-((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Summable uniform majorant coefficients for the kernel summands and their
first two height derivatives. -/
def xiKernelDerivMajorantCoeff (j n : ℕ) : ℝ :=
  32 ^ j * 2 ^ (3 + j) * ((3 + j).factorial : ℝ) * Real.exp (-((n : ℝ) + 1))

/-- The derivative-majorant coefficients are nonnegative. -/
theorem xiKernelDerivMajorantCoeff_nonneg (j n : ℕ) :
    0 ≤ xiKernelDerivMajorantCoeff j n := by
  unfold xiKernelDerivMajorantCoeff
  positivity

/-- Each derivative-majorant coefficient sequence is summable. -/
theorem xiKernelDerivMajorantCoeff_summable (j : ℕ) :
    Summable (xiKernelDerivMajorantCoeff j) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 0 * Real.exp (-1 * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 0 one_pos
  have heq : xiKernelDerivMajorantCoeff j = fun n : ℕ =>
      (32 ^ j * 2 ^ (3 + j) * ((3 + j).factorial : ℝ) * Real.exp (-1)) *
        ((n : ℝ) ^ 0 * Real.exp (-1 * n)) := by
    funext n
    unfold xiKernelDerivMajorantCoeff
    have hsplit : Real.exp (-((n : ℝ) + 1)) =
        Real.exp (-1) * Real.exp (-1 * n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, pow_zero, one_mul]
    ring
  rw [heq]
  exact hbase.mul_left _

/-- Closed form of the first height derivative of one kernel summand. -/
def xiKernelTermDeriv (n : ℕ) (u : ℝ) : ℝ :=
  xiKernelTermLogSlope n u * riemannXiKernelTerm n u

/-- Closed form of the second height derivative of one kernel summand. -/
def xiKernelTermDeriv2 (n : ℕ) (u : ℝ) : ℝ :=
  (xiKernelTermLogCurvature n u + xiKernelTermLogSlope n u ^ 2) *
    riemannXiKernelTerm n u

/-- The closed-form first derivative really is the derivative of one summand. -/
theorem xiKernelTermDeriv_hasDerivAt (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (riemannXiKernelTerm n) (xiKernelTermDeriv n u) u := by
  have h := riemannXiKernelTerm_hasDerivAt_logSlope_mul n hu
  apply h.congr_deriv
  rfl

/-- The closed-form second derivative really is the derivative of the
closed-form first derivative of one summand. -/
theorem xiKernelTermDeriv2_hasDerivAt (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (xiKernelTermDeriv n) (xiKernelTermDeriv2 n u) u := by
  have hslope := xiKernelTermLogSlope_hasDerivAt n hu
  have hterm := riemannXiKernelTerm_hasDerivAt_logSlope_mul n hu
  have h := hslope.mul hterm
  have hder : xiKernelTermDeriv2 n u =
      xiKernelTermLogCurvature n u * riemannXiKernelTerm n u +
        xiKernelTermLogSlope n u *
          (xiKernelTermLogSlope n u * riemannXiKernelTerm n u) := by
    unfold xiKernelTermDeriv2
    ring
  rw [show xiKernelTermDeriv n = fun y =>
      xiKernelTermLogSlope n y * riemannXiKernelTerm n y from rfl]
  rw [hder]
  exact h

/-- Uniform summable bound for the first derivative of one kernel summand on
the physical half-line. -/
theorem xiKernelTermDeriv_norm_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ‖xiKernelTermDeriv n u‖ ≤ xiKernelDerivMajorantCoeff 1 n := by
  have hterm_pos := riemannXiKernelTerm_pos n hu
  have hslope := xiKernelTermLogSlope_abs_le n hu
  have hq1 := xiKernelQ_pow_mul_term_le 1 n hu
  have h : ‖xiKernelTermDeriv n u‖ ≤
      5 * (xiKernelQ n u ^ 1 * riemannXiKernelTerm n u) := by
    unfold xiKernelTermDeriv
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hterm_pos]
    calc
      |xiKernelTermLogSlope n u| * riemannXiKernelTerm n u ≤
          5 * xiKernelQ n u * riemannXiKernelTerm n u :=
        mul_le_mul_of_nonneg_right hslope hterm_pos.le
      _ = 5 * (xiKernelQ n u ^ 1 * riemannXiKernelTerm n u) := by
        rw [pow_one]
        ring
  calc
    ‖xiKernelTermDeriv n u‖ ≤
        5 * (xiKernelQ n u ^ 1 * riemannXiKernelTerm n u) := h
    _ ≤ 5 * (2 ^ (3 + 1) * ((3 + 1).factorial : ℝ) *
          Real.exp (-((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hq1 (by norm_num)
    _ = 5 * (2 ^ (3 + 1) * ((3 + 1).factorial : ℝ)) *
          Real.exp (-((n : ℝ) + 1)) := by ring
    _ ≤ 32 ^ 1 * 2 ^ (3 + 1) * ((3 + 1).factorial : ℝ) *
          Real.exp (-((n : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      norm_num [Nat.factorial]
    _ = xiKernelDerivMajorantCoeff 1 n := rfl

/-- Uniform summable bound for the second derivative of one kernel summand on
the physical half-line. -/
theorem xiKernelTermDeriv2_norm_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ‖xiKernelTermDeriv2 n u‖ ≤ xiKernelDerivMajorantCoeff 2 n := by
  have hterm_pos := riemannXiKernelTerm_pos n hu
  have hslope := xiKernelTermLogSlope_abs_le n hu
  have hcurv := xiKernelTermLogCurvature_abs_le n hu
  have hq3 := xiKernelQ_ge_three n hu
  have hq0 := xiKernelQ_pos n u
  have hq2 := xiKernelQ_pow_mul_term_le 2 n hu
  have hfactor : |xiKernelTermLogCurvature n u + xiKernelTermLogSlope n u ^ 2| ≤
      32 * xiKernelQ n u ^ 2 := by
    have hsq : xiKernelTermLogSlope n u ^ 2 ≤ (5 * xiKernelQ n u) ^ 2 := by
      have := sq_le_sq' (neg_le_of_abs_le hslope) (le_of_abs_le hslope)
      simpa using this
    calc
      |xiKernelTermLogCurvature n u + xiKernelTermLogSlope n u ^ 2| ≤
          |xiKernelTermLogCurvature n u| + xiKernelTermLogSlope n u ^ 2 := by
        have := abs_add_le (xiKernelTermLogCurvature n u)
          (xiKernelTermLogSlope n u ^ 2)
        simpa [abs_of_nonneg (sq_nonneg (xiKernelTermLogSlope n u))] using this
      _ ≤ 7 * xiKernelQ n u + 25 * xiKernelQ n u ^ 2 := by nlinarith
      _ ≤ 32 * xiKernelQ n u ^ 2 := by nlinarith
  have h : ‖xiKernelTermDeriv2 n u‖ ≤
      32 * (xiKernelQ n u ^ 2 * riemannXiKernelTerm n u) := by
    unfold xiKernelTermDeriv2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hterm_pos]
    calc
      |xiKernelTermLogCurvature n u + xiKernelTermLogSlope n u ^ 2| *
          riemannXiKernelTerm n u ≤
          32 * xiKernelQ n u ^ 2 * riemannXiKernelTerm n u :=
        mul_le_mul_of_nonneg_right hfactor hterm_pos.le
      _ = 32 * (xiKernelQ n u ^ 2 * riemannXiKernelTerm n u) := by ring
  calc
    ‖xiKernelTermDeriv2 n u‖ ≤
        32 * (xiKernelQ n u ^ 2 * riemannXiKernelTerm n u) := h
    _ ≤ 32 * (2 ^ (3 + 2) * ((3 + 2).factorial : ℝ) *
          Real.exp (-((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hq2 (by norm_num)
    _ = 32 * (2 ^ (3 + 2) * ((3 + 2).factorial : ℝ)) *
          Real.exp (-((n : ℝ) + 1)) := by ring
    _ ≤ 32 ^ 2 * 2 ^ (3 + 2) * ((3 + 2).factorial : ℝ) *
          Real.exp (-((n : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      norm_num [Nat.factorial]
    _ = xiKernelDerivMajorantCoeff 2 n := rfl

/-- **Term-by-term differentiation of the theta series.**  The summed Riemann
kernel is differentiable at every point of the open half-line, and its
derivative is the sum of the closed-form summand derivatives. -/
theorem riemannXiKernel_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt riemannXiKernel (4 * ∑' n, xiKernelTermDeriv n u) u := by
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (xiKernelDerivMajorantCoeff_summable 1) isOpen_Ioi isPreconnected_Ioi
    (fun n y hy => xiKernelTermDeriv_hasDerivAt n (le_of_lt hy))
    (fun n y hy => xiKernelTermDeriv_norm_le n (le_of_lt hy))
    (Set.mem_Ioi.mpr one_pos) (riemannXiKernelTerm_summable 1)
    (Set.mem_Ioi.mpr hu)
  have h4 := hsum.const_mul (4 : ℝ)
  exact h4

/-- The differentiated theta series is itself differentiable term by term on
the open half-line. -/
theorem riemannXiKernelDerivSeries_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => 4 * ∑' n, xiKernelTermDeriv n v)
      (4 * ∑' n, xiKernelTermDeriv2 n u) u := by
  have hsummable1 : Summable (fun n => xiKernelTermDeriv n 1) :=
    Summable.of_norm_bounded (xiKernelDerivMajorantCoeff_summable 1)
      (fun n => xiKernelTermDeriv_norm_le n (by norm_num))
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (xiKernelDerivMajorantCoeff_summable 2) isOpen_Ioi isPreconnected_Ioi
    (fun n y hy => xiKernelTermDeriv2_hasDerivAt n (le_of_lt hy))
    (fun n y hy => xiKernelTermDeriv2_norm_le n (le_of_lt hy))
    (Set.mem_Ioi.mpr one_pos) hsummable1 (Set.mem_Ioi.mpr hu)
  exact hsum.const_mul (4 : ℝ)

/-- First differentiated-series identity on the open half-line. -/
theorem riemannXiKernel_deriv_eq {u : ℝ} (hu : 0 < u) :
    deriv riemannXiKernel u = 4 * ∑' n, xiKernelTermDeriv n u :=
  (riemannXiKernel_hasDerivAt hu).deriv

/-- The literal `deriv` of the summed kernel is differentiable on the open
half-line, with term-by-term second derivative. -/
theorem riemannXiKernel_deriv_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (deriv riemannXiKernel)
      (4 * ∑' n, xiKernelTermDeriv2 n u) u := by
  have hev : deriv riemannXiKernel =ᶠ[nhds u]
      (fun v => 4 * ∑' n, xiKernelTermDeriv n v) := by
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hu)] with v hv
    exact riemannXiKernel_deriv_eq hv
  exact (riemannXiKernelDerivSeries_hasDerivAt hu).congr_of_eventuallyEq hev

/-- Second differentiated-series identity on the open half-line. -/
theorem riemannXiKernel_deriv2_eq {u : ℝ} (hu : 0 < u) :
    deriv (deriv riemannXiKernel) u = 4 * ∑' n, xiKernelTermDeriv2 n u :=
  (riemannXiKernel_deriv_hasDerivAt hu).deriv

/-! ## Phase C: the radial hazard and its exact derivative identity -/

/-- The exact scalar numerator controlling monotonicity of the radial hazard
of the summed Riemann kernel. -/
def xiRadialConcavityNumerator (u : ℝ) : ℝ :=
  u * (deriv riemannXiKernel u) ^ 2
    - u * riemannXiKernel u * deriv^[2] riemannXiKernel u
    + riemannXiKernel u * deriv riemannXiKernel u

/-- The radial concavity numerator has its forced origin zero. -/
theorem xiRadialConcavityNumerator_zero :
    xiRadialConcavityNumerator 0 = 0 := by
  unfold xiRadialConcavityNumerator
  rw [riemannXiKernel_deriv_zero]
  ring

/-- The numerator gate unfolded completely into the three absolutely
convergent differentiated theta series. -/
theorem xiRadialConcavityNumerator_series {u : ℝ} (hu : 0 < u) :
    xiRadialConcavityNumerator u =
      16 *
        (u * (∑' n : ℕ, xiKernelTermDeriv n u) ^ 2 -
          u * (∑' n : ℕ, riemannXiKernelTerm n u) *
            (∑' n : ℕ, xiKernelTermDeriv2 n u) +
          (∑' n : ℕ, riemannXiKernelTerm n u) *
            (∑' n : ℕ, xiKernelTermDeriv n u)) := by
  unfold xiRadialConcavityNumerator
  rw [show deriv^[2] riemannXiKernel u =
    deriv (deriv riemannXiKernel) u by rfl]
  rw [riemannXiKernel_deriv_eq hu, riemannXiKernel_deriv2_eq hu]
  unfold riemannXiKernel
  ring

/-! ## Phase D (opening): the single-term gate at the ground index -/

/-- The single-summand gate combination: log slope minus height times log
curvature.  The ground-index case is the dominant contribution to the scalar
concavity numerator. -/
def xiTermGate (n : ℕ) (u : ℝ) : ℝ :=
  xiKernelTermLogSlope n u - u * xiKernelTermLogCurvature n u

/-- The slope-square contribution of one theta summand. -/
def xiKernelTermSlopeSquareWeight (n : ℕ) (u : ℝ) : ℝ :=
  xiKernelTermLogSlope n u ^ 2 * riemannXiKernelTerm n u

/-- The log-curvature contribution of one theta summand. -/
def xiKernelTermCurvatureWeight (n : ℕ) (u : ℝ) : ℝ :=
  xiKernelTermLogCurvature n u * riemannXiKernelTerm n u

/-- The gate contribution of one theta summand. -/
def xiKernelTermGateWeight (n : ℕ) (u : ℝ) : ℝ :=
  xiTermGate n u * riemannXiKernelTerm n u

/-- On the far region `u ≥ 1/2` every summand's gate combination is positive:
the curvature reimbursement dominates termwise. -/
theorem xiTermGate_pos_of_half_le (n : ℕ) {u : ℝ} (hu : (1 : ℝ) / 2 ≤ u) :
    0 < xiTermGate n u := by
  have hu0 : (0 : ℝ) ≤ u := le_trans (by norm_num) hu
  have hq0 := xiKernelQ_pos n u
  have hI3 := xiKernelInner_ge_three n hu0
  have hI0 : (0 : ℝ) < xiKernelInner n u := by linarith
  have hslope_eq : xiKernelTermLogSlope n u =
      5 / 2 + 4 * xiKernelQ n u / xiKernelInner n u - 2 * xiKernelQ n u := by
    simp only [xiKernelTermLogSlope, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  have hcurv_eq : xiKernelTermLogCurvature n u =
      -(24 * xiKernelQ n u / xiKernelInner n u ^ 2) - 4 * xiKernelQ n u := by
    unfold xiKernelTermLogCurvature
    ring
  unfold xiTermGate
  rw [hslope_eq, hcurv_eq]
  have h1 : 0 ≤ 4 * xiKernelQ n u / xiKernelInner n u := by positivity
  have h2 : 0 ≤ 24 * xiKernelQ n u / xiKernelInner n u ^ 2 := by positivity
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u - 1 / 2) hq0.le,
    mul_nonneg hu0 h2]

/-- Padé upper bound for the exponential:
`e^x (2 - x) ≤ 2 + x` for `0 ≤ x`. -/
theorem exp_mul_two_sub_le {x : ℝ} (hx0 : 0 ≤ x) :
    Real.exp x * (2 - x) ≤ 2 + x := by
  have hmono : MonotoneOn (fun t : ℝ => (2 + t) - Real.exp t * (2 - t))
      (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have hderiv : HasDerivAt
          (fun t : ℝ => (2 + t) - Real.exp t * (2 - t))
          (1 - (Real.exp t * (2 - t) + Real.exp t * (-1))) t := by
        have h1 : HasDerivAt (fun t : ℝ => 2 + t) 1 t := by
          simpa using (hasDerivAt_id t).const_add (2 : ℝ)
        have h2sub : HasDerivAt (fun t : ℝ => 2 - t) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub (2 : ℝ)
        exact h1.sub ((Real.hasDerivAt_exp t).mul h2sub)
      rw [hderiv.deriv]
      have hexp : Real.exp t * (1 - t) ≤ 1 := by
        rcases le_total t 1 with h | h
        · have h1t : 1 - t ≤ Real.exp (-t) := by
            linarith [Real.add_one_le_exp (-t)]
          calc
            Real.exp t * (1 - t) ≤ Real.exp t * Real.exp (-t) :=
              mul_le_mul_of_nonneg_left h1t (Real.exp_pos t).le
            _ = 1 := by rw [← Real.exp_add]; simp
        · have hle : Real.exp t * (1 - t) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos t).le (by linarith)
          linarith
      nlinarith [hexp]
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx0) hx0
  dsimp only at h
  have h0 : ((2 : ℝ) + 0) - Real.exp 0 * (2 - 0) = 0 := by simp
  linarith

/-- Quadratic lower bound for the ground-index exponential coordinate. -/
theorem xiKernelQ_zero_lower {u : ℝ} (hu0 : 0 ≤ u) :
    Real.pi * (1 + 2 * u + 2 * u ^ 2) ≤ xiKernelQ 0 u := by
  have hq_eq : xiKernelQ 0 u = Real.pi * Real.exp (2 * u) := by
    unfold xiKernelQ
    norm_num
  have hsum := Real.sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * u) 3
  have hval : (∑ i ∈ Finset.range 3, (2 * u) ^ i / (i.factorial : ℝ)) =
      1 + 2 * u + 2 * u ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hval] at hsum
  rw [hq_eq]
  exact mul_le_mul_of_nonneg_left hsum Real.pi_pos.le

/-- Padé upper bound for the ground-index exponential coordinate on the
near region. -/
theorem xiKernelQ_zero_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    xiKernelQ 0 u * (2 - u) ^ 2 ≤ Real.pi * (2 + u) ^ 2 := by
  have hq_eq : xiKernelQ 0 u = Real.pi * Real.exp (2 * u) := by
    unfold xiKernelQ
    norm_num
  have hpos : (0 : ℝ) ≤ 2 - u := by linarith
  have habs : Real.exp u * (2 - u) ≤ 2 + u := exp_mul_two_sub_le hu0
  have hnn : 0 ≤ Real.exp u * (2 - u) :=
    mul_nonneg (Real.exp_pos u).le hpos
  have hexp2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : Real.exp (2 * u) * (2 - u) ^ 2 ≤ (2 + u) ^ 2 := by
    calc
      Real.exp (2 * u) * (2 - u) ^ 2 =
          (Real.exp u * (2 - u)) * (Real.exp u * (2 - u)) := by
        rw [hexp2]
        ring
      _ ≤ (2 + u) * (2 + u) := mul_le_mul habs habs hnn (by linarith)
      _ = (2 + u) ^ 2 := by ring
  rw [hq_eq]
  calc
    Real.pi * Real.exp (2 * u) * (2 - u) ^ 2 =
        Real.pi * (Real.exp (2 * u) * (2 - u) ^ 2) := by ring
    _ ≤ Real.pi * (2 + u) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq Real.pi_pos.le

/-- **The thin region of the ground-index gate**: positivity on `0 ≤ u ≤ 1/2`
by the two-sided exponential window and four-digit bounds for `π`. -/
theorem xiTermGate_zero_pos_of_le_half {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) : 0 < xiTermGate 0 u := by
  have hq0 := xiKernelQ_pos 0 u
  have hq3 := xiKernelQ_ge_three 0 hu0
  have hI3 := xiKernelInner_ge_three 0 hu0
  have hI0 : (0 : ℝ) < xiKernelInner 0 u := by linarith
  have hIdef : xiKernelInner 0 u = 2 * xiKernelQ 0 u - 3 := by
    unfold xiKernelInner
    rfl
  have hlow := xiKernelQ_zero_lower hu0
  have hup := xiKernelQ_zero_upper hu0 hu1
  have hpiL : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpiU : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hslope_eq : xiKernelTermLogSlope 0 u =
      5 / 2 + 4 * xiKernelQ 0 u / xiKernelInner 0 u - 2 * xiKernelQ 0 u := by
    simp only [xiKernelTermLogSlope, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  have hcurv_eq : xiKernelTermLogCurvature 0 u =
      -(24 * xiKernelQ 0 u / xiKernelInner 0 u ^ 2) - 4 * xiKernelQ 0 u := by
    unfold xiKernelTermLogCurvature
    ring
  set q := xiKernelQ 0 u with hqdef
  have hlow' : (3.1415 : ℝ) * (1 + 2 * u + 2 * u ^ 2) ≤ q := by
    nlinarith [hlow, hpiL, sq_nonneg u]
  have hup' : q * (2 - u) ^ 2 ≤ (3.1416 : ℝ) * (2 + u) ^ 2 := by
    nlinarith [hup, hpiU, sq_nonneg (2 + u)]
  have hP : 0 < 5 / 2 * (2 * q - 3) ^ 2 + 4 * q * (2 * q - 3) + 24 * u * q +
      (4 * u - 2) * q * (2 * q - 3) ^ 2 := by
    nlinarith [hlow', hup', hu0, hu1, hq3, mul_nonneg hu0 hq0.le,
      sq_nonneg (u - 1 / 8), mul_nonneg (mul_nonneg hu0 hu0) hq0.le,
      mul_nonneg hu0 (sq_nonneg (2 * q - 3)), mul_pos hq0 hq0,
      sq_nonneg (q - 3.3), sq_nonneg (q - 4.1)]
  unfold xiTermGate
  rw [hslope_eq, hcurv_eq]
  have hgate_eq : 5 / 2 + 4 * q / xiKernelInner 0 u - 2 * q -
      u * (-(24 * q / xiKernelInner 0 u ^ 2) - 4 * q) =
      (5 / 2 * (2 * q - 3) ^ 2 + 4 * q * (2 * q - 3) + 24 * u * q +
        (4 * u - 2) * q * (2 * q - 3) ^ 2) / (2 * q - 3) ^ 2 := by
    rw [hIdef]
    have hne : (2 * q - 3) ≠ 0 := by
      rw [← hIdef]
      exact ne_of_gt hI0
    field_simp
    ring
  rw [hgate_eq]
  apply div_pos hP
  have : (0 : ℝ) < 2 * q - 3 := by
    rw [← hIdef]
    exact hI0
  positivity

/-- **The ground-index gate is positive on the whole physical half-line.** -/
theorem xiTermGate_zero_pos {u : ℝ} (hu0 : 0 ≤ u) : 0 < xiTermGate 0 u := by
  rcases le_total u (1 / 2) with h | h
  · exact xiTermGate_zero_pos_of_le_half hu0 h
  · exact xiTermGate_pos_of_half_le 0 h

/-- The slope-square weights are absolutely summable at every physical
height. -/
theorem xiKernelTermSlopeSquareWeight_summable {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun n : ℕ => xiKernelTermSlopeSquareWeight n u) := by
  apply Summable.of_norm_bounded (xiKernelDerivMajorantCoeff_summable 2)
  intro n
  have hterm := riemannXiKernelTerm_pos n hu
  have hslope := xiKernelTermLogSlope_abs_le n hu
  have hsq : xiKernelTermLogSlope n u ^ 2 ≤ (5 * xiKernelQ n u) ^ 2 := by
    exact sq_le_sq' (neg_le_of_abs_le hslope) (le_of_abs_le hslope)
  have hq2 := xiKernelQ_pow_mul_term_le 2 n hu
  unfold xiKernelTermSlopeSquareWeight
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos hterm]
  calc
    xiKernelTermLogSlope n u ^ 2 * riemannXiKernelTerm n u ≤
        (5 * xiKernelQ n u) ^ 2 * riemannXiKernelTerm n u :=
      mul_le_mul_of_nonneg_right hsq hterm.le
    _ = 25 * (xiKernelQ n u ^ 2 * riemannXiKernelTerm n u) := by ring
    _ ≤ 25 * (2 ^ (3 + 2) * ((3 + 2).factorial : ℝ) *
        Real.exp (-((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hq2 (by norm_num)
    _ ≤ 32 ^ 2 * 2 ^ (3 + 2) * ((3 + 2).factorial : ℝ) *
        Real.exp (-((n : ℝ) + 1)) := by
      have he : 0 ≤ Real.exp (-((n : ℝ) + 1)) := (Real.exp_pos _).le
      nlinarith [he]
    _ = xiKernelDerivMajorantCoeff 2 n := rfl

/-- The curvature weights are absolutely summable at every physical height. -/
theorem xiKernelTermCurvatureWeight_summable {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun n : ℕ => xiKernelTermCurvatureWeight n u) := by
  apply Summable.of_norm_bounded (xiKernelDerivMajorantCoeff_summable 2)
  intro n
  have hterm := riemannXiKernelTerm_pos n hu
  have hcurv := xiKernelTermLogCurvature_abs_le n hu
  have hq3 := xiKernelQ_ge_three n hu
  have hq0 := xiKernelQ_pos n u
  have hqle : xiKernelQ n u ≤ xiKernelQ n u ^ 2 := by nlinarith
  have hq2 := xiKernelQ_pow_mul_term_le 2 n hu
  unfold xiKernelTermCurvatureWeight
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hterm]
  calc
    |xiKernelTermLogCurvature n u| * riemannXiKernelTerm n u ≤
        (7 * xiKernelQ n u) * riemannXiKernelTerm n u :=
      mul_le_mul_of_nonneg_right hcurv hterm.le
    _ ≤ 7 * (xiKernelQ n u ^ 2 * riemannXiKernelTerm n u) := by
      nlinarith
    _ ≤ 7 * (2 ^ (3 + 2) * ((3 + 2).factorial : ℝ) *
        Real.exp (-((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hq2 (by norm_num)
    _ ≤ 32 ^ 2 * 2 ^ (3 + 2) * ((3 + 2).factorial : ℝ) *
        Real.exp (-((n : ℝ) + 1)) := by
      have he : 0 ≤ Real.exp (-((n : ℝ) + 1)) := (Real.exp_pos _).le
      nlinarith [he]
    _ = xiKernelDerivMajorantCoeff 2 n := rfl

/-- The gate weights are absolutely summable at every physical height. -/
theorem xiKernelTermGateWeight_summable {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun n : ℕ => xiKernelTermGateWeight n u) := by
  have hderiv : Summable (fun n : ℕ => xiKernelTermDeriv n u) :=
    Summable.of_norm_bounded (xiKernelDerivMajorantCoeff_summable 1)
      (fun n => xiKernelTermDeriv_norm_le n hu)
  have hcurv := xiKernelTermCurvatureWeight_summable hu
  have heq : (fun n : ℕ => xiKernelTermGateWeight n u) =
      fun n => xiKernelTermDeriv n u - u * xiKernelTermCurvatureWeight n u := by
    funext n
    unfold xiKernelTermGateWeight xiTermGate xiKernelTermDeriv
      xiKernelTermCurvatureWeight
    ring
  rw [heq]
  exact hderiv.sub (hcurv.mul_left u)

/-- The differentiated summand splits into curvature and slope-square
weights. -/
theorem xiKernelTermDeriv2_eq_curvature_add_slopeSquare (n : ℕ) (u : ℝ) :
    xiKernelTermDeriv2 n u = xiKernelTermCurvatureWeight n u +
      xiKernelTermSlopeSquareWeight n u := by
  unfold xiKernelTermDeriv2 xiKernelTermCurvatureWeight
    xiKernelTermSlopeSquareWeight
  ring

/-- Tsum form of the second-derivative split. -/
theorem tsum_xiKernelTermDeriv2_eq_curvature_add_slopeSquare
    {u : ℝ} (hu : 0 ≤ u) :
    (∑' n : ℕ, xiKernelTermDeriv2 n u) =
      (∑' n : ℕ, xiKernelTermCurvatureWeight n u) +
        ∑' n : ℕ, xiKernelTermSlopeSquareWeight n u := by
  have hcurv := xiKernelTermCurvatureWeight_summable hu
  have hsq := xiKernelTermSlopeSquareWeight_summable hu
  calc
    (∑' n : ℕ, xiKernelTermDeriv2 n u) =
        ∑' n : ℕ, (xiKernelTermCurvatureWeight n u +
          xiKernelTermSlopeSquareWeight n u) := by
      apply tsum_congr
      intro n
      exact xiKernelTermDeriv2_eq_curvature_add_slopeSquare n u
    _ = _ := Summable.tsum_add hcurv hsq

/-- Tsum form of the gate-weight split. -/
theorem tsum_xiKernelTermGateWeight_eq {u : ℝ} (hu : 0 ≤ u) :
    (∑' n : ℕ, xiKernelTermGateWeight n u) =
      (∑' n : ℕ, xiKernelTermDeriv n u) -
        u * ∑' n : ℕ, xiKernelTermCurvatureWeight n u := by
  have hderiv : Summable (fun n : ℕ => xiKernelTermDeriv n u) :=
    Summable.of_norm_bounded (xiKernelDerivMajorantCoeff_summable 1)
      (fun n => xiKernelTermDeriv_norm_le n hu)
  have hcurv := xiKernelTermCurvatureWeight_summable hu
  calc
    (∑' n : ℕ, xiKernelTermGateWeight n u) =
        ∑' n : ℕ, (xiKernelTermDeriv n u -
          u * xiKernelTermCurvatureWeight n u) := by
      apply tsum_congr
      intro n
      unfold xiKernelTermGateWeight xiTermGate xiKernelTermDeriv
        xiKernelTermCurvatureWeight
      ring
    _ = (∑' n : ℕ, xiKernelTermDeriv n u) -
        ∑' n : ℕ, u * xiKernelTermCurvatureWeight n u :=
      Summable.tsum_sub hderiv (hcurv.mul_left u)
    _ = _ := by rw [tsum_mul_left]

/-- **Gate-minus-variance decomposition of the full radial numerator.** -/
theorem xiRadialConcavityNumerator_gate_variance {u : ℝ} (hu : 0 < u) :
    xiRadialConcavityNumerator u =
      16 *
        ((∑' n : ℕ, riemannXiKernelTerm n u) *
            (∑' n : ℕ, xiKernelTermGateWeight n u) -
          u *
            ((∑' n : ℕ, riemannXiKernelTerm n u) *
                (∑' n : ℕ, xiKernelTermSlopeSquareWeight n u) -
              (∑' n : ℕ, xiKernelTermDeriv n u) ^ 2)) := by
  rw [xiRadialConcavityNumerator_series hu,
    tsum_xiKernelTermDeriv2_eq_curvature_add_slopeSquare hu.le,
    tsum_xiKernelTermGateWeight_eq hu.le]
  ring

/-- The slope-variance defect in the gate decomposition is nonnegative. -/
theorem xiSlopeVarianceDefect_nonneg {u : ℝ} (hu : 0 ≤ u) :
    (∑' n : ℕ, xiKernelTermDeriv n u) ^ 2 ≤
      (∑' n : ℕ, riemannXiKernelTerm n u) *
        ∑' n : ℕ, xiKernelTermSlopeSquareWeight n u := by
  have hterm : Summable (fun n : ℕ => riemannXiKernelTerm n u) :=
    riemannXiKernelTerm_summable u
  have hderiv : Summable (fun n : ℕ => xiKernelTermDeriv n u) :=
    Summable.of_norm_bounded (xiKernelDerivMajorantCoeff_summable 1)
      (fun n => xiKernelTermDeriv_norm_le n hu)
  have hsq := xiKernelTermSlopeSquareWeight_summable hu
  have hfinite : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, xiKernelTermDeriv n u) ^ 2 ≤
        (∑ n ∈ Finset.range N, riemannXiKernelTerm n u) *
          ∑ n ∈ Finset.range N, xiKernelTermSlopeSquareWeight n u := by
    intro N
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro n hn
      exact (riemannXiKernelTerm_pos n hu).le
    · intro n hn
      unfold xiKernelTermSlopeSquareWeight
      exact mul_nonneg (sq_nonneg _) (riemannXiKernelTerm_pos n hu).le
    · intro n hn
      unfold xiKernelTermDeriv xiKernelTermSlopeSquareWeight
      nlinarith [sq_nonneg (xiKernelTermLogSlope n u),
        (riemannXiKernelTerm_pos n hu).le]
  have hleft : Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, xiKernelTermDeriv n u) ^ 2)
      Filter.atTop (nhds ((∑' n : ℕ, xiKernelTermDeriv n u) ^ 2)) :=
    hderiv.hasSum.tendsto_sum_nat.pow 2
  have hright : Filter.Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N, riemannXiKernelTerm n u) *
          ∑ n ∈ Finset.range N, xiKernelTermSlopeSquareWeight n u)
      Filter.atTop
      (nhds ((∑' n : ℕ, riemannXiKernelTerm n u) *
        ∑' n : ℕ, xiKernelTermSlopeSquareWeight n u)) :=
    hterm.hasSum.tendsto_sum_nat.mul hsq.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall hfinite)

/-- The ground-index gate weight is strictly positive. -/
theorem xiKernelTermGateWeight_zero_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < xiKernelTermGateWeight 0 u := by
  unfold xiKernelTermGateWeight
  exact mul_pos (xiTermGate_zero_pos hu) (riemannXiKernelTerm_pos 0 hu)

/-- Exact ground-plus-tail split of the gate series. -/
theorem tsum_xiKernelTermGateWeight_eq_ground_add_tail {u : ℝ} (hu : 0 ≤ u) :
    (∑' n : ℕ, xiKernelTermGateWeight n u) =
      xiKernelTermGateWeight 0 u +
        ∑' n : ℕ, xiKernelTermGateWeight (n + 1) u := by
  exact (xiKernelTermGateWeight_summable hu).tsum_eq_zero_add

/-!
**Boundary degeneracy and the corrected route to the gate (2026-08-15).**

The gate is degenerate at the origin: the completed theta kernel is even in
the height (Jacobi modularity), so all odd derivatives of `riemannXiKernel`
vanish at `0` (verified numerically to 50 digits: `k₁, k₃, k₅ ≈ 1e-50`), the
gate series vanishes at `u = 0`, and the numerator vanishes to THIRD order:

  `N(u) = (k₂² - k₀·k₄/3)·u³ + O(u⁵)`,  `k_j := K^(j)(0)`.

Consequently no u-uniform constant bound on the gate-series tail can prove
the domination criterion below near `u = 0` — both sides vanish — and the
plan of record must be replaced by the following five steps:

* **(A) Evenness.**  `riemannXiKernel (-u) = riemannXiKernel u`, from the
  one-dimensional Jacobi/Poisson inversion compiled in
  `CarrierLatticePoisson.lean`; all odd-derivative vanishing at `0` follows.
* **(B) Cubic cornerstone.**  The explicit theta-constant inequality
  `3·k₂² > k₀·k₄`.  Measured: `k₀ = 1.78679`, `k₂ = -33.46100`,
  `k₄ = 1624.32567`, giving `k₂² - k₀k₄/3 = 152.197` — a 14% relative
  margin, provable by three-term partial sums with the compiled tail
  majorants and certified rational bounds on `exp (-π)`, `exp (-4π)`.
* **(C) Near-origin quantitative form.**  Extend the derivative majorants to
  orders 3 and 4 (the Phase B template extends verbatim), bound the Taylor
  remainders of `K, K', K''` on `[0, 1/4]`, and conclude
  `N(u) ≥ (a/2)·u³` on an explicit `[0, δ]` with `a = 152.19…`.
* **(D) Bulk region.**  The constant-bound tail domination of the previous
  plan is valid on `[δ, ∞)` (its constants `1920 + 26880u`, `96000` check
  out); combined with `xiTermGate_pos_of_half_le` the far region is already
  termwise clean.
* **(E) Glue.**  A–D give `xiRadialConcavityNumerator_pos`; the compiled
  criterion below and the Phase F–G chain then deliver the strict central
  Turán inequality and Theta–Wronskian levels one through five
  unconditionally.
-/

/-- Pointwise positivity of the radial numerator is exactly domination of the
weighted slope variance by the mass-times-gate term. -/
theorem xiRadialConcavityNumerator_pos_iff_gate_dominates_variance
    {u : ℝ} (hu : 0 < u) :
    0 < xiRadialConcavityNumerator u ↔
      u *
          ((∑' n : ℕ, riemannXiKernelTerm n u) *
              (∑' n : ℕ, xiKernelTermSlopeSquareWeight n u) -
            (∑' n : ℕ, xiKernelTermDeriv n u) ^ 2) <
        (∑' n : ℕ, riemannXiKernelTerm n u) *
          ∑' n : ℕ, xiKernelTermGateWeight n u := by
  rw [xiRadialConcavityNumerator_gate_variance hu]
  constructor <;> intro h <;> nlinarith

/-- The radial hazard of the summed Riemann kernel: the negative logarithmic
derivative read in the squared-height variable. -/
def xiRadialHazard (u : ℝ) : ℝ :=
  -deriv riemannXiKernel u / (2 * u * riemannXiKernel u)

/-- **Exact derivative identity for the radial hazard** on the open half-line:
the hazard's derivative is the scalar concavity numerator over the explicit
positive denominator. -/
theorem xiRadialHazard_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt xiRadialHazard
      (xiRadialConcavityNumerator u /
        (2 * u ^ 2 * riemannXiKernel u ^ 2)) u := by
  have hKpos := riemannXiKernel_pos hu.le
  have hK : HasDerivAt riemannXiKernel (deriv riemannXiKernel u) u := by
    rw [riemannXiKernel_deriv_eq hu]
    exact riemannXiKernel_hasDerivAt hu
  have hK2 : HasDerivAt (deriv riemannXiKernel)
      (deriv (deriv riemannXiKernel) u) u := by
    rw [riemannXiKernel_deriv2_eq hu]
    exact riemannXiKernel_deriv_hasDerivAt hu
  have hnum : HasDerivAt (fun v => -deriv riemannXiKernel v)
      (-(deriv (deriv riemannXiKernel) u)) u := hK2.neg
  have hid : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have hden : HasDerivAt (fun v => 2 * v * riemannXiKernel v)
      (2 * riemannXiKernel u + 2 * u * deriv riemannXiKernel u) u := by
    have h := hid.mul hK
    apply h.congr_deriv
    dsimp only
  have hden_ne : 2 * u * riemannXiKernel u ≠ 0 :=
    (mul_pos (mul_pos two_pos hu) hKpos).ne'
  have hdiv := hnum.div hden hden_ne
  have hune : u ≠ 0 := ne_of_gt hu
  have hKne : riemannXiKernel u ≠ 0 := ne_of_gt hKpos
  have hval : (-(deriv (deriv riemannXiKernel) u) * (2 * u * riemannXiKernel u) -
        -deriv riemannXiKernel u *
          (2 * riemannXiKernel u + 2 * u * deriv riemannXiKernel u)) /
        (2 * u * riemannXiKernel u) ^ 2 =
      xiRadialConcavityNumerator u / (2 * u ^ 2 * riemannXiKernel u ^ 2) := by
    have hiter : deriv^[2] riemannXiKernel = deriv (deriv riemannXiKernel) := rfl
    unfold xiRadialConcavityNumerator
    rw [hiter]
    field_simp [hune, hKne]
    ring
  rw [show xiRadialHazard = fun v =>
      -deriv riemannXiKernel v / (2 * v * riemannXiKernel v) from rfl]
  rw [← hval]
  exact hdiv

/-- Positivity of the scalar concavity numerator forces strict monotonicity of
the radial hazard on the open half-line: the single analytic gate of the
program, in interface form. -/
theorem xiRadialHazard_strictMonoOn_of_numerator_pos
    (hpos : ∀ u : ℝ, 0 < u → 0 < xiRadialConcavityNumerator u) :
    StrictMonoOn xiRadialHazard (Set.Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro u hu
    have hu0 : 0 < u := hu
    exact (xiRadialHazard_hasDerivAt hu0).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    have hu0 : 0 < u := hu
    rw [(xiRadialHazard_hasDerivAt hu0).deriv]
    have hK := riemannXiKernel_pos hu0.le
    have hN := hpos u hu0
    positivity

/-! ## Phase E: boundary decay of weighted kernels -/

/-- Weighted decay at infinity: any natural power times the summed kernel
tends to zero, by the compiled exponential majorant. -/
theorem tendsto_pow_mul_xiKernel_atTop (k : ℕ) :
    Filter.Tendsto (fun u => u ^ k * riemannXiKernel u)
      Filter.atTop (nhds 0) := by
  have hdecay : Filter.Tendsto
      (fun x : ℝ => xiKernelMajorantConstant * (x ^ k * Real.exp (-3 * x / 2)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℕ) : ℝ)
      (3 / 2) (by norm_num)
    have h' : Filter.Tendsto (fun x : ℝ => x ^ k * Real.exp (-3 * x / 2))
        Filter.atTop (nhds 0) := by
      apply h.congr
      intro x
      rw [Real.rpow_natCast, show -(3 / 2 : ℝ) * x = -3 * x / 2 from by ring]
    have := h'.const_mul xiKernelMajorantConstant
    simpa using this
  apply squeeze_zero' ?_ ?_ hdecay
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_nonneg (pow_nonneg hu k) (riemannXiKernel_nonneg hu)
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    calc
      u ^ k * riemannXiKernel u ≤
          u ^ k * (xiKernelMajorantConstant * Real.exp (-3 * u / 2)) :=
        mul_le_mul_of_nonneg_left (riemannXiKernel_le_majorant hu)
          (pow_nonneg hu k)
      _ = xiKernelMajorantConstant * (u ^ k * Real.exp (-3 * u / 2)) := by
        ring

/-- The linear-weight boundary term at infinity vanishes. -/
theorem tendsto_u_mul_xiKernel_atTop :
    Filter.Tendsto (fun u => u * riemannXiKernel u)
      Filter.atTop (nhds 0) := by
  have h := tendsto_pow_mul_xiKernel_atTop 1
  simpa using h

/-- The cubic-weight boundary term at infinity vanishes. -/
theorem tendsto_u_cube_mul_xiKernel_atTop :
    Filter.Tendsto (fun u => u ^ 3 * riemannXiKernel u)
      Filter.atTop (nhds 0) :=
  tendsto_pow_mul_xiKernel_atTop 3

/-- Weighted continuity at the origin: any positive natural power times the
summed kernel tends to zero from inside the half-line. -/
theorem tendsto_pow_mul_xiKernel_zero (k : ℕ) (hk : 0 < k) :
    Filter.Tendsto (fun u => u ^ k * riemannXiKernel u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hK : ContinuousWithinAt riemannXiKernel (Set.Ici 0) 0 :=
    riemannXiKernel_continuousOn 0 (Set.mem_Ici.mpr le_rfl)
  have hpow : ContinuousWithinAt (fun u : ℝ => u ^ k) (Set.Ici 0) 0 :=
    (continuousWithinAt_id.pow k)
  have hmul : ContinuousWithinAt
      (fun u : ℝ => u ^ k * riemannXiKernel u) (Set.Ici 0) 0 := hpow.mul hK
  have hval : (0 : ℝ) ^ k * riemannXiKernel 0 = 0 := by
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hk), zero_mul]
  have h : Filter.Tendsto (fun u : ℝ => u ^ k * riemannXiKernel u)
      (nhdsWithin 0 (Set.Ici 0)) (nhds ((0 : ℝ) ^ k * riemannXiKernel 0)) := hmul
  rw [hval] at h
  exact h.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

/-- The linear-weight boundary term at the origin vanishes. -/
theorem tendsto_u_mul_xiKernel_zero :
    Filter.Tendsto (fun u => u * riemannXiKernel u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h := tendsto_pow_mul_xiKernel_zero 1 one_pos
  simpa using h

/-- The cubic-weight boundary term at the origin vanishes. -/
theorem tendsto_u_cube_mul_xiKernel_zero :
    Filter.Tendsto (fun u => u ^ 3 * riemannXiKernel u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  tendsto_pow_mul_xiKernel_zero 3 (by norm_num)

/-- Every polynomial moment of the actual Xi kernel is integrable on the
positive half-line. -/
theorem xiThetaMoment_integrable (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ k * riemannXiKernel u) (Set.Ioi 0) := by
  have hbase : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ (k : ℝ) *
        Real.exp (-(3 / 2 : ℝ) * u ^ (1 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) (b := (3 / 2 : ℝ))
      (by have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
      (by norm_num) (by norm_num)
  have hdecay : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ k * Real.exp (-3 * u / 2)) (Set.Ioi 0) :=
    hbase.congr_fun (fun u _ => by
      dsimp only
      rw [Real.rpow_natCast, Real.rpow_one]
      congr 2
      ring) measurableSet_Ioi
  have hmajor : MeasureTheory.IntegrableOn
      (fun u : ℝ => xiKernelMajorantConstant *
        (u ^ k * Real.exp (-3 * u / 2))) (Set.Ioi 0) :=
    hdecay.const_mul xiKernelMajorantConstant
  apply hmajor.mono'
  · exact ((measurable_id.pow_const k).mul riemannXiKernel_measurable).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg hu0 k) (riemannXiKernel_nonneg hu0))]
    calc
      u ^ k * riemannXiKernel u ≤
          u ^ k * (xiKernelMajorantConstant * Real.exp (-3 * u / 2)) :=
        mul_le_mul_of_nonneg_left (riemannXiKernel_le_majorant hu0)
          (pow_nonneg hu0 k)
      _ = xiKernelMajorantConstant *
          (u ^ k * Real.exp (-3 * u / 2)) := by ring

/-- All half-line moments of the actual Riemann kernel are nonnegative. -/
theorem xiThetaMoment_nonneg (k : ℕ) : 0 ≤ xiThetaMoment k := by
  unfold xiThetaMoment
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg (pow_nonneg hu.le k) (riemannXiKernel_nonneg hu.le)

/-- Every half-line Xi-kernel moment is strictly positive. -/
theorem xiThetaMoment_pos (k : ℕ) : 0 < xiThetaMoment k := by
  unfold xiThetaMoment
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun u : ℝ => u ^ k * riemannXiKernel u) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (pow_nonneg hu.le k) (riemannXiKernel_nonneg hu.le)
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    hnonneg (xiThetaMoment_integrable k)]
  have hsub : Set.Ioo (1 : ℝ) 2 ⊆
      Function.support (fun u : ℝ => u ^ k * riemannXiKernel u) := by
    intro u hu
    exact ne_of_gt (mul_pos
      (pow_pos (lt_trans zero_lt_one hu.1) k)
      (riemannXiKernel_pos (le_of_lt (lt_trans zero_lt_one hu.1))))
  have hopen : 0 <
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioo 1 2) := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo]
    norm_num [Set.Ioo_inter_Ioi]
  exact hopen.trans_le (MeasureTheory.measure_mono hsub)

/-! ## Phase E (completion): the exact hazard-moment identities -/

/-- The index-exponential tail sequence is summable. -/
theorem summable_exp_neg_index :
    Summable (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 0 * Real.exp (-1 * n)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 0 one_pos
  have heq : (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) = fun n : ℕ =>
      Real.exp (-1) * ((n : ℝ) ^ 0 * Real.exp (-1 * n)) := by
    funext n
    have hsplit : Real.exp (-((n : ℝ) + 1)) =
        Real.exp (-1) * Real.exp (-1 * n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, pow_zero, one_mul]
  rw [heq]
  exact hbase.mul_left _

/-- Decay-strengthened bound: any fixed power of the exponential coordinate
times one kernel summand decays exponentially in both index and height. -/
theorem xiKernelQ_pow_mul_term_le_decay (m n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
      2 ^ (3 + m) * ((3 + m).factorial : ℝ) *
        (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
  have hq0 := xiKernelQ_pos n u
  have hterm := riemannXiKernelTerm_le_qcube n hu
  have hr : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hexp1 : 1 + 2 * u ≤ Real.exp (2 * u) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * u)
  have hq_lower : 3 * ((n : ℝ) + 1) ^ 2 * (1 + 2 * u) ≤ xiKernelQ n u := by
    unfold xiKernelQ
    dsimp only
    calc
      3 * ((n : ℝ) + 1) ^ 2 * (1 + 2 * u) ≤
          Real.pi * ((n : ℝ) + 1) ^ 2 * (1 + 2 * u) := by
        have hprod : 0 ≤ ((n : ℝ) + 1) ^ 2 * (1 + 2 * u) :=
          mul_nonneg (sq_nonneg _) (by linarith)
        nlinarith [Real.pi_gt_three, hprod]
      _ ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) :=
        mul_le_mul_of_nonneg_left hexp1 (by positivity)
  have hhalf : ((n : ℝ) + 1) + u ≤ xiKernelQ n u / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr2) hu, sq_nonneg ((n : ℝ) + 1 - 1)]
  have h1 : xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
      xiKernelQ n u ^ (3 + m) * Real.exp (-xiKernelQ n u) := by
    calc
      xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
          xiKernelQ n u ^ m *
            (xiKernelQ n u ^ 3 * Real.exp (-xiKernelQ n u)) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = xiKernelQ n u ^ (3 + m) * Real.exp (-xiKernelQ n u) := by
        rw [pow_add]
        ring
  have h2 := pow_mul_exp_neg_le_exp_neg_half (3 + m) hq0.le
  have h3 : Real.exp (-xiKernelQ n u / 2) ≤
      Real.exp (-((n : ℝ) + 1)) * Real.exp (-u) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc
    xiKernelQ n u ^ m * riemannXiKernelTerm n u ≤
        xiKernelQ n u ^ (3 + m) * Real.exp (-xiKernelQ n u) := h1
    _ ≤ 2 ^ (3 + m) * ((3 + m).factorial : ℝ) *
          Real.exp (-xiKernelQ n u / 2) := h2
    _ ≤ 2 ^ (3 + m) * ((3 + m).factorial : ℝ) *
          (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Pointwise decaying bound for the first derivative of one kernel summand. -/
theorem xiKernelTermDeriv_abs_le_decay (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |xiKernelTermDeriv n u| ≤
      1920 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
  have hterm_pos := riemannXiKernelTerm_pos n hu
  have hslope := xiKernelTermLogSlope_abs_le n hu
  have hq1 := xiKernelQ_pow_mul_term_le_decay 1 n hu
  have h : |xiKernelTermDeriv n u| ≤
      5 * (xiKernelQ n u ^ 1 * riemannXiKernelTerm n u) := by
    unfold xiKernelTermDeriv
    rw [abs_mul, abs_of_pos hterm_pos]
    calc
      |xiKernelTermLogSlope n u| * riemannXiKernelTerm n u ≤
          5 * xiKernelQ n u * riemannXiKernelTerm n u :=
        mul_le_mul_of_nonneg_right hslope hterm_pos.le
      _ = 5 * (xiKernelQ n u ^ 1 * riemannXiKernelTerm n u) := by
        rw [pow_one]
        ring
  calc
    |xiKernelTermDeriv n u| ≤
        5 * (xiKernelQ n u ^ 1 * riemannXiKernelTerm n u) := h
    _ ≤ 5 * (2 ^ (3 + 1) * ((3 + 1).factorial : ℝ) *
          (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) :=
      mul_le_mul_of_nonneg_left hq1 (by norm_num)
    _ = 1920 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
      norm_num [Nat.factorial]
      ring

/-- Pointwise decaying bound for the slope-square weight. -/
theorem xiKernelTermSlopeSquareWeight_le_decay
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    xiKernelTermSlopeSquareWeight n u ≤
      96000 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
  have hterm := riemannXiKernelTerm_pos n hu
  have hslope := xiKernelTermLogSlope_abs_le n hu
  have hsq : xiKernelTermLogSlope n u ^ 2 ≤ (5 * xiKernelQ n u) ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le hslope) (le_of_abs_le hslope)
  have hq2 := xiKernelQ_pow_mul_term_le_decay 2 n hu
  unfold xiKernelTermSlopeSquareWeight
  calc
    xiKernelTermLogSlope n u ^ 2 * riemannXiKernelTerm n u ≤
        (5 * xiKernelQ n u) ^ 2 * riemannXiKernelTerm n u :=
      mul_le_mul_of_nonneg_right hsq hterm.le
    _ = 25 * (xiKernelQ n u ^ 2 * riemannXiKernelTerm n u) := by ring
    _ ≤ 25 * (2 ^ (3 + 2) * ((3 + 2).factorial : ℝ) *
          (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) :=
      mul_le_mul_of_nonneg_left hq2 (by norm_num)
    _ = 96000 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
      norm_num [Nat.factorial]
      ring

/-- Pointwise decaying bound for the absolute curvature weight. -/
theorem xiKernelTermCurvatureWeight_abs_le_decay
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |xiKernelTermCurvatureWeight n u| ≤
      2688 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
  have hterm := riemannXiKernelTerm_pos n hu
  have hcurv := xiKernelTermLogCurvature_abs_le n hu
  have hq1 := xiKernelQ_pow_mul_term_le_decay 1 n hu
  unfold xiKernelTermCurvatureWeight
  rw [abs_mul, abs_of_pos hterm]
  calc
    |xiKernelTermLogCurvature n u| * riemannXiKernelTerm n u ≤
        7 * xiKernelQ n u * riemannXiKernelTerm n u :=
      mul_le_mul_of_nonneg_right hcurv hterm.le
    _ = 7 * (xiKernelQ n u ^ 1 * riemannXiKernelTerm n u) := by
      rw [pow_one]
      ring
    _ ≤ 7 * (2 ^ (3 + 1) * ((3 + 1).factorial : ℝ) *
          (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) :=
      mul_le_mul_of_nonneg_left hq1 (by norm_num)
    _ = 2688 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
      norm_num [Nat.factorial]
      ring

/-- Pointwise decaying bound for the absolute gate weight. -/
theorem xiKernelTermGateWeight_abs_le_decay
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |xiKernelTermGateWeight n u| ≤
      (1920 + 2688 * u) *
        (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by
  have hgate : xiKernelTermGateWeight n u =
      xiKernelTermDeriv n u - u * xiKernelTermCurvatureWeight n u := by
    unfold xiKernelTermGateWeight xiTermGate xiKernelTermDeriv
      xiKernelTermCurvatureWeight
    ring
  rw [hgate]
  calc
    |xiKernelTermDeriv n u - u * xiKernelTermCurvatureWeight n u| ≤
        |xiKernelTermDeriv n u| +
          |u * xiKernelTermCurvatureWeight n u| := abs_sub _ _
    _ = |xiKernelTermDeriv n u| +
        u * |xiKernelTermCurvatureWeight n u| := by
      rw [abs_mul, abs_of_nonneg hu]
    _ ≤ 1920 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) +
        u * (2688 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) := by
      exact add_le_add (xiKernelTermDeriv_abs_le_decay n hu)
        (mul_le_mul_of_nonneg_left
          (xiKernelTermCurvatureWeight_abs_le_decay n hu) hu)
    _ = (1920 + 2688 * u) *
        (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := by ring

/-- The index majorant remains summable after deleting its ground term. -/
theorem summable_exp_neg_shifted_index :
    Summable (fun n : ℕ => Real.exp (-(((n + 1 : ℕ) : ℝ) + 1))) := by
  exact (summable_nat_add_iff 1).2 summable_exp_neg_index

/-- The numerical exponential mass of the shifted index tail. -/
def xiShiftedIndexTail : ℝ :=
  ∑' n : ℕ, Real.exp (-(((n + 1 : ℕ) : ℝ) + 1))

/-- The shifted exponential tail is nonnegative. -/
theorem xiShiftedIndexTail_nonneg : 0 ≤ xiShiftedIndexTail := by
  unfold xiShiftedIndexTail
  exact tsum_nonneg fun n => (Real.exp_pos _).le

/-- Closed form of the unshifted exponential index mass. -/
theorem tsum_exp_neg_index_eq :
    (∑' n : ℕ, Real.exp (-((n : ℝ) + 1))) =
      Real.exp (-1) / (1 - Real.exp (-1)) := by
  have hq0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hq1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [show (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) =
      fun n : ℕ => Real.exp (-1) * Real.exp (-1) ^ n from
    funext fun n => by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rfl

/-- Closed form of the positive-index exponential tail. -/
theorem xiShiftedIndexTail_eq :
    xiShiftedIndexTail =
      Real.exp (-1) ^ 2 / (1 - Real.exp (-1)) := by
  have hq0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hq1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold xiShiftedIndexTail
  rw [show (fun n : ℕ => Real.exp (-(((n + 1 : ℕ) : ℝ) + 1))) =
      fun n : ℕ => Real.exp (-1) ^ 2 * Real.exp (-1) ^ n from
    funext fun n => by
      rw [← pow_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rfl

/-- Absolute decay estimate for the complete positive-index gate tail. -/
theorem xiGateTail_abs_le {u : ℝ} (hu : 0 ≤ u) :
    |∑' n : ℕ, xiKernelTermGateWeight (n + 1) u| ≤
      (1920 + 2688 * u) * Real.exp (-u) * xiShiftedIndexTail := by
  have hcoef : 0 ≤ 1920 + 2688 * u := by nlinarith
  have hmajor : Summable (fun n : ℕ =>
      (1920 + 2688 * u) *
        (Real.exp (-(((n + 1 : ℕ) : ℝ) + 1)) * Real.exp (-u))) :=
    (summable_exp_neg_shifted_index.mul_right (Real.exp (-u))).mul_left
      (1920 + 2688 * u)
  have hgate : Summable (fun n : ℕ => xiKernelTermGateWeight (n + 1) u) :=
    (summable_nat_add_iff 1).2 (xiKernelTermGateWeight_summable hu)
  have habs : |∑' n : ℕ, xiKernelTermGateWeight (n + 1) u| ≤
      ∑' n : ℕ, |xiKernelTermGateWeight (n + 1) u| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm
        (f := fun n : ℕ => xiKernelTermGateWeight (n + 1) u)
        (by simpa [Real.norm_eq_abs] using hgate.abs)
  have hle : (∑' n : ℕ, |xiKernelTermGateWeight (n + 1) u|) ≤
      ∑' n : ℕ, (1920 + 2688 * u) *
        (Real.exp (-(((n + 1 : ℕ) : ℝ) + 1)) * Real.exp (-u)) :=
    Summable.tsum_le_tsum
      (fun n => xiKernelTermGateWeight_abs_le_decay (n + 1) hu)
      hgate.abs hmajor
  calc
    |∑' n : ℕ, xiKernelTermGateWeight (n + 1) u| ≤
        ∑' n : ℕ, |xiKernelTermGateWeight (n + 1) u| := habs
    _ ≤ ∑' n : ℕ, (1920 + 2688 * u) *
        (Real.exp (-(((n + 1 : ℕ) : ℝ) + 1)) * Real.exp (-u)) := hle
    _ = (1920 + 2688 * u) * Real.exp (-u) * xiShiftedIndexTail := by
      rw [show (fun n : ℕ => (1920 + 2688 * u) *
          (Real.exp (-(((n + 1 : ℕ) : ℝ) + 1)) * Real.exp (-u))) =
          fun n : ℕ => ((1920 + 2688 * u) * Real.exp (-u)) *
            Real.exp (-(((n + 1 : ℕ) : ℝ) + 1)) from
        funext fun n => by ring]
      rw [tsum_mul_left]
      rfl

/-- Decay estimate for the complete slope-square series. -/
theorem tsum_xiKernelTermSlopeSquareWeight_le {u : ℝ} (hu : 0 ≤ u) :
    (∑' n : ℕ, xiKernelTermSlopeSquareWeight n u) ≤
      96000 * Real.exp (-u) *
        (∑' n : ℕ, Real.exp (-((n : ℝ) + 1))) := by
  have hmajor : Summable (fun n : ℕ =>
      96000 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) :=
    (summable_exp_neg_index.mul_right (Real.exp (-u))).mul_left 96000
  have hsq := xiKernelTermSlopeSquareWeight_summable hu
  have hle : (∑' n : ℕ, xiKernelTermSlopeSquareWeight n u) ≤
      ∑' n : ℕ,
        96000 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) :=
    Summable.tsum_le_tsum
      (fun n => xiKernelTermSlopeSquareWeight_le_decay n hu) hsq hmajor
  calc
    (∑' n : ℕ, xiKernelTermSlopeSquareWeight n u) ≤
        ∑' n : ℕ,
          96000 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) := hle
    _ = 96000 * Real.exp (-u) *
        (∑' n : ℕ, Real.exp (-((n : ℝ) + 1))) := by
      rw [show (fun n : ℕ =>
          96000 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) =
          fun n : ℕ => (96000 * Real.exp (-u)) *
            Real.exp (-((n : ℝ) + 1)) from funext fun n => by ring]
      exact tsum_mul_left

/-- The full gate series is bounded below by its ground term minus the
absolute positive-index tail majorant. -/
theorem tsum_xiKernelTermGateWeight_ge_ground_sub_tail {u : ℝ}
    (hu : 0 ≤ u) :
    xiKernelTermGateWeight 0 u -
        (1920 + 2688 * u) * Real.exp (-u) * xiShiftedIndexTail ≤
      ∑' n : ℕ, xiKernelTermGateWeight n u := by
  have htail := xiGateTail_abs_le hu
  have hlower :
      -((1920 + 2688 * u) * Real.exp (-u) * xiShiftedIndexTail) ≤
        ∑' n : ℕ, xiKernelTermGateWeight (n + 1) u :=
    neg_le_of_abs_le htail
  rw [tsum_xiKernelTermGateWeight_eq_ground_add_tail hu]
  linarith

/-- Explicit ground-versus-tail criterion implying positivity of the radial
concavity numerator on the open half-line. -/
theorem xiRadialConcavityNumerator_pos_of_ground_dominates_decay
    {u : ℝ} (hu : 0 < u)
    (hdom :
      u *
          (96000 * Real.exp (-u) *
            (∑' n : ℕ, Real.exp (-((n : ℝ) + 1)))) <
        xiKernelTermGateWeight 0 u -
          (1920 + 2688 * u) * Real.exp (-u) * xiShiftedIndexTail) :
    0 < xiRadialConcavityNumerator u := by
  rw [xiRadialConcavityNumerator_pos_iff_gate_dominates_variance hu]
  let mass : ℝ := ∑' n : ℕ, riemannXiKernelTerm n u
  let slope : ℝ := ∑' n : ℕ, xiKernelTermSlopeSquareWeight n u
  let slopeBound : ℝ :=
    96000 * Real.exp (-u) *
      (∑' n : ℕ, Real.exp (-((n : ℝ) + 1)))
  let derivSum : ℝ := ∑' n : ℕ, xiKernelTermDeriv n u
  let gate : ℝ := ∑' n : ℕ, xiKernelTermGateWeight n u
  let gateLower : ℝ := xiKernelTermGateWeight 0 u -
    (1920 + 2688 * u) * Real.exp (-u) * xiShiftedIndexTail
  have hmass : 0 < mass := by
    dsimp [mass]
    exact (riemannXiKernelTerm_summable u).tsum_pos
      (fun n => (riemannXiKernelTerm_pos n hu.le).le) 0
      (riemannXiKernelTerm_pos 0 hu.le)
  have hslope : slope ≤ slopeBound := by
    dsimp [slope, slopeBound]
    exact tsum_xiKernelTermSlopeSquareWeight_le hu.le
  have hgate : gateLower ≤ gate := by
    dsimp [gateLower, gate]
    exact tsum_xiKernelTermGateWeight_ge_ground_sub_tail hu.le
  have hvar : mass * slope - derivSum ^ 2 ≤ mass * slopeBound := by
    have hmul := mul_le_mul_of_nonneg_left hslope hmass.le
    nlinarith [sq_nonneg derivSum]
  have hleft : u * (mass * slope - derivSum ^ 2) ≤
      mass * (u * slopeBound) := by
    calc
      u * (mass * slope - derivSum ^ 2) ≤ u * (mass * slopeBound) :=
        mul_le_mul_of_nonneg_left hvar hu.le
      _ = mass * (u * slopeBound) := by ring
  have hmid : mass * (u * slopeBound) < mass * gateLower := by
    apply mul_lt_mul_of_pos_left
    · simpa [slopeBound, gateLower] using hdom
    · exact hmass
  have hright : mass * gateLower ≤ mass * gate :=
    mul_le_mul_of_nonneg_left hgate hmass.le
  change u * (mass * slope - derivSum ^ 2) < mass * gate
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hmid hright)

/-- Fully elementary bulk criterion, with both index sums evaluated as
geometric series. -/
theorem xiRadialConcavityNumerator_pos_of_ground_dominates_closed_decay
    {u : ℝ} (hu : 0 < u)
    (hdom :
      u *
          (96000 * Real.exp (-u) *
            (Real.exp (-1) / (1 - Real.exp (-1)))) <
        xiKernelTermGateWeight 0 u -
          (1920 + 2688 * u) * Real.exp (-u) *
            (Real.exp (-1) ^ 2 / (1 - Real.exp (-1)))) :
    0 < xiRadialConcavityNumerator u := by
  apply xiRadialConcavityNumerator_pos_of_ground_dominates_decay hu
  rw [tsum_exp_neg_index_eq, xiShiftedIndexTail_eq]
  exact hdom

/-- Global decaying constant for the derivative of the summed kernel. -/
def xiDerivDecayConstant : ℝ :=
  4 * 1920 * ∑' n : ℕ, Real.exp (-((n : ℝ) + 1))

/-- The derivative-decay constant is nonnegative. -/
theorem xiDerivDecayConstant_nonneg : 0 ≤ xiDerivDecayConstant := by
  unfold xiDerivDecayConstant
  have h : 0 ≤ ∑' n : ℕ, Real.exp (-((n : ℝ) + 1)) :=
    tsum_nonneg fun n => (Real.exp_pos _).le
  nlinarith

/-- The derivative of the summed kernel decays exponentially on the open
half-line. -/
theorem riemannXiKernel_deriv_abs_le {u : ℝ} (hu : 0 < u) :
    |deriv riemannXiKernel u| ≤ xiDerivDecayConstant * Real.exp (-u) := by
  have hsum_bound : Summable (fun n : ℕ =>
      1920 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) :=
    (summable_exp_neg_index.mul_right (Real.exp (-u))).mul_left 1920
  have hsummable : Summable (fun n => xiKernelTermDeriv n u) :=
    Summable.of_norm_bounded hsum_bound (fun n => by
      rw [Real.norm_eq_abs]
      exact xiKernelTermDeriv_abs_le_decay n hu.le)
  have habs : |∑' n, xiKernelTermDeriv n u| ≤
      ∑' n, |xiKernelTermDeriv n u| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun n => xiKernelTermDeriv n u)
        (by simpa [Real.norm_eq_abs] using hsummable.abs)
  have h1 : (∑' n : ℕ, |xiKernelTermDeriv n u|) ≤
      ∑' n : ℕ, 1920 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u)) :=
    Summable.tsum_le_tsum (fun n => xiKernelTermDeriv_abs_le_decay n hu.le)
      hsummable.abs hsum_bound
  have h2 : (∑' n : ℕ, 1920 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) =
      1920 * Real.exp (-u) * ∑' n : ℕ, Real.exp (-((n : ℝ) + 1)) := by
    rw [show (fun n : ℕ =>
        1920 * (Real.exp (-((n : ℝ) + 1)) * Real.exp (-u))) =
        fun n : ℕ => 1920 * Real.exp (-u) * Real.exp (-((n : ℝ) + 1)) from
      funext fun n => by ring]
    exact tsum_mul_left
  rw [riemannXiKernel_deriv_eq hu, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
  calc
    4 * |∑' n, xiKernelTermDeriv n u| ≤
        4 * (1920 * Real.exp (-u) * ∑' n : ℕ, Real.exp (-((n : ℝ) + 1))) := by
      have := habs.trans h1
      rw [h2] at this
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    _ = xiDerivDecayConstant * Real.exp (-u) := by
      unfold xiDerivDecayConstant
      ring

/-- Any polynomial weight times the kernel derivative is integrable on the
half-line. -/
theorem integrable_pow_mul_xiKernel_deriv (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ k * deriv riemannXiKernel u) (Set.Ioi 0) := by
  have hbase : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ (k : ℝ) *
        Real.exp (-(1 : ℝ) * u ^ (1 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) (b := (1 : ℝ))
      (by have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
      (by norm_num) (by norm_num)
  have hdecay : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ k * Real.exp (-u)) (Set.Ioi 0) :=
    hbase.congr_fun (fun u _ => by
      dsimp only
      rw [Real.rpow_natCast, Real.rpow_one]
      congr 2
      ring) measurableSet_Ioi
  have hmajor := hdecay.const_mul xiDerivDecayConstant
  apply hmajor.mono'
  · exact ((measurable_id.pow_const k).mul
      (measurable_deriv _)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu.le k)]
    calc
      u ^ k * |deriv riemannXiKernel u| ≤
          u ^ k * (xiDerivDecayConstant * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left (riemannXiKernel_deriv_abs_le hu)
          (pow_nonneg hu.le k)
      _ = xiDerivDecayConstant * (u ^ k * Real.exp (-u)) := by ring

/-- Integration by parts with linear weight: the derivative's first moment is
minus the kernel's zeroth moment. -/
theorem integral_u_mul_xiKernel_deriv :
    ∫ u in Set.Ioi (0 : ℝ), u * deriv riemannXiKernel u =
      -xiThetaMoment 0 := by
  have hK0 : MeasureTheory.IntegrableOn riemannXiKernel (Set.Ioi 0) :=
    (xiThetaMoment_integrable 0).congr_fun
      (fun u _ => by simp) measurableSet_Ioi
  have hUK : MeasureTheory.IntegrableOn
      (fun u : ℝ => u * deriv riemannXiKernel u) (Set.Ioi 0) :=
    (integrable_pow_mul_xiKernel_deriv 1).congr_fun
      (fun u _ => by simp) measurableSet_Ioi
  have hcont : ContinuousWithinAt
      (fun u : ℝ => u * riemannXiKernel u) (Set.Ici 0) 0 :=
    continuousWithinAt_id.mul
      (riemannXiKernel_continuousOn 0 (Set.mem_Ici.mpr le_rfl))
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun u => u * riemannXiKernel u)
        (riemannXiKernel x + x * deriv riemannXiKernel x) x := by
    intro x hx
    have hK : HasDerivAt riemannXiKernel (deriv riemannXiKernel x) x := by
      rw [riemannXiKernel_deriv_eq hx]
      exact riemannXiKernel_hasDerivAt hx
    have h := (hasDerivAt_id x).mul hK
    apply h.congr_deriv
    simp only [id_eq, one_mul]
  have hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => riemannXiKernel x + x * deriv riemannXiKernel x)
      (Set.Ioi 0) := hK0.add hUK
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcont hderiv hint tendsto_u_mul_xiKernel_atTop
  rw [zero_mul, sub_zero] at hftc
  rw [MeasureTheory.integral_add hK0 hUK] at hftc
  have hm0 : xiThetaMoment 0 = ∫ u in Set.Ioi (0 : ℝ), riemannXiKernel u := by
    unfold xiThetaMoment
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp
  linarith

/-- Integration by parts with cubic weight: the derivative's third moment is
minus three times the kernel's second moment. -/
theorem integral_u_cube_mul_xiKernel_deriv :
    ∫ u in Set.Ioi (0 : ℝ), u ^ 3 * deriv riemannXiKernel u =
      -(3 * xiThetaMoment 2) := by
  have hK2 : MeasureTheory.IntegrableOn
      (fun u : ℝ => 3 * (u ^ 2 * riemannXiKernel u)) (Set.Ioi 0) :=
    (xiThetaMoment_integrable 2).const_mul 3
  have hUK : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ 3 * deriv riemannXiKernel u) (Set.Ioi 0) :=
    integrable_pow_mul_xiKernel_deriv 3
  have hcont : ContinuousWithinAt
      (fun u : ℝ => u ^ 3 * riemannXiKernel u) (Set.Ici 0) 0 :=
    (continuousWithinAt_id.pow 3).mul
      (riemannXiKernel_continuousOn 0 (Set.mem_Ici.mpr le_rfl))
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun u => u ^ 3 * riemannXiKernel u)
        (3 * (x ^ 2 * riemannXiKernel x) +
          x ^ 3 * deriv riemannXiKernel x) x := by
    intro x hx
    have hK : HasDerivAt riemannXiKernel (deriv riemannXiKernel x) x := by
      rw [riemannXiKernel_deriv_eq hx]
      exact riemannXiKernel_hasDerivAt hx
    have hpow : HasDerivAt (fun y : ℝ => y ^ 3)
        (3 * x ^ 2) x := by
      simpa using hasDerivAt_pow 3 x
    have h := hpow.mul hK
    apply h.congr_deriv
    ring
  have hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => 3 * (x ^ 2 * riemannXiKernel x) +
        x ^ 3 * deriv riemannXiKernel x) (Set.Ioi 0) := hK2.add hUK
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcont hderiv hint tendsto_u_cube_mul_xiKernel_atTop
  have h03 : (0 : ℝ) ^ 3 = 0 := by norm_num
  rw [h03, zero_mul, sub_zero] at hftc
  rw [MeasureTheory.integral_add hK2 hUK] at hftc
  have h3m : (∫ u in Set.Ioi (0 : ℝ), 3 * (u ^ 2 * riemannXiKernel u)) =
      3 * xiThetaMoment 2 := by
    rw [MeasureTheory.integral_const_mul]
    rfl
  rw [h3m] at hftc
  linarith

/-- **Exact hazard-moment identity with quadratic weight.** -/
theorem xiRadialHazard_weight_two :
    ∫ u in Set.Ioi (0 : ℝ),
        u ^ 2 * riemannXiKernel u * xiRadialHazard u =
      xiThetaMoment 0 / 2 := by
  have hcongr : Set.EqOn
      (fun u : ℝ => u ^ 2 * riemannXiKernel u * xiRadialHazard u)
      (fun u : ℝ => -(1 / 2) * (u * deriv riemannXiKernel u))
      (Set.Ioi 0) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hK := riemannXiKernel_pos hu0.le
    dsimp only
    unfold xiRadialHazard
    field_simp [ne_of_gt hu0, ne_of_gt hK]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    MeasureTheory.integral_const_mul, integral_u_mul_xiKernel_deriv]
  ring

/-- **Exact hazard-moment identity with quartic weight.** -/
theorem xiRadialHazard_weight_four :
    ∫ u in Set.Ioi (0 : ℝ),
        u ^ 4 * riemannXiKernel u * xiRadialHazard u =
      3 * xiThetaMoment 2 / 2 := by
  have hcongr : Set.EqOn
      (fun u : ℝ => u ^ 4 * riemannXiKernel u * xiRadialHazard u)
      (fun u : ℝ => -(1 / 2) * (u ^ 3 * deriv riemannXiKernel u))
      (Set.Ioi 0) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hK := riemannXiKernel_pos hu0.le
    dsimp only
    unfold xiRadialHazard
    field_simp [ne_of_gt hu0, ne_of_gt hK]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    MeasureTheory.integral_const_mul, integral_u_cube_mul_xiKernel_deriv]
  ring

/-! ## Phase F: the covariance integrand and its exact evaluation -/

/-- Pointwise identification of the quadratic hazard weight with the exact
derivative form on the half-line. -/
theorem sq_mul_hazard_eqOn : Set.EqOn
    (fun u : ℝ => u ^ 2 * riemannXiKernel u * xiRadialHazard u)
    (fun u : ℝ => -(1 / 2) * (u * deriv riemannXiKernel u)) (Set.Ioi 0) := by
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hK := riemannXiKernel_pos hu0.le
  dsimp only
  unfold xiRadialHazard
  field_simp [ne_of_gt hu0, ne_of_gt hK]

/-- Pointwise identification of the quartic hazard weight with the exact
derivative form on the half-line. -/
theorem pow4_mul_hazard_eqOn : Set.EqOn
    (fun u : ℝ => u ^ 4 * riemannXiKernel u * xiRadialHazard u)
    (fun u : ℝ => -(1 / 2) * (u ^ 3 * deriv riemannXiKernel u)) (Set.Ioi 0) := by
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hK := riemannXiKernel_pos hu0.le
  dsimp only
  unfold xiRadialHazard
  field_simp [ne_of_gt hu0, ne_of_gt hK]

/-- The quadratic hazard weight is integrable on the half-line. -/
theorem integrable_sq_mul_xiKernel_hazard :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ 2 * riemannXiKernel u * xiRadialHazard u)
      (Set.Ioi 0) := by
  have h0 : MeasureTheory.IntegrableOn
      (fun u : ℝ => -(1 / 2) * (u ^ 1 * deriv riemannXiKernel u))
      (Set.Ioi 0) :=
    (integrable_pow_mul_xiKernel_deriv 1).const_mul (-(1 / 2))
  have hbase : MeasureTheory.IntegrableOn
      (fun u : ℝ => -(1 / 2) * (u * deriv riemannXiKernel u)) (Set.Ioi 0) :=
    h0.congr_fun (fun u _ => by simp) measurableSet_Ioi
  exact hbase.congr_fun (fun u hu => (sq_mul_hazard_eqOn hu).symm)
    measurableSet_Ioi

/-- The quartic hazard weight is integrable on the half-line. -/
theorem integrable_pow4_mul_xiKernel_hazard :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ 4 * riemannXiKernel u * xiRadialHazard u)
      (Set.Ioi 0) := by
  have hbase : MeasureTheory.IntegrableOn
      (fun u : ℝ => -(1 / 2) * (u ^ 3 * deriv riemannXiKernel u))
      (Set.Ioi 0) :=
    (integrable_pow_mul_xiKernel_deriv 3).const_mul (-(1 / 2))
  exact hbase.congr_fun (fun u hu => (pow4_mul_hazard_eqOn hu).symm)
    measurableSet_Ioi

/-- The symmetric covariance integrand of the radial hazard. -/
def xiRadialCovarianceIntegrand (u v : ℝ) : ℝ :=
  (u ^ 2 - v ^ 2) * (xiRadialHazard u - xiRadialHazard v) *
    (u ^ 2 * riemannXiKernel u) * (v ^ 2 * riemannXiKernel v)

/-- **Exact evaluation of the covariance double integral** through the two
hazard-moment identities: the result is the central Turán combination. -/
theorem xiRadialCovarianceIntegral_eq :
    (∫ u in Set.Ioi (0 : ℝ), ∫ v in Set.Ioi (0 : ℝ),
        xiRadialCovarianceIntegrand u v) =
      3 * xiThetaMoment 2 ^ 2 - xiThetaMoment 0 * xiThetaMoment 4 := by
  have hm2 : (∫ v in Set.Ioi (0 : ℝ), v ^ 2 * riemannXiKernel v) =
      xiThetaMoment 2 := rfl
  have hm4 : (∫ v in Set.Ioi (0 : ℝ), v ^ 4 * riemannXiKernel v) =
      xiThetaMoment 4 := rfl
  have hinner : Set.EqOn
      (fun u : ℝ => ∫ v in Set.Ioi (0 : ℝ), xiRadialCovarianceIntegrand u v)
      (fun u : ℝ =>
        xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u) +
          -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u) +
          -xiThetaMoment 4 * (u ^ 2 * riemannXiKernel u * xiRadialHazard u) +
          3 * xiThetaMoment 2 / 2 * (u ^ 2 * riemannXiKernel u))
      (Set.Ioi 0) := by
    intro u _
    dsimp only
    have hc1 : MeasureTheory.IntegrableOn
        (fun v : ℝ => u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
          (v ^ 2 * riemannXiKernel v)) (Set.Ioi 0) :=
      (xiThetaMoment_integrable 2).const_mul _
    have hc2 : MeasureTheory.IntegrableOn
        (fun v : ℝ => -(u ^ 2 * riemannXiKernel u * u ^ 2) *
          (v ^ 2 * riemannXiKernel v * xiRadialHazard v)) (Set.Ioi 0) :=
      integrable_sq_mul_xiKernel_hazard.const_mul _
    have hc3 : MeasureTheory.IntegrableOn
        (fun v : ℝ => -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
          (v ^ 4 * riemannXiKernel v)) (Set.Ioi 0) :=
      (xiThetaMoment_integrable 4).const_mul _
    have hc4 : MeasureTheory.IntegrableOn
        (fun v : ℝ => u ^ 2 * riemannXiKernel u *
          (v ^ 4 * riemannXiKernel v * xiRadialHazard v)) (Set.Ioi 0) :=
      integrable_pow4_mul_xiKernel_hazard.const_mul _
    have heq : (fun v : ℝ => xiRadialCovarianceIntegrand u v) =
        fun v : ℝ =>
          u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
              (v ^ 2 * riemannXiKernel v) +
            -(u ^ 2 * riemannXiKernel u * u ^ 2) *
              (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
            -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
              (v ^ 4 * riemannXiKernel v) +
            u ^ 2 * riemannXiKernel u *
              (v ^ 4 * riemannXiKernel v * xiRadialHazard v) := by
      funext v
      unfold xiRadialCovarianceIntegrand
      ring
    rw [heq,
      show (∫ v in Set.Ioi (0 : ℝ),
          (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
              (v ^ 2 * riemannXiKernel v) +
            -(u ^ 2 * riemannXiKernel u * u ^ 2) *
              (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
            -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
              (v ^ 4 * riemannXiKernel v) +
            u ^ 2 * riemannXiKernel u *
              (v ^ 4 * riemannXiKernel v * xiRadialHazard v))) =
        (∫ v in Set.Ioi (0 : ℝ),
          (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
              (v ^ 2 * riemannXiKernel v) +
            -(u ^ 2 * riemannXiKernel u * u ^ 2) *
              (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
            -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
              (v ^ 4 * riemannXiKernel v))) +
          ∫ v in Set.Ioi (0 : ℝ),
            u ^ 2 * riemannXiKernel u *
              (v ^ 4 * riemannXiKernel v * xiRadialHazard v) from
        MeasureTheory.integral_add ((hc1.add hc2).add hc3) hc4,
      show (∫ v in Set.Ioi (0 : ℝ),
          (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
              (v ^ 2 * riemannXiKernel v) +
            -(u ^ 2 * riemannXiKernel u * u ^ 2) *
              (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
            -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
              (v ^ 4 * riemannXiKernel v))) =
        (∫ v in Set.Ioi (0 : ℝ),
          (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
              (v ^ 2 * riemannXiKernel v) +
            -(u ^ 2 * riemannXiKernel u * u ^ 2) *
              (v ^ 2 * riemannXiKernel v * xiRadialHazard v))) +
          ∫ v in Set.Ioi (0 : ℝ),
            -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
              (v ^ 4 * riemannXiKernel v) from
        MeasureTheory.integral_add (hc1.add hc2) hc3,
      show (∫ v in Set.Ioi (0 : ℝ),
          (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
              (v ^ 2 * riemannXiKernel v) +
            -(u ^ 2 * riemannXiKernel u * u ^ 2) *
              (v ^ 2 * riemannXiKernel v * xiRadialHazard v))) =
        (∫ v in Set.Ioi (0 : ℝ),
          u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v)) +
          ∫ v in Set.Ioi (0 : ℝ),
            -(u ^ 2 * riemannXiKernel u * u ^ 2) *
              (v ^ 2 * riemannXiKernel v * xiRadialHazard v) from
        MeasureTheory.integral_add hc1 hc2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hm2, hm4, xiRadialHazard_weight_two, xiRadialHazard_weight_four]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinner]
  have hf1 : MeasureTheory.IntegrableOn
      (fun u : ℝ => xiThetaMoment 2 *
        (u ^ 4 * riemannXiKernel u * xiRadialHazard u)) (Set.Ioi 0) :=
    integrable_pow4_mul_xiKernel_hazard.const_mul _
  have hf2 : MeasureTheory.IntegrableOn
      (fun u : ℝ => -(xiThetaMoment 0 / 2) *
        (u ^ 4 * riemannXiKernel u)) (Set.Ioi 0) :=
    (xiThetaMoment_integrable 4).const_mul _
  have hf3 : MeasureTheory.IntegrableOn
      (fun u : ℝ => -xiThetaMoment 4 *
        (u ^ 2 * riemannXiKernel u * xiRadialHazard u)) (Set.Ioi 0) :=
    integrable_sq_mul_xiKernel_hazard.const_mul _
  have hf4 : MeasureTheory.IntegrableOn
      (fun u : ℝ => 3 * xiThetaMoment 2 / 2 *
        (u ^ 2 * riemannXiKernel u)) (Set.Ioi 0) :=
    (xiThetaMoment_integrable 2).const_mul _
  rw [show (∫ u in Set.Ioi (0 : ℝ),
        (xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u) +
          -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u) +
          -xiThetaMoment 4 * (u ^ 2 * riemannXiKernel u * xiRadialHazard u) +
          3 * xiThetaMoment 2 / 2 * (u ^ 2 * riemannXiKernel u))) =
      (∫ u in Set.Ioi (0 : ℝ),
        (xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u) +
          -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u) +
          -xiThetaMoment 4 *
            (u ^ 2 * riemannXiKernel u * xiRadialHazard u))) +
        ∫ u in Set.Ioi (0 : ℝ),
          3 * xiThetaMoment 2 / 2 * (u ^ 2 * riemannXiKernel u) from
      MeasureTheory.integral_add ((hf1.add hf2).add hf3) hf4,
    show (∫ u in Set.Ioi (0 : ℝ),
        (xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u) +
          -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u) +
          -xiThetaMoment 4 *
            (u ^ 2 * riemannXiKernel u * xiRadialHazard u))) =
      (∫ u in Set.Ioi (0 : ℝ),
        (xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u) +
          -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u))) +
        ∫ u in Set.Ioi (0 : ℝ),
          -xiThetaMoment 4 *
            (u ^ 2 * riemannXiKernel u * xiRadialHazard u) from
      MeasureTheory.integral_add (hf1.add hf2) hf3,
    show (∫ u in Set.Ioi (0 : ℝ),
        (xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u) +
          -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u))) =
      (∫ u in Set.Ioi (0 : ℝ),
        xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u)) +
        ∫ u in Set.Ioi (0 : ℝ),
          -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u) from
      MeasureTheory.integral_add hf1 hf2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hm2, hm4, xiRadialHazard_weight_two, xiRadialHazard_weight_four]
  ring

/-- The covariance integrand is pointwise nonnegative on the open quadrant
under strict hazard monotonicity. -/
theorem xiRadialCovarianceIntegrand_nonneg
    (hmono : StrictMonoOn xiRadialHazard (Set.Ioi (0 : ℝ)))
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 ≤ xiRadialCovarianceIntegrand u v := by
  have hKu := riemannXiKernel_pos hu.le
  have hKv := riemannXiKernel_pos hv.le
  unfold xiRadialCovarianceIntegrand
  have hfac : 0 ≤ (u ^ 2 - v ^ 2) *
      (xiRadialHazard u - xiRadialHazard v) := by
    rcases lt_trichotomy u v with h | h | h
    · have h2 : u ^ 2 ≤ v ^ 2 := by nlinarith
      have hH : xiRadialHazard u < xiRadialHazard v :=
        hmono (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr hv) h
      nlinarith
    · subst h
      simp
    · have h2 : v ^ 2 ≤ u ^ 2 := by nlinarith
      have hH : xiRadialHazard v < xiRadialHazard u :=
        hmono (Set.mem_Ioi.mpr hv) (Set.mem_Ioi.mpr hu) h
      nlinarith
  exact mul_nonneg (mul_nonneg hfac (by positivity)) (by positivity)

/-- The covariance integrand is strictly positive off the diagonal. -/
theorem xiRadialCovarianceIntegrand_pos
    (hmono : StrictMonoOn xiRadialHazard (Set.Ioi (0 : ℝ)))
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    0 < xiRadialCovarianceIntegrand u v := by
  have hKu := riemannXiKernel_pos hu.le
  have hKv := riemannXiKernel_pos hv.le
  unfold xiRadialCovarianceIntegrand
  have hfac : 0 < (u ^ 2 - v ^ 2) *
      (xiRadialHazard u - xiRadialHazard v) := by
    rcases lt_or_gt_of_ne huv with h | h
    · have h2 : u ^ 2 < v ^ 2 := by nlinarith
      have hH : xiRadialHazard u < xiRadialHazard v :=
        hmono (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr hv) h
      nlinarith
    · have h2 : v ^ 2 < u ^ 2 := by nlinarith
      have hH : xiRadialHazard v < xiRadialHazard u :=
        hmono (Set.mem_Ioi.mpr hv) (Set.mem_Ioi.mpr hu) h
      nlinarith
  exact mul_pos (mul_pos hfac (by positivity)) (by positivity)

/-- Every vertical slice of the covariance integrand is integrable. -/
theorem integrable_covariance_slice {u : ℝ} :
    MeasureTheory.IntegrableOn
      (fun v : ℝ => xiRadialCovarianceIntegrand u v) (Set.Ioi 0) := by
  have hc1 : MeasureTheory.IntegrableOn
      (fun v : ℝ => u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
        (v ^ 2 * riemannXiKernel v)) (Set.Ioi 0) :=
    (xiThetaMoment_integrable 2).const_mul _
  have hc2 : MeasureTheory.IntegrableOn
      (fun v : ℝ => -(u ^ 2 * riemannXiKernel u * u ^ 2) *
        (v ^ 2 * riemannXiKernel v * xiRadialHazard v)) (Set.Ioi 0) :=
    integrable_sq_mul_xiKernel_hazard.const_mul _
  have hc3 : MeasureTheory.IntegrableOn
      (fun v : ℝ => -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
        (v ^ 4 * riemannXiKernel v)) (Set.Ioi 0) :=
    (xiThetaMoment_integrable 4).const_mul _
  have hc4 : MeasureTheory.IntegrableOn
      (fun v : ℝ => u ^ 2 * riemannXiKernel u *
        (v ^ 4 * riemannXiKernel v * xiRadialHazard v)) (Set.Ioi 0) :=
    integrable_pow4_mul_xiKernel_hazard.const_mul _
  have heq : (fun v : ℝ => xiRadialCovarianceIntegrand u v) =
      fun v : ℝ =>
        u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v) +
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
          -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
            (v ^ 4 * riemannXiKernel v) +
          u ^ 2 * riemannXiKernel u *
            (v ^ 4 * riemannXiKernel v * xiRadialHazard v) := by
    funext v
    unfold xiRadialCovarianceIntegrand
    ring
  rw [heq]
  exact ((hc1.add hc2).add hc3).add hc4

/-- Every covariance slice has strictly positive integral under strict hazard
monotonicity. -/
theorem covariance_slice_pos
    (hmono : StrictMonoOn xiRadialHazard (Set.Ioi (0 : ℝ)))
    {u : ℝ} (hu : 0 < u) :
    0 < ∫ v in Set.Ioi (0 : ℝ), xiRadialCovarianceIntegrand u v := by
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun v : ℝ => xiRadialCovarianceIntegrand u v) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
    exact xiRadialCovarianceIntegrand_nonneg hmono hu hv
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnonneg
    integrable_covariance_slice]
  have hsub : Set.Ioo (u + 1) (u + 2) ⊆
      Function.support (fun v : ℝ => xiRadialCovarianceIntegrand u v) := by
    intro v hv
    have hvu : u < v := by linarith [hv.1]
    have hv0 : 0 < v := lt_trans hu hvu
    exact ne_of_gt (xiRadialCovarianceIntegrand_pos hmono hu hv0 hvu.ne)
  have hsub2 : Set.Ioo (u + 1) (u + 2) ⊆ Set.Ioi (0 : ℝ) := by
    intro v hv
    have : u + 1 < v := hv.1
    exact Set.mem_Ioi.mpr (by linarith)
  have hopen : 0 <
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (Set.Ioo (u + 1) (u + 2)) := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left hsub2, Real.volume_Ioo,
      show u + 2 - (u + 1) = 1 from by ring]
    simp
  exact hopen.trans_le (MeasureTheory.measure_mono hsub)

/-- Closed-form evaluation of every covariance slice (the inner integral). -/
theorem xiRadialCovariance_inner_eval : Set.EqOn
    (fun u : ℝ => ∫ v in Set.Ioi (0 : ℝ), xiRadialCovarianceIntegrand u v)
    (fun u : ℝ =>
      xiThetaMoment 2 * (u ^ 4 * riemannXiKernel u * xiRadialHazard u) +
        -(xiThetaMoment 0 / 2) * (u ^ 4 * riemannXiKernel u) +
        -xiThetaMoment 4 * (u ^ 2 * riemannXiKernel u * xiRadialHazard u) +
        3 * xiThetaMoment 2 / 2 * (u ^ 2 * riemannXiKernel u))
    (Set.Ioi 0) := by
  have hm2 : (∫ v in Set.Ioi (0 : ℝ), v ^ 2 * riemannXiKernel v) =
      xiThetaMoment 2 := rfl
  have hm4 : (∫ v in Set.Ioi (0 : ℝ), v ^ 4 * riemannXiKernel v) =
      xiThetaMoment 4 := rfl
  intro u _
  dsimp only
  have hc1 : MeasureTheory.IntegrableOn
      (fun v : ℝ => u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
        (v ^ 2 * riemannXiKernel v)) (Set.Ioi 0) :=
    (xiThetaMoment_integrable 2).const_mul _
  have hc2 : MeasureTheory.IntegrableOn
      (fun v : ℝ => -(u ^ 2 * riemannXiKernel u * u ^ 2) *
        (v ^ 2 * riemannXiKernel v * xiRadialHazard v)) (Set.Ioi 0) :=
    integrable_sq_mul_xiKernel_hazard.const_mul _
  have hc3 : MeasureTheory.IntegrableOn
      (fun v : ℝ => -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
        (v ^ 4 * riemannXiKernel v)) (Set.Ioi 0) :=
    (xiThetaMoment_integrable 4).const_mul _
  have hc4 : MeasureTheory.IntegrableOn
      (fun v : ℝ => u ^ 2 * riemannXiKernel u *
        (v ^ 4 * riemannXiKernel v * xiRadialHazard v)) (Set.Ioi 0) :=
    integrable_pow4_mul_xiKernel_hazard.const_mul _
  have heq : (fun v : ℝ => xiRadialCovarianceIntegrand u v) =
      fun v : ℝ =>
        u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v) +
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
          -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
            (v ^ 4 * riemannXiKernel v) +
          u ^ 2 * riemannXiKernel u *
            (v ^ 4 * riemannXiKernel v * xiRadialHazard v) := by
    funext v
    unfold xiRadialCovarianceIntegrand
    ring
  rw [heq,
    show (∫ v in Set.Ioi (0 : ℝ),
        (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v) +
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
          -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
            (v ^ 4 * riemannXiKernel v) +
          u ^ 2 * riemannXiKernel u *
            (v ^ 4 * riemannXiKernel v * xiRadialHazard v))) =
      (∫ v in Set.Ioi (0 : ℝ),
        (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v) +
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
          -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
            (v ^ 4 * riemannXiKernel v))) +
        ∫ v in Set.Ioi (0 : ℝ),
          u ^ 2 * riemannXiKernel u *
            (v ^ 4 * riemannXiKernel v * xiRadialHazard v) from
      MeasureTheory.integral_add ((hc1.add hc2).add hc3) hc4,
    show (∫ v in Set.Ioi (0 : ℝ),
        (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v) +
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v) +
          -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
            (v ^ 4 * riemannXiKernel v))) =
      (∫ v in Set.Ioi (0 : ℝ),
        (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v) +
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v))) +
        ∫ v in Set.Ioi (0 : ℝ),
          -(u ^ 2 * riemannXiKernel u * xiRadialHazard u) *
            (v ^ 4 * riemannXiKernel v) from
      MeasureTheory.integral_add (hc1.add hc2) hc3,
    show (∫ v in Set.Ioi (0 : ℝ),
        (u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
            (v ^ 2 * riemannXiKernel v) +
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v))) =
      (∫ v in Set.Ioi (0 : ℝ),
        u ^ 2 * riemannXiKernel u * (u ^ 2 * xiRadialHazard u) *
          (v ^ 2 * riemannXiKernel v)) +
        ∫ v in Set.Ioi (0 : ℝ),
          -(u ^ 2 * riemannXiKernel u * u ^ 2) *
            (v ^ 2 * riemannXiKernel v * xiRadialHazard v) from
      MeasureTheory.integral_add hc1 hc2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hm2, hm4, xiRadialHazard_weight_two, xiRadialHazard_weight_four]
  ring

/-- **Strict positivity of the covariance double integral** under strict
hazard monotonicity. -/
theorem xiRadialCovarianceIntegral_pos
    (hmono : StrictMonoOn xiRadialHazard (Set.Ioi (0 : ℝ))) :
    0 < ∫ u in Set.Ioi (0 : ℝ), ∫ v in Set.Ioi (0 : ℝ),
        xiRadialCovarianceIntegrand u v := by
  have houter_int : MeasureTheory.IntegrableOn
      (fun u : ℝ => ∫ v in Set.Ioi (0 : ℝ),
        xiRadialCovarianceIntegrand u v) (Set.Ioi 0) := by
    have hf1 : MeasureTheory.IntegrableOn
        (fun u : ℝ => xiThetaMoment 2 *
          (u ^ 4 * riemannXiKernel u * xiRadialHazard u)) (Set.Ioi 0) :=
      integrable_pow4_mul_xiKernel_hazard.const_mul _
    have hf2 : MeasureTheory.IntegrableOn
        (fun u : ℝ => -(xiThetaMoment 0 / 2) *
          (u ^ 4 * riemannXiKernel u)) (Set.Ioi 0) :=
      (xiThetaMoment_integrable 4).const_mul _
    have hf3 : MeasureTheory.IntegrableOn
        (fun u : ℝ => -xiThetaMoment 4 *
          (u ^ 2 * riemannXiKernel u * xiRadialHazard u)) (Set.Ioi 0) :=
      integrable_sq_mul_xiKernel_hazard.const_mul _
    have hf4 : MeasureTheory.IntegrableOn
        (fun u : ℝ => 3 * xiThetaMoment 2 / 2 *
          (u ^ 2 * riemannXiKernel u)) (Set.Ioi 0) :=
      (xiThetaMoment_integrable 2).const_mul _
    exact (((hf1.add hf2).add hf3).add hf4).congr_fun
      (fun u hu => (xiRadialCovariance_inner_eval hu).symm) measurableSet_Ioi
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun u : ℝ => ∫ v in Set.Ioi (0 : ℝ),
          xiRadialCovarianceIntegrand u v) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact (covariance_slice_pos hmono hu).le
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnonneg houter_int]
  have hsub : Set.Ioo (1 : ℝ) 2 ⊆
      Function.support (fun u : ℝ => ∫ v in Set.Ioi (0 : ℝ),
        xiRadialCovarianceIntegrand u v) := by
    intro u hu
    exact ne_of_gt (covariance_slice_pos hmono (lt_trans zero_lt_one hu.1))
  have hopen : 0 <
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (Set.Ioo (1 : ℝ) 2) := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo]
    norm_num [Set.Ioo_inter_Ioi]
  exact hopen.trans_le (MeasureTheory.measure_mono hsub)

/-- **Gate ⟹ strict central moment inequality**: numerator positivity forces
the third-moment Turán combination. -/
theorem xiThetaMoment_three_strict_of_numerator_pos
    (hpos : ∀ u : ℝ, 0 < u → 0 < xiRadialConcavityNumerator u) :
    xiThetaMoment 0 * xiThetaMoment 4 < 3 * xiThetaMoment 2 ^ 2 := by
  have hmono := xiRadialHazard_strictMonoOn_of_numerator_pos hpos
  have hpos' := xiRadialCovarianceIntegral_pos hmono
  have heval := xiRadialCovarianceIntegral_eq
  linarith

/-- The factorial-normalized central Xi coefficients.  With
`Ξ(t) = ∑ (-1)^k γ(k)t^(2k)/k!`, one has
`γ(k) = k! m_(2k)/(2k)!`. -/
def xiCentralCoeff (k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) * xiThetaMoment (2 * k) / (Nat.factorial (2 * k) : ℝ)

/-- The normalization audit at the first three central coefficients. -/
theorem xiCentralCoeff_zero_one_two :
    xiCentralCoeff 0 = xiThetaMoment 0 ∧
      xiCentralCoeff 1 = xiThetaMoment 2 / 2 ∧
      xiCentralCoeff 2 = xiThetaMoment 4 / 12 := by
  norm_num [xiCentralCoeff]
  ring

/-- The central coefficient Turán inequality implies the sharp moment bound
`m₀m₄ ≤ 3m₂²`, after the factorial normalization is carried out. -/
theorem centralTuran_implies_theta_moment_three
    (hTuran : xiCentralCoeff 0 * xiCentralCoeff 2 ≤ xiCentralCoeff 1 ^ 2) :
    xiThetaMoment 0 * xiThetaMoment 4 ≤ 3 * xiThetaMoment 2 ^ 2 := by
  rcases xiCentralCoeff_zero_one_two with ⟨h0, h1, h2⟩
  rw [h0, h1, h2] at hTuran
  nlinarith

/-- The strict central Turán inequality, unfolded exactly to the corresponding
raw moment inequality. -/
theorem xiCentralTuran_iff_theta_moment_three :
    xiCentralCoeff 0 * xiCentralCoeff 2 < xiCentralCoeff 1 ^ 2 ↔
      xiThetaMoment 0 * xiThetaMoment 4 < 3 * xiThetaMoment 2 ^ 2 := by
  rcases xiCentralCoeff_zero_one_two with ⟨h0, h1, h2⟩
  rw [h0, h1, h2]
  constructor <;> intro h <;> nlinarith

/-! ## 1. The finite Wronskian hierarchy -/

/-- The determinant definition of the Wronskian of a finite polynomial family. -/
def polynomialWronskian (n : ℕ) (p : Fin n → ℝ[X]) : ℝ[X] :=
  Matrix.det fun i j => Polynomial.derivative^[i.1] (p j)

/-- A real polynomial has all of its complex zeros on the imaginary axis. -/
def AllZerosImaginary (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, Polynomial.eval₂ Complex.ofRealHom z p = 0 → z.re = 0

/-- The first monic polynomial for an even moment functional. -/
def thetaP1 : ℝ[X] := X

/-- The second monic polynomial, where `a = m₂ / m₀`. -/
def thetaP2 (a : ℝ) : ℝ[X] := X ^ 2 - C a

/-- The third monic polynomial, where `b = m₄ / m₂`. -/
def thetaP3 (b : ℝ) : ℝ[X] := X ^ 3 - C b * X

/-- The fourth monic polynomial for an even moment functional. -/
def thetaP4 (c d : ℝ) : ℝ[X] := X ^ 4 - C c * X ^ 2 + C d

/-- The fifth monic polynomial for an even moment functional. -/
def thetaP5 (e f : ℝ) : ℝ[X] := X ^ 5 - C e * X ^ 3 + C f * X

/-- The three-function Wronskian, expanded along its first row. -/
def wronskianThree (p q r : ℝ[X]) : ℝ[X] :=
  p * (derivative q * derivative^[2] r - derivative r * derivative^[2] q) -
  q * (derivative p * derivative^[2] r - derivative r * derivative^[2] p) +
  r * (derivative p * derivative^[2] q - derivative q * derivative^[2] p)

/-- An iterated-derivative `3 × 3` minor. -/
def jetDetThree (k : ℕ) (p q r : ℝ[X]) : ℝ[X] :=
  derivative^[k] p *
      (derivative^[k + 1] q * derivative^[k + 2] r -
       derivative^[k + 1] r * derivative^[k + 2] q) -
  derivative^[k] q *
      (derivative^[k + 1] p * derivative^[k + 2] r -
       derivative^[k + 1] r * derivative^[k + 2] p) +
  derivative^[k] r *
      (derivative^[k + 1] p * derivative^[k + 2] q -
       derivative^[k + 1] q * derivative^[k + 2] p)

/-- The four-function Wronskian, expanded along its first row. -/
def wronskianFour (p q r s : ℝ[X]) : ℝ[X] :=
  p * jetDetThree 1 q r s - q * jetDetThree 1 p r s +
    r * jetDetThree 1 p q s - s * jetDetThree 1 p q r

/-- An iterated-derivative `4 × 4` minor, expanded along its first row. -/
def jetDetFour (k : ℕ) (p q r s : ℝ[X]) : ℝ[X] :=
  derivative^[k] p * jetDetThree (k + 1) q r s -
    derivative^[k] q * jetDetThree (k + 1) p r s +
    derivative^[k] r * jetDetThree (k + 1) p q s -
    derivative^[k] s * jetDetThree (k + 1) p q r

/-- The five-function Wronskian, expanded along its first row. -/
def wronskianFive (p q r s t : ℝ[X]) : ℝ[X] :=
  p * jetDetFour 1 q r s t - q * jetDetFour 1 p r s t +
    r * jetDetFour 1 p q s t - s * jetDetFour 1 p q r t +
    t * jetDetFour 1 p q r s

/-- The first finite theta Wronskian is `X`. -/
theorem theta_wronskian_one : AllZerosImaginary thetaP1 := by
  intro z hz
  have hz0 : z = 0 := by simpa [thetaP1] using hz
  simp [hz0]

/-- Exact level-two identity: the parameter is the positive variance `a`. -/
theorem theta_wronskian_two_formula (a : ℝ) :
    Polynomial.wronskian thetaP1 (thetaP2 a) = X ^ 2 + C a := by
  simp [Polynomial.wronskian, thetaP1, thetaP2]
  ring

/-- Exact level-three identity.  The fourth-moment coefficient `b` cancels. -/
theorem theta_wronskian_three_formula (a b : ℝ) :
    wronskianThree thetaP1 (thetaP2 a) (thetaP3 b) =
      2 * X * (X ^ 2 + 3 * C a) := by
  simp [wronskianThree, thetaP1, thetaP2, thetaP3,
    Function.iterate_succ_apply']
  have hC2 : C (2 : ℝ) = (2 : ℝ[X]) :=
    map_natCast (Polynomial.C : ℝ →+* ℝ[X]) 2
  rw [hC2]
  ring

/-- Exact level-four identity.  The odd coefficient `b` cancels; the first new
quantity is `a*c-d`. -/
theorem theta_wronskian_four_formula (a b c d : ℝ) :
    wronskianFour thetaP1 (thetaP2 a) (thetaP3 b) (thetaP4 c d) =
      12 * (X ^ 4 + 6 * C a * X ^ 2 + C (a * c - d)) := by
  simp [wronskianFour, jetDetThree, thetaP1, thetaP2, thetaP3, thetaP4,
    Function.iterate_succ_apply']
  have hC2 : C (2 : ℝ) = (2 : ℝ[X]) :=
    map_natCast (Polynomial.C : ℝ →+* ℝ[X]) 2
  have hC3 : C (3 : ℝ) = (3 : ℝ[X]) :=
    map_natCast (Polynomial.C : ℝ →+* ℝ[X]) 3
  rw [hC2, hC3]
  ring

/-- A quadratic `z² + a` with `a > 0` has purely imaginary zeros. -/
theorem quadratic_zero_realPart {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ^ 2 + (a : ℂ) = 0) : z.re = 0 := by
  have him := congrArg Complex.im hz
  have hre := congrArg Complex.re hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hprod : z.re * z.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h | h
  · exact h
  · nlinarith [sq_nonneg z.re]

/-- TW at level two, using only positivity of the variance. -/
theorem theta_wronskian_two (a : ℝ) (ha : 0 < a) :
    AllZerosImaginary (X ^ 2 + C a) := by
  intro z hz
  simp at hz
  exact quadratic_zero_realPart ha hz

/-- TW at level three, again using only positivity of the variance. -/
theorem theta_wronskian_three (a : ℝ) (ha : 0 < a) :
    AllZerosImaginary (2 * X * (X ^ 2 + 3 * C a)) := by
  intro z hz
  simp only [eval₂_mul, eval₂_ofNat, eval₂_X, eval₂_add, eval₂_pow,
    eval₂_C] at hz
  rcases mul_eq_zero.mp hz with hzlin | hzq
  · rcases mul_eq_zero.mp hzlin with h2 | hz0
    · norm_num at h2
    · simp [hz0]
  · apply quadratic_zero_realPart (by positivity : 0 < 3 * a)
    simpa using hzq

/-- A quartic `z⁴ + 6 a z² + q` has purely imaginary zeros under the exact
level-four moment inequality `q ≤ 9a²`. -/
theorem quartic_zero_realPart {a q : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hk : q ≤ 9 * a ^ 2) {z : ℂ}
    (hz : z ^ 4 + (6 * a : ℂ) * z ^ 2 + (q : ℂ) = 0) :
    z.re = 0 := by
  let y : ℂ := z ^ 2
  have hy : y ^ 2 + (6 * a : ℂ) * y + (q : ℂ) = 0 := by
    dsimp [y]
    calc
      (z ^ 2) ^ 2 + (6 * a : ℂ) * z ^ 2 + (q : ℂ)
          = z ^ 4 + (6 * a : ℂ) * z ^ 2 + (q : ℂ) := by ring
      _ = 0 := hz
  have hyim := congrArg Complex.im hy
  have hyre := congrArg Complex.re hy
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hyim hyre
  have hy_im_zero : y.im = 0 := by
    by_contra hne
    have hfactor : (y.re + 3 * a) * y.im = 0 := by nlinarith
    have hre : y.re = -3 * a := by
      rcases mul_eq_zero.mp hfactor with h | h
      · linarith
      · exact absurd h hne
    have hyimpos : 0 < y.im ^ 2 := sq_pos_of_ne_zero hne
    nlinarith
  have hy_re_neg : y.re < 0 := by
    nlinarith [sq_nonneg y.re]
  have hydef_re : y.re = z.re ^ 2 - z.im ^ 2 := by
    simp [y, pow_two, Complex.mul_re]
  have hydef_im : y.im = 2 * z.re * z.im := by
    simp [y, pow_two, Complex.mul_im]
    ring
  have hprod : z.re * z.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h | h
  · exact h
  · nlinarith [sq_nonneg z.re]

/-- TW at level four, isolated at its precise fourth-moment inequality. -/
theorem theta_wronskian_four (a q : ℝ)
    (ha : 0 < a) (hq : 0 < q) (hk : q ≤ 9 * a ^ 2) :
    AllZerosImaginary (X ^ 4 + 6 * C a * X ^ 2 + C q) := by
  intro z hz
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_ofNat,
    eval₂_C] at hz
  apply quartic_zero_realPart ha hq hk
  simpa [mul_assoc] using hz

/-- Orthogonality of `p₄` identifies its Wronskian constant with `m₄/m₀`. -/
theorem thetaP4_wronskian_constant
    {m0 m2 m4 c d : ℝ} (hm0 : m0 ≠ 0)
    (horth : m4 - c * m2 + d * m0 = 0) :
    (m2 / m0) * c - d = m4 / m0 := by
  field_simp
  nlinarith

/-- Moment form of the exact level-four gate. -/
theorem theta_fourth_moment_gate
    {m0 m2 m4 : ℝ} (hm0 : 0 < m0)
    (hk : m0 * m4 ≤ 9 * m2 ^ 2) :
    m4 / m0 ≤ 9 * (m2 / m0) ^ 2 := by
  have hm0sq : 0 < m0 ^ 2 := sq_pos_of_pos hm0
  apply (div_le_iff₀ hm0).2
  rw [div_pow]
  field_simp
  nlinarith

/-- Level four stated directly from the first three even theta moments. -/
theorem finite_theta_wronskian_level_four
    {m0 m2 m4 : ℝ} (hm0 : 0 < m0) (hm2 : 0 < m2) (hm4 : 0 < m4)
    (hk : m0 * m4 ≤ 9 * m2 ^ 2) :
    AllZerosImaginary
      (X ^ 4 + 6 * C (m2 / m0) * X ^ 2 + C (m4 / m0)) := by
  exact theta_wronskian_four _ _ (div_pos hm2 hm0) (div_pos hm4 hm0)
    (theta_fourth_moment_gate hm0 hk)

/-- The normalized level-five Leclerc/Jensen moment polynomial.  Under
Leclerc's determinant identity this is the level-five theta Wronskian up to a
nonzero scalar. -/
def thetaMomentQ5 (a q : ℝ) : ℝ[X] :=
  X * (X ^ 4 + 10 * C a * X ^ 2 + 5 * C q)

private theorem theta_jetDetFour_2345 (a b c d e f : ℝ) :
    jetDetFour 1 (thetaP2 a) (thetaP3 b) (thetaP4 c d) (thetaP5 e f) =
      288 * (C (b * e) + 10 * C b * X ^ 2 - C f + 5 * X ^ 4) := by
  simp [jetDetFour, jetDetThree, thetaP2, thetaP3, thetaP4, thetaP5,
    Function.iterate_succ_apply']
  norm_num [map_ofNat]
  ring

private theorem theta_jetDetFour_1345 (b c d e f : ℝ) :
    jetDetFour 1 thetaP1 (thetaP3 b) (thetaP4 c d) (thetaP5 e f) =
      1440 * X * (C c + 2 * X ^ 2) := by
  simp [jetDetFour, jetDetThree, thetaP1, thetaP3, thetaP4, thetaP5,
    Function.iterate_succ_apply']
  norm_num [map_ofNat]
  ring

private theorem theta_jetDetFour_1245 (a c d e f : ℝ) :
    jetDetFour 1 thetaP1 (thetaP2 a) (thetaP4 c d) (thetaP5 e f) =
      288 * (C e + 10 * X ^ 2) := by
  simp [jetDetFour, jetDetThree, thetaP1, thetaP2, thetaP4, thetaP5,
    Function.iterate_succ_apply']
  norm_num [map_ofNat]
  ring

private theorem theta_jetDetFour_1235 (a b e f : ℝ) :
    jetDetFour 1 thetaP1 (thetaP2 a) (thetaP3 b) (thetaP5 e f) =
      1440 * X := by
  simp [jetDetFour, jetDetThree, thetaP1, thetaP2, thetaP3, thetaP5,
    Function.iterate_succ_apply']
  norm_num [map_ofNat]
  ring

private theorem theta_jetDetFour_1234 (a b c d : ℝ) :
    jetDetFour 1 thetaP1 (thetaP2 a) (thetaP3 b) (thetaP4 c d) = 288 := by
  simp [jetDetFour, jetDetThree, thetaP1, thetaP2, thetaP3, thetaP4,
    Function.iterate_succ_apply']
  norm_num [map_ofNat]

/-- Exact level-five determinant identity.  The coefficients of `p₃` and
`p₅` cancel, and the remaining constant is the same `a*c-d` already selected
by level-four orthogonality. -/
theorem theta_wronskian_five_formula (a b c d e f : ℝ) :
    wronskianFive thetaP1 (thetaP2 a) (thetaP3 b) (thetaP4 c d)
        (thetaP5 e f) =
      288 * thetaMomentQ5 a (a * c - d) := by
  rw [wronskianFive, theta_jetDetFour_2345, theta_jetDetFour_1345,
    theta_jetDetFour_1245, theta_jetDetFour_1235, theta_jetDetFour_1234]
  simp only [thetaP1, thetaP2, thetaP3, thetaP4, thetaP5, thetaMomentQ5]
  simp only [map_mul, map_sub]
  ring

/-- Root calculation for the level-five moment polynomial.  Its first new
condition is the exact quadratic-discriminant gate `q ≤ 5 a²`. -/
theorem theta_moment_level_five (a q : ℝ)
    (ha : 0 < a) (hq : 0 < q) (hdisc : q ≤ 5 * a ^ 2) :
    AllZerosImaginary (thetaMomentQ5 a q) := by
  intro z hz
  have hz' : z * (z ^ 4 + 10 * (a : ℂ) * z ^ 2 + 5 * (q : ℂ)) = 0 := by
    simpa [thetaMomentQ5] using hz
  rcases mul_eq_zero.mp hz' with hz0 | hz4
  · simp [hz0]
  · apply quartic_zero_realPart (a := 5 * a / 3) (q := 5 * q)
    · positivity
    · positivity
    · nlinarith [sq_nonneg a]
    · have hcoeff :
          z ^ 4 + 6 * ((5 * a / 3 : ℝ) : ℂ) * z ^ 2 + ((5 * q : ℝ) : ℂ) =
            z ^ 4 + 10 * (a : ℂ) * z ^ 2 + 5 * (q : ℂ) := by
        push_cast
        ring
      rw [hcoeff]
      exact hz4

/-- TW at level five, now stated for the literal five-function Wronskian. -/
theorem theta_wronskian_five (a b c d e f : ℝ)
    (ha : 0 < a) (hq : 0 < a * c - d)
    (hdisc : a * c - d ≤ 5 * a ^ 2) :
    AllZerosImaginary
      (wronskianFive thetaP1 (thetaP2 a) (thetaP3 b) (thetaP4 c d)
        (thetaP5 e f)) := by
  rw [theta_wronskian_five_formula]
  intro z hz
  apply theta_moment_level_five a (a * c - d) ha hq hdisc z
  simpa using hz

/-- Level five stated directly from the first three even theta moments. -/
theorem finite_theta_wronskian_level_five
    {m0 m2 m4 : ℝ} (hm0 : 0 < m0) (hm2 : 0 < m2) (hm4 : 0 < m4)
    (hk : m0 * m4 ≤ 5 * m2 ^ 2) :
    AllZerosImaginary (thetaMomentQ5 (m2 / m0) (m4 / m0)) := by
  apply theta_moment_level_five
  · exact div_pos hm2 hm0
  · exact div_pos hm4 hm0
  · have hm0sq : 0 < m0 ^ 2 := sq_pos_of_pos hm0
    apply (div_le_iff₀ hm0).2
    rw [div_pow]
    field_simp
    nlinarith

/-- Level five for the literal Wronskian, with orthogonality identifying
`a*c-d` with the normalized fourth moment. -/
theorem finite_theta_wronskian_level_five_literal
    {m0 m2 m4 b c d e f : ℝ}
    (hm0 : 0 < m0) (hm2 : 0 < m2) (hm4 : 0 < m4)
    (horth : m4 - c * m2 + d * m0 = 0)
    (hk : m0 * m4 ≤ 5 * m2 ^ 2) :
    AllZerosImaginary
      (wronskianFive thetaP1 (thetaP2 (m2 / m0)) (thetaP3 b)
        (thetaP4 c d) (thetaP5 e f)) := by
  have hconst : (m2 / m0) * c - d = m4 / m0 :=
    thetaP4_wronskian_constant hm0.ne' horth
  apply theta_wronskian_five
  · exact div_pos hm2 hm0
  · rw [hconst]
    exact div_pos hm4 hm0
  · rw [hconst]
    have hm0sq : 0 < m0 ^ 2 := sq_pos_of_pos hm0
    apply (div_le_iff₀ hm0).2
    rw [div_pow]
    field_simp
    nlinarith

/-- Positivity of the theta mass and second moment makes their ratio positive. -/
theorem theta_variance_pos {m0 m2 : ℝ} (hm0 : 0 < m0) (hm2 : 0 < m2) :
    0 < m2 / m0 := div_pos hm2 hm0

/-- The first three finite Wronskian conclusions, expressed from moments. -/
theorem finite_theta_wronskian_levels_one_to_three
    {m0 m2 : ℝ} (hm0 : 0 < m0) (hm2 : 0 < m2) :
    AllZerosImaginary thetaP1 ∧
      AllZerosImaginary (X ^ 2 + C (m2 / m0)) ∧
      AllZerosImaginary (2 * X * (X ^ 2 + 3 * C (m2 / m0))) := by
  have ha : 0 < m2 / m0 := theta_variance_pos hm0 hm2
  exact ⟨theta_wronskian_one, theta_wronskian_two _ ha,
    theta_wronskian_three _ ha⟩

/-- The first three finite Wronskian conclusions for the actual Riemann theta
moments, with no moment hypotheses remaining. -/
theorem riemann_theta_wronskian_levels_one_to_three :
    AllZerosImaginary thetaP1 ∧
      AllZerosImaginary
        (X ^ 2 + C (xiThetaMoment 2 / xiThetaMoment 0)) ∧
      AllZerosImaginary
        (2 * X * (X ^ 2 + 3 * C (xiThetaMoment 2 / xiThetaMoment 0))) := by
  exact finite_theta_wronskian_levels_one_to_three
    (xiThetaMoment_pos 0) (xiThetaMoment_pos 2)

/-- The central coefficient Turán inequality closes both nontrivial finite gates
at levels four and five: its normalized constant is `3`, while the two required
constants are respectively `9` and `5`. -/
theorem centralTuran_closes_theta_levels_four_and_five
    (hm0 : 0 < xiThetaMoment 0) (hm2 : 0 < xiThetaMoment 2)
    (hm4 : 0 < xiThetaMoment 4)
    (hTuran : xiCentralCoeff 0 * xiCentralCoeff 2 ≤ xiCentralCoeff 1 ^ 2) :
    AllZerosImaginary
        (X ^ 4 + 6 * C (xiThetaMoment 2 / xiThetaMoment 0) * X ^ 2 +
          C (xiThetaMoment 4 / xiThetaMoment 0)) ∧
      AllZerosImaginary
        (thetaMomentQ5 (xiThetaMoment 2 / xiThetaMoment 0)
          (xiThetaMoment 4 / xiThetaMoment 0)) := by
  have hthree := centralTuran_implies_theta_moment_three hTuran
  constructor
  · exact finite_theta_wronskian_level_four hm0 hm2 hm4 (by nlinarith)
  · exact finite_theta_wronskian_level_five hm0 hm2 hm4 (by nlinarith)

/-- For the actual Xi kernel, positivity and integrability are discharged.  The
conclusion is the literal level-four Wronskian polynomial together with the
normalized level-five polynomial appearing in the exact determinant identity
`theta_wronskian_five_formula`. -/
theorem centralTuran_closes_actual_theta_levels_four_and_five
    (hTuran : xiCentralCoeff 0 * xiCentralCoeff 2 ≤ xiCentralCoeff 1 ^ 2) :
    AllZerosImaginary
        (X ^ 4 + 6 * C (xiThetaMoment 2 / xiThetaMoment 0) * X ^ 2 +
          C (xiThetaMoment 4 / xiThetaMoment 0)) ∧
      AllZerosImaginary
        (thetaMomentQ5 (xiThetaMoment 2 / xiThetaMoment 0)
          (xiThetaMoment 4 / xiThetaMoment 0)) := by
  exact centralTuran_closes_theta_levels_four_and_five
    (xiThetaMoment_pos 0) (xiThetaMoment_pos 2) (xiThetaMoment_pos 4) hTuran

/-! ## Phase G: the gate closes the central Turán inequality, TW 4, and the
level-five Leclerc/Jensen moment polynomial -/

/-- **Gate ⟹ the central Turán inequality** of the actual Xi function. -/
theorem xiCentralTuran_of_numerator_pos
    (hpos : ∀ u : ℝ, 0 < u → 0 < xiRadialConcavityNumerator u) :
    xiCentralCoeff 0 * xiCentralCoeff 2 < xiCentralCoeff 1 ^ 2 :=
  xiCentralTuran_iff_theta_moment_three.mpr
    (xiThetaMoment_three_strict_of_numerator_pos hpos)

/-- **Gate ⟹ TW 4 plus the normalized level-five polynomial**: positivity of
the scalar concavity numerator closes the two displayed polynomial targets. -/
theorem theta_wronskian_levels_four_five_of_numerator_pos
    (hpos : ∀ u : ℝ, 0 < u → 0 < xiRadialConcavityNumerator u) :
    AllZerosImaginary
        (X ^ 4 + 6 * C (xiThetaMoment 2 / xiThetaMoment 0) * X ^ 2 +
          C (xiThetaMoment 4 / xiThetaMoment 0)) ∧
      AllZerosImaginary
        (thetaMomentQ5 (xiThetaMoment 2 / xiThetaMoment 0)
          (xiThetaMoment 4 / xiThetaMoment 0)) :=
  centralTuran_closes_actual_theta_levels_four_and_five
    (xiCentralTuran_of_numerator_pos hpos).le

/-- **Gate ⟹ the five normalized polynomial targets at once.** -/
theorem theta_wronskian_levels_one_to_five_of_numerator_pos
    (hpos : ∀ u : ℝ, 0 < u → 0 < xiRadialConcavityNumerator u) :
    (AllZerosImaginary thetaP1 ∧
      AllZerosImaginary (X ^ 2 + C (xiThetaMoment 2 / xiThetaMoment 0)) ∧
      AllZerosImaginary
        (2 * X * (X ^ 2 + 3 * C (xiThetaMoment 2 / xiThetaMoment 0)))) ∧
      AllZerosImaginary
        (X ^ 4 + 6 * C (xiThetaMoment 2 / xiThetaMoment 0) * X ^ 2 +
          C (xiThetaMoment 4 / xiThetaMoment 0)) ∧
      AllZerosImaginary
        (thetaMomentQ5 (xiThetaMoment 2 / xiThetaMoment 0)
          (xiThetaMoment 4 / xiThetaMoment 0)) :=
  ⟨riemann_theta_wronskian_levels_one_to_three,
    (theta_wronskian_levels_four_five_of_numerator_pos hpos).1,
    (theta_wronskian_levels_four_five_of_numerator_pos hpos).2⟩

/-- **Gate ⟹ the literal level-five Wronskian** for every choice of the odd
orthogonal-polynomial coefficients and every level-four coefficient pair
satisfying its moment orthogonality equation. -/
theorem theta_wronskian_level_five_literal_of_numerator_pos
    {b c d e f : ℝ}
    (horth : xiThetaMoment 4 - c * xiThetaMoment 2 +
      d * xiThetaMoment 0 = 0)
    (hpos : ∀ u : ℝ, 0 < u → 0 < xiRadialConcavityNumerator u) :
    AllZerosImaginary
      (wronskianFive thetaP1
        (thetaP2 (xiThetaMoment 2 / xiThetaMoment 0)) (thetaP3 b)
        (thetaP4 c d) (thetaP5 e f)) := by
  apply finite_theta_wronskian_level_five_literal
    (xiThetaMoment_pos 0) (xiThetaMoment_pos 2) (xiThetaMoment_pos 4) horth
  nlinarith [xiThetaMoment_three_strict_of_numerator_pos hpos]

/-! ## Phase H (opening): half-line and even-moment Hankel matrices -/

/-- The Hankel matrix of the actual Xi-kernel half-line moments. -/
def xiMomentMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => xiThetaMoment ((i : ℕ) + (j : ℕ))

/-- The moment matrix is Hermitian. -/
theorem xiMomentMatrix_isHermitian (N : ℕ) :
    (xiMomentMatrix N).IsHermitian := by
  ext i j
  simp [xiMomentMatrix, Matrix.conjTranspose_apply, add_comm]

/-- Energy identity: the moment quadratic form is the half-line integral of
the squared test polynomial against the kernel. -/
theorem xiMomentMatrix_energy (N : ℕ) (c : Fin N → ℝ) :
    c ⬝ᵥ (xiMomentMatrix N).mulVec c =
      ∫ u in Set.Ioi (0 : ℝ),
        (∑ i : Fin N, c i * u ^ (i : ℕ)) ^ 2 * riemannXiKernel u := by
  have hlhs : c ⬝ᵥ (xiMomentMatrix N).mulVec c =
      ∑ i : Fin N, ∑ j : Fin N,
        c i * c j * xiThetaMoment ((i : ℕ) + (j : ℕ)) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [xiMomentMatrix, Matrix.of_apply]
    ring
  have hpoint : Set.EqOn
      (fun u : ℝ =>
        (∑ i : Fin N, c i * u ^ (i : ℕ)) ^ 2 * riemannXiKernel u)
      (fun u : ℝ => ∑ i : Fin N, ∑ j : Fin N,
        c i * c j * (u ^ ((i : ℕ) + (j : ℕ)) * riemannXiKernel u))
      (Set.Ioi 0) := by
    intro u _
    dsimp only
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  have hinner : ∀ i : Fin N, ∀ j : Fin N, MeasureTheory.IntegrableOn
      (fun u : ℝ => c i * c j *
        (u ^ ((i : ℕ) + (j : ℕ)) * riemannXiKernel u)) (Set.Ioi 0) :=
    fun i j => (xiThetaMoment_integrable ((i : ℕ) + (j : ℕ))).const_mul _
  have houter : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun u : ℝ => ∑ j : Fin N, c i * c j *
        (u ^ ((i : ℕ) + (j : ℕ)) * riemannXiKernel u)) (Set.Ioi 0) :=
    fun i => MeasureTheory.integrable_finsetSum _ (fun j _ => hinner i j)
  rw [hlhs, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint,
    MeasureTheory.integral_finsetSum _ (fun i _ => houter i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => hinner i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- The test polynomial attached to a coefficient vector. -/
def xiTestPolynomial (N : ℕ) (c : Fin N → ℝ) : ℝ[X] :=
  ∑ i : Fin N, C (c i) * X ^ (i : ℕ)

/-- Coefficient audit for the test polynomial. -/
theorem xiTestPolynomial_coeff (N : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    (xiTestPolynomial N c).coeff (i : ℕ) = c i := by
  unfold xiTestPolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.val_injective h.symm)
    simp [Polynomial.coeff_X_pow, hne]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Evaluation audit for the test polynomial. -/
theorem xiTestPolynomial_eval (N : ℕ) (c : Fin N → ℝ) (u : ℝ) :
    (xiTestPolynomial N c).eval u = ∑ i : Fin N, c i * u ^ (i : ℕ) := by
  unfold xiTestPolynomial
  simp [Polynomial.eval_finsetSum]

/-- **The Hankel moment matrix of the Xi kernel is positive definite** at
every finite size. -/
theorem xiMomentMatrix_posDef (N : ℕ) : (xiMomentMatrix N).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨xiMomentMatrix_isHermitian N, ?_⟩
  intro c hc
  have henergy := xiMomentMatrix_energy N c
  obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (_root_.funext h)
  have hPne : xiTestPolynomial N c ≠ 0 := by
    intro hP0
    apply hi0
    rw [← xiTestPolynomial_coeff N c i0, hP0, Polynomial.coeff_zero]
  have hroots : {x : ℝ | (xiTestPolynomial N c).IsRoot x}.Finite := by
    apply Set.Finite.ofFinset (xiTestPolynomial N c).roots.toFinset
    intro x
    simp [Multiset.mem_toFinset, Polynomial.mem_roots', hPne]
  have hintegrand_nonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun u : ℝ =>
          (∑ i : Fin N, c i * u ^ (i : ℕ)) ^ 2 * riemannXiKernel u) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (sq_nonneg _) (riemannXiKernel_nonneg hu.le)
  have hintegrable : MeasureTheory.IntegrableOn
      (fun u : ℝ =>
        (∑ i : Fin N, c i * u ^ (i : ℕ)) ^ 2 * riemannXiKernel u)
      (Set.Ioi 0) := by
    have hinner : ∀ i : Fin N, ∀ j : Fin N, MeasureTheory.IntegrableOn
        (fun u : ℝ => c i * c j *
          (u ^ ((i : ℕ) + (j : ℕ)) * riemannXiKernel u)) (Set.Ioi 0) :=
      fun i j => (xiThetaMoment_integrable ((i : ℕ) + (j : ℕ))).const_mul _
    have hsum : MeasureTheory.IntegrableOn
        (fun u : ℝ => ∑ i : Fin N, ∑ j : Fin N, c i * c j *
          (u ^ ((i : ℕ) + (j : ℕ)) * riemannXiKernel u)) (Set.Ioi 0) :=
      MeasureTheory.integrable_finsetSum _ (fun i _ =>
        MeasureTheory.integrable_finsetSum _ (fun j _ => hinner i j))
    have hpoint : Set.EqOn
        (fun u : ℝ =>
          (∑ i : Fin N, c i * u ^ (i : ℕ)) ^ 2 * riemannXiKernel u)
        (fun u : ℝ => ∑ i : Fin N, ∑ j : Fin N,
          c i * c j * (u ^ ((i : ℕ) + (j : ℕ)) * riemannXiKernel u))
        (Set.Ioi 0) := by
      intro u _
      dsimp only
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    exact hsum.congr_fun (fun u hu => (hpoint hu).symm) measurableSet_Ioi
  have hpos : 0 < ∫ u in Set.Ioi (0 : ℝ),
      (∑ i : Fin N, c i * u ^ (i : ℕ)) ^ 2 * riemannXiKernel u := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      hintegrand_nonneg hintegrable]
    have hsub : Set.Ioo (1 : ℝ) 2 \
        {x : ℝ | (xiTestPolynomial N c).IsRoot x} ⊆
        Function.support (fun u : ℝ =>
          (∑ i : Fin N, c i * u ^ (i : ℕ)) ^ 2 * riemannXiKernel u) := by
      intro u hu
      have hu0 : 0 < u := lt_trans zero_lt_one hu.1.1
      have hne : (∑ i : Fin N, c i * u ^ (i : ℕ)) ≠ 0 := by
        intro h0
        apply hu.2
        show (xiTestPolynomial N c).IsRoot u
        unfold Polynomial.IsRoot
        rw [xiTestPolynomial_eval]
        exact h0
      exact ne_of_gt (mul_pos (by positivity) (riemannXiKernel_pos hu0.le))
    have hzero : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        {x : ℝ | (xiTestPolynomial N c).IsRoot x} = 0 := by
      rw [MeasureTheory.Measure.restrict_apply hroots.measurableSet]
      exact MeasureTheory.measure_mono_null Set.inter_subset_left
        (hroots.measure_zero _)
    have hIoo : 0 < (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (Set.Ioo (1 : ℝ) 2) := by
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo]
      norm_num [Set.Ioo_inter_Ioi]
    have hdiff : 0 < (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (Set.Ioo (1 : ℝ) 2 \
          {x : ℝ | (xiTestPolynomial N c).IsRoot x}) := by
      rw [MeasureTheory.measure_sdiff_null hzero]
      exact hIoo
    exact hdiff.trans_le (MeasureTheory.measure_mono hsub)
  have hgoal : (0 : ℝ) < c ⬝ᵥ (xiMomentMatrix N).mulVec c := by
    rw [henergy]
    exact hpos
  simpa using hgoal

/-- The embedding selecting the even rows and columns of the full half-line
moment matrix. -/
def xiEvenIndex (N : ℕ) (i : Fin N) : Fin (2 * N) :=
  ⟨2 * (i : ℕ), by omega⟩

/-- The even-index embedding is injective. -/
theorem xiEvenIndex_injective (N : ℕ) : Function.Injective (xiEvenIndex N) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [xiEvenIndex] at hval
  omega

/-- The Hankel matrix used by the theta hierarchy: its `(i,j)` entry is the
even moment `m_(2(i+j))`.  It is the even principal submatrix of the full
half-line Stieltjes moment matrix. -/
def xiEvenMomentMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (xiMomentMatrix (2 * N)).submatrix (xiEvenIndex N) (xiEvenIndex N)

/-- Entry audit for the theta even-moment matrix. -/
theorem xiEvenMomentMatrix_apply (N : ℕ) (i j : Fin N) :
    xiEvenMomentMatrix N i j =
      xiThetaMoment (2 * ((i : ℕ) + (j : ℕ))) := by
  simp only [xiEvenMomentMatrix, Matrix.submatrix_apply, xiMomentMatrix,
    Matrix.of_apply, xiEvenIndex]
  congr 1
  omega

/-- Energy identity for the actual theta even-moment matrix. -/
theorem xiEvenMomentMatrix_energy (N : ℕ) (c : Fin N → ℝ) :
    c ⬝ᵥ (xiEvenMomentMatrix N).mulVec c =
      ∫ u in Set.Ioi (0 : ℝ),
        (∑ i : Fin N, c i * u ^ (2 * (i : ℕ))) ^ 2 *
          riemannXiKernel u := by
  have hlhs : c ⬝ᵥ (xiEvenMomentMatrix N).mulVec c =
      ∑ i : Fin N, ∑ j : Fin N,
        c i * c j * xiThetaMoment (2 * ((i : ℕ) + (j : ℕ))) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [xiEvenMomentMatrix_apply]
    ring
  have hpoint : Set.EqOn
      (fun u : ℝ =>
        (∑ i : Fin N, c i * u ^ (2 * (i : ℕ))) ^ 2 * riemannXiKernel u)
      (fun u : ℝ => ∑ i : Fin N, ∑ j : Fin N,
        c i * c j *
          (u ^ (2 * ((i : ℕ) + (j : ℕ))) * riemannXiKernel u))
      (Set.Ioi 0) := by
    intro u _
    dsimp only
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [show 2 * ((i : ℕ) + (j : ℕ)) =
      2 * (i : ℕ) + 2 * (j : ℕ) by omega, pow_add]
    ring
  have hinner : ∀ i : Fin N, ∀ j : Fin N, MeasureTheory.IntegrableOn
      (fun u : ℝ => c i * c j *
        (u ^ (2 * ((i : ℕ) + (j : ℕ))) * riemannXiKernel u))
      (Set.Ioi 0) :=
    fun i j =>
      (xiThetaMoment_integrable (2 * ((i : ℕ) + (j : ℕ)))).const_mul _
  have houter : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun u : ℝ => ∑ j : Fin N, c i * c j *
        (u ^ (2 * ((i : ℕ) + (j : ℕ))) * riemannXiKernel u))
      (Set.Ioi 0) :=
    fun i => MeasureTheory.integrable_finsetSum _ (fun j _ => hinner i j)
  rw [hlhs, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint,
    MeasureTheory.integral_finsetSum _ (fun i _ => houter i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => hinner i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- **The theta even-moment Hankel matrix is positive definite** at every
finite size. -/
theorem xiEvenMomentMatrix_posDef (N : ℕ) : (xiEvenMomentMatrix N).PosDef := by
  exact (xiMomentMatrix_posDef (2 * N)).submatrix (xiEvenIndex_injective N)

/-! ## 2. The independent finite Suzuki Gram hierarchy -/

/-- Suzuki's analysis symbol `P̂` is represented at operator level by the
Bochner integral of the analytic kernel vector `S t` against the test function.
The codomain `E` can later be instantiated by the relevant `L²` space. -/
def suzukiAnalysisIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ℝ → E) (φ : ℝ → ℝ) : E :=
  ∫ t, φ t • S t

/-- The actual integral analysis map commutes with every finite linear
combination of integrable test images. -/
theorem suzukiAnalysisIntegral_finset
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Fintype ι] (S : ℝ → E) (φ : ι → ℝ → ℝ) (c : ι → ℝ)
    (hint : ∀ i, MeasureTheory.Integrable (fun t => φ i t • S t)) :
    suzukiAnalysisIntegral S (fun t => ∑ i, c i * φ i t) =
      ∑ i, c i • suzukiAnalysisIntegral S (φ i) := by
  unfold suzukiAnalysisIntegral
  calc
    (∫ t, (∑ i, c i * φ i t) • S t) =
        ∫ t, ∑ i, c i • (φ i t • S t) := by
          congr 1
          funext t
          simp [Finset.sum_smul, smul_smul]
    _ = ∑ i, ∫ t, c i • (φ i t • S t) := by
          apply MeasureTheory.integral_finsetSum
          intro i hi
          refine ((hint i).smul (c i)).congr ?_
          filter_upwards with t
          simp only [Pi.smul_apply, smul_smul]
    _ = ∑ i, c i • ∫ t, φ i t • S t := by
          apply Finset.sum_congr rfl
          intro i hi
          exact MeasureTheory.integral_smul (c i) _

/-- The finite matrix generated by the genuine Suzuki integral transform is its
Gram matrix, with no projection substituted for `P̂`. -/
def suzukiIntegralGram
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (S : ℝ → E) (φ : ι → ℝ → ℝ) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun i => suzukiAnalysisIntegral S (φ i))

/-- Exact coefficient-energy identity for the integral Suzuki Gram matrix. -/
theorem suzukiIntegralGram_energy
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Fintype ι] (S : ℝ → E) (φ : ι → ℝ → ℝ)
    (c : ι → ℝ)
    (hint : ∀ i, MeasureTheory.Integrable (fun t => φ i t • S t)) :
    c ⬝ᵥ suzukiIntegralGram S φ *ᵥ c =
      ‖suzukiAnalysisIntegral S (fun t => ∑ i, c i * φ i t)‖ ^ 2 := by
  calc
    c ⬝ᵥ suzukiIntegralGram S φ *ᵥ c =
        inner ℝ (∑ i, c i • suzukiAnalysisIntegral S (φ i))
          (∑ i, c i • suzukiAnalysisIntegral S (φ i)) := by
            simpa only [suzukiIntegralGram, star_trivial] using
              (Matrix.star_dotProduct_gram_mulVec
                (fun i => suzukiAnalysisIntegral S (φ i)) c c)
    _ = ‖∑ i, c i • suzukiAnalysisIntegral S (φ i)‖ ^ 2 :=
          real_inner_self_eq_norm_sq _
    _ = ‖suzukiAnalysisIntegral S (fun t => ∑ i, c i * φ i t)‖ ^ 2 := by
          rw [suzukiAnalysisIntegral_finset S φ c hint]

/-- The finite Gram defect `W - G`. -/
def gramDefect {ι : Type*} [Fintype ι]
    (W G : Matrix ι ι ℝ) : Matrix ι ι ℝ := W - G

/-- The finite Suzuki inequality for two Hermitian matrices. -/
def FiniteSuzukiGramInequality {ι : Type*} [Fintype ι]
    (W G : Matrix ι ι ℝ) : Prop :=
  ∀ c : ι → ℝ, c ⬝ᵥ G *ᵥ c ≤ c ⬝ᵥ W *ᵥ c

/-- SG is exactly positivity of the finite Gram defect. -/
theorem finiteSuzukiGram_iff_defect_posSemidef
    {ι : Type*} [Fintype ι] (W G : Matrix ι ι ℝ)
    (hW : W.IsHermitian) (hG : G.IsHermitian) :
    FiniteSuzukiGramInequality W G ↔ (gramDefect W G).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨hW.sub hG, ?_⟩
    intro c
    simp only [gramDefect, Matrix.sub_mulVec, dotProduct_sub, star_trivial]
    exact sub_nonneg.mpr (h c)
  · rintro ⟨_, h⟩ c
    have hc := h c
    simp only [gramDefect, Matrix.sub_mulVec, dotProduct_sub, star_trivial] at hc
    exact sub_nonneg.mp hc

/-- The analysis matrix of a finite family is a genuine Gram matrix and hence PSD. -/
theorem finiteSuzuki_analysisGram_posSemidef
    {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Finite ι] (analysis : ι → E) :
    (Matrix.gram ℝ analysis).PosSemidef :=
  Matrix.posSemidef_gram ℝ analysis

/-- The genuine integral Suzuki matrix is positive semidefinite because it is
literally a Gram matrix of Bochner-integral analysis vectors. -/
theorem suzukiIntegralGram_posSemidef
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (S : ℝ → E) (φ : ι → ℝ → ℝ) :
    (suzukiIntegralGram S φ).PosSemidef :=
  Matrix.posSemidef_gram ℝ (fun i => suzukiAnalysisIntegral S (φ i))

/-- Independent SG construction: a contractive factorization of the Suzuki
analysis family through the Weil family makes every finite Gram defect PSD.
This is the correct abstract target for Suzuki's integral transform. -/
theorem finiteSuzukiGram_of_contractive_factorization
    {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (u : ι → E) :
    (Matrix.gram ℝ u - Matrix.gram ℝ (fun i => T (u i))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_gram ℝ u).sub
      (Matrix.isHermitian_gram ℝ (fun i => T (u i)))) ?_
  intro c
  rw [Matrix.sub_mulVec, dotProduct_sub,
    Matrix.star_dotProduct_gram_mulVec,
    Matrix.star_dotProduct_gram_mulVec]
  have hmap :
      (∑ i, c i • T (u i)) = T (∑ i, c i • u i) := by
    simp
  rw [hmap]
  simp only [real_inner_self_eq_norm_sq]
  have hnorm : ‖T (∑ i, c i • u i)‖ ≤ ‖∑ i, c i • u i‖ := by
    calc
      ‖T (∑ i, c i • u i)‖ ≤ ‖T‖ * ‖∑ i, c i • u i‖ := T.le_opNorm _
      _ ≤ 1 * ‖∑ i, c i • u i‖ := by
        exact mul_le_mul_of_nonneg_right hT (norm_nonneg _)
      _ = ‖∑ i, c i • u i‖ := one_mul _
  nlinarith [hnorm, norm_nonneg (T (∑ i, c i • u i)),
    norm_nonneg (∑ i, c i • u i)]

/-- Operator-level SG for the genuine integral analysis map.  Once its values on
the finite test family are identified with a contraction of the Weil vectors,
the exact Suzuki Gram defect is positive semidefinite. -/
theorem suzukiIntegralGram_defect_of_contraction
    {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (u : ι → E)
    (S : ℝ → F) (φ : ι → ℝ → ℝ)
    (hidentify : ∀ i, suzukiAnalysisIntegral S (φ i) = T (u i)) :
    (Matrix.gram ℝ u - suzukiIntegralGram S φ).PosSemidef := by
  have hfamily :
      (fun i => suzukiAnalysisIntegral S (φ i)) = (fun i => T (u i)) :=
    funext hidentify
  rw [suzukiIntegralGram, hfamily]
  exact finiteSuzukiGram_of_contractive_factorization T hT u

/-- Coefficient form of SG for the genuine Suzuki integral transform. -/
theorem finiteSuzukiGram_integral_of_contraction
    {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (u : ι → E)
    (S : ℝ → F) (φ : ι → ℝ → ℝ)
    (hidentify : ∀ i, suzukiAnalysisIntegral S (φ i) = T (u i)) :
    FiniteSuzukiGramInequality (Matrix.gram ℝ u) (suzukiIntegralGram S φ) := by
  apply (finiteSuzukiGram_iff_defect_posSemidef _ _
    (Matrix.isHermitian_gram ℝ u)
    (Matrix.isHermitian_gram ℝ
      (fun i => suzukiAnalysisIntegral S (φ i)))).2
  exact suzukiIntegralGram_defect_of_contraction T hT u S φ hidentify

/-! ## 3. Galerkin/Toda discretization only -/

/-- Suzuki's multiplicative Hankel kernel before completion to an `L²` operator. -/
def suzukiHankelKernel (h : ℝ → ℝ) (x y : ℝ) : ℝ := h (x * y)

/-- The pointwise integral action of the Suzuki Hankel kernel on the positive
half-line. -/
def suzukiHankelAction (h f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), suzukiHankelKernel h x y * f y

/-- Multiplicative Hankel kernels are symmetric. -/
theorem suzukiHankelKernel_symm (h : ℝ → ℝ) (x y : ℝ) :
    suzukiHankelKernel h x y = suzukiHankelKernel h y x := by
  simp only [suzukiHankelKernel, mul_comm]

/-- The weighted Nyström/Galerkin matrix of the multiplicative Hankel kernel.
This is where a corrected finite pencil belongs. -/
def suzukiHankelGalerkin
    {ι : Type*} [Fintype ι] (h : ℝ → ℝ) (node weight : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => Real.sqrt (weight i) * Real.sqrt (weight j) *
    suzukiHankelKernel h (node i) (node j)

/-- Every weighted Galerkin matrix of Suzuki's Hankel kernel is symmetric. -/
theorem suzukiHankelGalerkin_isSymm
    {ι : Type*} [Fintype ι] (h : ℝ → ℝ) (node weight : ι → ℝ) :
    (suzukiHankelGalerkin h node weight).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [suzukiHankelGalerkin, suzukiHankelKernel]
  congr 1
  · ring
  · rw [mul_comm]

/-- Over the real field the same Galerkin matrix is Hermitian, as required by
the self-adjoint finite Fredholm approximants. -/
theorem suzukiHankelGalerkin_isHermitian
    {ι : Type*} [Fintype ι] (h : ℝ → ℝ) (node weight : ι → ℝ) :
    (suzukiHankelGalerkin h node weight).IsHermitian := by
  exact Matrix.isHermitian_iff_isSymm.mpr
    (suzukiHankelGalerkin_isSymm h node weight)

/-- Orthogonal compression gives the finite energy inequality used by a Galerkin model. -/
theorem galerkin_projection_energy
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (u : ι → E) (c : ι → ℝ) :
    ‖∑ i, c i • K.starProjection (u i)‖ ^ 2 ≤
      ‖∑ i, c i • u i‖ ^ 2 := by
  have hmap :
      (∑ i, c i • K.starProjection (u i)) =
        K.starProjection (∑ i, c i • u i) := by
    simp
  rw [hmap]
  nlinarith [K.norm_starProjection_apply_le (∑ i, c i • u i),
    norm_nonneg (K.starProjection (∑ i, c i • u i)),
    norm_nonneg (∑ i, c i • u i)]

/-- Matrix form of the Galerkin contraction: the original Gram matrix minus the
compressed Gram matrix is positive semidefinite. -/
theorem galerkin_gram_defect_posSemidef
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (u : ι → E) :
    (Matrix.gram ℝ u -
      Matrix.gram ℝ (fun i => K.starProjection (u i))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_gram ℝ u).sub
      (Matrix.isHermitian_gram ℝ (fun i => K.starProjection (u i)))) ?_
  intro c
  rw [Matrix.sub_mulVec, dotProduct_sub,
    Matrix.star_dotProduct_gram_mulVec,
    Matrix.star_dotProduct_gram_mulVec]
  have hmap :
      (∑ i, c i • K.starProjection (u i)) =
        K.starProjection (∑ i, c i • u i) := by
    simp
  rw [hmap]
  simp only [real_inner_self_eq_norm_sq]
  nlinarith [K.norm_starProjection_apply_le (∑ i, c i • u i),
    norm_nonneg (K.starProjection (∑ i, c i • u i)),
    norm_nonneg (∑ i, c i • u i)]

/-! ## 4. Fredholm bridge F1 -/

/-- Finite F1 for the actual Galerkin matrix: a strict matrix contraction makes
both signed Fredholm determinants nonzero. -/
theorem galerkin_fredholm_determinants_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : ‖A‖ < 1) :
    Matrix.det (1 - A) ≠ 0 ∧ Matrix.det (1 + A) ≠ 0 := by
  have hminus : IsUnit (1 - A) := isUnit_one_sub_of_norm_lt_one hA
  have hneg : ‖-A‖ < 1 := by simpa using hA
  have hplus : IsUnit (1 + A) := by
    simpa [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (x := -A) hneg)
  exact ⟨((Matrix.isUnit_iff_isUnit_det (1 - A)).mp hminus).ne_zero,
    ((Matrix.isUnit_iff_isUnit_det (1 + A)).mp hplus).ne_zero⟩

/-- A strict contraction has both Fredholm signs invertible.  This is the exact
operator bridge used after establishing `‖H‖ < 1`. -/
theorem fredholm_plus_minus_of_norm_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : E →L[ℝ] E) (hH : ‖H‖ < 1) :
    IsUnit (1 - H) ∧ IsUnit (1 + H) := by
  constructor
  · exact isUnit_one_sub_of_norm_lt_one hH
  · have hneg : ‖-H‖ < 1 := by simpa using hH
    simpa [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (x := -H) hneg)

/-- F1 in equation form: both signed Fredholm equations have unique solutions. -/
theorem fredholm_signed_equations_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : E →L[ℝ] E) (hH : ‖H‖ < 1) (f : E) :
    (∃! x, (1 - H) x = f) ∧ (∃! x, (1 + H) x = f) := by
  have hsign := fredholm_plus_minus_of_norm_lt_one H hH
  constructor
  · have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hsign.1
    obtain ⟨x, hx⟩ := hbij.2 f
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact hbij.1 (hy.trans hx.symm)
  · have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hsign.2
    obtain ⟨x, hx⟩ := hbij.2 f
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact hbij.1 (hy.trans hx.symm)

/-- F2 as an identification principle.  Once the analytic and Fredholm
constructions satisfy the same two signed equations, strict contraction forces
their equality.  No spectral data from a finite pencil enters this step. -/
theorem fredholm_signed_identification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : E →L[ℝ] E) (hH : ‖H‖ < 1) (f : E)
    {xMinus yMinus xPlus yPlus : E}
    (hxMinus : (1 - H) xMinus = f) (hyMinus : (1 - H) yMinus = f)
    (hxPlus : (1 + H) xPlus = f) (hyPlus : (1 + H) yPlus = f) :
    xMinus = yMinus ∧ xPlus = yPlus := by
  have hsign := fredholm_plus_minus_of_norm_lt_one H hH
  constructor
  · exact (ContinuousLinearMap.isUnit_iff_bijective.mp hsign.1).1
      (hxMinus.trans hyMinus.symm)
  · exact (ContinuousLinearMap.isUnit_iff_bijective.mp hsign.2).1
      (hxPlus.trans hyPlus.symm)

/-- The finite theta constant at the origin: the zeroth and fourth kernel
jets are strictly dominated by three times the square of the second jet. -/
theorem xiOriginThetaConstant_pos :
    riemannXiKernel 0 * deriv^[4] riemannXiKernel 0 <
      3 * (deriv^[2] riemannXiKernel 0) ^ 2 := by
  let S0 : ℝ := ∑' n : ℕ, xiKernelGaussianJet0 n 0
  let S2 : ℝ := ∑' n : ℕ, xiKernelGaussianJet2 n 0
  let S4 : ℝ := ∑' n : ℕ, xiKernelGaussianJet4 n 0
  have hs : S0 < (9 : ℝ) / 20 ∧
      S2 < -(8333 : ℝ) / 1000 ∧ S4 < 410 := by
    simpa only [S0, S2, S4] using xiOriginJetSeries_bounds
  have hS0pos : 0 < S0 := by
    have hK := riemannXiKernel_pos (u := 0) (by norm_num)
    rw [riemannXiKernel_zero_eq] at hK
    change 0 < 4 * S0 at hK
    nlinarith
  have hcore : S0 * S4 < 3 * S2 ^ 2 := by
    by_cases hS4 : S4 ≤ 0
    · have hleft : S0 * S4 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hS0pos.le hS4
      have hS2neg : S2 < 0 := hs.2.1.trans (by norm_num)
      have hS2sq : 0 < S2 ^ 2 := sq_pos_of_neg hS2neg
      have hright : 0 < 3 * S2 ^ 2 := by nlinarith
      linarith
    · have hS4pos : 0 < S4 := lt_of_not_ge hS4
      have hprod : S0 * S4 < ((9 : ℝ) / 20) * 410 :=
        mul_lt_mul hs.1 hs.2.2.le hS4pos (by norm_num)
      have hsquare : ((8333 : ℝ) / 1000) ^ 2 < S2 ^ 2 := by
        nlinarith [sq_nonneg (S2 + (8333 : ℝ) / 1000)]
      have hnumeric : ((9 : ℝ) / 20) * 410 <
          3 * ((8333 : ℝ) / 1000) ^ 2 := by norm_num
      exact hprod.trans (hnumeric.trans
        (mul_lt_mul_of_pos_left hsquare (by norm_num)))
  rw [riemannXiKernel_zero_eq, riemannXiKernel_deriv4_zero_eq,
    riemannXiKernel_deriv2_zero_eq]
  simpa only [S0, S2, S4] using (show (4 * S0) * (4 * S4) <
    3 * (4 * S2) ^ 2 by nlinarith)

theorem xiOriginCubicCoefficient_pos :
    0 < (deriv^[2] riemannXiKernel 0) ^ 2 -
      riemannXiKernel 0 * deriv^[4] riemannXiKernel 0 / 3 :=
  (xiOriginCubicCoefficient_pos_iff _ _ _).2 xiOriginThetaConstant_pos

end CriticalLinePhasor.ThetaWronskianSuzukiGram

#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_le_majorant
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_continuousOn
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaMoment_integrable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaMoment_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.centralTuran_closes_theta_levels_four_and_five
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_two_formula
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_three_formula
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.finite_theta_wronskian_levels_one_to_three
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemann_theta_wronskian_levels_one_to_three
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_four_formula
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.finite_theta_wronskian_level_four
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_moment_level_five
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_five_formula
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_five
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.finite_theta_wronskian_level_five_literal
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.suzukiAnalysisIntegral_finset
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.suzukiIntegralGram_energy
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.suzukiIntegralGram_posSemidef
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.finiteSuzukiGram_iff_defect_posSemidef
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.finiteSuzukiGram_of_contractive_factorization
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.suzukiIntegralGram_defect_of_contraction
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.finiteSuzukiGram_integral_of_contraction
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.galerkin_gram_defect_posSemidef
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.suzukiHankelGalerkin_isHermitian
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.galerkin_fredholm_determinants_ne_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.fredholm_plus_minus_of_norm_lt_one
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.fredholm_signed_equations_unique
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.fredholm_signed_identification
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_factorized
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelQ_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelInner_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelTermLogSlope_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelTermLogCurvature_neg
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiCentralTuran_iff_theta_moment_three
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_log_hasDerivAt_deriv
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiExpFiveHalves_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_hasDerivAt_logSlope_mul
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_log_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelTermLogSlope_strictAntiOn
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_log_strictConcaveOn
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelDerivMajorantCoeff_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv2_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialConcavityNumerator_series
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelTermGateWeight_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialConcavityNumerator_gate_variance
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiSlopeVarianceDefect_nonneg
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tsum_xiKernelTermGateWeight_eq_ground_add_tail
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialConcavityNumerator_pos_iff_gate_dominates_variance
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialHazard_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialHazard_strictMonoOn_of_numerator_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tendsto_u_mul_xiKernel_atTop
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tendsto_u_cube_mul_xiKernel_atTop
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tendsto_u_mul_xiKernel_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tendsto_u_cube_mul_xiKernel_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialHazard_weight_two
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialHazard_weight_four
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialCovarianceIntegral_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialCovarianceIntegral_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaMoment_three_strict_of_numerator_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_levels_four_five_of_numerator_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_levels_one_to_five_of_numerator_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.theta_wronskian_level_five_literal_of_numerator_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiMomentMatrix_energy
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiMomentMatrix_posDef
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiEvenMomentMatrix_energy
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiEvenMomentMatrix_posDef
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.exp_mul_two_sub_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiTermGate_zero_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelTermSlopeSquareWeight_le_decay
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelTermCurvatureWeight_abs_le_decay
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelTermGateWeight_abs_le_decay
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tsum_exp_neg_index_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiShiftedIndexTail_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiGateTail_abs_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tsum_xiKernelTermSlopeSquareWeight_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tsum_xiKernelTermGateWeight_ge_ground_sub_tail
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialConcavityNumerator_pos_of_ground_dominates_decay
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialConcavityNumerator_pos_of_ground_dominates_closed_decay
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_neg
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_eq_zero_add_positive
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_eq_profileOperatorSeries
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaSeriesTerm_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaSeriesDeriv1_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaLocalMajorantCoeff_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelQ_pow_mul_exp_neg_le_local
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaSeriesDeriv1_norm_le_local
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaSeriesDeriv2_norm_le_local
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaSeriesTerm_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaSeriesDeriv1_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaSeriesDeriv2_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_deriv_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_operatorSeries_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_eq_profile_operator
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_deriv_reflection
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_deriv2_reflection
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_operator_reflection
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_neg
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiEvenQuarticJet_radialNumerator
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginCubicCoefficient_pos_iff
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiGaussianJet3_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_eq_gaussianJet0
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_deriv4_eq_gaussianJet4
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelJet4LocalMajorantCoeff_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiGaussianJet4_norm_le_component_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet4_norm_le_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelJet3LocalMajorantCoeff_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiGaussianJet3_norm_le_component_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet3_norm_le_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet3_summable_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet3Series_hasDerivAt_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet2Series_hasDerivAt_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet1Series_hasDerivAt_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet0Series_hasDerivAt_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet3Series_hasDerivAt_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_hasDerivAt_gaussianJet1_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv_hasDerivAt_gaussianJet2_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv2_hasDerivAt_gaussianJet3_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv3_hasDerivAt_gaussianJet4_local_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv4_zero_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.exp_pi_lt_one_hundred_sixteen_div_five
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.twenty_three_lt_exp_pi
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.five_div_one_hundred_sixteen_lt_exp_neg_pi
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.exp_neg_pi_lt_one_div_twenty_three
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.originIndexAddThree_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.originSevenStepExponent_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.originNomePow12_pointwise_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tsum_originNomePow12_tail_lt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet0_zero_formula
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet2_zero_formula
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet4_zero_formula
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.exp_neg_pi_mul_index_sq_eq_nome_pow
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_zero_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_deriv2_zero_eq
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiRadialConcavityNumerator_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.originNomePow12Tail_summable
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginJet0Polynomial_bounds
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginJet2Polynomial_bounds
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginJet4Polynomial_bounds
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginLeadingPolynomial_bounds
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet0_shifted_abs_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet2_shifted_abs_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet4_shifted_abs_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.abs_tsum_xiKernelGaussianJet0_shifted_lt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.abs_tsum_xiKernelGaussianJet2_shifted_lt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.abs_tsum_xiKernelGaussianJet4_shifted_lt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginLeadingModes_bounds
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiKernelGaussianJet4_summable_zero
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.tsum_eq_first_two_add_tail
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginJetSeries_bounds
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginThetaConstant_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiOriginCubicCoefficient_pos
