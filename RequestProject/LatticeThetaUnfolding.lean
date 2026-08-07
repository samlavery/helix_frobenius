import RequestProject.CarrierLatticePair
import RequestProject.TransportClosure

/-!
# The matrix transformation law, unfolded: the genuine arithmetic rung family at every rank

Certifier (a) of the standing wave, third brick.  The compiled rank-uniform lattice FE-pair
(`matrixLatticePair`: the completed FE of the matrix bank at every rank) receives its
**arithmetic chart**: the Mellin transform of the DC-split bank is identified, on the
half-plane, with the completed Epstein zeta of the matrix lattice —

  `Λ_r(s) = π^{-s}·Γ(s)·∑_{n≥1} r_{(r+1)²}(n)·n^{-s}`,

with `r_N(n)` the representation numbers of the sum of `N` squares.  Combined with the
compiled `matrixLattice_functional_equation`, this is a genuine arithmetic family of
completed functional equations at every rank simultaneously — the lattice → gate → FE
pipeline inhabited end-to-end on a real Dirichlet series, fiber-free.

* `latticeNormSq` / `latticeRepCount` — the ℕ-valued strand norm and its representation
  numbers, with finite fibers (`fiberFinite`), the DC count (`latticeRepCount_zero`),
  and polynomial growth (`latticeRepCount_le`);
* `bankGauss_eq_repSum` — **the grouping identity**: the Gaussian bank is the sum of its
  representation numbers against the exponential clock (fiberwise regrouping of the
  lattice tsum, `Equiv.sigmaFiberEquiv` + `tsum_const`);
* `expClock_mellin` — the exponential clock carries `π^{-s}·Γ(s)`;
* `bankGauss_arithmetic_hasMellin` — the arithmetic chart over any finite strand set;
* `matrixLattice_arithmetic_chart` — the capstone at the matrix lattice, every rank.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex
open scoped Real LSeries.notation

namespace CriticalLinePhasor.LatticeThetaUnfolding

open CriticalLinePhasor.CarrierLatticePoisson CriticalLinePhasor.CarrierLatticePair
open CriticalLinePhasor.CarrierTheta CriticalLinePhasor.TransportClosure
open Set MeasureTheory Filter

variable {ι : Type*} [Fintype ι]

/-- The ℕ-valued lattice norm of a strand vector. -/
def latticeNormSq (A : ι → ℤ) : ℕ := ∑ i, (A i).natAbs ^ 2

theorem latticeNormSq_cast (A : ι → ℤ) :
    ((latticeNormSq A : ℕ) : ℝ) = ∑ i, ((A i : ℤ) : ℝ) ^ 2 := by
  unfold latticeNormSq
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (((A i).natAbs : ℕ) : ℝ) = |((A i : ℤ) : ℝ)| by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]]
  exact sq_abs _

theorem natAbs_le_of_normSq {A : ι → ℤ} {n : ℕ} (h : latticeNormSq A = n) (i : ι) :
    (A i).natAbs ≤ n := by
  have h1 : (A i).natAbs ^ 2 ≤ latticeNormSq A :=
    Finset.single_le_sum (f := fun i => (A i).natAbs ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : (A i).natAbs ≤ (A i).natAbs ^ 2 := Nat.le_self_pow two_ne_zero _
  omega

/-- The norm fiber embeds into a finite box. -/
def fiberEmbed (n : ℕ) (A : {A : ι → ℤ // latticeNormSq A = n}) :
    ι → (Finset.Icc (-(n : ℤ)) n) := fun i =>
  ⟨A.1 i, by
    rw [Finset.mem_Icc]
    have := natAbs_le_of_normSq A.2 i
    omega⟩

theorem fiberEmbed_injective (n : ℕ) :
    Function.Injective (fiberEmbed (ι := ι) n) := by
  intro A B h
  apply Subtype.ext
  funext i
  have := congrFun h i
  exact congrArg Subtype.val this

instance fiberFinite (n : ℕ) : Finite {A : ι → ℤ // latticeNormSq A = n} :=
  Finite.of_injective _ (fiberEmbed_injective n)

/-- The representation numbers of the strand lattice: how many vectors have norm `n`. -/
noncomputable def latticeRepCount (ι : Type*) [Fintype ι] (n : ℕ) : ℕ :=
  Nat.card {A : ι → ℤ // latticeNormSq (ι := ι) A = n}

instance : Unique {A : ι → ℤ // latticeNormSq (ι := ι) A = 0} where
  default := ⟨fun _ => 0, by simp [latticeNormSq]⟩
  uniq := by
    rintro ⟨A, hA⟩
    have hz : ∀ i, A i = 0 := by
      intro i
      unfold latticeNormSq at hA
      have h := (Finset.sum_eq_zero_iff).mp hA i (Finset.mem_univ i)
      exact Int.natAbs_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
    apply Subtype.ext
    funext i
    exact hz i

theorem latticeRepCount_zero : latticeRepCount ι 0 = 1 := by
  unfold latticeRepCount
  exact Nat.card_unique

/-- Polynomial growth of the representation numbers. -/
theorem latticeRepCount_le (n : ℕ) :
    latticeRepCount ι n ≤ (2 * n + 1) ^ (Fintype.card ι) := by
  unfold latticeRepCount
  calc Nat.card {A : ι → ℤ // latticeNormSq A = n}
      ≤ Nat.card (ι → (Finset.Icc (-(n : ℤ)) n)) :=
        Nat.card_le_card_of_injective _ (fiberEmbed_injective n)
    _ = (2 * n + 1) ^ (Fintype.card ι) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc,
          Nat.card_eq_fintype_card]
        congr 1
        omega

/-- General-strand summability of the Gaussian bank. -/
theorem summable_bankGauss {a : ℝ} (ha : 0 < a) :
    Summable fun A : ι → ℤ => Real.exp (-π * a * ∑ i, ((A i : ℤ) : ℝ) ^ 2) := by
  refine ((Equiv.arrowCongr (Fintype.equivFin ι)
    (Equiv.refl ℤ)).symm.summable_iff).mp ?_
  refine (summable_bankGaussFin ha (Fintype.card ι)).congr fun B => ?_
  show Real.exp (-π * a * ∑ i, ((B i : ℤ) : ℝ) ^ 2) = _
  congr 1
  congr 1
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ fun x => by
    simp [Equiv.arrowCongr]

/-- The inner fiber sum collapses to the representation count. -/
theorem fiber_tsum_eq (a : ℝ) (n : ℕ) :
    (∑' A : {A : ι → ℤ // latticeNormSq A = n},
        Real.exp (-π * a * ∑ i, ((A.1 i : ℤ) : ℝ) ^ 2))
      = (latticeRepCount ι n : ℝ) * Real.exp (-π * a * n) := by
  have hconst : ∀ A : {A : ι → ℤ // latticeNormSq A = n},
      Real.exp (-π * a * ∑ i, ((A.1 i : ℤ) : ℝ) ^ 2)
        = Real.exp (-π * a * n) := by
    intro A
    rw [← latticeNormSq_cast, A.2]
  rw [tsum_congr hconst, tsum_const, nsmul_eq_mul]
  rfl

/-- **The grouping identity**: the Gaussian bank is the Dirichlet-type sum of its
representation numbers against the exponential clock. -/
theorem bankGauss_eq_repSum {a : ℝ} (ha : 0 < a) :
    bankGauss ι a
      = ∑' n : ℕ, (latticeRepCount ι n : ℝ) * Real.exp (-π * a * n) := by
  unfold bankGauss
  rw [← (Equiv.sigmaFiberEquiv (latticeNormSq (ι := ι))).tsum_eq]
  have hsum' : Summable (fun p : Σ n : ℕ, {A : ι → ℤ // latticeNormSq A = n} =>
      Real.exp (-π * a * ∑ i,
        ((((Equiv.sigmaFiberEquiv (latticeNormSq (ι := ι))) p) i : ℤ) : ℝ) ^ 2)) :=
    (Equiv.sigmaFiberEquiv (latticeNormSq (ι := ι))).summable_iff.mpr
      (summable_bankGauss ha)
  rw [Summable.tsum_sigma hsum']
  exact tsum_congr fun n => fiber_tsum_eq a n

/-- Outer summability of the representation sum. -/
theorem summable_repSum {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => (latticeRepCount ι n : ℝ) * Real.exp (-π * a * n) := by
  have h : Summable (fun p : Σ n : ℕ, {A : ι → ℤ // latticeNormSq A = n} =>
      Real.exp (-π * a * ∑ i,
        ((((Equiv.sigmaFiberEquiv (latticeNormSq (ι := ι))) p) i : ℤ) : ℝ) ^ 2)) :=
    (Equiv.sigmaFiberEquiv (latticeNormSq (ι := ι))).summable_iff.mpr
      (summable_bankGauss ha)
  have h2 := (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mp h
  exact h2.2.congr fun n => fiber_tsum_eq a n

/-- The DC split: the bank is `1` plus the positive-norm representation sum. -/
theorem bankGauss_sub_one {a : ℝ} (ha : 0 < a) :
    bankGauss ι a
      = 1 + ∑' n : ℕ,
          (latticeRepCount ι (n + 1) : ℝ) * Real.exp (-π * a * (n + 1)) := by
  rw [bankGauss_eq_repSum ha, (summable_repSum ha).tsum_eq_zero_add]
  congr 1
  · simp [latticeRepCount_zero]
  · exact tsum_congr fun n => by push_cast; ring_nf


/-- The exponential clock `e^{−πx}` — the archimedean factor of the strand lattice. -/
noncomputable def expClock (x : ℝ) : ℂ := ((Real.exp (-π * x) : ℝ) : ℂ)

theorem expClock_mellinConvergent {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent expClock s := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hbase : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) s := by
    rw [MellinConvergent]
    simpa [smul_eq_mul, mul_comm] using (Complex.GammaIntegral_convergent hs)
  have h := (MellinConvergent.comp_mul_left hπ).2 hbase
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  unfold expClock
  norm_num

theorem expClock_mellin {s : ℂ} (hs : 0 < s.re) :
    mellin expClock s = (1 / (π : ℂ)) ^ s * Complex.Gamma s := by
  rw [show mellin expClock s
      = ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-((π : ℂ) * t)) by
    unfold mellin
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    unfold expClock
    rw [smul_eq_mul, Complex.ofReal_exp,
      show ((-π * t : ℝ) : ℂ) = -((π : ℂ) * (t : ℂ)) by push_cast; ring]]
  exact Complex.integral_cpow_mul_exp_neg_mul_Ioi hs Real.pi_pos

/-- The representation-number coefficients, shifted to the theta index. -/
noncomputable def repCoeff (ι : Type*) [Fintype ι] : ℕ → ℂ :=
  fun j => ((latticeRepCount ι (j + 1) : ℕ) : ℂ)

theorem repCoeff_bound (j : ℕ) :
    ‖repCoeff ι j‖ ≤ (3 : ℝ) ^ (Fintype.card ι) *
      (((j + 1 : ℕ) : ℝ) ^ ((Fintype.card ι : ℕ) : ℝ)) := by
  unfold repCoeff
  rw [Complex.norm_natCast]
  calc ((latticeRepCount ι (j + 1) : ℕ) : ℝ)
      ≤ (((2 * (j + 1) + 1) ^ (Fintype.card ι) : ℕ) : ℝ) := by
        exact_mod_cast latticeRepCount_le (j + 1)
    _ ≤ (((3 * (j + 1)) ^ (Fintype.card ι) : ℕ) : ℝ) := by
        have : (2 * (j + 1) + 1) ≤ 3 * (j + 1) := by omega
        exact_mod_cast Nat.pow_le_pow_left this _
    _ = (3 : ℝ) ^ (Fintype.card ι) *
          (((j + 1 : ℕ) : ℝ) ^ ((Fintype.card ι : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
        push_cast
        rw [mul_pow]

/-- On the positive carrier the DC-split bank is the coefficient theta of the
representation numbers against the exponential clock. -/
theorem bankGaussC_sub_one_eq_theta {t : ℝ} (ht : 0 < t) :
    ((bankGauss ι t : ℝ) : ℂ) - 1 = theta (repCoeff ι) expClock t := by
  rw [bankGauss_sub_one ht]
  push_cast
  rw [add_sub_cancel_left]
  unfold theta repCoeff expClock
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_exp, show ((-π * (((n + 1 : ℕ) : ℝ) * t) : ℝ) : ℂ)
      = -(π : ℂ) * (t : ℂ) * ((n : ℂ) + 1) by push_cast; ring]

theorem repCoeffArith_summable {s : ℂ}
    (hs : ((Fintype.card ι : ℕ) : ℝ) + 1 < s.re) :
    LSeriesSummable (⇑(coefficientArithmetic (repCoeff ι))) s := by
  refine LSeriesSummable_of_le_const_mul_rpow
    (x := ((Fintype.card ι : ℕ) : ℝ) + 1) hs
    ⟨(3 : ℝ) ^ (Fintype.card ι), fun m hm => ?_⟩
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hval : (coefficientArithmetic (repCoeff ι)) m = repCoeff ι (m - 1) := by
    show (if m = 0 then 0 else repCoeff ι (m - 1)) = repCoeff ι (m - 1)
    rw [if_neg hm]
  rw [hval]
  have hb := repCoeff_bound (ι := ι) (m - 1)
  rw [show m - 1 + 1 = m from by omega] at hb
  calc ‖repCoeff ι (m - 1)‖
      ≤ (3 : ℝ) ^ (Fintype.card ι) * ((m : ℝ) ^ ((Fintype.card ι : ℕ) : ℝ)) := hb
    _ = (3 : ℝ) ^ (Fintype.card ι) *
          ((m : ℝ) ^ ((((Fintype.card ι : ℕ) : ℝ) + 1) - 1)) := by
        norm_num

/-- **The arithmetic chart of the strand-lattice bank**: on the half-plane, the Mellin
transform of the DC-split Gaussian bank is `π^{-s}·Γ(s)` times the L-series of the
representation numbers — the completed Epstein readout, over any finite strand set. -/
theorem bankGauss_arithmetic_hasMellin {s : ℂ}
    (hs : ((Fintype.card ι : ℕ) : ℝ) + 1 < s.re) :
    HasMellin (fun t : ℝ => ((bankGauss ι t : ℝ) : ℂ) - 1) s
      ((1 / (π : ℂ)) ^ s * Complex.Gamma s *
        LSeries (⇑(coefficientArithmetic (repCoeff ι))) s) := by
  have hs0 : 0 < s.re := by
    have : (0 : ℝ) ≤ ((Fintype.card ι : ℕ) : ℝ) := by positivity
    linarith
  have hθ := theta_hasMellin_of_polynomial (repCoeff ι) expClock s
    ((3 : ℝ) ^ (Fintype.card ι)) ((Fintype.card ι : ℕ) : ℝ)
    (expClock_mellinConvergent hs0) (fun j => repCoeff_bound j) hs
  constructor
  · refine hθ.1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [bankGaussC_sub_one_eq_theta (ι := ι) (Set.mem_Ioi.mp ht)]
  · rw [show mellin (fun t : ℝ => ((bankGauss ι t : ℝ) : ℂ) - 1) s
        = mellin (theta (repCoeff ι) expClock) s by
      unfold mellin
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      dsimp only
      rw [bankGaussC_sub_one_eq_theta (Set.mem_Ioi.mp ht)]]
    rw [hθ.2, expClock_mellin hs0]
    have hcoeff : repCoeff ι = fun j => (coefficientArithmetic (repCoeff ι)) (j + 1) := by
      funext j
      simp [coefficientArithmetic]
    rw [hcoeff, dirichlet_shift_eq_LSeries _ (repCoeffArith_summable hs), ← hcoeff]
    ring

/-- **The matrix transformation law, unfolded — the genuine arithmetic rung family at every rank**:
the completed transform of the rank-`r` matrix bank is identified on the half-plane with
`π^{-s}·Γ(s)·L(r_{(r+1)²}, s)`, the completed Epstein zeta of the matrix lattice, whose
functional equation `Λ((r+1)²/2 − s) = Λ(s)` is already compiled. -/
theorem matrixLattice_arithmetic_chart (r : ℕ) {s : ℂ}
    (hs : ((Fintype.card (Fin (r + 1) × Fin (r + 1)) : ℕ) : ℝ) + 1 < s.re) :
    (matrixLatticePair r).Λ s
      = (1 / (π : ℂ)) ^ s * Complex.Gamma s *
        LSeries (⇑(coefficientArithmetic
          (repCoeff (Fin (r + 1) × Fin (r + 1))))) s := by
  have hcard : ((Fintype.card (Fin (r + 1) × Fin (r + 1)) : ℕ) : ℝ)
      = ((r : ℝ) + 1) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hk : (matrixLatticePair r).k < s.re := by
    rw [matrixLatticePair_k]
    rw [hcard] at hs
    nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hM := (matrixLatticePair r).hasMellin hk
  have hA := bankGauss_arithmetic_hasMellin (ι := Fin (r + 1) × Fin (r + 1)) hs
  rw [← hM.2, ← hA.2]
  rfl

end CriticalLinePhasor.LatticeThetaUnfolding

#print axioms CriticalLinePhasor.LatticeThetaUnfolding.latticeRepCount_zero
#print axioms CriticalLinePhasor.LatticeThetaUnfolding.latticeRepCount_le
#print axioms CriticalLinePhasor.LatticeThetaUnfolding.bankGauss_eq_repSum
#print axioms CriticalLinePhasor.LatticeThetaUnfolding.expClock_mellin
#print axioms CriticalLinePhasor.LatticeThetaUnfolding.bankGauss_arithmetic_hasMellin
#print axioms CriticalLinePhasor.LatticeThetaUnfolding.matrixLattice_arithmetic_chart
