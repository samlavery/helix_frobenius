import Mathlib

/-!
# The carrier-lattice Poisson identity at every rank: rank-uniform self-duality

Certifier (a) of the standing wave, first brick.  The carrier bank of the rank-`r` rung
lives on the matrix lattice `M_{r+1}(ℤ)`; at carrier height `t` (the scalar slice
`Y = t·I` of the general self-duality `θ(Y⁻¹) = det(Y)^{1/2}·θ(Y)`), the Gaussian bank

  `θ_r(t) = ∑_{A ∈ M_{r+1}(ℤ)} exp(-π t ‖A‖²)`

factorizes through the `(r+1)²` coordinate strands: `θ_r(t) = S(t)^{(r+1)²}`, with `S`
the one-strand theta.  One application of the compiled Gaussian Poisson identity to the
single strand then yields the transformation law at EVERY rank simultaneously:

  `θ_r(1/t) = t^{(r+1)²/2} · θ_r(t)`     (`matrixTheta_inv`)

* rank-uniform: one theorem, all `r` — no per-rank input, no induction over rungs;
* fiber-free: no cusp form, no automorphy, no L-function enters — classical Poisson on
  a vector space is the only analytic input (through Mathlib's
  `Real.tsum_exp_neg_mul_int_sq`);
* the exact analog, at every rank, of the compiled `latticeTheta_inv` transformation law that drives
  the r = 2 Rankin–Selberg box: this is the self-dual profile the house pairs with the
  bank — in the *weak* coupling shape (`WeakBankThetaProfileCoupling3D`), since the DC
  mode below is nonzero; only the profile-reflection field shape is shared with the
  strong type.

`bankGauss_inv` is the general form over an arbitrary finite strand set; `matrixTheta`
reads it on the matrix lattice.  `one_le_matrixTheta` records the DC mode: the identity
matrix `A = 0` contributes mass `1`, so the profile carries a nonzero constant term —
its home is the weak coupling shape (`WeakBankThetaProfileCoupling3D`), like the r = 2
profile.

Scope: this is the self-duality of the *carrier* lattice — the geometric half of
certifier (a).  It does not by itself discharge any rung's standing wave: the remaining
half is the coupling of this self-dual bank to the rung's arithmetic profile.
-/

open Real Finset

namespace CriticalLinePhasor.CarrierLatticePoisson

/-! ## The single strand -/

/-- One-strand Gaussian summability. -/
lemma summable_gaussInt {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ => Real.exp (-π * a * (n : ℝ) ^ 2) := by
  have hlt : Real.exp (-π * a) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hgeom : Summable fun n : ℕ => Real.exp (-π * a) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hlt
  have hnat : ∀ n : ℕ, Real.exp (-π * a * (n : ℝ) ^ 2) ≤ Real.exp (-π * a) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast Nat.le_self_pow two_ne_zero n
    nlinarith [mul_nonneg Real.pi_pos.le ha.le]
  refine (summable_int_iff_summable_nat_and_neg).mpr ⟨?_, ?_⟩ <;>
    [refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_ hgeom;
     refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_ hgeom] <;>
    intro n <;> [simpa using hnat n; simpa using hnat n]

/-- The one-strand theta at height `a`. -/
noncomputable def strandTheta (a : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-π * a * (n : ℝ) ^ 2)

/-- The one-strand transformation law, read off Mathlib's Gaussian Poisson identity:
`S(1/t) = t^{1/2}·S(t)`. -/
theorem strandTheta_inv {t : ℝ} (ht : 0 < t) :
    strandTheta t⁻¹ = t ^ ((1 : ℝ) / 2) * strandTheta t := by
  have h := Real.tsum_exp_neg_mul_int_sq ht
  have hids : (∑' n : ℤ, Real.exp (-π / t * (n : ℝ) ^ 2)) =
      ∑' n : ℤ, Real.exp (-π * t⁻¹ * (n : ℝ) ^ 2) :=
    tsum_congr fun n => by rw [div_eq_mul_inv]
  rw [hids] at h
  have hne : (t : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  unfold strandTheta
  rw [h]
  field_simp

/-- The one-strand theta dominates its DC mode. -/
lemma one_le_strandTheta {a : ℝ} (ha : 0 < a) : 1 ≤ strandTheta a := by
  have h := (summable_gaussInt ha).le_tsum 0 fun n _ => (Real.exp_pos _).le
  unfold strandTheta
  calc (1 : ℝ) = Real.exp (-π * a * ((0 : ℤ) : ℝ) ^ 2) := by norm_num
    _ ≤ _ := h

/-! ## The multi-strand bank -/

/-- The Gaussian bank over a finite strand set `ι`: the lattice `ι → ℤ` at height `a`. -/
noncomputable def bankGauss (ι : Type*) [Fintype ι] (a : ℝ) : ℝ :=
  ∑' A : ι → ℤ, Real.exp (-π * a * ∑ i, ((A i : ℤ) : ℝ) ^ 2)

/-- The bank integrand splits one strand off the front. -/
private lemma bank_split {n : ℕ} (a : ℝ) (k : ℤ) (B : Fin n → ℤ) :
    Real.exp (-π * a * ∑ i, (((Fin.cons k B : Fin (n + 1) → ℤ) i : ℤ) : ℝ) ^ 2) =
      Real.exp (-π * a * ((k : ℝ)) ^ 2) *
        Real.exp (-π * a * ∑ i, ((B i : ℤ) : ℝ) ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- Summability of the `Fin n`-strand bank, by strand induction. -/
lemma summable_bankGaussFin {a : ℝ} (ha : 0 < a) :
    ∀ n : ℕ, Summable fun A : Fin n → ℤ =>
      Real.exp (-π * a * ∑ i, ((A i : ℤ) : ℝ) ^ 2) := by
  intro n
  induction n with
  | zero => exact .of_finite
  | succ n ih =>
      rw [← (Equiv.summable_iff (Fin.consEquiv fun _ : Fin (n + 1) => ℤ))]
      have heq : ∀ p : ℤ × (Fin n → ℤ),
          Real.exp (-π * a * ∑ i, ((((Fin.consEquiv fun _ => ℤ) p) i : ℤ) : ℝ) ^ 2) =
            Real.exp (-π * a * ((p.1 : ℝ)) ^ 2) *
              Real.exp (-π * a * ∑ i, ((p.2 i : ℤ) : ℝ) ^ 2) := fun p =>
        bank_split a p.1 p.2
      refine Summable.congr ?_ fun p => (heq p).symm
      exact (summable_gaussInt ha).mul_of_nonneg ih
        (fun k => (Real.exp_pos _).le) (fun B => (Real.exp_pos _).le)

set_option maxHeartbeats 1000000 in
/-- The `Fin n`-strand bank is the `n`-th power of the single strand. -/
lemma bankGaussFin_eq {a : ℝ} (ha : 0 < a) :
    ∀ n : ℕ, bankGauss (Fin n) a = strandTheta a ^ n := by
  intro n
  induction n with
  | zero =>
      unfold bankGauss
      rw [tsum_eq_single (fun i => i.elim0) fun b hb =>
        absurd (Subsingleton.elim b _) hb]
      simp
  | succ n ih =>
      unfold bankGauss
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).tsum_eq
        (fun A : Fin (n + 1) → ℤ =>
          Real.exp (-π * a * ∑ i, ((A i : ℤ) : ℝ) ^ 2))]
      have heq : ∀ p : ℤ × (Fin n → ℤ),
          Real.exp (-π * a * ∑ i, ((((Fin.consEquiv fun _ => ℤ) p) i : ℤ) : ℝ) ^ 2) =
            Real.exp (-π * a * ((p.1 : ℝ)) ^ 2) *
              Real.exp (-π * a * ∑ i, ((p.2 i : ℤ) : ℝ) ^ 2) := fun p =>
        bank_split a p.1 p.2
      rw [tsum_congr heq]
      have hprod : Summable fun p : ℤ × (Fin n → ℤ) =>
          Real.exp (-π * a * ((p.1 : ℝ)) ^ 2) *
            Real.exp (-π * a * ∑ i, ((p.2 i : ℤ) : ℝ) ^ 2) :=
        (summable_gaussInt ha).mul_of_nonneg (summable_bankGaussFin ha n)
          (fun k => (Real.exp_pos _).le) (fun B => (Real.exp_pos _).le)
      have hfib : ∀ k : ℤ, Summable fun B : Fin n → ℤ =>
          Real.exp (-π * a * ((k : ℝ)) ^ 2) *
            Real.exp (-π * a * ∑ i, ((B i : ℤ) : ℝ) ^ 2) :=
        fun k => (summable_bankGaussFin ha n).mul_left _
      rw [hprod.tsum_prod' hfib]
      calc (∑' k : ℤ, ∑' B : Fin n → ℤ,
              Real.exp (-π * a * ((k : ℝ)) ^ 2) *
                Real.exp (-π * a * ∑ i, ((B i : ℤ) : ℝ) ^ 2))
          = ∑' k : ℤ, Real.exp (-π * a * ((k : ℝ)) ^ 2) *
              ∑' B : Fin n → ℤ, Real.exp (-π * a * ∑ i, ((B i : ℤ) : ℝ) ^ 2) := by
            exact tsum_congr fun k => tsum_mul_left
        _ = strandTheta a * bankGauss (Fin n) a := tsum_mul_right
        _ = strandTheta a ^ (n + 1) := by rw [ih]; ring

/-- **The bank factorizes through its strands**: over any finite strand set,
`bank(a) = S(a)^{card ι}`. -/
theorem bankGauss_eq_pow (ι : Type*) [Fintype ι] {a : ℝ} (ha : 0 < a) :
    bankGauss ι a = strandTheta a ^ Fintype.card ι := by
  unfold bankGauss
  rw [← (Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl ℤ)).symm.tsum_eq]
  have heq : ∀ B : Fin (Fintype.card ι) → ℤ,
      Real.exp (-π * a * ∑ i,
        ((((Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl ℤ)).symm B) i : ℤ) : ℝ) ^ 2)
        = Real.exp (-π * a * ∑ j, ((B j : ℤ) : ℝ) ^ 2) := by
    intro B
    congr 1
    congr 1
    exact Fintype.sum_equiv (Fintype.equivFin ι) _ _ fun i => by
      simp [Equiv.arrowCongr]
  rw [tsum_congr heq]
  exact bankGaussFin_eq ha (Fintype.card ι)

/-- **The rank-uniform lattice transformation law over any strand set**: `bank(1/t) = t^{card ι / 2}·bank(t)`. -/
theorem bankGauss_inv (ι : Type*) [Fintype ι] {t : ℝ} (ht : 0 < t) :
    bankGauss ι t⁻¹ = t ^ ((Fintype.card ι : ℝ) / 2) * bankGauss ι t := by
  rw [bankGauss_eq_pow ι (inv_pos.mpr ht), bankGauss_eq_pow ι ht, strandTheta_inv ht,
    mul_pow, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 2)) (Fintype.card ι),
    ← Real.rpow_mul ht.le]
  ring_nf

/-! ## The matrix carrier bank -/

/-- The carrier-matrix bank at rank `r`: the Gaussian bank of the matrix lattice
`M_{r+1}(ℤ)` at carrier height `t`, read through its `(r+1)²` strands. -/
noncomputable def matrixTheta (r : ℕ) (t : ℝ) : ℝ :=
  bankGauss (Fin (r + 1) × Fin (r + 1)) t

/-- **The carrier-lattice Poisson identity at every rank** — the scalar-height slice of
`θ(Y⁻¹) = det(Y)^{1/2}·θ(Y)` on `M_{r+1}(ℤ)`:

  `θ_r(1/t) = t^{(r+1)²/2} · θ_r(t)`.

One theorem, all ranks; classical Poisson on a vector space is the only analytic input.
No cusp form, no automorphy, no L-function. -/
theorem matrixTheta_inv (r : ℕ) {t : ℝ} (ht : 0 < t) :
    matrixTheta r t⁻¹ = t ^ ((((r : ℝ) + 1) ^ 2) / 2) * matrixTheta r t := by
  have h := bankGauss_inv (Fin (r + 1) × Fin (r + 1)) ht
  unfold matrixTheta
  rw [h]
  congr 2
  simp [Fintype.card_prod]
  ring

/-- The matrix bank factorizes into its strand power: `θ_r(t) = S(t)^{(r+1)²}`. -/
theorem matrixTheta_eq_pow (r : ℕ) {t : ℝ} (ht : 0 < t) :
    matrixTheta r t = strandTheta t ^ ((r + 1) * (r + 1)) := by
  unfold matrixTheta
  rw [bankGauss_eq_pow _ ht, Fintype.card_prod, Fintype.card_fin]

/-- The DC mode of the matrix bank: the zero matrix contributes mass `1`, so the
rank-`r` profile carries a nonzero constant term — its home is the weak coupling
shape, like the r = 2 Rankin–Selberg profile. -/
theorem one_le_matrixTheta (r : ℕ) {t : ℝ} (ht : 0 < t) : 1 ≤ matrixTheta r t := by
  rw [matrixTheta_eq_pow r ht]
  exact one_le_pow₀ (one_le_strandTheta ht)

end CriticalLinePhasor.CarrierLatticePoisson

#print axioms CriticalLinePhasor.CarrierLatticePoisson.strandTheta_inv
#print axioms CriticalLinePhasor.CarrierLatticePoisson.bankGauss_eq_pow
#print axioms CriticalLinePhasor.CarrierLatticePoisson.bankGauss_inv
#print axioms CriticalLinePhasor.CarrierLatticePoisson.matrixTheta_inv
#print axioms CriticalLinePhasor.CarrierLatticePoisson.matrixTheta_eq_pow
#print axioms CriticalLinePhasor.CarrierLatticePoisson.one_le_matrixTheta
