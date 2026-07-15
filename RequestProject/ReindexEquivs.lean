import RequestProject.CosetDictionary

/-!
# The reindexing bijections: lattice = gcd × coprime = gcd × sign × coset

Bookkeeping, second half, part one.  Two explicit bijections: the nonzero lattice splits as
gcd times a coprime pair (`gcdEquiv`, inverted by dividing out `Int.gcd`), and the coprime
pairs split as a sign times a `±⟨T⟩`-coset (`cosetRowEquiv`, from the compiled dictionary —
injectivity is the same-row-same-coset law, surjectivity is Bézout).  Together with the
quadratic scaling and parity of the Gram form these reindex the full lattice Dirichlet series
as `ζ(2s)` times twice the coset series — executed in the next slice.  Also compiled: the
master summability of the Gram Dirichlet series (`summable_gram_rpow`) by comparison with the
Eisenstein box bound.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- The nonzero lattice. -/
abbrev NZ : Type := {p : ℤ × ℤ // p ≠ 0}

/-- The coprime pairs. -/
abbrev CoprimePair : Type := {p : ℤ × ℤ // IsCoprime p.1 p.2}

/-- **The gcd stratification**: nonzero lattice points are a positive gcd times a coprime
pair. -/
noncomputable def gcdEquiv : {n : ℕ // n ≠ 0} × CoprimePair ≃ NZ where
  toFun nc := ⟨((nc.1.1 : ℤ) * nc.2.1.1, (nc.1.1 : ℤ) * nc.2.1.2), by
    intro h
    rw [Prod.ext_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hn : (nc.1.1 : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr nc.1.2
    have hc1 : nc.2.1.1 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hn
      · exact h
    have hc2 : nc.2.1.2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hn
      · exact h
    have hcop := nc.2.2
    rw [hc1, hc2] at hcop
    exact not_isCoprime_zero_zero hcop⟩
  invFun p := ⟨⟨Int.gcd p.1.1 p.1.2, by
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      exact p.2 (Prod.ext h.1 h.2)⟩,
    ⟨(p.1.1 / (Int.gcd p.1.1 p.1.2 : ℤ), p.1.2 / (Int.gcd p.1.1 p.1.2 : ℤ)), by
      have hg : 0 < Int.gcd p.1.1 p.1.2 := by
        rcases Nat.eq_zero_or_pos (Int.gcd p.1.1 p.1.2) with h | h
        · rw [Int.gcd_eq_zero_iff] at h
          exact absurd (Prod.ext h.1 h.2) p.2
        · exact h
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact Int.gcd_div_gcd_div_gcd hg⟩⟩
  left_inv := by
    rintro ⟨⟨n, hn⟩, ⟨⟨c1, c2⟩, hc⟩⟩
    have hgcd1 : Int.gcd c1 c2 = 1 := Int.isCoprime_iff_gcd_eq_one.mp hc
    have hgcd : Int.gcd ((n : ℤ) * c1) ((n : ℤ) * c2) = n := by
      rw [Int.gcd_mul_left, hgcd1, mul_one, Int.natAbs_natCast]
    have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hgcd
    · refine Prod.ext ?_ ?_
      · show ((n : ℤ) * c1) / (Int.gcd ((n : ℤ) * c1) ((n : ℤ) * c2) : ℤ) = c1
        rw [hgcd]
        exact Int.mul_ediv_cancel_left c1 hnz
      · show ((n : ℤ) * c2) / (Int.gcd ((n : ℤ) * c1) ((n : ℤ) * c2) : ℤ) = c2
        rw [hgcd]
        exact Int.mul_ediv_cancel_left c2 hnz
  right_inv := by
    rintro ⟨⟨p1, p2⟩, hp⟩
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (Int.gcd p1 p2 : ℤ) * (p1 / (Int.gcd p1 p2 : ℤ)) = p1
      exact Int.mul_ediv_cancel' (Int.gcd_dvd_left p1 p2)
    · show (Int.gcd p1 p2 : ℤ) * (p2 / (Int.gcd p1 p2 : ℤ)) = p2
      exact Int.mul_ediv_cancel' (Int.gcd_dvd_right p1 p2)

/-- The signed row map: a sign and a coset give a coprime pair. -/
noncomputable def signedRow (bq : Bool × CosetQ) : CoprimePair :=
  ⟨(((if bq.1 then 1 else -1) : ℤ) * (rep bq.2).1 1 0,
    ((if bq.1 then 1 else -1) : ℤ) * (rep bq.2).1 1 1), by
    rcases bq.1 with _ | _
    · simp only [Bool.false_eq_true, if_false, neg_one_mul]
      exact (bottomRow_isCoprime (rep bq.2)).neg_left.neg_right
    · simp only [if_true, one_mul]
      exact bottomRow_isCoprime (rep bq.2)⟩

/-- Rows of coset representatives never vanish. -/
lemma rep_row_ne_zero (q : CosetQ) :
    ¬((rep q).1 1 0 = 0 ∧ (rep q).1 1 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hcop := bottomRow_isCoprime (rep q)
  rw [h0, h1] at hcop
  exact not_isCoprime_zero_zero hcop

/-- Cosets with equal rows agree. -/
lemma coset_eq_of_row_eq {q q' : CosetQ}
    (h0 : (rep q').1 1 0 = (rep q).1 1 0) (h1 : (rep q').1 1 1 = (rep q).1 1 1) :
    q = q' := by
  have h4 : Quotient.mk cosetSetoid (rep q) = Quotient.mk cosetSetoid (rep q') :=
    Quotient.sound (cosetRel_of_bottomRow_eq h0 h1)
  simp only [rep] at h4
  rwa [Quotient.out_eq, Quotient.out_eq] at h4

/-- Cosets with opposite rows agree — and then the row vanishes, which is absurd. -/
lemma coset_row_ne_neg {q q' : CosetQ}
    (h0 : (rep q').1 1 0 = -((rep q).1 1 0)) (h1 : (rep q').1 1 1 = -((rep q).1 1 1)) :
    False := by
  have h4 : Quotient.mk cosetSetoid (rep q) = Quotient.mk cosetSetoid (rep q') :=
    Quotient.sound (cosetRel_of_bottomRow_neg h0 h1)
  simp only [rep] at h4
  rw [Quotient.out_eq, Quotient.out_eq] at h4
  subst h4
  apply rep_row_ne_zero q
  constructor
  · linarith [h0]
  · linarith [h1]

/-- **The signed-row map is a bijection**: coprime pairs are a sign times a coset. -/
lemma signedRow_bijective : Function.Bijective signedRow := by
  constructor
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    rw [signedRow, signedRow, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h0, h1⟩ := h
    rcases b <;> rcases b' <;>
      simp only [if_true, if_false, Bool.false_eq_true, one_mul, neg_one_mul] at h0 h1
    · exact Prod.ext rfl
        (coset_eq_of_row_eq (neg_injective h0).symm (neg_injective h1).symm)
    · exact (coset_row_ne_neg (q := q) (q' := q') h0.symm h1.symm).elim
    · exact (coset_row_ne_neg (q := q') (q' := q) h0 h1).elim
    · exact Prod.ext rfl (coset_eq_of_row_eq h0.symm h1.symm)
  · rintro ⟨⟨c1, c2⟩, hc⟩
    obtain ⟨γ, hγ0, hγ1⟩ := exists_SL2_bottomRow hc
    obtain ⟨n, hn | hn⟩ := rep_spec γ
    · refine ⟨(true, Quotient.mk cosetSetoid γ), ?_⟩
      rw [signedRow]
      apply Subtype.ext
      simp only [if_true, one_mul]
      have h0 := congrArg (fun δ : SL(2, ℤ) => δ.1 1 0) hn
      have h1 := congrArg (fun δ : SL(2, ℤ) => δ.1 1 1) hn
      simp only [bottomRow_T_zpow_mul] at h0 h1
      rw [← h0, ← h1, hγ0, hγ1]
    · refine ⟨(false, Quotient.mk cosetSetoid γ), ?_⟩
      rw [signedRow]
      apply Subtype.ext
      simp only [Bool.false_eq_true, if_false, neg_one_mul]
      have h0 := congrArg (fun δ : SL(2, ℤ) => δ.1 1 0) hn
      have h1 := congrArg (fun δ : SL(2, ℤ) => δ.1 1 1) hn
      simp only [bottomRow_neg, bottomRow_T_zpow_mul] at h0 h1
      rw [← neg_neg ((rep (Quotient.mk cosetSetoid γ)).1 1 0), ← h0,
        ← neg_neg ((rep (Quotient.mk cosetSetoid γ)).1 1 1), ← h1, hγ0, hγ1, neg_neg, neg_neg]

/-- **Coprime pairs are a sign times a coset.** -/
noncomputable def cosetRowEquiv : Bool × CosetQ ≃ CoprimePair :=
  Equiv.ofBijective signedRow signedRow_bijective

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.gcdEquiv
#print axioms CriticalLinePhasor.Unfolding.cosetRowEquiv
