import RequestProject.MonomialShadow

/-!
# The polynomial ceiling: temperedness from the honest per-rung strength

The tower ceiling consumed so far is rank-uniform: `‖α^r‖ ≤ C` for every `r`.
The classical per-rung input (Jacquet–Shalika through the symmetric-power ladder)
honestly supplies constants that may grow polynomially in the rank — `(r+1)^k`
from the `r+1` channels of `Sym^r`.  This file closes that calibration gap:

* `le_one_of_pow_le_poly` — **the polynomial radial limit**: `ρ^r ≤ C·(r+1)^k`
  for all `r ≥ 1` forces `ρ ≤ 1` — the exponential beats every polynomial, so
  the `r`-th roots still close at `1`;
* `strand_radius_one_of_poly_ceiling` — temperedness (`‖α‖ = 1`) from the
  polynomial ceiling on both channels;
* `MaassPolyCeiling` / `MaassPolyCeiling.toCeiling` — the typed per-rung input at
  its honest polynomial strength, and the derived *uniform* ceiling with `C = 1`:
  once the radius closes at `1`, every power is exactly unimodular, so the whole
  downstream corpus (the Sato–Tate family, the fork, the shadow detector)
  inherits verbatim;
* `maass_temperedness_poly` — Sato–Tate (i) at the seed from the polynomial
  input;
* `maass_no_shadow_of_ST` — **the non-Galois-type hypothesis, compiled**: an
  equidistributing seed admits no monomial shadow at any finite order — the
  corollary's "non-dihedral" hypothesis is now the theorem-shaped absence the
  fork detects, not a prose exclusion.

No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.PolyCeiling

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.MaassSatoTate
open CriticalLinePhasor.RamanujanLimit CriticalLinePhasor.SatoTateCarrier3D
open CriticalLinePhasor.ShadowDetector

/-- **The polynomial radial limit**: `ρ^n ≤ C·(n+1)^k` for all `n ≥ 1` forces
`ρ ≤ 1` — the exponential beats every polynomial. -/
theorem le_one_of_pow_le_poly {ρ C : ℝ} (k : ℕ) (_hρ : 0 ≤ ρ) (hC : 0 < C)
    (h : ∀ n : ℕ, 1 ≤ n → ρ ^ n ≤ C * ((n + 1 : ℕ) : ℝ) ^ k) : ρ ≤ 1 := by
  by_contra hgt
  rw [not_le] at hgt
  have hρ1 : 1 < ρ := hgt
  have hinv : |ρ⁻¹| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact inv_lt_one_of_one_lt₀ hρ1
  have hsum : Summable (fun n : ℕ => ((n : ℝ)) ^ k * (ρ⁻¹) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (k := k)
      (r := (ρ⁻¹ : ℝ)) (by simpa using hinv)
  have htend : Tendsto (fun n : ℕ => ((n : ℝ)) ^ k * (ρ⁻¹) ^ n) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  -- eventually the term drops below (2^k · C)⁻¹, contradicting the bound
  have hpos : (0 : ℝ) < ((2 ^ k : ℝ) * C)⁻¹ := by positivity
  have hev := htend.eventually (eventually_lt_nhds hpos)
  obtain ⟨n, hnlt, hn1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hbound := h n hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hstep : ((n + 1 : ℕ) : ℝ) ^ k ≤ (2 : ℝ) ^ k * ((n : ℝ)) ^ k := by
    have h2n : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      push_cast
      linarith
    calc ((n + 1 : ℕ) : ℝ) ^ k ≤ (2 * (n : ℝ)) ^ k :=
          pow_le_pow_left₀ (by positivity) h2n k
      _ = (2 : ℝ) ^ k * ((n : ℝ)) ^ k := by rw [mul_pow]
  have hchain : ρ ^ n ≤ C * ((2 : ℝ) ^ k * ((n : ℝ)) ^ k) :=
    le_trans hbound (mul_le_mul_of_nonneg_left hstep hC.le)
  have hρn : (0 : ℝ) < ρ ^ n := by positivity
  have h2 : ((n : ℝ)) ^ k * (ρ ^ n)⁻¹ < ((2 ^ k : ℝ) * C)⁻¹ := by
    simpa [inv_pow] using hnlt
  have hflip : ((n : ℝ)) ^ k < ((2 ^ k : ℝ) * C)⁻¹ * ρ ^ n := by
    calc ((n : ℝ)) ^ k = ((n : ℝ)) ^ k * (ρ ^ n)⁻¹ * ρ ^ n := by
          field_simp
      _ < ((2 ^ k : ℝ) * C)⁻¹ * ρ ^ n :=
          mul_lt_mul_of_pos_right h2 hρn
  have hCk : (0 : ℝ) < (2 ^ k : ℝ) * C := by positivity
  have hfinal : C * ((2 : ℝ) ^ k * ((n : ℝ)) ^ k) < ρ ^ n := by
    calc C * ((2 : ℝ) ^ k * ((n : ℝ)) ^ k)
        = ((2 ^ k : ℝ) * C) * ((n : ℝ)) ^ k := by ring
      _ < ((2 ^ k : ℝ) * C) * (((2 ^ k : ℝ) * C)⁻¹ * ρ ^ n) :=
          mul_lt_mul_of_pos_left hflip hCk
      _ = ρ ^ n := by field_simp
  linarith

/-- **Temperedness from the polynomial ceiling** on both channels. -/
theorem strand_radius_one_of_poly_ceiling {α : ℂ} (hα : α ≠ 0) {C : ℝ} (k : ℕ)
    (hC : 0 < C)
    (htop : ∀ r : ℕ, 1 ≤ r → ‖α ^ r‖ ≤ C * ((r + 1 : ℕ) : ℝ) ^ k)
    (hbot : ∀ r : ℕ, 1 ≤ r → ‖(α⁻¹) ^ r‖ ≤ C * ((r + 1 : ℕ) : ℝ) ^ k) :
    ‖α‖ = 1 := by
  have hpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have h1 : ‖α‖ ≤ 1 :=
    le_one_of_pow_le_poly k (norm_nonneg α) hC (fun n hn => by
      simpa [norm_pow] using htop n hn)
  have h2 : ‖α‖⁻¹ ≤ 1 := by
    have := le_one_of_pow_le_poly k (norm_nonneg α⁻¹) hC (fun n hn => by
      simpa [norm_pow] using hbot n hn)
    simpa [norm_inv] using this
  exact eq_one_of_le_one_inv_le_one hpos h1 h2

/-! ## The seed layer at the honest strength -/

/-- **The polynomial per-rung ceiling** on the Maass seed — the classical
Jacquet–Shalika shape, with constants allowed to grow like the `r+1` channels of
`Sym^r`. -/
structure MaassPolyCeiling (M : MaassEigenData) where
  C : Nat.Primes → ℝ
  C_pos : ∀ p : Nat.Primes, 0 < C p
  k : ℕ
  top : ∀ (p : Nat.Primes) (r : ℕ), 1 ≤ r →
    ‖(SatakeSeed.ofMaass M).satake p ^ r‖ ≤ C p * ((r + 1 : ℕ) : ℝ) ^ k
  bottom : ∀ (p : Nat.Primes) (r : ℕ), 1 ≤ r →
    ‖((SatakeSeed.ofMaass M).satake p)⁻¹ ^ r‖ ≤ C p * ((r + 1 : ℕ) : ℝ) ^ k

/-- **Sato–Tate (i) from the polynomial input**: temperedness at every prime. -/
theorem maass_temperedness_poly (M : MaassEigenData) (hP : MaassPolyCeiling M)
    (p : Nat.Primes) : ‖(SatakeSeed.ofMaass M).satake p‖ = 1 :=
  strand_radius_one_of_poly_ceiling ((SatakeSeed.ofMaass M).satake_ne_zero p)
    hP.k (hP.C_pos p) (hP.top p) (hP.bottom p)

/-- Once the radius closes at `1`, the **uniform** ceiling holds with `C = 1`:
the polynomial input manufactures the uniform one, and the entire downstream
corpus — the Sato–Tate family, the Hodge fork, the shadow detector — inherits
verbatim. -/
noncomputable def MaassPolyCeiling.toCeiling {M : MaassEigenData}
    (hP : MaassPolyCeiling M) : MaassTowerCeiling M where
  C := fun _ => 1
  top := fun p r _ => by
    rw [norm_pow, maass_temperedness_poly M hP p, one_pow]
  bottom := fun p r _ => by
    rw [norm_pow, norm_inv, maass_temperedness_poly M hP p, inv_one, one_pow]

/-- **The non-Galois-type hypothesis, compiled**: an equidistributing seed admits
no monomial shadow at any finite order — the classical corollary's
"non-dihedral" exclusion is now the theorem-shaped absence the fork detects. -/
theorem maass_no_shadow_of_ST (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (h : Tendsto (empiricalPrimeCarrierMeasure (maassSatoTateFamily M hC).angle)
      atTop (nhds carrierProbability)) :
    ¬ Nonempty (CriticalLinePhasor.ShadowDetector.MonomialShadow
      (maassSatoTateFamily M hC)) :=
  no_shadow_of_equidistributed _ h

end CriticalLinePhasor.PolyCeiling

#print axioms CriticalLinePhasor.PolyCeiling.le_one_of_pow_le_poly
#print axioms CriticalLinePhasor.PolyCeiling.strand_radius_one_of_poly_ceiling
#print axioms CriticalLinePhasor.PolyCeiling.maass_temperedness_poly
#print axioms CriticalLinePhasor.PolyCeiling.MaassPolyCeiling.toCeiling
#print axioms CriticalLinePhasor.PolyCeiling.maass_no_shadow_of_ST
