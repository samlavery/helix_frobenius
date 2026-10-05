import RequestProject.SmoothedPrimeSignalRH

/-!
# The one input of the smoothed-prime-signal chain, stated exactly

`LowerBound` is the single hypothesis of `SmoothedPrimeSignal.riemannHypothesis_of_lowerBound` (ledger 917):
the smoothed prime signal `W(y) = Σ Λ(n) n^{−½} e^{−(y − log n)²}` never falls more than a fixed amount below its
exact DC `D e^{y/2}`, `D = √π e^{1/16}`.

* `lowerBound_iff_isBoundedUnder`: only the tail matters — the input says the deficit `D e^{y/2} − W(y)` is bounded
  above as `y → ∞` (on any bounded range it is bounded for free, since `W ≥ 0`).
* `lowerBound_iff_psiK`: in the multiplicative chart `x = e^y` the input reads `ψ_K(x) ≥ D x − C √x` for `x ≥ 1`, with
  `ψ_K(x) = Σ Λ(n) (x/n)^{1/2} e^{−log²(x/n)}`.
-/

open Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace SmoothedPrimeSignal

/-- **The one input.** -/
def LowerBound : Prop := ∃ C : ℝ, ∀ y : ℝ, 0 ≤ y → D * Real.exp (y / 2) - C ≤ W y

theorem riemannHypothesis_of_LowerBound (h : LowerBound) : RiemannHypothesis := by
  obtain ⟨C, hC⟩ := h
  exact riemannHypothesis_of_lowerBound C hC

theorem D_pos : 0 < D := mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)

/-- **Only the tail matters.** -/
theorem lowerBound_iff_eventually :
    LowerBound ↔ ∃ C Y : ℝ, ∀ y : ℝ, Y ≤ y → D * Real.exp (y / 2) - C ≤ W y := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, 0, hC⟩
  · rintro ⟨C, Y, hC⟩
    refine ⟨max C (D * Real.exp (max Y 0 / 2)), fun y _ => ?_⟩
    rcases le_or_gt Y y with hyY | hyY
    · have h1 := hC y hyY
      have h2 : C ≤ max C (D * Real.exp (max Y 0 / 2)) := le_max_left _ _
      linarith
    · have hW := W_nonneg y
      have hexp : D * Real.exp (y / 2) ≤ D * Real.exp (max Y 0 / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [le_max_left Y 0])) D_pos.le
      have h2 : D * Real.exp (max Y 0 / 2) ≤ max C (D * Real.exp (max Y 0 / 2)) := le_max_right _ _
      linarith

/-- **The input is a statement about `y → ∞`**: the deficit of the smoothed prime signal below its exact DC is
bounded above along `atTop`. -/
theorem lowerBound_iff_isBoundedUnder :
    LowerBound ↔ IsBoundedUnder (· ≤ ·) atTop (fun y => D * Real.exp (y / 2) - W y) := by
  rw [lowerBound_iff_eventually]
  constructor
  · rintro ⟨C, Y, hC⟩
    refine ⟨C, eventually_map.2 (eventually_atTop.2 ⟨Y, fun y hy => ?_⟩)⟩
    have h := hC y hy
    show D * Real.exp (y / 2) - W y ≤ C
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨Y, hY⟩ := eventually_atTop.1 (eventually_map.1 hC)
    refine ⟨C, Y, fun y hy => ?_⟩
    have h : D * Real.exp (y / 2) - W y ≤ C := hY y hy
    linarith

/-- The smoothed prime signal in the multiplicative chart `x = e^y`. -/
noncomputable def psiK (x : ℝ) : ℝ :=
  ∑' n : ℕ, Λ n * (x / n) ^ (1 / 2 : ℝ) * Real.exp (-(Real.log (x / n)) ^ 2)

theorem psiK_eq {x : ℝ} (hx : 0 < x) : psiK x = Real.sqrt x * W (Real.log x) := by
  unfold psiK W
  rw [← tsum_mul_left]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hpow : (n : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn' _).ne'
    rw [Real.div_rpow hx.le hn'.le, Real.log_div hx.ne' hn'.ne', Real.sqrt_eq_rpow]
    simp only [a, K]
    rw [Real.rpow_neg hn'.le]
    field_simp

theorem exp_half_log {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

/-- **The input in the multiplicative chart**: `ψ_K(x) ≥ D x − C √x` for every `x ≥ 1`. -/
theorem lowerBound_iff_psiK :
    LowerBound ↔ ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → D * x - C * Real.sqrt x ≤ psiK x := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have h := hC (Real.log x) (Real.log_nonneg hx)
    rw [exp_half_log hx0] at h
    rw [psiK_eq hx0]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hm := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg x)
    calc D * x - C * Real.sqrt x = Real.sqrt x * (D * Real.sqrt x - C) := by
          linear_combination (-D) * hxx
      _ ≤ Real.sqrt x * W (Real.log x) := hm
  · rintro ⟨C, hC⟩
    refine ⟨C, fun y hy => ?_⟩
    have hx : 1 ≤ Real.exp y := by simpa using Real.exp_le_exp.mpr hy
    have h := hC (Real.exp y) hx
    have hsq : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
      rw [← exp_half_log (Real.exp_pos y), Real.log_exp]
    rw [psiK_eq (Real.exp_pos y), Real.log_exp, hsq] at h
    have hpos : 0 < Real.exp (y / 2) := Real.exp_pos _
    have hexp : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hexp] at h
    have h' : Real.exp (y / 2) * (D * Real.exp (y / 2) - C) ≤ Real.exp (y / 2) * W y := by
      calc Real.exp (y / 2) * (D * Real.exp (y / 2) - C)
          = D * (Real.exp (y / 2) * Real.exp (y / 2)) - C * Real.exp (y / 2) := by ring
        _ ≤ Real.exp (y / 2) * W y := h
    exact le_of_mul_le_mul_left h' hpos

/-! ## No finite set of prime powers is consumed by the input -/

/-- The signal with the prime powers in a finite set `S` removed. -/
noncomputable def Wdrop (S : Finset ℕ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, (if n ∈ S then 0 else a n) * K (y - Real.log n)

theorem K_le_one (x : ℝ) : K x ≤ 1 := by
  unfold K
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg x]

theorem W_eq_Wdrop_add (S : Finset ℕ) (y : ℝ) :
    W y = Wdrop S y + ∑ n ∈ S, a n * K (y - Real.log n) := by
  have hf := summable_terms y
  have hg : Summable (fun n : ℕ => (if n ∈ S then 0 else a n) * K (y - Real.log n)) := by
    refine hf.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · split_ifs
      · simp
      · exact term_nonneg y n
    · split_ifs
      · simpa using term_nonneg y n
      · exact le_rfl
  have hh : Summable (fun n : ℕ => if n ∈ S then a n * K (y - Real.log n) else 0) :=
    summable_of_ne_finset_zero (s := S) (fun n hn => by simp [hn])
  have htot : ∑' n : ℕ, a n * K (y - Real.log n) =
      ∑' n : ℕ, (if n ∈ S then 0 else a n) * K (y - Real.log n) +
        ∑' n : ℕ, (if n ∈ S then a n * K (y - Real.log n) else 0) := by
    rw [← hg.tsum_add hh]
    exact tsum_congr fun n => by split_ifs <;> ring
  have hfin : ∑' n : ℕ, (if n ∈ S then a n * K (y - Real.log n) else 0) =
      ∑ n ∈ S, a n * K (y - Real.log n) := by
    rw [tsum_eq_sum (s := S) (fun n hn => by simp [hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [hn])
  unfold W Wdrop
  rw [htot, hfin]

/-- **The input does not depend on any finite set of prime powers.**  Removing the terms `n ∈ S` changes the signal by
at most `Σ_{n ∈ S} Λ(n) n^{−½}` at every `y`, so the one-sided bound holds for the full signal iff it holds for the
depleted one. What the input reads is the tail of the prime-power distribution. -/
theorem lowerBound_iff_drop (S : Finset ℕ) :
    LowerBound ↔ ∃ C : ℝ, ∀ y : ℝ, 0 ≤ y → D * Real.exp (y / 2) - C ≤ Wdrop S y := by
  have hle : ∀ y, ∑ n ∈ S, a n * K (y - Real.log n) ≤ ∑ n ∈ S, a n := fun y =>
    Finset.sum_le_sum fun n _ => by
      simpa using mul_le_mul_of_nonneg_left (K_le_one (y - Real.log n)) (a_nonneg n)
  have hnn : ∀ y, 0 ≤ ∑ n ∈ S, a n * K (y - Real.log n) := fun y =>
    Finset.sum_nonneg fun n _ => term_nonneg y n
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + ∑ n ∈ S, a n, fun y hy => ?_⟩
    have h1 := hC y hy
    have h2 := W_eq_Wdrop_add S y
    have h3 := hle y
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C, fun y hy => ?_⟩
    have h1 := hC y hy
    have h2 := W_eq_Wdrop_add S y
    have h3 := hnn y
    linarith

end SmoothedPrimeSignal
