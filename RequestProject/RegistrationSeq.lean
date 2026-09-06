import RequestProject.RegistrationDC
import RequestProject.RegistrationResidualSupport
import RequestProject.PrimeStrain

/-!
# Height-matched registration: one strain per station (ledger 604, Draft A)

The fixed-cutoff door (601) is empty: a single bounded strain would force `S` bounded (603). The
registry uses one bank per window, so the object is a SEQUENCE of strains `Ŝ_n`, each continuous
and bounded, with the bank growing in `n`. The `n`-th station is the first crossing above `10` of the
level `n − 3/2` by `ϑ/π + Ŝ_n`:

  `seqStation Ŝ n := station (Ŝ n) n`.

Everything of 601 applies per index. New here:

* `seqStation_tendsto`: the stations escape to infinity as soon as the bank bounds grow slower than
  the index (`B n ≤ n/2` eventually);
* `seqResid_station`: at the `n`-th station the residual against its own strain is `N(t_n) − n + ½`
  exactly;
* `onePerGap_of_seqResid`: strict station order plus the adjacent residual law
  `|R_{n+1}(t_{n+1}) − R_n(t_n)| < 1` give one zero per gap;
* `nontrivialZeros_online_of_seqResid`, `simple_of_seqResid`: RH and simplicity, the first station at
  or below `58`;
* `nontrivialZeros_online_of_primeSeqResid`: the same on the registry's object, cutoffs `X n`;
* `seqResid_station_abs_le`: the DC of 602 per station, with the explicit constant `24 + |A'| + B n`.

**Inhabitant under RH and simplicity (the 603 calibration rule).** Take `Ŝ_n ≡ n − 3/2 − ϑ(γ_n)/π`
with `γ_n` the `n`-th positive ordinate. Then `ϑ/π + Ŝ_n` crosses `n − 3/2` first at `γ_n` (`ϑ`
strictly increasing above `10`), the stations are the zeros, strictly increasing, and
`R_n(γ_n) = N(γ_n) − n + ½ = ½` for every `n`, so the adjacent law holds with margin `1`. The
hypothesis is inhabited; what the registry adds is that the inhabitant is prime-computable.
-/

open Complex Finset Filter Topology Set
open CriticalLinePhasor.CarrierScale (theta clockRate)

namespace CriticalLinePhasor.ContourArgument

/-- A strain per station index, each continuous and bounded. -/
structure StrainSeq where
  q : ℕ → ℝ → ℝ
  B : ℕ → ℝ
  cont : ∀ n, Continuous (q n)
  bound : ∀ n t, |q n t| ≤ B n

/-- The `n`-th station of the height-matched clock. -/
noncomputable def seqStation (Q : StrainSeq) (n : ℕ) : ℝ := station (Q.q n) n

/-- Admissibility of an index: its level lies above its own clock at `10`. -/
def StrainSeq.Adm (Q : StrainSeq) (n : ℕ) : Prop := regClock (Q.q n) 10 < stationLevel n

theorem seqStation_spec (Q : StrainSeq) {n : ℕ} (hn : Q.Adm n) :
    10 ≤ seqStation Q n ∧ regClock (Q.q n) (seqStation Q n) = stationLevel n :=
  station_spec (Q.cont n) (Q.bound n) hn

/-- Bank growth slower than the index forces the stations to escape. -/
theorem seqStation_tendsto (Q : StrainSeq) (hadm : ∀ n, Q.Adm n)
    (hgrow : ∀ᶠ n in atTop, Q.B n ≤ (n : ℝ) / 2) :
    Tendsto (seqStation Q) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  -- ϑ is bounded on `[10, max 10 M]`; a station there would have level ≤ bounded + B n ≤ bounded + n/2
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (10:ℝ)) (b := max 10 M)).exists_bound_of_continuousOn
    (CriticalLinePhasor.CarrierScale.theta_continuous.continuousOn)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hgrow
  refine ⟨max N₁ (⌈2 * K / Real.pi⌉₊ + 4), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : ⌈2 * K / Real.pi⌉₊ + 4 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨h10, hG⟩ := seqStation_spec Q (hadm n)
  by_contra hlt
  simp only [not_le] at hlt
  have hmem : seqStation Q n ∈ Icc (10:ℝ) (max 10 M) := ⟨h10, hlt.le.trans (le_max_right _ _)⟩
  have hθ := hK _ hmem
  rw [Real.norm_eq_abs] at hθ
  have hπ := Real.pi_pos
  have hq := (abs_le.1 (Q.bound n (seqStation Q n))).2
  have hBn := hN₁ n hn1
  -- level = ϑ/π + q ≤ K/π + n/2
  unfold regClock stationLevel at hG
  have hθπ : theta (seqStation Q n) / Real.pi ≤ K / Real.pi :=
    div_le_div_of_nonneg_right (abs_le.1 hθ).2 hπ.le
  have hKπ : 2 * K / Real.pi ≤ (⌈2 * K / Real.pi⌉₊ : ℝ) := Nat.le_ceil _
  have hn2' : (⌈2 * K / Real.pi⌉₊ : ℝ) + 4 ≤ n := by exact_mod_cast hn2
  have hK2 : K / Real.pi ≤ (n : ℝ) / 2 - 2 := by
    have : 2 * K / Real.pi = 2 * (K / Real.pi) := by ring
    linarith
  linarith

/-- **The residual at the `n`-th station, against its own strain, is `N(t_n) − n + ½` exactly.** -/
theorem seqResid_station (Q : StrainSeq) {n : ℕ} (hn : Q.Adm n) :
    resid (Q.q n) (seqStation Q n) = (stripZeroCountMult (seqStation Q n) : ℝ) - n + 1 / 2 :=
  resid_station (Q.cont n) (Q.bound n) hn

/-- The adjacent residual difference is the gap count minus one. -/
theorem seqResid_adjacent (Q : StrainSeq) {n : ℕ} (hn : Q.Adm n) (hn' : Q.Adm (n + 1))
    (hlt : seqStation Q n < seqStation Q (n + 1)) :
    resid (Q.q (n + 1)) (seqStation Q (n + 1)) - resid (Q.q n) (seqStation Q n)
      = (bandCountMult (seqStation Q n) (seqStation Q (n + 1)) : ℝ) - 1 := by
  rw [seqResid_station Q hn', seqResid_station Q hn]
  have hc := bandCountMult_add hlt.le
  have hcr : (bandCountMult (seqStation Q n) (seqStation Q (n + 1)) : ℝ) +
      stripZeroCountMult (seqStation Q n) = stripZeroCountMult (seqStation Q (n + 1)) := by
    exact_mod_cast hc
  push_cast
  linarith

/-- **One zero per gap from the adjacent residual law.** -/
theorem onePerGap_of_seqResid (Q : StrainSeq) (hadm : ∀ n, Q.Adm n)
    (hmono : StrictMono (seqStation Q))
    (hgrow : ∀ᶠ n in atTop, Q.B n ≤ (n : ℝ) / 2) {n₀ : ℕ}
    (hstep : ∀ n, n₀ ≤ n →
      |resid (Q.q (n + 1)) (seqStation Q (n + 1)) - resid (Q.q n) (seqStation Q n)| < 1) :
    OnePerGap (fun k => seqStation Q (n₀ + k)) where
  mono := fun a b hab => hmono (by omega)
  unbounded := by
    have h := (seqStation_tendsto Q hadm hgrow).comp (tendsto_add_atTop_nat n₀)
    refine h.congr (fun k => ?_)
    simp [Function.comp_def, add_comm]
  one := by
    intro k
    have h := hstep (n₀ + k) (Nat.le_add_right n₀ k)
    rw [seqResid_adjacent Q (hadm _) (hadm _) (hmono (Nat.lt_succ_self _))] at h
    have hi : (bandCountMult (seqStation Q (n₀ + k)) (seqStation Q (n₀ + k + 1)) : ℤ) = 1 := by
      apply int_eq_of_abs_sub_lt_one
      exact_mod_cast h
    have hi' : bandCountMult (seqStation Q (n₀ + k)) (seqStation Q (n₀ + k + 1)) = 1 := by
      exact_mod_cast hi
    simpa only [Nat.add_assoc] using hi'

/-- **RH from the height-matched adjacent residual law**, first station at or below `58`. -/
theorem nontrivialZeros_online_of_seqResid (Q : StrainSeq) (hadm : ∀ n, Q.Adm n)
    (hmono : StrictMono (seqStation Q))
    (hgrow : ∀ᶠ n in atTop, Q.B n ≤ (n : ℝ) / 2) {n₀ : ℕ} (h58 : seqStation Q n₀ ≤ 58)
    (hstep : ∀ n, n₀ ≤ n →
      |resid (Q.q (n + 1)) (seqStation Q (n + 1)) - resid (Q.q n) (seqStation Q n)| < 1) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  nontrivialZeros_online_of_onePerGap_of_le_58 (onePerGap_of_seqResid Q hadm hmono hgrow hstep)
    (by simpa using h58)

/-- Simplicity above the first station. -/
theorem simple_of_seqResid (Q : StrainSeq) (hadm : ∀ n, Q.Adm n)
    (hmono : StrictMono (seqStation Q))
    (hgrow : ∀ᶠ n in atTop, Q.B n ≤ (n : ℝ) / 2) {n₀ : ℕ}
    (hstep : ∀ n, n₀ ≤ n →
      |resid (Q.q (n + 1)) (seqStation Q (n + 1)) - resid (Q.q n) (seqStation Q n)| < 1)
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hpos : 0 < ρ.im) (hab : seqStation Q n₀ < ρ.im) :
    ZD.xiOrderNat ρ = 1 :=
  (online_simple_of_onePerGap (onePerGap_of_seqResid Q hadm hmono hgrow hstep) hρ hpos
    (by simpa using hab)).2

/-! ## The registry's object: prime banks with growing cutoffs -/

/-- The height-matched prime strain: cutoff `X n` at station `n`. -/
noncomputable def primeStrainSeq (X : ℕ → ℕ) : StrainSeq where
  q := fun n => primeStrain (X n)
  B := fun n => primeStrainBound (X n)
  cont := fun n => primeStrain_continuous (X n)
  bound := fun n t => abs_primeStrain_le (X n) t

theorem primeStrainSeq_station (X : ℕ → ℕ) (n : ℕ) :
    seqStation (primeStrainSeq X) n = primeStation (X n) n := rfl

/-- **The RH door on the registry's height-matched object.** -/
theorem nontrivialZeros_online_of_primeSeqResid (X : ℕ → ℕ)
    (hadm : ∀ n, regClock (primeStrain (X n)) 10 < stationLevel n)
    (hmono : StrictMono (fun n => primeStation (X n) n))
    (hgrow : ∀ᶠ n in atTop, primeStrainBound (X n) ≤ (n : ℝ) / 2) {n₀ : ℕ}
    (h58 : primeStation (X n₀) n₀ ≤ 58)
    (hstep : ∀ n, n₀ ≤ n →
      |resid (primeStrain (X (n + 1))) (primeStation (X (n + 1)) (n + 1))
        - resid (primeStrain (X n)) (primeStation (X n) n)| < 1) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  nontrivialZeros_online_of_seqResid (primeStrainSeq X) hadm hmono hgrow h58 hstep

/-! ## The DC per station, with its explicit constant -/

/-- **DC of the residual at the `n`-th station, unconditional, constant `24 + |A'| + B n`.** -/
theorem seqResid_station_abs_le (Q : StrainSeq) {A' : ℝ}
    (hA : ∀ t : ℝ, 2 ≤ t → clockRate t ≤ A' + (1 / 2) * Real.log t)
    {n : ℕ} (hn : Q.Adm n) (ht : Real.exp 6 + 1 ≤ seqStation Q n) :
    |resid (Q.q n) (seqStation Q n)|
      ≤ (24 + |A'| + Q.B n) * (Real.log (seqStation Q n + 1) + 1) :=
  resid_station_abs_le' (Q.cont n) (Q.bound n) hA hn ht

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.seqStation_tendsto
#print axioms CriticalLinePhasor.ContourArgument.onePerGap_of_seqResid
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_primeSeqResid
#print axioms CriticalLinePhasor.ContourArgument.seqResid_station_abs_le
