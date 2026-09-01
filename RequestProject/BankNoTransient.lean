import RequestProject.HilbertPolyaResolventTrace
import RequestProject.PrimeClockData

/-!
# The named no-transient residual for the ordered prime-clock bank

This file fixes the data of the D8 Herglotz bank to the canonical prime-power
teeth and square-grid exhaustion from `PrimeClockOrdering`.

The raw Cayley bank contains one positive DC term `ℓ/2` per tooth.  The
quantitative disk-kernel estimate below proves that its negative real part is
at least `N²` times a positive constant at every point left of the half-line.
Consequently the raw `PrimeToothNoTransient` predicate is false for every
unimodular face assignment.  The exact finite centering identity identifies
the corrected bank by subtracting those DC terms.

Search audit:

```
rg -n -i 'PrimeToothNoTransient|primeToothHerglotzBank|no[_ -]?transient|transient[_ -]?free' \
  RequestProject --glob '*.lean'
rg -n -i 'Tendsto.*logDeriv.*riemannXi|Herglotz.*Tendsto|Tendsto.*Herglotz|ledger_balance_constant_free' \
  RequestProject --glob '*.lean'
rg -n -i 'mean.*pointwise|pointwise.*mean|Vitali|Montel|normal family|locally uniform' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n 'normSq.*(add|sub|div)|div_re|re_div|norm_conj|tendsto_atTop_mono' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'
```
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankNoTransient

open CriticalLinePhasor.PrimeClockOrdering

/-- The disk point of a prime-power tooth in the Hilbert--Pólya chart. -/
def primeToothDiskPoint (α : Nat.Primes → ℂ) (i : PrimeTooth) (s : ℂ) : ℂ :=
  (starRingEnd ℂ) (primeToothFace α i) *
    Complex.exp (Complex.I * primeToothLength i *
      CriticalLinePhasor.HilbertPolya.spectralCoord s)

/-- One weighted Cayley/Herglotz tooth. -/
def primeToothHerglotzTerm (α : Nat.Primes → ℂ) (i : PrimeTooth) (s : ℂ) : ℂ :=
  ((primeToothLength i / 2 : ℝ) : ℂ) *
    ((1 + primeToothDiskPoint α i s) / (1 - primeToothDiskPoint α i s))

/-- The finite D8 Herglotz sum for the canonical prime-power tooth bank. -/
def primeToothHerglotzBank (α : Nat.Primes → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  -∑ i ∈ primeToothExhaustion N, primeToothHerglotzTerm α i s

/-- The named pointwise residual: the ordered prime-clock bank has no transient
on the asymptotic channel. -/
def PrimeToothNoTransient (α : Nat.Primes → ℂ) (A : ℝ) : Prop :=
  ∀ s : ℂ, 1269 / 2 < |s.im| →
    A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
    Tendsto (fun N => primeToothHerglotzBank α N s)
      atTop (𝓝 (logDeriv ZD.riemannXi s))

/-- The real part of the disk Cayley kernel in norm-square form. -/
theorem cayley_re_eq (w : ℂ) :
    ((1 + w) / (1 - w)).re =
      (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  rw [Complex.div_re]
  simp only [← Complex.normSq_eq_norm_sq, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.normSq_apply]
  ring

/-- A uniform lower bound for the real part of a disk Cayley kernel. -/
theorem cayley_re_lower {w : ℂ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw : ‖w‖ ≤ q) :
    (1 - q ^ 2) / 4 ≤ ((1 + w) / (1 - w)).re := by
  rw [cayley_re_eq]
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw hq1
  have hwne : 1 - w ≠ 0 := by
    intro h
    have hweq : w = 1 := (eq_of_sub_eq_zero h).symm
    rw [hweq, norm_one] at hw1
    exact (lt_irrefl 1) hw1
  have hden0 : 0 < ‖1 - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwne)
  have hnorm : ‖1 - w‖ ≤ 2 := by
    calc
      ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 1 + q := by simpa using add_le_add_left hw 1
      _ ≤ 2 := by linarith
  have hden4 : ‖1 - w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 - w)]
  have hqnum : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hnum : 1 - q ^ 2 ≤ 1 - ‖w‖ ^ 2 := by
    nlinarith [norm_nonneg w]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hden0]
  calc
    (1 - q ^ 2) * ‖1 - w‖ ^ 2 ≤ (1 - q ^ 2) * 4 :=
      mul_le_mul_of_nonneg_left hden4 hqnum
    _ ≤ (1 - ‖w‖ ^ 2) * 4 :=
      mul_le_mul_of_nonneg_right hnum (by norm_num)

/-- The nonconstant part of one Cayley tooth. -/
def primeToothCenteredTerm (α : Nat.Primes → ℂ) (i : PrimeTooth) (s : ℂ) : ℂ :=
  ((primeToothLength i : ℝ) : ℂ) *
    primeToothDiskPoint α i s / (1 - primeToothDiskPoint α i s)

/-- The second tooth over a prime has twice the first tooth's length. -/
theorem primeToothLength_second_eq_two_mul_first (r : ℕ) :
    primeToothLength (r, 1) = 2 * primeToothLength (r, 0) := by
  simp [primeToothLength, toothExponent]

/-- For unit faces, that second tooth is the square of the first disk mode. -/
theorem primeToothDiskPoint_one_second_eq_first_sq (r : ℕ) (s : ℂ) :
    primeToothDiskPoint (fun _ => 1) (r, 1) s =
      primeToothDiskPoint (fun _ => 1) (r, 0) s ^ 2 := by
  simp [primeToothDiskPoint, primeToothFace, toothExponent, primeToothLength]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The frequency `2·log p` occurs from two teeth and has total weight
`3·log p`, exhibiting the divisor overcount in the all-prime-power bank. -/
theorem first_two_centered_modes_eq_three (r : ℕ) (s : ℂ) :
    ((primeToothLength (r, 0) : ℝ) : ℂ) *
          primeToothDiskPoint (fun _ => 1) (r, 0) s ^ (1 + 1) +
        ((primeToothLength (r, 1) : ℝ) : ℂ) *
          primeToothDiskPoint (fun _ => 1) (r, 1) s ^ (0 + 1) =
      3 * ((primeToothLength (r, 0) : ℝ) : ℂ) *
        primeToothDiskPoint (fun _ => 1) (r, 0) s ^ 2 := by
  rw [primeToothLength_second_eq_two_mul_first,
    primeToothDiskPoint_one_second_eq_first_sq]
  push_cast
  ring

/-- The two-tooth coefficient is not the single von Mangoldt coefficient at
the same frequency, so this bank is not a reindexing of the eta/ledger bank. -/
theorem first_two_centered_modes_ne_single (r : ℕ) (s : ℂ) :
    ((primeToothLength (r, 0) : ℝ) : ℂ) *
          primeToothDiskPoint (fun _ => 1) (r, 0) s ^ (1 + 1) +
        ((primeToothLength (r, 1) : ℝ) : ℂ) *
          primeToothDiskPoint (fun _ => 1) (r, 1) s ^ (0 + 1) ≠
      ((primeToothLength (r, 0) : ℝ) : ℂ) *
        primeToothDiskPoint (fun _ => 1) (r, 0) s ^ 2 := by
  rw [first_two_centered_modes_eq_three]
  have hlength : ((primeToothLength (r, 0) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (primeToothLength_pos (r, 0)))
  have hdisk : primeToothDiskPoint (fun _ => 1) (r, 0) s ≠ 0 := by
    simp [primeToothDiskPoint, primeToothFace]
  have hx : ((primeToothLength (r, 0) : ℝ) : ℂ) *
      primeToothDiskPoint (fun _ => 1) (r, 0) s ^ 2 ≠ 0 :=
    mul_ne_zero hlength (pow_ne_zero 2 hdisk)
  intro h
  apply hx
  linear_combination (1 / 2 : ℂ) * h

theorem log_two_le_primeToothLength (i : PrimeTooth) :
    Real.log 2 ≤ primeToothLength i := by
  rw [primeToothLength_eq_log_toothNat]
  apply Real.log_le_log (by norm_num)
  exact_mod_cast toothNat_two_le i

theorem primeToothDiskPoint_norm_eq
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (i : PrimeTooth) (s : ℂ) :
    ‖primeToothDiskPoint α i s‖ =
      Real.exp (-primeToothLength i * (1 / 2 - s.re)) := by
  rw [primeToothDiskPoint, norm_mul]
  change ‖star (primeToothFace α i)‖ * ‖Complex.exp _‖ = _
  rw [norm_star, primeToothFace_norm α hα, one_mul, Complex.norm_exp]
  have hcoord : (CriticalLinePhasor.HilbertPolya.spectralCoord s).im =
      1 / 2 - s.re := by
    unfold CriticalLinePhasor.HilbertPolya.spectralCoord
    norm_num [Complex.mul_im, Complex.sub_re, Complex.sub_im]
  congr 1
  rw [Complex.mul_re]
  simp [hcoord]

theorem primeToothDiskPoint_norm_lt_one
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (i : PrimeTooth) {s : ℂ} (hs : s.re < 1 / 2) :
    ‖primeToothDiskPoint α i s‖ < 1 := by
  rw [primeToothDiskPoint_norm_eq α hα, Real.exp_lt_one_iff]
  have hpos := mul_pos (primeToothLength_pos i) (sub_pos.mpr hs)
  nlinarith

/-- Every centered tooth expands into all positive multiples of its own clock. -/
theorem primeToothCenteredTerm_hasSum
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (i : PrimeTooth) {s : ℂ} (hs : s.re < 1 / 2) :
    HasSum
      (fun m : ℕ => ((primeToothLength i : ℝ) : ℂ) *
        (primeToothDiskPoint α i s) ^ (m + 1))
      (primeToothCenteredTerm α i s) := by
  have hw : ‖primeToothDiskPoint α i s‖ < 1 :=
    primeToothDiskPoint_norm_lt_one α hα i hs
  have hgeom := (hasSum_geometric_of_norm_lt_one hw).mul_left
    (((primeToothLength i : ℝ) : ℂ) * primeToothDiskPoint α i s)
  rw [show primeToothCenteredTerm α i s =
      (((primeToothLength i : ℝ) : ℂ) * primeToothDiskPoint α i s) *
        (1 - primeToothDiskPoint α i s)⁻¹ by
      simp [primeToothCenteredTerm, div_eq_mul_inv, mul_assoc]]
  simpa only [pow_succ', mul_assoc] using hgeom

theorem primeToothDiskPoint_norm_le_uniform
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (i : PrimeTooth) {s : ℂ} (hs : s.re < 1 / 2) :
    ‖primeToothDiskPoint α i s‖ ≤
      Real.exp (-Real.log 2 * (1 / 2 - s.re)) := by
  rw [primeToothDiskPoint_norm_eq α hα]
  apply Real.exp_le_exp.mpr
  have hy : 0 ≤ 1 / 2 - s.re := (sub_pos.mpr hs).le
  have hl := log_two_le_primeToothLength i
  nlinarith [mul_le_mul_of_nonneg_right hl hy]

theorem primeToothHerglotzTerm_re_lower
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (i : PrimeTooth) {s : ℂ} (hs : s.re < 1 / 2) :
    Real.log 2 / 2 *
        ((1 - (Real.exp (-Real.log 2 * (1 / 2 - s.re))) ^ 2) / 4)
      ≤ (primeToothHerglotzTerm α i s).re := by
  let q : ℝ := Real.exp (-Real.log 2 * (1 / 2 - s.re))
  have hy : 0 < 1 / 2 - s.re := sub_pos.mpr hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos hlog2 hy]
  have hkernel := cayley_re_lower hq0 hq1
    (primeToothDiskPoint_norm_le_uniform α hα i hs)
  have hkernel0 : 0 ≤ (1 - q ^ 2) / 4 := by
    have hprod : 0 < (1 - q) * (1 + q) :=
      mul_pos (sub_pos.mpr hq1) (by linarith)
    nlinarith
  have hlength := log_two_le_primeToothLength i
  unfold primeToothHerglotzTerm
  rw [Complex.re_ofReal_mul]
  dsimp [q] at hkernel0 hkernel ⊢
  calc
    Real.log 2 / 2 *
          ((1 - Real.exp (-Real.log 2 * (1 / 2 - s.re)) ^ 2) / 4)
        ≤ (primeToothLength i / 2) *
          ((1 - Real.exp (-Real.log 2 * (1 / 2 - s.re)) ^ 2) / 4) := by
            gcongr
    _ ≤ (primeToothLength i / 2) *
          ((1 + primeToothDiskPoint α i s) /
            (1 - primeToothDiskPoint α i s)).re := by
            exact mul_le_mul_of_nonneg_left hkernel
              (by positivity [primeToothLength_pos i])

/-- A positive floor shared by every tooth at a fixed left-half-plane point. -/
def primeToothKernelFloor (s : ℂ) : ℝ :=
  Real.log 2 / 2 *
    ((1 - (Real.exp (-Real.log 2 * (1 / 2 - s.re))) ^ 2) / 4)

theorem primeToothKernelFloor_pos {s : ℂ} (hs : s.re < 1 / 2) :
    0 < primeToothKernelFloor s := by
  unfold primeToothKernelFloor
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy : 0 < 1 / 2 - s.re := sub_pos.mpr hs
  have hq : Real.exp (-Real.log 2 * (1 / 2 - s.re)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos hlog2 hy]
  have hq0 : 0 ≤ Real.exp (-Real.log 2 * (1 / 2 - s.re)) :=
    (Real.exp_pos _).le
  have hprod : 0 <
      (1 - Real.exp (-Real.log 2 * (1 / 2 - s.re))) *
        (1 + Real.exp (-Real.log 2 * (1 / 2 - s.re))) :=
    mul_pos (sub_pos.mpr hq) (by linarith)
  have hsquare : 0 < 1 - Real.exp (-Real.log 2 * (1 / 2 - s.re)) ^ 2 := by
    nlinarith
  positivity

/-- The raw bank's negative real part has a quadratic lower bound. -/
theorem primeToothBank_neg_re_lower
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (N : ℕ) {s : ℂ} (hs : s.re < 1 / 2) :
    (N : ℝ) ^ 2 * primeToothKernelFloor s ≤
      (-primeToothHerglotzBank α N s).re := by
  have hcard : (primeToothExhaustion N).card = N * N := by
    simp [primeToothExhaustion]
  calc
    (N : ℝ) ^ 2 * primeToothKernelFloor s =
        ∑ _i ∈ primeToothExhaustion N, primeToothKernelFloor s := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
          push_cast
          ring
    _ ≤ ∑ i ∈ primeToothExhaustion N,
        (primeToothHerglotzTerm α i s).re := by
          apply Finset.sum_le_sum
          intro i hi
          exact primeToothHerglotzTerm_re_lower α hα i hs
    _ = (-primeToothHerglotzBank α N s).re := by
          simp [primeToothHerglotzBank]

theorem primeToothBank_neg_re_tendsto_atTop
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    {s : ℂ} (hs : s.re < 1 / 2) :
    Tendsto (fun N : ℕ => (-primeToothHerglotzBank α N s).re)
      atTop atTop := by
  have hbase : Tendsto
      (fun N : ℕ => (N : ℝ) * primeToothKernelFloor s) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const (primeToothKernelFloor_pos hs))
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [eventually_ge_atTop 1] with N hN
  calc
    (N : ℝ) * primeToothKernelFloor s ≤
        (N : ℝ) ^ 2 * primeToothKernelFloor s := by
          apply mul_le_mul_of_nonneg_right _ (primeToothKernelFloor_pos hs).le
          have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith
    _ ≤ (-primeToothHerglotzBank α N s).re :=
      primeToothBank_neg_re_lower α hα N hs

/-- The raw bank has no finite pointwise limit anywhere left of the line. -/
theorem primeToothHerglotzBank_not_tendsto_nhds
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    {s L : ℂ} (hs : s.re < 1 / 2) :
    ¬ Tendsto (fun N : ℕ => primeToothHerglotzBank α N s)
        atTop (𝓝 L) := by
  intro h
  have hreal : Tendsto
      (fun N : ℕ => (-primeToothHerglotzBank α N s).re)
      atTop (𝓝 (-L).re) :=
    (Complex.continuous_re.tendsto (-L)).comp h.neg
  exact (not_tendsto_atTop_of_tendsto_nhds hreal)
    (primeToothBank_neg_re_tendsto_atTop α hα hs)

theorem not_primeToothNoTransient_of_channel_point
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    {A : ℝ} {s : ℂ}
    (him : 1269 / 2 < |s.im|)
    (hlow : A / (Real.log |s.im|) ^ 9 < s.re)
    (hhigh : s.re < 1 / 2) :
    ¬ PrimeToothNoTransient α A := by
  intro h
  exact primeToothHerglotzBank_not_tendsto_nhds α hα hhigh
    (h s him hlow hhigh)

/-- No positive corridor constant makes the raw bank converge. -/
theorem no_positive_primeToothNoTransient
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1) :
    ¬ ∃ A : ℝ, 0 < A ∧ PrimeToothNoTransient α A := by
  rintro ⟨A, hA, htransient⟩
  let x : ℝ := A + 1000
  let t : ℝ := Real.exp x
  let s : ℂ := (1 / 4 : ℝ) + Complex.I * t
  have hx0 : 0 < x := by dsimp [x]; linarith
  have ht0 : 0 < t := by dsimp [t]; exact Real.exp_pos _
  have hsre : s.re = 1 / 4 := by simp [s]
  have hsim : |s.im| = t := by simp [s, abs_of_pos ht0]
  have him : 1269 / 2 < |s.im| := by
    rw [hsim]
    have hexp : x + 1 ≤ t := by
      dsimp [t]
      exact Real.add_one_le_exp x
    dsimp [x] at hexp
    linarith
  have hlow : A / (Real.log |s.im|) ^ 9 < s.re := by
    rw [hsim, hsre]
    change A / (Real.log (Real.exp x)) ^ 9 < (1 / 4 : ℝ)
    rw [Real.log_exp]
    have hx1 : 1 ≤ x := by dsimp [x]; linarith
    have hxpow : x ^ 2 ≤ x ^ 9 := pow_le_pow_right₀ hx1 (by norm_num)
    have hx2 : 4 * A < x ^ 2 := by
      dsimp [x]
      nlinarith [sq_nonneg A]
    rw [div_lt_iff₀ (pow_pos hx0 9)]
    nlinarith
  have hhigh : s.re < 1 / 2 := by rw [hsre]; norm_num
  exact (not_primeToothNoTransient_of_channel_point α hα him hlow hhigh)
    htransient

theorem no_positive_primeToothNoTransient_one :
    ¬ ∃ A : ℝ, 0 < A ∧ PrimeToothNoTransient (fun _ => 1) A :=
  no_positive_primeToothNoTransient (fun _ => 1) (fun _ => norm_one)

theorem one_sub_primeToothDiskPoint_ne_zero
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (i : PrimeTooth) {s : ℂ} (hs : s.re < 1 / 2) :
    1 - primeToothDiskPoint α i s ≠ 0 := by
  intro h
  have hw : primeToothDiskPoint α i s = 1 := (eq_of_sub_eq_zero h).symm
  have := primeToothDiskPoint_norm_lt_one α hα i hs
  rw [hw, norm_one] at this
  exact (lt_irrefl 1) this

/-- Each raw tooth is its DC term plus its centered term. -/
theorem primeToothHerglotzTerm_eq_dc_add_centered
    (α : Nat.Primes → ℂ) (i : PrimeTooth) (s : ℂ)
    (hdenom : 1 - primeToothDiskPoint α i s ≠ 0) :
    primeToothHerglotzTerm α i s =
      ((primeToothLength i / 2 : ℝ) : ℂ) + primeToothCenteredTerm α i s := by
  unfold primeToothHerglotzTerm primeToothCenteredTerm
  field_simp
  push_cast
  ring

def primeToothDCMass (N : ℕ) : ℂ :=
  ∑ i ∈ primeToothExhaustion N, ((primeToothLength i / 2 : ℝ) : ℂ)

def primeToothCenteredBank (α : Nat.Primes → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  -∑ i ∈ primeToothExhaustion N, primeToothCenteredTerm α i s

/-- Exact finite-rank separation of the divergent DC mass. -/
theorem primeToothHerglotzBank_eq_neg_dc_add_centered
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (N : ℕ) {s : ℂ} (hs : s.re < 1 / 2) :
    primeToothHerglotzBank α N s =
      -primeToothDCMass N + primeToothCenteredBank α N s := by
  unfold primeToothHerglotzBank primeToothDCMass primeToothCenteredBank
  rw [Finset.sum_congr rfl (fun i _ =>
    primeToothHerglotzTerm_eq_dc_add_centered α i s
      (one_sub_primeToothDiskPoint_ne_zero α hα i hs))]
  rw [Finset.sum_add_distrib]
  ring

/-- The explicitly renormalized bank. -/
def primeToothRenormalizedBank (α : Nat.Primes → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  primeToothHerglotzBank α N s + primeToothDCMass N

theorem primeToothRenormalizedBank_eq_centered
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (N : ℕ) {s : ℂ} (hs : s.re < 1 / 2) :
    primeToothRenormalizedBank α N s = primeToothCenteredBank α N s := by
  rw [primeToothRenormalizedBank,
    primeToothHerglotzBank_eq_neg_dc_add_centered α hα N hs]
  ring

/-- The corrected pointwise residual after removing the explicit DC mass. -/
def PrimeToothCenteredNoTransient (α : Nat.Primes → ℂ) (A : ℝ) : Prop :=
  ∀ s : ℂ, 1269 / 2 < |s.im| →
    A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
    Tendsto (fun N => primeToothCenteredBank α N s)
      atTop (𝓝 (logDeriv ZD.riemannXi s))

end CriticalLinePhasor.BankNoTransient

#print axioms CriticalLinePhasor.BankNoTransient.PrimeToothNoTransient
#print axioms CriticalLinePhasor.BankNoTransient.cayley_re_lower
#print axioms CriticalLinePhasor.BankNoTransient.primeToothCenteredTerm_hasSum
#print axioms CriticalLinePhasor.BankNoTransient.first_two_centered_modes_eq_three
#print axioms CriticalLinePhasor.BankNoTransient.first_two_centered_modes_ne_single
#print axioms CriticalLinePhasor.BankNoTransient.primeToothBank_neg_re_tendsto_atTop
#print axioms CriticalLinePhasor.BankNoTransient.primeToothHerglotzBank_not_tendsto_nhds
#print axioms CriticalLinePhasor.BankNoTransient.no_positive_primeToothNoTransient
#print axioms CriticalLinePhasor.BankNoTransient.no_positive_primeToothNoTransient_one
#print axioms CriticalLinePhasor.BankNoTransient.primeToothHerglotzBank_eq_neg_dc_add_centered
#print axioms CriticalLinePhasor.BankNoTransient.primeToothRenormalizedBank_eq_centered
#print axioms CriticalLinePhasor.BankNoTransient.PrimeToothCenteredNoTransient
