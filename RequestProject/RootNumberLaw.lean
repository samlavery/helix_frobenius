import Mathlib

/-!
# The root-number law of the tensor tower: forced central zeros at `g = 2^k + 1`

The tensor-tower atlas' arithmetic reflex, formalised as pure combinatorial number
theory.  For the `g`-fold tensor of weight-1 motives the archimedean piece of the global
root number is `i^{A(g)}`, where `A(g)` is the **archimedean exponent** read off the Hodge
diamond: pairing the conjugate lanes `(p, q)` with `p + q = g`, each contributes
`(q - p + 1)·C(g, p)` to `A`, plus a half-share `C(g, g/2)/2` of the balanced middle block
when `g` is even (`archExponent`).  Measured against the atlas this is exact —
`A(2..20) = 4, 10, 20, 46, 92, 204, 408, 886, …` (`#eval` matches the ledger termwise).

The law, proven here unconditionally:

  **`A(g)` is always even (so `ε = i^{A(g)} ∈ {±1}`, self-dual at every grade), and for odd
  `g ≥ 3` the sign is `−1` — a forced central zero — iff `g = 2^k + 1`.**

Everything reduces to a closed form and a Kummer-style 2-adic digit condition:

* `archExponent_closed_form` — the diamond sum collapses to `A(g) = 2^{g-1} + g·C(g-1,
  ⌊(g-1)/2⌋)` for `g ≥ 1`.  Proof: the deviation part `∑ (g-2p)·C(g,p)` telescopes
  (`telescope`, `telescopeNat`) to `g·C(g-1, ⌊(g-1)/2⌋)`; the flat part is a half-row sum,
  `2^{g-1}` (`Nat.sum_range_choose_halfway` for odd `g`, `even_half` for even).
* `archExponent_even` — `A(g)` is even (central binomial parity), so `ε` is real.
* `rootNumber` / `rootNumber_eq_neg_one_iff` / `rootNumber_eq_one_iff` — `ε = i^{A(g)}`,
  and since `A(g)` is even `ε = (-1)^{A(g)/2}`, so `ε = −1 ↔ A(g) ≡ 2 (mod 4)` and
  `ε = 1 ↔ A(g) ≡ 0 (mod 4)` (`rootNumber_eq_one_or_neg_one` records that these exhaust it).
* `v2_central` — `v₂(C(2m, m)) = s₂(m)`, the base-2 digit sum of `m`, via Legendre's
  formula (`v₂(m!) = m - s₂(m)`) and `v₂((2m)!) = v₂(m!) + m`.
* `sum_digits_two_eq_one_iff_pow` — `s₂(m) = 1 ↔ m` is a power of two.  Together with
  `v2_central` this is the Kummer criterion `v₂(C(2m, m)) = 1 ↔ m = 2^j`.
* `odd_mod_four` — for odd `g = 2m+1`, `A(g) ≡ 2 (mod 4) ↔ ∃ j, m = 2^j`
  (`2^{2m} ≡ 0`, the odd cofactor `2m+1` is a unit mod 4, and `v₂(C(2m,m)) = 1 ↔ C ≡ 2`).
* `even_mod_four` — for even `g`, `A(g) ≡ 0 (mod 4)`: no even grade forces a zero.
* `eps_neg_iff` — **the headline**: for odd `g ≥ 3`, `i^{A(g)} = −1 ↔ g = 2^k + 1` with
  `k ≥ 1`; `eps_even` gives `i^{A(g)} = 1` for even `g`.
* `eps_three`, `eps_five`, `eps_nine`, `eps_seventeen` (`= −1`) and `eps_seven`,
  `eps_eleven` (`= +1`) — the pre-committed prediction grades pinned as theorems.  Grades 3
  and 5 are measured (the Ceresa rung and its successor); `9` and `17` are the pre-committed
  forced-vanishing predictions (`g = 2^3 + 1`, `g = 2^4 + 1`); `7` and `11`, though odd,
  do **not** vanish — the guard against the naive "odd weight ⇒ sign `−1`" guess.

**Scope.**  This formalises the *arithmetic* of the house archimedean-exponent recipe and
the forced-vanishing criterion it produces: the closed form, the parity of `A(g)`, and the
2-adic digit law for the sign.  The identification of `A(g)` with Deligne's archimedean
`ε`-exponent for the tensor motive — hence of `i^{A(g)}` with the actual archimedean root
number — is the cited classical input (Deligne, *Les constantes des équations
fonctionnelles des fonctions L*, LNM 349), used to name the object, not claimed here.
Nothing here assumes or proves RH/GRH.  No `axiom`, no `sorry`.
-/

open Finset

namespace RootNumberLaw

/-- The **archimedean exponent** of the `g`-fold tensor tower, read off the Hodge diamond.
Indexing the conjugate lanes by `p < g/2` with partner `q = g - p`, lane `p` contributes
`(q - p + 1)·C(g, p) = (g - 2p + 1)·C(g, p)` (the summation range `range ((g+1)/2)` is
exactly `{p : 2p < g}`); when `g` is even the balanced middle block adds its half-share
`C(g, g/2)/2`.  The archimedean root number is `i^{archExponent g}`. -/
def archExponent (g : ℕ) : ℕ :=
  (∑ p ∈ Finset.range ((g + 1) / 2), (g - 2 * p + 1) * Nat.choose g p)
    + (if Even g then Nat.choose g (g / 2) / 2 else 0)

/-! ## The closed form -/

/-- **Telescoping identity** (in `ℤ`): the Hodge-deviation sum `∑_{p ≤ n} (g - 2p)·C(g, p)`
collapses to `g·C(g-1, n)`.  Each summand is the forward difference
`g·C(g-1, p) - g·C(g-1, p-1)` (Pascal `C(g, p+1) = C(g-1, p) + C(g-1, p+1)` and absorption
`(p+1)·C(g, p+1) = g·C(g-1, p)`), so the sum telescopes. -/
theorem telescope (g : ℕ) (hg : 1 ≤ g) (n : ℕ) :
    (∑ p ∈ range (n + 1), ((g : ℤ) - 2 * p) * (g.choose p : ℤ)) = g * ((g - 1).choose n : ℤ) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hpasc : ((g' + 1).choose (n + 1) : ℤ) = (g'.choose n : ℤ) + (g'.choose (n + 1) : ℤ) := by
        exact_mod_cast Nat.choose_succ_succ g' n
      have habs : (((g' + 1) * g'.choose n : ℕ) : ℤ)
          = ((g' + 1).choose (n + 1) : ℤ) * ((n : ℤ) + 1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq g' n
      push_cast at hpasc habs ⊢
      linear_combination ((g' : ℤ) + 1) * hpasc + 2 * habs

/-- The telescoping identity transported to `ℕ`: for `2n ≤ g` (so `g - 2p` is the genuine
difference on the whole range), `∑_{p ≤ n} (g - 2p)·C(g, p) = g·C(g-1, n)`. -/
theorem telescopeNat (g : ℕ) (hg : 1 ≤ g) (n : ℕ) (hn : 2 * n ≤ g) :
    (∑ p ∈ range (n + 1), (g - 2 * p) * g.choose p) = g * (g - 1).choose n := by
  have key := telescope g hg n
  have hz : ((∑ p ∈ range (n + 1), (g - 2 * p) * g.choose p : ℕ) : ℤ)
          = ∑ p ∈ range (n + 1), ((g : ℤ) - 2 * (p : ℤ)) * (g.choose p : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [Finset.mem_range] at hp
    have h2 : 2 * p ≤ g := by omega
    rw [Nat.cast_mul, Nat.cast_sub h2]; push_cast; ring
  rw [key] at hz; exact_mod_cast hz

/-- **Half of a symmetric even row**: `2·∑_{p < m} C(2m, p) + C(2m, m) = 4^m`.  The full row
sums to `2^{2m} = 4^m` (`Nat.sum_range_choose`) and the strict upper half reflects onto the
strict lower half (`Finset.sum_range_reflect`, `Nat.choose_symm`). -/
theorem even_half (m : ℕ) :
    2 * (∑ p ∈ range m, (2 * m).choose p) + (2 * m).choose m = 4 ^ m := by
  have hfull : (∑ p ∈ range (2 * m + 1), (2 * m).choose p) = 4 ^ m := by
    rw [Nat.sum_range_choose, pow_mul]; norm_num
  rw [Finset.range_eq_Ico] at hfull
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) (by omega : m + 1 ≤ 2 * m + 1)] at hfull
  have hlow : (∑ p ∈ Ico 0 (m + 1), (2 * m).choose p)
      = (∑ p ∈ range m, (2 * m).choose p) + (2 * m).choose m := by
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ]
  have hup : (∑ p ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose p)
      = (∑ p ∈ range m, (2 * m).choose p) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h1 : (2 * m + 1) - (m + 1) = m := by omega
    rw [h1, ← Finset.sum_range_reflect (fun j => (2 * m).choose j) m]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    have hk : m + 1 + j ≤ 2 * m := by omega
    have hs := Nat.choose_symm hk
    have he : 2 * m - (m + 1 + j) = m - 1 - j := by omega
    rw [he] at hs; rw [hs]
  rw [hlow, hup] at hfull; omega

/-- **The closed form**: `archExponent g = 2^{g-1} + g·C(g-1, ⌊(g-1)/2⌋)` for `g ≥ 1`.  The
deviation part telescopes to `g·C(g-1, ⌊(g-1)/2⌋)`; the flat part plus the even middle-block
half-share is the half-row sum `2^{g-1}`. -/
theorem archExponent_closed_form (g : ℕ) (hg : 1 ≤ g) :
    archExponent g = 2 ^ (g - 1) + g * (g - 1).choose ((g - 1) / 2) := by
  have hrange : (g + 1) / 2 = (g - 1) / 2 + 1 := by omega
  have hsplit : (∑ p ∈ range ((g + 1) / 2), (g - 2 * p + 1) * g.choose p)
      = (∑ p ∈ range ((g + 1) / 2), (g - 2 * p) * g.choose p)
        + (∑ p ∈ range ((g + 1) / 2), g.choose p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by rw [add_mul, one_mul])
  have htel : (∑ p ∈ range ((g + 1) / 2), (g - 2 * p) * g.choose p)
      = g * (g - 1).choose ((g - 1) / 2) := by
    rw [hrange]; exact telescopeNat g hg ((g - 1) / 2) (by omega)
  have hrow : (∑ p ∈ range ((g + 1) / 2), g.choose p)
      + (if Even g then g.choose (g / 2) / 2 else 0) = 2 ^ (g - 1) := by
    rcases Nat.even_or_odd g with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have hm1 : 1 ≤ m := by omega
      have hif : (if Even (m + m) then (m + m).choose ((m + m) / 2) / 2 else 0)
          = (2 * m).choose m / 2 := by
        rw [if_pos ⟨m, rfl⟩, show m + m = 2 * m from by ring, show (2 * m) / 2 = m from by omega]
      have hrng : (m + m + 1) / 2 = m := by omega
      rw [hrng, hif]
      have heh := even_half m
      have hdvd : 2 ∣ (2 * m).choose m := by
        rw [← Nat.centralBinom_eq_two_mul_choose]; exact Nat.two_dvd_centralBinom_of_one_le hm1
      obtain ⟨c, hc⟩ := hdvd
      have hpow : (4 : ℕ) ^ m = 2 * 2 ^ (m + m - 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']; congr 1; omega
      have hcast : (∑ p ∈ range m, (m + m).choose p) = (∑ p ∈ range m, (2 * m).choose p) :=
        Finset.sum_congr rfl (fun p _ => by rw [two_mul])
      rw [hcast]; omega
    · subst hm
      have hif : (if Even (2 * m + 1) then (2 * m + 1).choose ((2 * m + 1) / 2) / 2 else 0) = 0 :=
        if_neg (fun h => (Nat.even_add_one.mp h) ⟨m, two_mul m⟩)
      have hrng : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [hrng, hif, add_zero]
      have hh := Nat.sum_range_choose_halfway m
      rw [hh, show 2 * m + 1 - 1 = 2 * m from by omega, pow_mul]; norm_num
  unfold archExponent
  rw [hsplit, add_assoc, hrow, htel]; ring

/-! ## Parity: the sign is real -/

/-- **`A(g)` is even at every grade**, so `ε = i^{A(g)}` is real (`± 1`) — the tensor tower is
self-dual grade by grade, with no half-integral anomaly.  For `g ≥ 2` both `2^{g-1}` and
`g·C(g-1, ⌊(g-1)/2⌋)` are even (the latter by `g` even, or by the central binomial being
even). -/
theorem archExponent_even (g : ℕ) : Even (archExponent g) := by
  match g with
  | 0 => decide
  | 1 => decide
  | (n + 2) =>
    rw [archExponent_closed_form (n + 2) (by omega)]
    refine Even.add ⟨2 ^ n, by rw [show n + 2 - 1 = n + 1 from rfl, pow_succ]; ring⟩ ?_
    rcases Nat.even_or_odd (n + 2) with he | ho
    · exact he.mul_right _
    · obtain ⟨j, hj⟩ := ho
      have hm1 : 1 ≤ (n + 1) / 2 := by omega
      have hcb : Even ((n + 2 - 1).choose ((n + 2 - 1) / 2)) := by
        have hrw : (n + 2 - 1).choose ((n + 2 - 1) / 2)
            = (2 * ((n + 1) / 2)).choose ((n + 1) / 2) := by
          rw [show n + 2 - 1 = 2 * ((n + 1) / 2) from by omega,
            show 2 * ((n + 1) / 2) / 2 = (n + 1) / 2 from by omega]
        rw [hrw, ← Nat.centralBinom_eq_two_mul_choose]
        obtain ⟨c, hc⟩ := Nat.two_dvd_centralBinom_of_one_le hm1
        exact ⟨c, by omega⟩
      exact hcb.mul_left _

/-! ## The root number `ε = i^{A(g)}` -/

/-- The **archimedean root number** of grade `g`: `ε = i^{A(g)}`. -/
noncomputable def rootNumber (g : ℕ) : ℂ := Complex.I ^ archExponent g

/-- Since `A(g)` is even, `ε = i^{A(g)} = (i²)^{A(g)/2} = (-1)^{A(g)/2}`. -/
theorem rootNumber_eq_neg_one_pow (g : ℕ) :
    rootNumber g = (-1 : ℂ) ^ (archExponent g / 2) := by
  obtain ⟨k, hk⟩ := archExponent_even g
  have hk2 : archExponent g = 2 * k := by omega
  rw [rootNumber, hk2, pow_mul, Complex.I_sq]; congr 1; omega

/-- **`ε` is real**: `ε = 1` or `ε = −1` at every grade. -/
theorem rootNumber_eq_one_or_neg_one (g : ℕ) : rootNumber g = 1 ∨ rootNumber g = -1 := by
  rw [rootNumber_eq_neg_one_pow]
  rcases Nat.even_or_odd (archExponent g / 2) with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

/-- **`ε = −1 ↔ A(g) ≡ 2 (mod 4)`**: the forced central zero is read off `A(g)` mod `4`. -/
theorem rootNumber_eq_neg_one_iff (g : ℕ) :
    rootNumber g = -1 ↔ archExponent g % 4 = 2 := by
  rw [rootNumber_eq_neg_one_pow]
  obtain ⟨k, hk⟩ := archExponent_even g
  have hk2 : archExponent g / 2 = k := by omega
  rw [hk2]
  constructor
  · intro h
    by_contra hne
    have hev : Even k := Nat.even_iff.mpr (by omega)
    rw [hev.neg_one_pow] at h; exact absurd h (by norm_num)
  · intro h
    rw [(Nat.odd_iff.mpr (by omega : k % 2 = 1)).neg_one_pow]

/-- **`ε = 1 ↔ A(g) ≡ 0 (mod 4)`**: the non-vanishing sign. -/
theorem rootNumber_eq_one_iff (g : ℕ) :
    rootNumber g = 1 ↔ archExponent g % 4 = 0 := by
  rw [rootNumber_eq_neg_one_pow]
  obtain ⟨k, hk⟩ := archExponent_even g
  have hk2 : archExponent g / 2 = k := by omega
  rw [hk2]
  constructor
  · intro h
    by_contra hne
    have hodd : Odd k := Nat.odd_iff.mpr (by omega)
    rw [hodd.neg_one_pow] at h; exact absurd h (by norm_num)
  · intro h
    rw [(Nat.even_iff.mpr (by omega : k % 2 = 0)).neg_one_pow]

/-! ## The 2-adic digit law -/

/-- The base-2 digit sum of a power of two is `1`. -/
theorem pow_two_digit_sum (j : ℕ) : (Nat.digits 2 (2 ^ j)).sum = 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hpos : 0 < 2 ^ j * 2 := by positivity
    rw [pow_succ, Nat.digits_def' (by norm_num : 1 < 2) hpos]
    have h1 : (2 ^ j * 2) % 2 = 0 := by omega
    have h2 : (2 ^ j * 2) / 2 = 2 ^ j := by omega
    rw [h1, h2, List.sum_cons, ih]

/-- A number with base-2 digit sum `0` is `0` (a positive number has a nonzero last digit,
hence a positive digit sum). -/
theorem digit_sum_two_eq_zero (n : ℕ) (h : (Nat.digits 2 n).sum = 0) : n = 0 := by
  by_contra hn
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hne : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hn
  have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
  have hle := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  omega

/-- `s₂(m) = 1 → m` is a power of two (the hard direction), by strong induction: peeling the
lowest base-2 digit, an odd number with digit sum `1` is `1 = 2^0`, and an even one is twice
a power of two. -/
theorem sum_one_imp_pow : ∀ m, 1 ≤ m → (Nat.digits 2 m).sum = 1 → ∃ j, m = 2 ^ j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm h
    rw [Nat.digits_def' (by norm_num : 1 < 2) hm] at h
    simp only [List.sum_cons] at h
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hmod : m % 2 = 0 := by omega
      rw [hmod, zero_add] at h
      have hmd : m / 2 = t := by omega
      have ht1 : 1 ≤ t := by omega
      rw [hmd] at h
      obtain ⟨j, hj⟩ := ih t (by omega) ht1 h
      exact ⟨j + 1, by rw [pow_succ]; omega⟩
    · have hmod : m % 2 = 1 := by omega
      rw [hmod] at h
      have h0 : (Nat.digits 2 (m / 2)).sum = 0 := by omega
      have hz := digit_sum_two_eq_zero _ h0
      refine ⟨0, ?_⟩; simp only [pow_zero]; omega

/-- **`s₂(m) = 1 ↔ m` is a power of two** — the base-2 digit-sum characterisation of powers of
two. -/
theorem sum_digits_two_eq_one_iff_pow {m : ℕ} (hm : 1 ≤ m) :
    (Nat.digits 2 m).sum = 1 ↔ ∃ j, m = 2 ^ j :=
  ⟨sum_one_imp_pow m hm, by rintro ⟨j, rfl⟩; exact pow_two_digit_sum j⟩

/-- **Kummer for the central binomial**: `v₂(C(2m, m)) = s₂(m)`, the base-2 digit sum of `m`.
From `C(2m, m)·(m!)² = (2m)!`, Legendre's `v₂(m!) = m - s₂(m)`, and `v₂((2m)!) = v₂(m!) + m`. -/
theorem v2_central (m : ℕ) : padicValNat 2 ((2 * m).choose m) = (Nat.digits 2 m).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rwa [show 2 * m - m = m by omega] at h
  have hcne : (2 * m).choose m ≠ 0 := (Nat.choose_pos (show m ≤ 2 * m by omega)).ne'
  have hfne : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hv : padicValNat 2 (2 * m).factorial
      = padicValNat 2 ((2 * m).choose m) + padicValNat 2 m.factorial + padicValNat 2 m.factorial := by
    rw [← hfact, padicValNat.mul (Nat.mul_ne_zero hcne hfne) hfne, padicValNat.mul hcne hfne]
  have hrhs : padicValNat 2 (2 * m).factorial = padicValNat 2 m.factorial + m :=
    padicValNat_factorial_mul m
  have hfact2 : padicValNat 2 m.factorial = m - (Nat.digits 2 m).sum := by
    have h := sub_one_mul_padicValNat_factorial (p := 2) m
    simpa using h
  have hle : padicValNat 2 m.factorial ≤ m := padicValNat_factorial_le 2 m
  have hs_le : (Nat.digits 2 m).sum ≤ m := Nat.digit_sum_le 2 m
  omega

/-- **The Kummer criterion**: `v₂(C(2m, m)) = 1 ↔ m` is a power of two — the arithmetic
heart of the forced-vanishing law. -/
theorem v2_central_eq_one_iff_pow {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 ((2 * m).choose m) = 1 ↔ ∃ j, m = 2 ^ j := by
  rw [v2_central, sum_digits_two_eq_one_iff_pow hm]

/-! ## Assembling the mod-4 sign -/

/-- Multiplying by an odd number is a unit mod `4`: `(a·c) ≡ 2 (mod 4) ↔ c ≡ 2 (mod 4)`. -/
theorem odd_mul_mod_four (a c : ℕ) (ha : a % 2 = 1) : (a * c) % 4 = 2 ↔ c % 4 = 2 := by
  rw [Nat.mul_mod]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hc4 : c % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases ha4 with h | h <;> rw [h] <;> omega

/-- For nonzero `n`, `v₂(n) = 1 ↔ n ≡ 2 (mod 4)` (`2 ∣ n` but `4 ∤ n`). -/
theorem valuation_one_iff_mod_four (n : ℕ) (hn : n ≠ 0) :
    padicValNat 2 n = 1 ↔ n % 4 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : ℕ) ^ 1 ∣ n ↔ 1 ≤ padicValNat 2 n := padicValNat_dvd_iff_le hn
  have h4 : (2 : ℕ) ^ 2 ∣ n ↔ 2 ≤ padicValNat 2 n := padicValNat_dvd_iff_le hn
  simp only [pow_one] at h2
  norm_num at h4
  omega

/-- **Odd grade, mod 4**: for odd `g = 2m+1` (with `m ≥ 1`), `A(g) ≡ 2 (mod 4) ↔ ∃ j, m = 2^j`.
The leading `2^{2m} ≡ 0`, the cofactor `2m+1` is a mod-4 unit, and `v₂(C(2m,m)) = 1 ↔ C ≡ 2`
via the Kummer criterion. -/
theorem odd_mod_four (m : ℕ) (hm : 1 ≤ m) :
    archExponent (2 * m + 1) % 4 = 2 ↔ ∃ j, m = 2 ^ j := by
  rw [archExponent_closed_form (2 * m + 1) (by omega)]
  rw [show 2 * m + 1 - 1 = 2 * m from by omega, show (2 * m) / 2 = m from by omega]
  have hpow4 : 4 ∣ 2 ^ (2 * m) := by
    have h := pow_dvd_pow 2 (show 2 ≤ 2 * m by omega); norm_num at h; exact h
  have hcne : (2 * m).choose m ≠ 0 := (Nat.choose_pos (by omega : m ≤ 2 * m)).ne'
  have hAmod : (2 ^ (2 * m) + (2 * m + 1) * (2 * m).choose m) % 4
      = ((2 * m + 1) * (2 * m).choose m) % 4 := by
    obtain ⟨q, hq⟩ := hpow4; omega
  rw [hAmod, odd_mul_mod_four _ _ (by omega : (2 * m + 1) % 2 = 1),
      ← valuation_one_iff_mod_four _ hcne, v2_central_eq_one_iff_pow hm]

/-- `4 ∣ m·C(2m, m)` for `m ≥ 2`: either `m` is even (times the even central binomial), or `m`
is odd (`m ≥ 3` is not a power of two, so `s₂(m) ≥ 2` and `4 ∣ C(2m, m)`). -/
theorem four_dvd_m_centralBinom (m : ℕ) (hm : 2 ≤ m) : 4 ∣ m * (2 * m).choose m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.even_or_odd m with hme | hmo
  · obtain ⟨t, ht⟩ := hme
    have hCe : 2 ∣ (2 * m).choose m := by
      rw [← Nat.centralBinom_eq_two_mul_choose]; exact Nat.two_dvd_centralBinom_of_one_le (by omega)
    obtain ⟨s, hs⟩ := hCe
    exact ⟨t * s, by rw [hs, ht]; ring⟩
  · have hs2 : 2 ≤ (Nat.digits 2 m).sum := by
      have h1 : 1 ≤ (Nat.digits 2 m).sum := by
        by_contra h
        have hz : (Nat.digits 2 m).sum = 0 := by omega
        have := digit_sum_two_eq_zero m hz; omega
      have hne1 : (Nat.digits 2 m).sum ≠ 1 := by
        intro hcontra
        obtain ⟨j, hj⟩ := (sum_digits_two_eq_one_iff_pow (by omega)).mp hcontra
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0; simp at hj; obtain ⟨t, ht⟩ := hmo; omega
        · have hd : 2 ∣ m := by rw [hj]; exact dvd_pow_self 2 (by omega)
          obtain ⟨t, ht⟩ := hmo; omega
      omega
    have h4C : (4 : ℕ) ∣ (2 * m).choose m := by
      have hle : 2 ≤ padicValNat 2 ((2 * m).choose m) := by rw [v2_central]; exact hs2
      have hd := (padicValNat_dvd_iff_le (p := 2) (n := 2)
                  (a := (2 * m).choose m) ((Nat.choose_pos (by omega : m ≤ 2 * m)).ne')).mpr hle
      norm_num at hd; exact hd
    exact h4C.mul_left m

/-- **Even grade, mod 4**: for even `g` (with `g ≥ 2`), `A(g) ≡ 0 (mod 4)` — no even grade
forces a central zero.  The leading `2^{2m-1}` is divisible by `4` (`m ≥ 2`), and
`2m·C(2m-1, m-1) = m·C(2m, m)` is too (`four_dvd_m_centralBinom`); grade `2` is `A(2) = 4`. -/
theorem even_mod_four (m : ℕ) (hm : 1 ≤ m) : archExponent (2 * m) % 4 = 0 := by
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · have : m = 1 := by omega
    subst this; decide
  · rw [archExponent_closed_form (2 * m) (by omega)]
    rw [show (2 * m - 1) / 2 = m - 1 from by omega]
    have hpow : (4 : ℕ) ∣ 2 ^ (2 * m - 1) := by
      have h := pow_dvd_pow 2 (show 2 ≤ 2 * m - 1 by omega); norm_num at h; exact h
    have hp : (2 * m).choose m = (2 * m - 1).choose (m - 1) + (2 * m - 1).choose m := by
      have h := Nat.choose_succ_succ (2 * m - 1) (m - 1)
      simp only [Nat.succ_eq_add_one] at h
      rw [show 2 * m - 1 + 1 = 2 * m from by omega, show m - 1 + 1 = m from by omega] at h; exact h
    have hsym : (2 * m - 1).choose m = (2 * m - 1).choose (m - 1) := by
      have h := Nat.choose_symm (show m ≤ 2 * m - 1 by omega)
      rw [show 2 * m - 1 - m = m - 1 from by omega] at h; exact h.symm
    have hcentral : (2 * m).choose m = 2 * (2 * m - 1).choose (m - 1) := by rw [hp, hsym]; ring
    have hconv : 2 * m * (2 * m - 1).choose (m - 1) = m * (2 * m).choose m := by rw [hcentral]; ring
    have hterm : (4 : ℕ) ∣ 2 * m * (2 * m - 1).choose (m - 1) := by
      rw [hconv]; exact four_dvd_m_centralBinom m (by omega)
    obtain ⟨a, ha⟩ := hpow; obtain ⟨b, hb⟩ := hterm; omega

/-! ## The headline and the pre-committed grades -/

/-- **THE ROOT-NUMBER LAW**: for odd `g ≥ 3`, the archimedean root number `i^{A(g)} = −1` —
a forced central zero — **iff `g = 2^k + 1`** for some `k ≥ 1`.  In `2..20` this fires
exactly at `g = 3, 5, 9, 17`; the next is `g = 33`.  The criterion is the Kummer
2-adic-valuation condition on the central binomial coefficient — the tower's arithmetic
reflex is a base-2 digit condition on `g - 1`. -/
theorem eps_neg_iff {g : ℕ} (hg : 3 ≤ g) (hodd : Odd g) :
    rootNumber g = -1 ↔ ∃ k, 1 ≤ k ∧ g = 2 ^ k + 1 := by
  obtain ⟨m, rfl⟩ := hodd
  have hm : 1 ≤ m := by omega
  rw [rootNumber_eq_neg_one_iff, odd_mod_four m hm]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j + 1, by omega, by rw [pow_succ]; ring⟩
  · rintro ⟨k, hk1, hk⟩
    refine ⟨k - 1, ?_⟩
    have h2m : 2 * m = 2 ^ k := by omega
    rw [show k = (k - 1) + 1 from by omega, pow_succ] at h2m
    omega

/-- **Even grades never force a zero**: for even `g` (with `g ≥ 2`), `i^{A(g)} = 1`. -/
theorem eps_even {g : ℕ} (hg : 1 ≤ g) (heven : Even g) : rootNumber g = 1 := by
  obtain ⟨m, rfl⟩ := heven
  rw [rootNumber_eq_one_iff, show m + m = 2 * m from by ring]
  exact even_mod_four m (by omega)

/-- Grade 3 (the Ceresa rung): `ε = −1`, forced central zero (`3 = 2^1 + 1`). -/
theorem eps_three : rootNumber 3 = -1 :=
  (rootNumber_eq_neg_one_iff 3).mpr (by rw [archExponent_closed_form 3 (by norm_num)]; decide)

/-- Grade 5: `ε = −1`, forced central zero (`5 = 2^2 + 1`). -/
theorem eps_five : rootNumber 5 = -1 :=
  (rootNumber_eq_neg_one_iff 5).mpr (by rw [archExponent_closed_form 5 (by norm_num)]; decide)

/-- Grade 9 (pre-committed prediction): `ε = −1`, forced central zero (`9 = 2^3 + 1`). -/
theorem eps_nine : rootNumber 9 = -1 :=
  (rootNumber_eq_neg_one_iff 9).mpr (by rw [archExponent_closed_form 9 (by norm_num)]; decide)

/-- Grade 17 (pre-committed prediction): `ε = −1`, forced central zero (`17 = 2^4 + 1`). -/
theorem eps_seventeen : rootNumber 17 = -1 :=
  (rootNumber_eq_neg_one_iff 17).mpr (by rw [archExponent_closed_form 17 (by norm_num)]; decide)

/-- Grade 7: `ε = +1` — odd, yet **not** forced (`7 ≠ 2^k + 1`).  The guard against the naive
"odd weight ⇒ sign `−1`" guess. -/
theorem eps_seven : rootNumber 7 = 1 :=
  (rootNumber_eq_one_iff 7).mpr (by rw [archExponent_closed_form 7 (by norm_num)]; decide)

/-- Grade 11: `ε = +1` — odd, yet **not** forced (`11 ≠ 2^k + 1`). -/
theorem eps_eleven : rootNumber 11 = 1 :=
  (rootNumber_eq_one_iff 11).mpr (by rw [archExponent_closed_form 11 (by norm_num)]; decide)

end RootNumberLaw

#print axioms RootNumberLaw.archExponent_closed_form
#print axioms RootNumberLaw.archExponent_even
#print axioms RootNumberLaw.rootNumber_eq_neg_one_pow
#print axioms RootNumberLaw.rootNumber_eq_one_or_neg_one
#print axioms RootNumberLaw.rootNumber_eq_neg_one_iff
#print axioms RootNumberLaw.rootNumber_eq_one_iff
#print axioms RootNumberLaw.v2_central
#print axioms RootNumberLaw.sum_digits_two_eq_one_iff_pow
#print axioms RootNumberLaw.v2_central_eq_one_iff_pow
#print axioms RootNumberLaw.odd_mod_four
#print axioms RootNumberLaw.even_mod_four
#print axioms RootNumberLaw.eps_neg_iff
#print axioms RootNumberLaw.eps_even
#print axioms RootNumberLaw.eps_three
#print axioms RootNumberLaw.eps_five
#print axioms RootNumberLaw.eps_nine
#print axioms RootNumberLaw.eps_seventeen
#print axioms RootNumberLaw.eps_seven
#print axioms RootNumberLaw.eps_eleven
