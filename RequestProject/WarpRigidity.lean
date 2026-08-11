import RequestProject.PolarCorrection

/-!
# Three-warp rigidity: warped finite ledgers are central

The rigidity half of the three-warp theorem (registered 2026-08-10),
compiled with the warp action as an explicit hypothesis.  In the carrier
coordinate `u = log y` (carrier `y^{-1/2}` stripped, centered exponents
`λ_ρ = ρ − 1/2`), the harmonized additive transform at a prime `q` is
claimed to act on the polar correction as the affine reflection
`W_q : u ↦ −u − 6 log q` up to a scalar.  Granting that action at THREE
distinct primes:

* `translation_extraction` — scalar-translation invariance of a finite
  exponential sum gives per-mode eigenvalue equations
  `c_i (e^{μ_i h} − w) = 0` (via the compiled coefficient extraction);
* `occupied_exponent_unique` — ℤ-independence of the two composed
  translation lengths forces all occupied exponents EQUAL — with distinct
  exponents, at most one mode survives;
* `log_primes_int_independent` / `log_diff_int_independent` — the
  ℤ-independence, unconditional: integer relations among logs of three
  distinct primes are trivial (unique factorization);
* `three_warp_central_support` — **the assembly**: three warps at distinct
  primes force every occupied mode to the centre `μ = 0` (i.e. `ρ = 1/2`),
  the reflection warp itself supplying the parity closure — no root-number
  harmonization is needed for rigidity, scalars are fully tolerated.

Register.  The two load-bearing OPEN pieces are stated, not consumed:
(1) the WARP LEMMA — that the harmonized Kl₅ additive identity really
induces `W_q` on the polar part (the `hw` hypothesis fields below); (2) the
CENTRAL-MODE EXCLUSION at `ρ = 1/2`.  Jordan blocks are outside the
compiled scope (simple modes), consistent with the ledger's semisimplicity
computation.  No `axiom`, no `sorry`.
-/

open Complex Finset

namespace CriticalLinePhasor.WarpRigidity

open CriticalLinePhasor.PolarCorrection

variable {n : ℕ}

/-- **Translation extraction**: if a finite exponential sum satisfies
`f(u+h) = w·f(u)` identically, each mode satisfies its eigenvalue
equation. -/
theorem translation_extraction (μ c : Fin n → ℂ) (hμ : Function.Injective μ)
    (w h : ℂ)
    (hid : ∀ u : ℂ, expSum μ c 0 (u + h) = w * expSum μ c 0 u) :
    ∀ i, c i * (Complex.exp (μ i * h) - w) = 0 := by
  have hzero : ∀ z : ℂ,
      expSum μ (fun i => c i * (Complex.exp (μ i * h) - w)) 0 z = 0 := by
    intro z
    have h1 := hid z
    simp only [expSum, pow_zero, one_mul, mul_one] at h1 ⊢
    have h2 : ∀ i : Fin n,
        c i * (Complex.exp (μ i * h) - w) * Complex.exp (μ i * z)
          = c i * Complex.exp (μ i * (z + h))
            - w * (c i * Complex.exp (μ i * z)) := by
      intro i
      have h3 : μ i * (z + h) = μ i * z + μ i * h := by ring
      rw [h3, Complex.exp_add]
      ring
    rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_sub_distrib,
      ← Finset.mul_sum, h1]
    ring
  exact expSum_coeffs_eq_zero_of_zero μ _ hμ hzero

/-- **Two incommensurate scalar-translations collapse the occupied set**:
all occupied exponents are equal. -/
theorem occupied_exponent_unique (μ c : Fin n → ℂ) (hμ : Function.Injective μ)
    {h₁ h₂ : ℝ}
    (hind : ∀ k l : ℤ, (k : ℝ) * h₂ = (l : ℝ) * h₁ → k = 0 ∧ l = 0)
    (w₁ w₂ : ℂ)
    (hid₁ : ∀ u : ℂ, expSum μ c 0 (u + (h₁ : ℂ)) = w₁ * expSum μ c 0 u)
    (hid₂ : ∀ u : ℂ, expSum μ c 0 (u + (h₂ : ℂ)) = w₂ * expSum μ c 0 u) :
    ∀ i j, c i ≠ 0 → c j ≠ 0 → μ i = μ j := by
  have h₁ne : h₁ ≠ 0 := by
    intro h0
    rcases hind 0 1 (by simp [h0]) with ⟨_, h⟩
    exact one_ne_zero h
  have e₁ := translation_extraction μ c hμ w₁ h₁ hid₁
  have e₂ := translation_extraction μ c hμ w₂ h₂ hid₂
  intro i j hi hj
  have Ei₁ : Complex.exp (μ i * h₁) = w₁ :=
    sub_eq_zero.mp ((mul_eq_zero.mp (e₁ i)).resolve_left hi)
  have Ej₁ : Complex.exp (μ j * h₁) = w₁ :=
    sub_eq_zero.mp ((mul_eq_zero.mp (e₁ j)).resolve_left hj)
  have Ei₂ : Complex.exp (μ i * h₂) = w₂ :=
    sub_eq_zero.mp ((mul_eq_zero.mp (e₂ i)).resolve_left hi)
  have Ej₂ : Complex.exp (μ j * h₂) = w₂ :=
    sub_eq_zero.mp ((mul_eq_zero.mp (e₂ j)).resolve_left hj)
  by_contra hne
  have hδ : μ i - μ j ≠ 0 := sub_ne_zero.mpr hne
  have hd₁ : Complex.exp ((μ i - μ j) * h₁) = 1 := by
    rw [sub_mul, Complex.exp_sub, Ei₁, Ej₁, div_self (Ej₁ ▸ Complex.exp_ne_zero _)]
  have hd₂ : Complex.exp ((μ i - μ j) * h₂) = 1 := by
    rw [sub_mul, Complex.exp_sub, Ei₂, Ej₂, div_self (Ej₂ ▸ Complex.exp_ne_zero _)]
  rw [Complex.exp_eq_one_iff] at hd₁ hd₂
  obtain ⟨k, hk⟩ := hd₁
  obtain ⟨l, hl⟩ := hd₂
  -- cross-multiply the two quantizations and cancel δ·2πi
  have m1 : (μ i - μ j) * h₁ * ((l : ℂ) * (2 * Real.pi * I))
      = (μ i - μ j) * h₂ * ((k : ℂ) * (2 * Real.pi * I)) := by
    rw [hk, hl]; ring
  have h2piI : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcross : (k : ℂ) * (h₂ : ℂ) = (l : ℂ) * (h₁ : ℂ) := by
    have hfac : ((μ i - μ j) * (2 * Real.pi * I)) * ((l : ℂ) * h₁)
        = ((μ i - μ j) * (2 * Real.pi * I)) * ((k : ℂ) * h₂) := by
      linear_combination m1
    exact (mul_left_cancel₀ (mul_ne_zero hδ h2piI) hfac).symm
  have hreal : (k : ℝ) * h₂ = (l : ℝ) * h₁ := by exact_mod_cast hcross
  rcases hind k l hreal with ⟨hk0, _⟩
  rw [hk0] at hk
  simp only [Int.cast_zero, zero_mul] at hk
  rcases mul_eq_zero.mp hk with h | h
  · exact hδ h
  · exact Complex.ofReal_ne_zero.mpr h₁ne h

/-! ## ℤ-independence of prime logarithms -/

/-- A signed-power split: `x^m = x^{m⁺}/x^{m⁻}` for `x ≠ 0`. -/
lemma zpow_toNat_split {x : ℝ} (hx : x ≠ 0) (m : ℤ) :
    x ^ m = x ^ m.toNat / x ^ (-m).toNat := by
  rcases m.eq_nat_or_neg with ⟨k, rfl | rfl⟩
  · simp [zpow_natCast]
  · rw [zpow_neg, zpow_natCast]
    simp [hx]

/-- **Integer relations among logs of three distinct primes are trivial.** -/
theorem log_primes_int_independent {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ a b c : ℤ,
      (a : ℝ) * Real.log p + (b : ℝ) * Real.log q + (c : ℝ) * Real.log r = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  intro a b c habc
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hexp : ∀ (x : ℝ), 0 < x → ∀ m : ℤ,
      Real.exp ((m : ℝ) * Real.log x) = x ^ m := by
    intro x hx m
    rw [← Real.rpow_intCast x m, Real.rpow_def_of_pos hx]
    ring_nf
  have key : (p : ℝ) ^ a * (q : ℝ) ^ b * (r : ℝ) ^ c = 1 := by
    rw [← hexp _ hp0, ← hexp _ hq0, ← hexp _ hr0,
      ← Real.exp_add, ← Real.exp_add, habc, Real.exp_zero]
  -- move to natural exponents
  have key2 : (p : ℝ) ^ a.toNat * (q : ℝ) ^ b.toNat * (r : ℝ) ^ c.toNat
      = (p : ℝ) ^ (-a).toNat * (q : ℝ) ^ (-b).toNat * (r : ℝ) ^ (-c).toNat := by
    have hka := zpow_toNat_split hp0.ne' a
    have hkb := zpow_toNat_split hq0.ne' b
    have hkc := zpow_toNat_split hr0.ne' c
    rw [hka, hkb, hkc] at key
    field_simp at key
    linarith [key]
  have hnat : p ^ a.toNat * q ^ b.toNat * r ^ c.toNat
      = p ^ (-a).toNat * q ^ (-b).toNat * r ^ (-c).toNat := by
    exact_mod_cast key2
  -- read off exponents by unique factorization
  have hval : ∀ s : ℕ, s.Prime →
      (p ^ a.toNat * q ^ b.toNat * r ^ c.toNat).factorization s
        = (p ^ (-a).toNat * q ^ (-b).toNat * r ^ (-c).toNat).factorization s := by
    intro s _
    rw [hnat]
  have hpn : ∀ m : ℕ, p ^ m ≠ 0 := fun m => pow_ne_zero m hp.pos.ne'
  have hqn : ∀ m : ℕ, q ^ m ≠ 0 := fun m => pow_ne_zero m hq.pos.ne'
  have hrn : ∀ m : ℕ, r ^ m ≠ 0 := fun m => pow_ne_zero m hr.pos.ne'
  have hfac : ∀ (m₁ m₂ m₃ : ℕ),
      (p ^ m₁ * q ^ m₂ * r ^ m₃).factorization p = m₁ := by
    intro m₁ m₂ m₃
    rw [Nat.factorization_mul (mul_ne_zero (hpn m₁) (hqn m₂)) (hrn m₃),
      Nat.factorization_mul (hpn m₁) (hqn m₂),
      hp.factorization_pow, hq.factorization_pow, hr.factorization_pow]
    simp [Finsupp.single_apply, Ne.symm hpq, Ne.symm hpr]
  have hfacq : ∀ (m₁ m₂ m₃ : ℕ),
      (p ^ m₁ * q ^ m₂ * r ^ m₃).factorization q = m₂ := by
    intro m₁ m₂ m₃
    rw [Nat.factorization_mul (mul_ne_zero (hpn m₁) (hqn m₂)) (hrn m₃),
      Nat.factorization_mul (hpn m₁) (hqn m₂),
      hp.factorization_pow, hq.factorization_pow, hr.factorization_pow]
    simp [Finsupp.single_apply, hpq, Ne.symm hqr]
  have hfacr : ∀ (m₁ m₂ m₃ : ℕ),
      (p ^ m₁ * q ^ m₂ * r ^ m₃).factorization r = m₃ := by
    intro m₁ m₂ m₃
    rw [Nat.factorization_mul (mul_ne_zero (hpn m₁) (hqn m₂)) (hrn m₃),
      Nat.factorization_mul (hpn m₁) (hqn m₂),
      hp.factorization_pow, hq.factorization_pow, hr.factorization_pow]
    simp [Finsupp.single_apply, hpr, hqr]
  have ha : a.toNat = (-a).toNat := by
    have := hval p hp
    rwa [hfac, hfac] at this
  have hb : b.toNat = (-b).toNat := by
    have := hval q hq
    rwa [hfacq, hfacq] at this
  have hc : c.toNat = (-c).toNat := by
    have := hval r hr
    rwa [hfacr, hfacr] at this
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The independence needed for the two composed warp translations. -/
theorem log_diff_int_independent {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ k l : ℤ,
      (k : ℝ) * (6 * (Real.log p - Real.log r))
        = (l : ℝ) * (6 * (Real.log p - Real.log q)) →
      k = 0 ∧ l = 0 := by
  intro k l hkl
  have hrel : ((k - l : ℤ) : ℝ) * Real.log p + (l : ℝ) * Real.log q
      + ((-k : ℤ) : ℝ) * Real.log r = 0 := by
    push_cast
    nlinarith [hkl]
  rcases log_primes_int_independent hp hq hr hpq hpr hqr _ _ _ hrel
    with ⟨h1, h2, h3⟩
  constructor <;> omega

/-! ## The assembly -/

/-- **Three-warp rigidity**: if the polar carrier of a finite simple ledger
is invariant (up to arbitrary scalars) under the affine warp
`u ↦ −u − 6 log q` at three distinct primes, then every occupied mode sits
at the centre `μ = 0` — i.e. every pole is at `ρ = 1/2`. -/
theorem three_warp_central_support (μ c : Fin n → ℂ)
    (hμ : Function.Injective μ)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (w₁ w₂ w₃ : ℂ) (hw₁0 : w₁ ≠ 0)
    (hw₁ : ∀ u : ℂ, expSum μ c 0 (-u - (6 * Real.log p : ℝ))
      = w₁ * expSum μ c 0 u)
    (hw₂ : ∀ u : ℂ, expSum μ c 0 (-u - (6 * Real.log q : ℝ))
      = w₂ * expSum μ c 0 u)
    (hw₃ : ∀ u : ℂ, expSum μ c 0 (-u - (6 * Real.log r : ℝ))
      = w₃ * expSum μ c 0 u) :
    ∀ i, c i ≠ 0 → μ i = 0 := by
  -- compose warps into genuine translations
  have hid₁ : ∀ u : ℂ,
      expSum μ c 0 (u + ((6 * (Real.log p - Real.log q) : ℝ) : ℂ))
        = (w₂ * w₁) * expSum μ c 0 u := by
    intro u
    have s1 := hw₁ u
    have s2 := hw₂ (-u - (6 * Real.log p : ℝ))
    have harg : -(-u - ((6 * Real.log p : ℝ) : ℂ)) - ((6 * Real.log q : ℝ) : ℂ)
        = u + ((6 * (Real.log p - Real.log q) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg] at s2
    rw [s2, s1]
    ring
  have hid₂ : ∀ u : ℂ,
      expSum μ c 0 (u + ((6 * (Real.log p - Real.log r) : ℝ) : ℂ))
        = (w₃ * w₁) * expSum μ c 0 u := by
    intro u
    have s1 := hw₁ u
    have s2 := hw₃ (-u - (6 * Real.log p : ℝ))
    have harg : -(-u - ((6 * Real.log p : ℝ) : ℂ)) - ((6 * Real.log r : ℝ) : ℂ)
        = u + ((6 * (Real.log p - Real.log r) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg] at s2
    rw [s2, s1]
    ring
  have huniq := occupied_exponent_unique μ c hμ
    (log_diff_int_independent hp hq hr hpq hpr hqr) (w₂ * w₁) (w₃ * w₁)
    hid₁ hid₂
  -- at most one occupied index; the surviving mode is pinned by the reflection
  intro i hi
  by_contra hμi
  -- f is the single mode c i · exp(μ i ·)
  have hsingle : ∀ u : ℂ, expSum μ c 0 u = c i * Complex.exp (μ i * u) := by
    intro u
    have hs := Finset.sum_eq_single_of_mem
      (f := fun j => c j * μ j ^ 0 * Complex.exp (μ j * u)) i
      (Finset.mem_univ i)
      (fun j _ hji => by
        by_cases hj : c j = 0
        · simp [hj]
        · exact absurd (hμ (huniq j i hj hi)) hji)
    simp only [expSum]
    rw [hs]
    ring
  -- extract the pure reflection identity for the single mode
  set A : ℂ := ((6 * Real.log p : ℝ) : ℂ) with hA
  have h2 : ∀ u : ℂ, Complex.exp (μ i * (-u - A)) = w₁ * Complex.exp (μ i * u) := by
    intro u
    have h1 := hw₁ u
    rw [hsingle u, hsingle (-u - A)] at h1
    have h1' : c i * Complex.exp (μ i * (-u - A))
        = c i * (w₁ * Complex.exp (μ i * u)) := by linear_combination h1
    exact mul_left_cancel₀ hi h1'
  -- evaluate at 0 to identify the scalar, then cancel it
  have h20 : Complex.exp (μ i * (-A)) = w₁ := by
    have := h2 0
    simpa using this
  have hkey : ∀ u : ℂ, Complex.exp (μ i * (-u)) = Complex.exp (μ i * u) := by
    intro u
    have h2u := h2 u
    have hsplit : Complex.exp (μ i * (-u - A))
        = Complex.exp (μ i * (-u)) * Complex.exp (μ i * (-A)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hsplit, h20] at h2u
    have hw : w₁ ≠ 0 := h20 ▸ Complex.exp_ne_zero _
    have : Complex.exp (μ i * (-u)) * w₁ = w₁ * Complex.exp (μ i * u) := h2u
    rw [mul_comm] at this
    exact mul_left_cancel₀ hw this
  -- exp(2 μ i u) = 1 for every u, then pin at u = πi/(2 μ i)
  have hone : ∀ u : ℂ, Complex.exp (2 * μ i * u) = 1 := by
    intro u
    have hk := hkey u
    have hs : Complex.exp (2 * μ i * u) * Complex.exp (μ i * (-u))
        = Complex.exp (μ i * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hk] at hs
    have h1 : Complex.exp (2 * μ i * u) * Complex.exp (μ i * u)
        = 1 * Complex.exp (μ i * u) := by rw [hs, one_mul]
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) h1
  have hden : (2 : ℂ) * μ i ≠ 0 :=
    mul_ne_zero two_ne_zero hμi
  have hpin := hone ((Real.pi : ℂ) * I / (2 * μ i))
  have harg : (2 : ℂ) * μ i * ((Real.pi : ℂ) * I / (2 * μ i))
      = (Real.pi : ℂ) * I := by field_simp
  rw [harg, Complex.exp_pi_mul_I] at hpin
  norm_num at hpin

/-! ## Warp realization at simple poles: the FE moves principal parts -/

/-- **Warp realization, simple-pole scope** — functoriality of principal
parts under the completed functional equation.  If
`H(s) = η·A^{1/2−s}·H^∨(1−s)` with `A ≠ 0`, a simple-pole residue of `H^∨`
at `1−ρ` transports exactly to the residue of `H` at `ρ`, with explicit
scalar `−η·A^{1/2−ρ}`.  Principal parts transform before any carrier
kernel is reconstructed: no Hankel analysis enters.  (Jordan blocks
transport triangularly — registered debt with the multiplicity extension.) -/
theorem fe_residue_transport {H Hdual : ℂ → ℂ} {η A : ℂ} (hA : A ≠ 0)
    (hFE : ∀ s : ℂ, H s = η * A ^ ((1 : ℂ)/2 - s) * Hdual (1 - s))
    {ρ res : ℂ}
    (hres : Filter.Tendsto (fun t => (t - (1 - ρ)) * Hdual t)
      (nhdsWithin (1 - ρ) {(1 - ρ)}ᶜ) (nhds res)) :
    Filter.Tendsto (fun s => (s - ρ) * H s) (nhdsWithin ρ {ρ}ᶜ)
      (nhds (-(η * A ^ ((1 : ℂ)/2 - ρ)) * res)) := by
  have hmap : Filter.Tendsto (fun s : ℂ => 1 - s) (nhdsWithin ρ {ρ}ᶜ)
      (nhdsWithin (1 - ρ) {(1 - ρ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact ((continuous_const.sub continuous_id).tendsto ρ).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      exact hs (by linear_combination -h)
  have hcomp := hres.comp hmap
  have hcont : Continuous (fun s : ℂ => η * A ^ ((1 : ℂ)/2 - s)) := by
    have hrw : (fun s : ℂ => η * A ^ ((1 : ℂ)/2 - s))
        = fun s => η * Complex.exp (Complex.log A * ((1 : ℂ)/2 - s)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero hA]
    rw [hrw]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub continuous_id)))
  have hconstT : Filter.Tendsto (fun s : ℂ => -(η * A ^ ((1 : ℂ)/2 - s)))
      (nhdsWithin ρ {ρ}ᶜ) (nhds (-(η * A ^ ((1 : ℂ)/2 - ρ)))) :=
    ((hcont.tendsto ρ).mono_left nhdsWithin_le_nhds).neg
  have hmul := hconstT.mul hcomp
  refine hmul.congr fun s => ?_
  show -(η * A ^ ((1 : ℂ)/2 - s)) * (((1 - s) - (1 - ρ)) * Hdual (1 - s))
      = (s - ρ) * H s
  rw [hFE s]
  ring

end CriticalLinePhasor.WarpRigidity

#print axioms CriticalLinePhasor.WarpRigidity.translation_extraction
#print axioms CriticalLinePhasor.WarpRigidity.occupied_exponent_unique
#print axioms CriticalLinePhasor.WarpRigidity.log_primes_int_independent
#print axioms CriticalLinePhasor.WarpRigidity.three_warp_central_support
#print axioms CriticalLinePhasor.WarpRigidity.fe_residue_transport
