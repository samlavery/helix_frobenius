import Mathlib

/-!
# The helix's own reflection splits the completed fiber into its two ends, exactly (ledger 1252)

The helix's functional equation is its own reflection: about the origin, signed height `h = 0`, with the
phases conjugated. The Lean variable `x` here is the positive encoding `exp h` of the signed height; the
reflection `h ↦ -h` reads `x ↦ 1/x` in it (`WeakFEPair.h_feq`, `f (1/x) = ε·x^k·g x`). The encoding's value at
the origin is not the origin. No χ-factor and no expansion enters below.

* `helixStrand P s = ∫_{x > 1} x^{s-1} (f x - f₀)`: the helix strand, the profile at positive signed height
  `h > 0`, with its constant mode removed; `helixEnd P s = helixStrand P s - f₀/s`: the strand with its
  constant-mode booking.
* `Λ₀_two_ended`, `Λ_two_ended`: **for every pair, exactly**,
  `Λ(s) = helixStrand P s + ε·helixStrand P.symm (k - s) - f₀/s - ε g₀/(k - s)`.
  The second strand is the profile at negative signed height, carried to positive height by the reflection
  `h ↦ -h`: the anti-helix strand.
* `helixStrand_symm_of_conj`: when the dual profile is the conjugate profile (`g = conj ∘ f`, `g₀ = conj f₀`),
  the anti-helix strand is the conjugate of the helix strand at the conjugate exponent:
  `helixStrand P.symm w = conj (helixStrand P (conj w))`.
* `Λ_axis`: on the axis `Re s = k/2` the anti-helix end is the J-image of the helix end:
  `Λ(s) = helixEnd P s + ε · conj (helixEnd P s)`.
* The self-dual Gaussian pair (`hurwitzEvenFEPair 0`, whose `h_feq` is the Gaussian theta inversion):
  `completedRiemannZeta_two_ended`: on `Re s = ½`, `completedRiemannZeta s = Re (helixEnd (s/2))`, real.
  `riemannZeta_eq_zero_iff_helixEnd`, `riemannZeta_eq_zero_iff_at_height`: at physical height `Z`,
  `ζ(½ + i·log Z) = 0 ⟺ Re (helixEnd ((½ + i·log Z)/2)) = 0`. The two-ended closure is the vanishing of one
  real number, the helix end plus its conjugate.

**Every cut.** A cut at signed height `hc` (encoded `c = exp hc`) is paired by the reflection with `-hc`
(encoded `1/c`). The cut at the origin is `hc = 0`.
* `slab_reflect`: the reflection carries the slab of signed heights `(hc, 0]` onto `[0, -hc)`.
* `Λ_two_ended_cut`: for every `c > 0` (`s ≠ 0, k`), exactly,
  `Λ(s) = helixStrandAt P c s + ε·helixStrandAt P.symm (1/c) (k - s) - c^s f₀/s - ε c^{s-k} g₀/(k - s)`:
  the helix strand above `c`, the anti-helix strand above `1/c`, and their constant-mode bookings.
* `Λ_axis_cut`: on the axis, with the conjugate dual, `Λ(s) = helixEndAt P c s + ε·conj (helixEndAt P (1/c) s)`.
  Reflection about the origin swaps the heads `c ↔ 1/c`; conjugation is J.
* `riemannZeta_eq_zero_iff_two_ended_cut`: at height `Z` and every cut `c > 0`,
  `ζ(½ + i·log Z) = 0 ⟺ helixEndAt c + conj (helixEndAt (1/c)) = 0` (at `(½ + i·log Z)/2`).
  A small cut is a large helix head; the anti-helix strand then lies above the large cut `1/c`, where the
  profile's tail decays faster than any power (`hf_top`). The closure is exact at every cut: the anti-helix
  strand carries exactly what the helix strand above `c` leaves.

Scope. These are exact identities about the completed (Mellin) fiber, from the pair's own reflection `h_feq`.
The expansion of a strand as a phasor bank with incomplete-Γ growth windows (`AntihelixWindow`) is not in this
file. The `smoothEntry` head fiber of `CarrierHeadFiniteFiber` is a different window; its tail expansion
(ledgers 1250–1251) is asymptotic and is not formalized here.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixTwoEndedClosure

open WeakFEPair

/-- The helix strand: the profile at positive signed height (`x = exp h`, `h > 0`), with its constant mode
removed. -/
def helixStrand (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)

/-- The helix end: the helix strand with its constant-mode booking `-f₀/s`. -/
def helixEnd (P : WeakFEPair ℂ) (s : ℂ) : ℂ := helixStrand P s - P.f₀ / s

/-- The upper piece of Mathlib's modified profile. -/
def upperPiece (P : WeakFEPair ℂ) : ℝ → ℂ := (Ioi 1).indicator (fun x => P.f x - P.f₀)

/-- The lower piece of Mathlib's modified profile. -/
def lowerPiece (P : WeakFEPair ℂ) : ℝ → ℂ :=
  (Ioo 0 1).indicator (fun x => P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀)

theorem f_modif_eq (P : WeakFEPair ℂ) : P.f_modif = upperPiece P + lowerPiece P := rfl

/-- The upper piece is the helix strand. -/
theorem mellin_upperPiece (P : WeakFEPair ℂ) (s : ℂ) :
    mellin (upperPiece P) s = helixStrand P s := by
  unfold mellin helixStrand upperPiece
  have h : (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Ioi 1).indicator (fun x => P.f x - P.f₀) t) =
      (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) * (P.f t - P.f₀)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp [indicator_of_mem ht, smul_eq_mul]
    · simp [indicator_of_notMem ht]
  rw [h, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

/-- **The reflection carries the lower piece above the origin**: it becomes `ε` times the anti-helix strand. -/
theorem mellin_lowerPiece (P : WeakFEPair ℂ) (s : ℂ) :
    mellin (lowerPiece P) s = P.ε * helixStrand P.symm (P.k - s) := by
  have key := mellin_comp_inv (fun u => lowerPiece P u⁻¹) s
  simp only [inv_inv] at key
  rw [key]
  unfold mellin helixStrand
  have h : EqOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) • lowerPiece P u⁻¹)
      ((Ioi 1).indicator (fun u : ℝ => P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g u - P.g₀))))
      (Ioi 0) := by
    intro u (hu : 0 < u)
    by_cases h1 : 1 < u
    · have hmem : u⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr hu, inv_lt_one_of_one_lt₀ h1⟩
      simp only [lowerPiece, indicator_of_mem hmem, indicator_of_mem (show u ∈ Ioi (1 : ℝ) from h1)]
      have hfeq := P.h_feq u hu
      rw [one_div] at hfeq
      rw [hfeq, Real.rpow_neg (inv_pos.mpr hu).le, Real.inv_rpow hu.le, inv_inv, smul_eq_mul,
        smul_eq_mul, smul_eq_mul]
      have hc : ((u ^ P.k : ℝ) : ℂ) = (u : ℂ) ^ (P.k : ℂ) := Complex.ofReal_cpow hu.le _
      rw [hc]
      have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
      have hpow : (u : ℂ) ^ (-s - 1) * (u : ℂ) ^ (P.k : ℂ) = (u : ℂ) ^ ((P.k : ℂ) - s - 1) := by
        rw [← Complex.cpow_add _ _ hu0]
        ring_nf
      linear_combination (P.ε * (P.g u - P.g₀)) * hpow
    · have hnot : u⁻¹ ∉ Ioo (0 : ℝ) 1 := fun h => h1 ((inv_lt_one₀ hu).mp h.2)
      simp only [lowerPiece, indicator_of_notMem hnot, smul_zero,
        indicator_of_notMem (show u ∉ Ioi (1 : ℝ) from h1)]
  rw [setIntegral_congr_fun measurableSet_Ioi h, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one), integral_const_mul]
  simp only [WeakFEPair.symm_f, WeakFEPair.symm_f₀]

/-- **The two-ended split of the entire part, exactly**: helix strand plus `ε` times the anti-helix strand. -/
theorem Λ₀_two_ended (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ₀ s = helixStrand P s + P.ε * helixStrand P.symm (P.k - s) := by
  have hc : MellinConvergent P.f_modif s := (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hup : MellinConvergent (upperPiece P) s := by
    have heq : (fun t : ℝ => (t : ℂ) ^ (s - 1) • upperPiece P t) =
        (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · have hnot : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt.mpr (le_of_lt ht)) h.2
        simp [upperPiece, f_modif_eq, lowerPiece, indicator_of_mem ht, indicator_of_notMem hnot]
      · simp [upperPiece, indicator_of_notMem ht]
    unfold MellinConvergent
    rw [heq]
    exact hc.indicator measurableSet_Ioi
  have hlow : MellinConvergent (lowerPiece P) s := by
    have heq : (fun t : ℝ => (t : ℂ) ^ (s - 1) • lowerPiece P t) =
        fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t - (t : ℂ) ^ (s - 1) • upperPiece P t := by
      funext t
      rw [f_modif_eq, Pi.add_apply, smul_add]
      ring
    unfold MellinConvergent
    rw [heq]
    exact hc.sub hup
  rw [Λ₀, f_modif_eq, ← mellin_upperPiece, ← mellin_lowerPiece]
  unfold mellin
  rw [← integral_add hup hlow]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Pi.add_apply, smul_add]

/-- **The two-ended split of the completed fiber, exactly.** -/
theorem Λ_two_ended (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ s = helixStrand P s + P.ε * helixStrand P.symm (P.k - s)
      - 1 / s * P.f₀ - P.ε / (P.k - s) * P.g₀ := by
  rw [WeakFEPair.Λ, Λ₀_two_ended, smul_eq_mul, smul_eq_mul]

/-- **The reflection conjugates**: with the conjugate dual profile, the anti-helix strand is the conjugate of
the helix strand at the conjugate exponent. -/
theorem helixStrand_symm_of_conj (P : WeakFEPair ℂ) (hg : ∀ x, 0 < x → P.g x = conj (P.f x))
    (hg₀ : P.g₀ = conj P.f₀) (w : ℂ) :
    helixStrand P.symm w = conj (helixStrand P (conj w)) := by
  unfold helixStrand
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => ?_
  have hx0 : 0 < x := zero_lt_one.trans hx
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx0.le]
    exact Real.pi_pos.ne
  have hcp : conj ((x : ℂ) ^ (conj w - 1)) = (x : ℂ) ^ (w - 1) := by
    have h1 : conj w - 1 = conj (w - 1) := by simp
    rw [h1, Complex.cpow_conj _ _ harg, Complex.conj_conj, Complex.conj_ofReal]
  simp only [WeakFEPair.symm_f, WeakFEPair.symm_f₀, map_mul, map_sub, hcp, hg x hx0, hg₀]

/-- On the axis `Re s = k/2`, the reflected exponent `k - s` is the conjugate exponent. -/
theorem k_sub_eq_conj (P : WeakFEPair ℂ) {s : ℂ} (hs : s.re = P.k / 2) : (P.k : ℂ) - s = conj s := by
  apply Complex.ext
  · simp only [sub_re, ofReal_re, conj_re]
    linarith
  · simp

/-- **On the axis the anti-helix end is the J-image of the helix end**, exactly. -/
theorem Λ_axis (P : WeakFEPair ℂ) (hg : ∀ x, 0 < x → P.g x = conj (P.f x)) (hg₀ : P.g₀ = conj P.f₀)
    {s : ℂ} (hs : s.re = P.k / 2) :
    P.Λ s = helixEnd P s + P.ε * conj (helixEnd P s) := by
  rw [Λ_two_ended, k_sub_eq_conj P hs, helixStrand_symm_of_conj P hg hg₀, Complex.conj_conj, hg₀]
  unfold helixEnd
  rw [map_sub, map_div₀]
  ring

/-! ## Every cut: the helix head at `c`, the anti-helix head at `1/c` -/

/-- The helix strand above the cut `x = c`. -/
def helixStrandAt (P : WeakFEPair ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi c, (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)

/-- The helix end at the cut `c`: the strand above `c` with its constant-mode booking `-c^s f₀/s`. -/
def helixEndAt (P : WeakFEPair ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  helixStrandAt P c s - (c : ℂ) ^ s / s * P.f₀

theorem helixStrandAt_one (P : WeakFEPair ℂ) (s : ℂ) : helixStrandAt P 1 s = helixStrand P s := rfl

theorem integrableOn_strand_Ioi_one (P : WeakFEPair ℂ) (s : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)) (Ioi 1) := by
  have hc : MellinConvergent P.f_modif s := (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t) (Ioi 1) :=
    hc.mono_set (Ioi_subset_Ioi zero_le_one)
  refine h1.congr_fun (fun t (ht : 1 < t) => ?_) measurableSet_Ioi
  have hnot : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt.mpr ht.le) h.2
  simp [f_modif_eq, upperPiece, lowerPiece, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht),
    indicator_of_notMem hnot, smul_eq_mul]

theorem integrableOn_strand_Icc (P : WeakFEPair ℂ) {a b : ℝ} (ha : 0 < a) (s : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)) (Icc a b) := by
  have hsub : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  have hf : IntegrableOn (fun x => P.f x - P.f₀) (Icc a b) :=
    (P.hf_int.sub (locallyIntegrableOn_const _)).integrableOn_compact_subset hsub isCompact_Icc
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Icc a b) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hsub hx).ne')).continuousWithinAt
  exact hf.continuousOn_mul hcont isCompact_Icc

theorem integrableOn_strand (P : WeakFEPair ℂ) {c : ℝ} (hc : 0 < c) (s : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)) (Ioi c) := by
  rcases le_or_gt c 1 with h | h
  · have hsub : Ioi c ⊆ Icc c 1 ∪ Ioi 1 := fun x (hx : c < x) => by
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx.le, hx1⟩
      · exact Or.inr (not_le.mp hx1)
    exact ((integrableOn_strand_Icc P hc s).union (integrableOn_strand_Ioi_one P s)).mono_set hsub
  · exact (integrableOn_strand_Ioi_one P s).mono_set (Ioi_subset_Ioi h.le)

/-- Moving the cut from `a` up to `b` moves the slab `(a, b]` out of the strand. -/
theorem helixStrandAt_split (P : WeakFEPair ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ) :
    helixStrandAt P a s =
      (∫ x in Ioc a b, (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)) + helixStrandAt P b s := by
  unfold helixStrandAt
  rw [← Ioc_union_Ioi_eq_Ioi hab, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    ((integrableOn_strand_Icc P ha s).mono_set Ioc_subset_Icc_self)
    (integrableOn_strand P (ha.trans_le hab) s)]

/-- **The reflection about the origin carries the slab `(c, 1]` to the slab `[1, 1/c)`.** -/
theorem slab_reflect (P : WeakFEPair ℂ) {c : ℝ} (hc : 0 < c) (s : ℂ) :
    ∫ x in Ioc c 1, (x : ℂ) ^ (s - 1) * (P.f x - P.f₀) =
      ∫ u in Ico 1 c⁻¹, (u : ℂ) ^ (-s - 1) * (P.f u⁻¹ - P.f₀) := by
  set F : ℝ → ℂ := (Ioc c 1).indicator (fun x => P.f x - P.f₀) with hF
  have h1 : mellin F s = ∫ x in Ioc c 1, (x : ℂ) ^ (s - 1) * (P.f x - P.f₀) := by
    unfold mellin
    have h : (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) =
        (Ioc c 1).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) * (P.f t - P.f₀)) := by
      funext t
      by_cases ht : t ∈ Ioc c 1
      · simp [hF, indicator_of_mem ht, smul_eq_mul]
      · simp [hF, indicator_of_notMem ht]
    have hsub : Ioc c 1 ⊆ Ioi (0 : ℝ) := fun x hx => show (0 : ℝ) < x from hc.trans hx.1
    rw [h, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr hsub]
  have key := mellin_comp_inv (fun u => F u⁻¹) s
  simp only [inv_inv] at key
  rw [← h1, key]
  unfold mellin
  have h2 : EqOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) • F u⁻¹)
      ((Ico 1 c⁻¹).indicator (fun u : ℝ => (u : ℂ) ^ (-s - 1) * (P.f u⁻¹ - P.f₀))) (Ioi 0) := by
    intro u (hu : 0 < u)
    have hiff : u⁻¹ ∈ Ioc c 1 ↔ u ∈ Ico (1 : ℝ) c⁻¹ := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(inv_le_one₀ hu).mp h2, (lt_inv_comm₀ hc hu).mp h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(lt_inv_comm₀ hc hu).mpr h2, (inv_le_one₀ hu).mpr h1⟩
    by_cases hm : u ∈ Ico (1 : ℝ) c⁻¹
    · simp [hF, indicator_of_mem (hiff.mpr hm), indicator_of_mem hm, smul_eq_mul]
    · have hn : u⁻¹ ∉ Ioc c 1 := fun h => hm (hiff.mp h)
      simp [hF, indicator_of_notMem hn, indicator_of_notMem hm]
  have hsub : Ico (1 : ℝ) c⁻¹ ⊆ Ioi (0 : ℝ) := fun x hx =>
    show (0 : ℝ) < x from lt_of_lt_of_le one_pos hx.1
  rw [setIntegral_congr_fun measurableSet_Ioi h2, setIntegral_indicator measurableSet_Ico,
    inter_eq_right.mpr hsub]

theorem ofReal_inv_cpow {c : ℝ} (hc : 0 < c) (z : ℂ) : ((c⁻¹ : ℝ) : ℂ) ^ z = (c : ℂ) ^ (-z) := by
  have harg : (c : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le]
    exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

/-- `∫_{(1, L]} u^{a-1} du = (L^a - 1)/a` for `L ≥ 1`, `a ≠ 0`. -/
theorem integral_Ioc_one_cpow {L : ℝ} (hL : 1 ≤ L) {a : ℂ} (ha : a ≠ 0) :
    ∫ u in Ioc (1 : ℝ) L, (u : ℂ) ^ (a - 1) = ((L : ℂ) ^ a - 1) / a := by
  rw [← intervalIntegral.integral_of_le hL, integral_cpow]
  · simp only [sub_add_cancel, Complex.ofReal_one, Complex.one_cpow]
  · right
    refine ⟨fun h => ha (by linear_combination h), ?_⟩
    rw [Set.uIcc_of_le hL]
    exact fun h => absurd h.1 (by norm_num)

theorem integrableOn_cpow_Icc {a b : ℝ} (ha : 0 < a) (z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ z) (Icc a b) :=
  (ContinuousOn.integrableOn_compact isCompact_Icc fun _ hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (lt_of_lt_of_le ha hx.1).ne')).continuousWithinAt)

/-- **The two-ended split at a cut `0 < c ≤ 1`.** -/
theorem Λ_two_ended_cut_le (P : WeakFEPair ℂ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) {s : ℂ}
    (hs0 : s ≠ 0) (hsk : s ≠ P.k) :
    P.Λ s = helixStrandAt P c s + P.ε * helixStrandAt P.symm c⁻¹ (P.k - s)
      - (c : ℂ) ^ s / s * P.f₀ - P.ε * (c : ℂ) ^ (s - P.k) / (P.k - s) * P.g₀ := by
  have hL : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr hc1
  have hks : (P.k : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsk)
  -- the helix strand: slab (c, 1] plus the origin strand
  have hH := helixStrandAt_split P hc hc1 s
  -- the anti-helix strand: slab (1, 1/c] plus the strand above 1/c
  have hA := helixStrandAt_split P.symm one_pos hL (P.k - s)
  simp only [helixStrandAt_one] at hA
  -- the slab (c, 1], reflected
  have hslab := slab_reflect P hc s
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo] at hslab
  have hpt : EqOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * (P.f u⁻¹ - P.f₀))
      (fun u : ℝ => P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.symm.f u - P.symm.f₀))
        + (P.ε * P.g₀) * (u : ℂ) ^ ((P.k - s) - 1) - P.f₀ * (u : ℂ) ^ (-s - 1)) (Ioc 1 c⁻¹) := by
    intro u (hu : 1 < u ∧ u ≤ c⁻¹)
    have hu0 : 0 < u := zero_lt_one.trans hu.1
    have hfeq := P.h_feq u hu0
    rw [one_div] at hfeq
    dsimp only
    rw [hfeq, smul_eq_mul, WeakFEPair.symm_f, WeakFEPair.symm_f₀]
    have hc' : ((u ^ P.k : ℝ) : ℂ) = (u : ℂ) ^ (P.k : ℂ) := Complex.ofReal_cpow hu0.le _
    rw [hc']
    have hne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
    have hpow : (u : ℂ) ^ (-s - 1) * (u : ℂ) ^ (P.k : ℂ) = (u : ℂ) ^ ((P.k : ℂ) - s - 1) := by
      rw [← Complex.cpow_add _ _ hne]
      ring_nf
    linear_combination (P.ε * P.g u) * hpow
  rw [setIntegral_congr_fun measurableSet_Ioc hpt] at hslab
  have hI1 : IntegrableOn (fun u : ℝ => P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) *
      (P.symm.f u - P.symm.f₀))) (Ioc 1 c⁻¹) :=
    ((integrableOn_strand_Icc P.symm one_pos ((P.k : ℂ) - s)).mono_set
      Ioc_subset_Icc_self).const_mul _
  have hI2 : IntegrableOn (fun u : ℝ => (P.ε * P.g₀) * (u : ℂ) ^ ((P.k - s) - 1)) (Ioc 1 c⁻¹) :=
    ((integrableOn_cpow_Icc one_pos _).mono_set Ioc_subset_Icc_self).const_mul _
  have hI3 : IntegrableOn (fun u : ℝ => P.f₀ * (u : ℂ) ^ (-s - 1)) (Ioc 1 c⁻¹) :=
    ((integrableOn_cpow_Icc one_pos _).mono_set Ioc_subset_Icc_self).const_mul _
  have hI12 : IntegrableOn (fun u : ℝ => P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) *
      (P.symm.f u - P.symm.f₀)) + (P.ε * P.g₀) * (u : ℂ) ^ ((P.k - s) - 1)) (Ioc 1 c⁻¹) :=
    hI1.add hI2
  rw [integral_sub hI12 hI3, integral_add hI1 hI2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_Ioc_one_cpow hL hks,
    show (-s - 1 : ℂ) = (-s) - 1 by ring, integral_Ioc_one_cpow hL (neg_ne_zero.mpr hs0),
    ofReal_inv_cpow hc, ofReal_inv_cpow hc, neg_neg] at hslab
  rw [helixStrandAt_one] at hH
  rw [Λ_two_ended, hH, hA, hslab]
  have hcs : (c : ℂ) ^ (-((P.k : ℂ) - s)) = (c : ℂ) ^ (s - P.k) := by ring_nf
  rw [hcs]
  generalize (∫ x in Ioc 1 c⁻¹, (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.symm.f x - P.symm.f₀)) = J
  field_simp
  ring

/-- **The two-ended split at every cut `c > 0`**: the helix strand above `c`, the anti-helix strand above
`1/c`, and the two constant-mode bookings. -/
theorem Λ_two_ended_cut (P : WeakFEPair ℂ) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs0 : s ≠ 0) (hsk : s ≠ P.k) :
    P.Λ s = helixStrandAt P c s + P.ε * helixStrandAt P.symm c⁻¹ (P.k - s)
      - (c : ℂ) ^ s / s * P.f₀ - P.ε * (c : ℂ) ^ (s - P.k) / (P.k - s) * P.g₀ := by
  rcases le_or_gt c 1 with h | h
  · exact Λ_two_ended_cut_le P hc h hs0 hsk
  · -- reflect: apply the first case to the dual pair at the cut 1/c and exponent k - s
    have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h.le
    have hw0 : (P.k : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsk)
    have hwk : (P.k : ℂ) - s ≠ P.symm.k := by
      simp only [WeakFEPair.symm_k]
      intro h'
      exact hs0 (by linear_combination -h')
    have hQ := Λ_two_ended_cut_le P.symm (inv_pos.mpr hc) hci hw0 hwk
    have hfe := P.functional_equation (P.k - s)
    rw [sub_sub_cancel] at hfe
    rw [hfe, smul_eq_mul, hQ]
    simp only [WeakFEPair.symm_k, WeakFEPair.symm_ε, WeakFEPair.symm_f₀, WeakFEPair.symm_g₀, inv_inv,
      sub_sub_cancel]
    have hsymm : helixStrandAt P.symm.symm c s = helixStrandAt P c s := by
      unfold helixStrandAt
      simp only [WeakFEPair.symm_f, WeakFEPair.symm_g, WeakFEPair.symm_f₀, WeakFEPair.symm_g₀]
    rw [hsymm, ofReal_inv_cpow hc, ofReal_inv_cpow hc]
    have hε := P.hε
    have e1 : (c : ℂ) ^ (-((P.k : ℂ) - s)) = (c : ℂ) ^ (s - P.k) := by ring_nf
    have e2 : (c : ℂ) ^ (-((P.k : ℂ) - s - P.k)) = (c : ℂ) ^ s := by ring_nf
    rw [e1, e2]
    field_simp
    ring

/-- The reflection conjugates, at every cut. -/
theorem helixStrandAt_symm_of_conj (P : WeakFEPair ℂ) (hg : ∀ x, 0 < x → P.g x = conj (P.f x))
    (hg₀ : P.g₀ = conj P.f₀) {c : ℝ} (hc : 0 < c) (w : ℂ) :
    helixStrandAt P.symm c w = conj (helixStrandAt P c (conj w)) := by
  unfold helixStrandAt
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : c < x) => ?_
  have hx0 : 0 < x := hc.trans hx
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx0.le]
    exact Real.pi_pos.ne
  have hcp : conj ((x : ℂ) ^ (conj w - 1)) = (x : ℂ) ^ (w - 1) := by
    have h1 : conj w - 1 = conj (w - 1) := by simp
    rw [h1, Complex.cpow_conj _ _ harg, Complex.conj_conj, Complex.conj_ofReal]
  simp only [WeakFEPair.symm_f, WeakFEPair.symm_f₀, map_mul, map_sub, hcp, hg x hx0, hg₀]

/-- **On the axis, at every cut: the helix end at `c` plus the J-image of the helix end at `1/c`.**
The reflection about the origin swaps the two heads `c ↔ 1/c`; the conjugation is J. -/
theorem Λ_axis_cut (P : WeakFEPair ℂ) (hg : ∀ x, 0 < x → P.g x = conj (P.f x)) (hg₀ : P.g₀ = conj P.f₀)
    {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : s.re = P.k / 2) (hs0 : s ≠ 0) :
    P.Λ s = helixEndAt P c s + P.ε * conj (helixEndAt P c⁻¹ s) := by
  have hks := k_sub_eq_conj P hs
  have hsk : s ≠ P.k := by
    intro h
    apply hs0
    have : (P.k : ℂ) - s = 0 := by rw [h]; ring
    rw [hks, map_eq_zero] at this
    exact this
  have hci : ((c⁻¹ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (inv_pos.mpr hc).le]
    exact Real.pi_pos.ne
  have hconjpow : conj (((c⁻¹ : ℝ) : ℂ) ^ s) = (c : ℂ) ^ (s - P.k) := by
    have h := Complex.cpow_conj ((c⁻¹ : ℝ) : ℂ) s hci
    rw [Complex.conj_ofReal] at h
    rw [← h, ← hks, ofReal_inv_cpow hc]
    ring_nf
  rw [Λ_two_ended_cut P hc hs0 hsk, hks, helixStrandAt_symm_of_conj P hg hg₀ (inv_pos.mpr hc),
    Complex.conj_conj, hg₀]
  unfold helixEndAt
  rw [map_sub, map_mul, map_div₀, hconjpow]
  have hsc : conj s ≠ 0 := by rwa [map_ne_zero]
  rw [← hks]
  field_simp
  ring

/-! ## The self-dual Gaussian pair -/

open HurwitzZeta

theorem riemannPair_conj (x : ℝ) :
    (hurwitzEvenFEPair 0).g x = conj ((hurwitzEvenFEPair 0).f x) := by
  simp [hurwitzEvenFEPair, HurwitzZeta.evenKernel_eq_cosKernel_of_zero]

theorem riemannPair_conj₀ : (hurwitzEvenFEPair 0).g₀ = conj (hurwitzEvenFEPair 0).f₀ := by
  simp [hurwitzEvenFEPair]

/-- **The completed zeta on the line is the real part of one helix end**: the helix end plus its J-image. -/
theorem completedRiemannZeta_two_ended {s : ℂ} (hs : s.re = 1 / 2) :
    completedRiemannZeta s = ((helixEnd (hurwitzEvenFEPair 0) (s / 2)).re : ℂ) := by
  have hk : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hs2 : (s / 2).re = (hurwitzEvenFEPair 0).k / 2 := by
    rw [hk, Complex.div_ofNat_re, hs]
  rw [completedRiemannZeta, completedHurwitzZetaEven,
    Λ_axis _ (fun x _ => riemannPair_conj x) riemannPair_conj₀ hs2, hε, one_mul, Complex.add_conj]
  push_cast
  ring

/-- **The two-ended closure on the line**: `ζ(s) = 0` exactly when the real part of the helix end vanishes. -/
theorem riemannZeta_eq_zero_iff_helixEnd {s : ℂ} (hs : s.re = 1 / 2) :
    riemannZeta s = 0 ↔ (helixEnd (hurwitzEvenFEPair 0) (s / 2)).re = 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff, or_iff_left hΓ,
    completedRiemannZeta_two_ended hs, Complex.ofReal_eq_zero]

/-- **At the physical height `Z`**: the readout `½ + i·log Z` is a zero exactly when the helix end at that
height has vanishing real part. -/
theorem riemannZeta_eq_zero_iff_at_height (Z : ℝ) :
    riemannZeta (1 / 2 + (Real.log Z : ℂ) * I) = 0 ↔
      (helixEnd (hurwitzEvenFEPair 0) ((1 / 2 + (Real.log Z : ℂ) * I) / 2)).re = 0 :=
  riemannZeta_eq_zero_iff_helixEnd (by simp)

/-- **The two-ended closure at height `Z`, at every cut `c > 0`**: the helix end at `c` cancels the J-image
of the helix end at `1/c` exactly when `ζ(½ + i·log Z) = 0`. -/
theorem riemannZeta_eq_zero_iff_two_ended_cut (Z : ℝ) {c : ℝ} (hc : 0 < c) :
    riemannZeta (1 / 2 + (Real.log Z : ℂ) * I) = 0 ↔
      helixEndAt (hurwitzEvenFEPair 0) c ((1 / 2 + (Real.log Z : ℂ) * I) / 2) +
        conj (helixEndAt (hurwitzEvenFEPair 0) c⁻¹ ((1 / 2 + (Real.log Z : ℂ) * I) / 2)) = 0 := by
  set s : ℂ := 1 / 2 + (Real.log Z : ℂ) * I with hsdef
  have hs : s.re = 1 / 2 := by simp [hsdef]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hs] at this
    norm_num at this
  have hs20 : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  have hs2 : (s / 2).re = (hurwitzEvenFEPair 0).k / 2 := by
    rw [show (hurwitzEvenFEPair 0).k = 1 / 2 from rfl, Complex.div_ofNat_re, hs]
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff, or_iff_left hΓ, completedRiemannZeta,
    completedHurwitzZetaEven, Λ_axis_cut _ (fun x _ => riemannPair_conj x) riemannPair_conj₀ hc hs2 hs20,
    show (hurwitzEvenFEPair 0).ε = 1 from rfl, one_mul, div_eq_zero_iff, or_iff_left two_ne_zero]

end CriticalLinePhasor.HelixTwoEndedClosure

end

#print axioms CriticalLinePhasor.HelixTwoEndedClosure.Λ₀_two_ended
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.Λ_two_ended
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.helixStrand_symm_of_conj
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.Λ_axis
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.completedRiemannZeta_two_ended
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.riemannZeta_eq_zero_iff_helixEnd
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.riemannZeta_eq_zero_iff_at_height
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.slab_reflect
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.Λ_two_ended_cut
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.helixStrandAt_symm_of_conj
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.Λ_axis_cut
#print axioms CriticalLinePhasor.HelixTwoEndedClosure.riemannZeta_eq_zero_iff_two_ended_cut
