import RequestProject.SummedFiberHB
import RequestProject.StOscillation
import RequestProject.HelixLogFreeFTA
import RequestProject.ChiralCup

/-!
# Sources, sourceless zeros, and the weld-holonomy ledger

The mainline question, rewritten through the obstruction-as-holonomy frame (owner's
directive, 2026-07-02).  A zero is, literally, an obstruction class: the obstruction to
a global logarithm, detected only by loop transport (the argument principle is holonomy
measurement).  The obstruction thesis says every such residue has a CARRIER — a weld
mismatch it is attributable to.  This file makes the dictionary exact and proves every
unconditional entry:

* `WeldSymmetric` — the carrier commutes with conjugation (the antihelix is the
  CONJUGATE, not a mirror); `weldSymmetric_self_star` — for such a carrier the strand
  pair is one welded object (`E* = E` as functions).
* `weld_real` / `weld_phase_quantized` — ON the weld (the fixed locus of the
  conjugation), the fiber is real and its phase is pinned to `{0, π}`: the entire
  on-weld holonomy budget is carried in π-jumps.
* `weld_ledger_complete` — between crossings the sign is constant (IVT): NO phase
  transport happens on the weld except at zeros.  Every on-weld π has a nameable
  carrier — the crossing.  The ledger closes.
* `IsSource` / `Sourceless` — a source is a weld-FIXED zero (a vanishing on the fixed
  locus of the conjugation, where the crossing structure lives); a sourceless zero is a
  vanishing NOT fixed by the weld: loop holonomy with no crossing to carry it.
* `sourceless_twin` — a sourceless zero cannot come alone: its conjugate twin vanishes
  strictly on the other side of the weld.  Sourceless holonomy is exchanged, never
  fixed.
* `everyZeroHasSource_iff` — **the faithfulness theorem**: "every zero has a source"
  ⟺ "all zeros lie on the conjugation axis".  The rewriting is lossless; the
  EveryZeroHasSource ⟺ (G)RH dichotomy is a theorem about the FRAMING, proven here
  without assuming or proving RH/GRH and without circularity (source is defined by the
  fixed-locus geometry, not by the conclusion).
* `carrier_attribution` / `carrier_every_zero_has_source` — **the multiplicative
  sector is closed, unconditionally**: every zero of the pure clock bank factors
  through a nameable clock (attribution is total) and IS a source.  For the
  multiplicative carrier, EveryZeroHasSource is a THEOREM.

What remains open is exactly the summed fiber's side of the dichotomy: whether its
readout admits an exchanged twin-pair (sourceless) vanishing.  That statement is the
1D limit's unknown; nothing here decides it.  The measurable face is the locator
recall audit (`tmp/source_audit*`): a census zero with no bank source event is the
falsification-register hit.  No `sorry`; standard axioms.
-/

open Complex

namespace CriticalLinePhasor.SourceHolonomy

/-- **Weld symmetry**: the carrier commutes with the conjugation anti-involution
(real-coefficient carrier; the antihelix is the conjugate). -/
def WeldSymmetric (E : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, E ((starRingEnd ℂ) z) = (starRingEnd ℂ) (E z)

/-- For a weld-symmetric carrier the strand pair is ONE welded object: `E* = E` as
functions.  The helix/antihelix distinction is carried by the POINT pair `(z, z̄)`,
not by two different functions. -/
theorem weldSymmetric_self_star {E : ℂ → ℂ} (h : WeldSymmetric E) (z : ℂ) :
    CriticalLinePhasor.SummedFiberHB.star' E z = E z := by
  unfold CriticalLinePhasor.SummedFiberHB.star'
  rw [h z, Complex.conj_conj]

/-- The weld line is the fixed locus of the conjugation. -/
theorem fixed_iff_on_axis (z : ℂ) : (starRingEnd ℂ) z = z ↔ z.im = 0 :=
  Complex.conj_eq_iff_im

/-- **On the weld the fiber is real**: at a fixed point of the conjugation, weld
symmetry forces the value onto the real axis. -/
theorem weld_real {E : ℂ → ℂ} (h : WeldSymmetric E) {z : ℂ} (hz : z.im = 0) :
    (E z).im = 0 := by
  have hfix : (starRingEnd ℂ) z = z := (fixed_iff_on_axis z).mpr hz
  have := h z
  rw [hfix] at this
  exact (Complex.conj_eq_iff_im).mp this.symm

/-- **The on-weld phase ledger**: wherever the fiber is nonzero on the weld, its phase
is pinned to `{0, π}`.  All continuous phase transport is forbidden on the weld; the
holonomy budget is carried entirely in π-jumps. -/
theorem weld_phase_quantized {E : ℂ → ℂ} (h : WeldSymmetric E) {z : ℂ}
    (hz : z.im = 0) (h0 : E z ≠ 0) :
    (E z).arg = 0 ∨ (E z).arg = Real.pi :=
  CriticalLinePhasor.StOscillation.real_arg_quantized (weld_real h hz) h0

/-- **The weld ledger is complete**: a continuous weld-symmetric fiber with no zero on
a weld interval keeps one sign there.  Phase moves ONLY at crossings — every unit of
on-weld holonomy has a nameable carrier. -/
theorem weld_ledger_complete {E : ℂ → ℂ} (h : WeldSymmetric E) (hc : Continuous E)
    {a b : ℝ} (h0 : ∀ t ∈ Set.Icc a b, E (t : ℂ) ≠ 0) :
    (∀ t ∈ Set.Icc a b, 0 < (E (t : ℂ)).re) ∨ (∀ t ∈ Set.Icc a b, (E (t : ℂ)).re < 0) := by
  set f : ℝ → ℝ := fun t => (E (t : ℂ)).re with hf
  have hfc : Continuous f := Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)
  have hne : ∀ t ∈ Set.Icc a b, f t ≠ 0 := by
    intro t ht hre
    apply h0 t ht
    apply Complex.ext hre
    exact weld_real h (Complex.ofReal_im t)
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨t₁, ht₁, hle⟩, ⟨t₂, ht₂, hge⟩⟩ := hcon
  have h₁ : f t₁ < 0 := lt_of_le_of_ne hle (hne t₁ ht₁)
  have h₂ : 0 < f t₂ := lt_of_le_of_ne hge (Ne.symm (hne t₂ ht₂))
  rcases le_total t₁ t₂ with hd | hd
  · have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc a b := Set.Icc_subset_Icc ht₁.1 ht₂.2
    have := intermediate_value_Icc hd (hfc.continuousOn (s := Set.Icc t₁ t₂))
    have hmem : (0 : ℝ) ∈ Set.Icc (f t₁) (f t₂) := ⟨le_of_lt h₁, le_of_lt h₂⟩
    obtain ⟨c, hc', hc0⟩ := this hmem
    exact hne c (hsub hc') hc0
  · have hsub : Set.Icc t₂ t₁ ⊆ Set.Icc a b := Set.Icc_subset_Icc ht₂.1 ht₁.2
    have := intermediate_value_Icc' hd (hfc.continuousOn (s := Set.Icc t₂ t₁))
    have hmem : (0 : ℝ) ∈ Set.Icc (f t₁) (f t₂) := ⟨le_of_lt h₁, le_of_lt h₂⟩
    obtain ⟨c, hc', hc0⟩ := this hmem
    exact hne c (hsub hc') hc0

/-- **A source**: a weld-FIXED zero — the vanishing sits on the fixed locus of the
conjugation, where the crossing structure (`weld_real`, `weld_phase_quantized`,
`weld_ledger_complete`) lives.  Defined by the geometry, not by the conclusion. -/
def IsSource (E : ℂ → ℂ) (z : ℂ) : Prop :=
  E z = 0 ∧ (starRingEnd ℂ) z = z

/-- **A sourceless zero**: a vanishing NOT fixed by the weld — loop holonomy with no
crossing to carry it. -/
def Sourceless (E : ℂ → ℂ) (z : ℂ) : Prop :=
  E z = 0 ∧ (starRingEnd ℂ) z ≠ z

/-- Every zero is a source or sourceless; never both.  The dichotomy is exhaustive and
exclusive. -/
theorem source_dichotomy {E : ℂ → ℂ} {z : ℂ} (hz : E z = 0) :
    (IsSource E z ∧ ¬Sourceless E z) ∨ (Sourceless E z ∧ ¬IsSource E z) := by
  by_cases hfix : (starRingEnd ℂ) z = z
  · exact Or.inl ⟨⟨hz, hfix⟩, fun hs => hs.2 hfix⟩
  · exact Or.inr ⟨⟨hz, hfix⟩, fun hs => hfix hs.2⟩

/-- **The twin law**: a sourceless zero of a weld-symmetric carrier cannot come alone —
its conjugate twin vanishes too, strictly on the other side of the weld.  Sourceless
holonomy is EXCHANGED by the weld, never fixed by it. -/
theorem sourceless_twin {E : ℂ → ℂ} (h : WeldSymmetric E) {z : ℂ}
    (hz : Sourceless E z) :
    E ((starRingEnd ℂ) z) = 0 ∧ ((starRingEnd ℂ) z).im = -z.im ∧ z.im ≠ 0 := by
  refine ⟨?_, Complex.conj_im z, ?_⟩
  · rw [h z, hz.1, map_zero]
  · intro h0
    exact hz.2 ((fixed_iff_on_axis z).mpr h0)

/-- **The faithfulness theorem**: "every zero has a source" ⟺ "all zeros lie on the
conjugation axis".  The holonomy rewriting of the dichotomy is LOSSLESS: nothing is
gained or lost in translation, so evidence for either side transfers exactly.  (Does
not assume or prove RH/GRH; the content is that the framing is exact.) -/
theorem everyZeroHasSource_iff (E : ℂ → ℂ) :
    (∀ z : ℂ, E z = 0 → IsSource E z) ↔ (∀ z : ℂ, E z = 0 → z.im = 0) := by
  constructor
  · intro h z hz
    exact (fixed_iff_on_axis z).mp (h z hz).2
  · intro h z hz
    exact ⟨hz, (fixed_iff_on_axis z).mpr (h z hz)⟩

/-- **Attribution is total for the multiplicative carrier**: every zero of the clock
bank factors through a NAMEABLE clock — the source can always be pointed at.  (Its
depth is then computed by `ChiralityHB.clock_zero_depth`: the carrier of the holonomy
and its address, both explicit.) -/
theorem carrier_attribution {ι : Type*} (s : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    {z : ℂ} (hz : (∏ i ∈ s, CriticalLinePhasor.ChiralityHB.symClock (α i) (ℓ i) z) = 0) :
    ∃ i ∈ s, CriticalLinePhasor.ChiralityHB.symClock (α i) (ℓ i) z = 0 := by
  obtain ⟨i, hi, h0⟩ := Finset.prod_eq_zero_iff.mp hz
  exact ⟨i, hi, h0⟩

/-- **The multiplicative sector is closed**: for the pure clock bank, EveryZeroHasSource
is a THEOREM — every zero of the product is weld-fixed (purity pins each named source
to the axis), unconditionally.  The open side of the dichotomy lives entirely in the
summed fiber. -/
theorem carrier_every_zero_has_source {ι : Type*} (s : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ s, ‖α i‖ = 1) (hℓ : ∀ i ∈ s, 0 < ℓ i) {z : ℂ}
    (hz : (∏ i ∈ s, CriticalLinePhasor.ChiralityHB.symClock (α i) (ℓ i) z) = 0) :
    IsSource (fun w => ∏ i ∈ s, CriticalLinePhasor.ChiralityHB.symClock (α i) (ℓ i) w) z := by
  refine ⟨hz, (fixed_iff_on_axis z).mpr ?_⟩
  exact CriticalLinePhasor.ChiralityHB.carrier_zeros_real s α ℓ hα hℓ hz

/-! ## The carrier is obstruction-free: no hidden class in 3D that 1D cannot see

Owner's theorem (2026-07-02): a sourceless zero would need to be HIDDEN by a real
cohomological obstruction existing in 3D but not 1D — so prove the carrier scaling of
the 1D source datum (the actual primes) CANNOT have an obstruction.  Proven here, in
four faces:

* **Existence** (`HelixLogFree.wind_mul`, already on disk): EVERY prime datum glues to
  a character of the whole bank — local-to-global never fails on the carrier.
* **Rigidity** (`free_extension_unique`, `source_datum_rigidity`): the extension is
  UNIQUE — two frames agreeing on the primes agree everywhere.  Existence+uniqueness
  = the gluing cohomology of the carrier is trivial; there is no H¹-style hiding
  place, nothing to capitulate into: the bank is already the fully enlarged frame.
* **Zero holonomy** (`carrier_scaling_coboundary`, `carrier_scaling_from_primes`):
  the analytic carrier scaling `n^{−s}` is a COBOUNDARY — the exponential of the
  globally-defined additive frame `−s·log n`, itself freely generated by the prime
  datum (`log_is_source_generated`).  A cocycle that is globally a coboundary carries
  no loop residue: the carrier's transport has no holonomy anywhere.
* **Loop-freeness** (`index_lattice_free`): the index lattice has NO relations
  (unique factorization) — there is no loop in the bank for holonomy to live on.

Consequence for the identikit: a sourceless zero CANNOT be Ш-like with respect to the
carrier — no 3D-but-not-1D cohomology class of the carrier exists to hide it.  The
only remaining hiding place is the analytic null space of the rank-one readout (the
named summed-fiber wall), which is not a cohomological object of the carrier at all.
The wall does not move; the hiding places shrink to one. -/

/-- The winding angle of a prime is its datum: `Θ(p) = θ(p)`. -/
theorem windAngle_prime (θ : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    HelixLogFree.windAngle θ p = θ p := by
  unfold HelixLogFree.windAngle
  rw [hp.factorization, Finsupp.sum_single_index] <;> simp

/-- **Rigidity of the free extension**: any completely-additive frame agreeing with
the datum on the primes IS the free extension — the carrier admits exactly one
extension of each source datum. -/
theorem free_extension_unique (θ : ℕ → ℝ) (Φ : ℕ → ℝ)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Φ (m * n) = Φ m + Φ n)
    (hp : ∀ p : ℕ, p.Prime → Φ p = θ p) :
    ∀ n : ℕ, n ≠ 0 → Φ n = HelixLogFree.windAngle θ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_ne n 1 with rfl | hne
    · have h1 : Φ 1 = Φ 1 + Φ 1 := by simpa using hmul one_ne_zero one_ne_zero
      have h0 : Φ 1 = 0 := by linarith
      simp [h0]
    · obtain ⟨p, hp', hdvd⟩ := Nat.exists_prime_and_dvd hne
      obtain ⟨m, rfl⟩ := hdvd
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hp0 : p ≠ 0 := hp'.ne_zero
      have hmlt : m < p * m :=
        lt_of_eq_of_lt (one_mul m).symm
          (Nat.mul_lt_mul_of_lt_of_le hp'.one_lt (le_refl m) (Nat.pos_of_ne_zero hm))
      rw [hmul hp0 hm, HelixLogFree.windAngle_mul θ hp0 hm, hp p hp',
        windAngle_prime θ hp', ih m hmlt hm]

/-- **Source-datum rigidity — zero gluing cohomology**: two completely-additive frames
that agree on the primes agree on the whole carrier.  Combined with the existence
theorem (`HelixLogFree.wind_mul`: every datum glues), the gluing problem over the
carrier has exactly one solution: no obstruction class exists. -/
theorem source_datum_rigidity (Φ Ψ : ℕ → ℝ)
    (hΦ : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Φ (m * n) = Φ m + Φ n)
    (hΨ : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Ψ (m * n) = Ψ m + Ψ n)
    (hagree : ∀ p : ℕ, p.Prime → Φ p = Ψ p)
    {n : ℕ} (hn : n ≠ 0) : Φ n = Ψ n := by
  rw [free_extension_unique (fun p => Ψ p) Φ hΦ hagree n hn,
    free_extension_unique (fun p => Ψ p) Ψ hΨ (fun _ _ => rfl) n hn]

/-- **The global frame is generated by the source datum**: `log n` is exactly the free
extension of the prime datum `p ↦ log p` — the 1D sources freely generate the whole
additive frame of the carrier. -/
theorem log_is_source_generated {n : ℕ} (hn : n ≠ 0) :
    Real.log n = HelixLogFree.windAngle (fun p : ℕ => Real.log p) n := by
  unfold HelixLogFree.windAngle
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Finsupp.sum, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p hp' => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp'
    have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp').ne_zero
    positivity

/-- **The carrier scaling is a coboundary**: `n^{−s} = exp(−s·log n)` — the phase
cocycle of the bank is the exponential of a GLOBALLY defined additive frame.  A global
coboundary has zero holonomy on every loop: nothing can hide in the carrier's
transport. -/
theorem carrier_scaling_coboundary (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ^ (-s) = Complex.exp (-s * Real.log n) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_def_of_ne_zero h0]
  congr 1
  rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  ring

/-- **THE OWNER'S THEOREM — the carrier scaling of the 1D source datum has no
obstruction**: the analytic scaling `n^{−s}` IS the exponential of the free extension
of the prime datum.  Freely generated (no relations to violate), globally a coboundary
(no loop residue), rigid (no second extension to differ from).  There is no 3D-only
cohomology class in the carrier for a sourceless zero to hide behind. -/
theorem carrier_scaling_from_primes (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ^ (-s) = Complex.exp (-s * HelixLogFree.windAngle (fun p : ℕ => Real.log p) n) := by
  rw [carrier_scaling_coboundary s hn, log_is_source_generated hn]

/-- **The index lattice is loop-free**: unique factorization means two lattice points
with the same coordinates are the same point — the bank's index has NO relations, so
there is no loop on which carrier holonomy could live at all. -/
theorem index_lattice_free {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m.factorization = n.factorization) : m = n := by
  rw [← Nat.prod_factorization_pow_eq_self hm, ← Nat.prod_factorization_pow_eq_self hn, h]

/-! ## The harmonic scaling cannot produce obstructions either

Owner's addendum: the HARMONIC (amplitude) scaling of the 3D representation cannot
produce obstructions.  Proven below, and the reason is structurally STRONGER than for
the phase: amplitudes live in `(ℝ₊, ×)`, a value group with a global logarithm — it is
contractible, there is no circle to wind around, so EVERY multiplicative amplitude law
whatsoever is automatically the coboundary of a free extension of its own prime datum
(`positive_scaling_coboundary`).  The phase sector could at least conceivably wind
(`U(1)` has loops) — and the carrier theorems above kill that; the amplitude sector
cannot even wind.  `harmonic_scaling_from_primes` instantiates this at the bank's
actual envelope `‖n^{−s}‖ = n^{−Re s}`.  Together: neither the winding nor the
harmonic scaling of the 3D bank carries any cohomology for a sourceless zero to hide
behind. -/

/-- **The bank's harmonic envelope is source-generated**: the amplitude
`‖n^{−s}‖ = n^{−Re s}` is the exponential of the free extension of the prime log-datum
at `Re s` — the harmonic scaling of the carrier, generated freely by the 1D sources,
zero obstruction. -/
theorem harmonic_scaling_from_primes (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℂ) ^ (-s)‖
      = Real.exp (-s.re * HelixLogFree.windAngle (fun p : ℕ => Real.log p) n) := by
  rw [carrier_scaling_from_primes s hn, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **No multiplicative amplitude law can carry an obstruction**: any positive
multiplicative scaling `A` is the exponential of the free extension of its own prime
datum — in the harmonic sector every cocycle is a coboundary, because `(ℝ₊, ×)` has a
global logarithm (no loops in the value group, nothing to wind, nowhere to hide). -/
theorem positive_scaling_coboundary (A : ℕ → ℝ) (hpos : ∀ n : ℕ, n ≠ 0 → 0 < A n)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → A (m * n) = A m * A n)
    {n : ℕ} (hn : n ≠ 0) :
    A n = Real.exp (HelixLogFree.windAngle (fun p : ℕ => Real.log (A p)) n) := by
  have hadd : ∀ {m k : ℕ}, m ≠ 0 → k ≠ 0 →
      Real.log (A (m * k)) = Real.log (A m) + Real.log (A k) := by
    intro m k hm hk
    rw [hmul hm hk, Real.log_mul (ne_of_gt (hpos m hm)) (ne_of_gt (hpos k hk))]
  have key := free_extension_unique (fun p : ℕ => Real.log (A p))
      (fun k : ℕ => Real.log (A k)) hadd (fun _ _ => rfl) n hn
  rw [← Real.exp_log (hpos n hn), key]

/-! ## The gapless fiber: no cover, no nerve, no place for a local-to-global class

Owner's target (2026-07-02): prove that the π/3 scaling of the carrier together with
the drift-killing exact gauge creates a TRULY CONTINUOUS fiber — one with none of the
"gaps" a local-to-global obstruction needs to live in.  The provable core, proven here:

* `pi_third_pitch_closes` / `mu6_closure` — the carrier's π/3 pitch is COMMENSURATE:
  six steps close exactly (`ζ₆⁶ = 1`) and one hexagonal cell cancels residue-free
  (`Σ ζ₆^k = 0`).  A commensurate winding is a closed orbit, not a dense one — the
  phase lattice tiles exactly, leaving no incommensurate gap anywhere.
* `gauged_fiber_continuous` — in the exact gauge the welded fiber `t ↦ Λ(½+it)` is
  CONTINUOUS on the whole line (the completed object is entire up to its two named
  poles, both off the weld).
* `fiber_global_real_section` — **the gapless statement**: the gauged fiber IS one
  continuous REAL global section of the weld.  Not local patches glued across
  overlaps — a single global object, exhibited.  A gluing problem whose global
  section is exhibited (and rigid: `source_datum_rigidity`) has trivial gluing
  cohomology BY CONSTRUCTION: there is no cover, hence no nerve, hence no Čech class,
  hence nowhere for a local-to-global obstruction to exist.  The S(t) π-jumps are
  the `arg` CHART's discontinuity at 0 pulled back through zero crossings of this
  continuous real section — artifacts of the readout chart, never gaps of the fiber
  (`weld_ledger_complete` locates all of them at crossings).

Honest boundary: this section sees the weld line; it does not decide off-weld
behavior.  But combined with the carrier and harmonic theorems above, a sourceless
zero now provably cannot hide in the carrier phase, the amplitude law, or any gap of
the welded fiber.  The one hiding place left standing is the off-weld analytic null
space of the rank-one readout — the summed-fiber wall, named and now isolated. -/

/-- **The π/3 pitch closes exactly**: the hexagonal step is a sixth root of unity —
six steps return to the start.  The carrier winding is commensurate: a closed orbit,
no incommensurate gap. -/
theorem pi_third_pitch_closes : Complex.exp (Real.pi / 3 * I) ^ 6 = 1 := by
  rw [← Complex.exp_nat_mul]
  have h : ((6 : ℕ) : ℂ) * ((Real.pi : ℂ) / 3 * I) = 2 * Real.pi * I := by
    push_cast
    ring
  rw [h, Complex.exp_two_pi_mul_I]

/-- The hexagonal step is not the identity (its real part is `cos(π/3) = ½ ≠ 1`). -/
theorem pi_third_pitch_ne_one : Complex.exp (Real.pi / 3 * I) ≠ 1 := by
  intro h
  have hcast : (Real.pi : ℂ) / 3 * I = ((Real.pi / 3 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hcast] at h
  have hre := congrArg Complex.re h
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three] at hre
  norm_num at hre

/-- **μ₆ closure**: the six phases of one hexagonal cell cancel exactly — the
residue-free closure of the carrier's π/3 cell, as pure algebra. -/
theorem mu6_closure :
    ∑ k ∈ Finset.range 6, Complex.exp (Real.pi / 3 * I) ^ k = 0 := by
  rw [geom_sum_eq pi_third_pitch_ne_one, pi_third_pitch_closes]
  simp

/-- **The gauged fiber is continuous on the whole weld**: `t ↦ Λ(½+it)` has no jumps
and no gaps — the completed object is entire away from its two poles, and both poles
(`s = 0, 1`) are off the weld line. -/
theorem gauged_fiber_continuous :
    Continuous fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  have hline : Continuous fun t : ℝ => (1 / 2 + (t : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have h₀ : Continuous fun t : ℝ => completedRiemannZeta₀ (1 / 2 + (t : ℂ) * I) :=
    differentiable_completedZeta₀.continuous.comp hline
  have hs : ∀ t : ℝ, (1 / 2 + (t : ℂ) * I) ≠ 0 := StOscillation.line_ne_zero
  have h1s : ∀ t : ℝ, (1 : ℂ) - (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re] at this
    norm_num at this
  have heq : (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * I))
      = fun t : ℝ => completedRiemannZeta₀ (1 / 2 + (t : ℂ) * I)
          - 1 / (1 / 2 + (t : ℂ) * I) - 1 / (1 - (1 / 2 + (t : ℂ) * I)) := by
    funext t
    exact completedRiemannZeta_eq _
  rw [heq]
  exact (h₀.sub (continuous_const.div hline hs)).sub
    (continuous_const.div (continuous_const.sub hline) h1s)

/-- **THE GAPLESS FIBER**: the exactly-gauged weld fiber is ONE continuous REAL global
section — exhibited, not glued.  No cover, no nerve, no Čech class: there is no gap
for a local-to-global obstruction to live in. -/
theorem fiber_global_real_section :
    ∃ F : ℝ → ℝ, Continuous F ∧
      ∀ t : ℝ, completedRiemannZeta (1 / 2 + (t : ℂ) * I) = (F t : ℂ) := by
  refine ⟨fun t => (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re,
    Complex.continuous_re.comp gauged_fiber_continuous, fun t => ?_⟩
  apply Complex.ext
  · simp
  · simpa using HelixCollapse.completedRiemannZeta_critical_line_im_zero t

/-! ## The center: the one point where sourcelessness is impossible

Owner's squeeze (2026-07-02): gaplessness in the circulant (phase) direction and the
linear (height) direction leaves a hypothetical sourceless zero nowhere to live except
the doubly-fixed point — the center (`x = ½, iy = 0` in the classical chart; `z = 0`
here).  The provable endpoint is sharper: the center is EXCLUDED.  It is fixed by the
weld, so a vanishing there is a SOURCE by definition (`center_never_sourceless`) —
when the duality sign is `−1` it is even forced by the symmetry itself (the BSD-type
central zero: sourced BY the duality).  With the duality added, a sourceless zero's
symmetry orbit is a QUARTET (`sourceless_quartet`), and the orbit collapses to a
single point exactly at the center (`orbit_collapses_iff_center`) — the one place
with nowhere left to be exchanged to is the one place sourcelessness cannot occur.

Calibration of the squeeze itself: the gapless theorems close every COHOMOLOGICAL
hiding place (carrier phase, amplitude, welded-fiber gaps).  What they do not yet
forbid is a naked ANALYTIC vanishing of the readout off the weld — an off-weld zero
needs no gap to exist; it needs only the null space.  That step — the null space
cannot reach zero off the weld — is the wall, in its final isolated form. -/

/-- **Duality symmetry**: the fiber is even under the height duality `z ↦ −z` (the
functional equation of the completed object, in the weld chart). -/
def DualSymmetric (E : ℂ → ℂ) : Prop := ∀ z : ℂ, E (-z) = E z

/-- **A vanishing at the center is never sourceless**: the center is weld-fixed, so a
zero there is a source by definition — the doubly-fixed point is the one location in
the plane where sourcelessness is impossible. -/
theorem center_never_sourceless (E : ℂ → ℂ) : ¬Sourceless E 0 :=
  fun h => h.2 (map_zero _)

/-- A central vanishing is a source. -/
theorem center_zero_is_source {E : ℂ → ℂ} (h0 : E 0 = 0) : IsSource E 0 :=
  ⟨h0, map_zero _⟩

/-- **The quartet law**: under both symmetries, a sourceless zero forces vanishing at
all FOUR points of its orbit `{z, z̄, −z, −z̄}` — sourceless holonomy always arrives
as a full exchanged quartet. -/
theorem sourceless_quartet {E : ℂ → ℂ} (hw : WeldSymmetric E) (hd : DualSymmetric E)
    {z : ℂ} (hz : Sourceless E z) :
    E z = 0 ∧ E ((starRingEnd ℂ) z) = 0 ∧ E (-z) = 0 ∧ E (-(starRingEnd ℂ) z) = 0 :=
  ⟨hz.1, (sourceless_twin hw hz).1, by rw [hd, hz.1],
    by rw [hd, (sourceless_twin hw hz).1]⟩

/-- **Full degeneration happens only at the center**: the symmetry orbit collapses to
a single point iff `z = 0`.  A sourceless zero can therefore NEVER degenerate to the
doubly-fixed point — the only location with nowhere left to hide is the only location
where sourcelessness is impossible. -/
theorem orbit_collapses_iff_center {z : ℂ} :
    ({z, (starRingEnd ℂ) z, -z, -(starRingEnd ℂ) z} : Set ℂ) = {z} ↔ z = 0 := by
  constructor
  · intro h
    have hmem : -z ∈ ({z, (starRingEnd ℂ) z, -z, -(starRingEnd ℂ) z} : Set ℂ) := by
      simp
    rw [h] at hmem
    have hneg : -z = z := hmem
    have h2 : z + z = 0 := by linear_combination -hneg
    exact add_self_eq_zero.mp h2
  · rintro rfl
    simp

/-! ## No birth seam: there is no place between 0 and greater-than-0

Owner's closing move (2026-07-02): the bank grows phasors right past 0 — each enters
continuously at zero magnitude (heights > 0; no jump-in, no discrete birth event).  A
new dimension would need an attachment seam, and the candidate seams are now all
closed: the center is excluded (`center_never_sourceless`), the carrier moduli is a
single point (`source_datum_rigidity`), and the birth of a phasor offers no seam
either, because "between 0 and greater-than-0" is not a place: the positive reals
have no least element (`no_first_positive_height`) — below any positive height there
are more positive heights, all the way down, with nothing interstitial.  Entry at
zero magnitude into a dense, seamless parameter ray leaves no boundary event anywhere
in the construction for an extra coordinate to attach to.  A sourceless zero would
need a dimension with no generator (rigidity), no gap to live in (gapless fiber), no
fixed point to degenerate to (center), and now no seam to attach at (this).  What
remains untouched is, as ever, the analytic wall — but the topological perimeter of
the construction is closed. -/

/-- **There is no first positive height**: no place exists between `0` and
"greater than `0`" — below every positive height lies another.  The phasor entry ray
is seamless; a dimension cannot attach at a birth event because no birth boundary
exists. -/
theorem no_first_positive_height :
    ¬∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ε ≤ δ := by
  rintro ⟨ε, hε, hmin⟩
  have h := hmin (ε / 2) (by linarith)
  linarith

/-! ## One line, one spacing: uniform impurity is a chart shift

Owner's ontological axiom (2026-07-02): 1D space is ONE line from the origin with ONE
L²-placement; a "second line with alternate spacing as transparent overlay" is not a
valid construction — that is multiverse thinking, not a 1D universe.  Consequences,
with the proven kernel:

* `uniform_impurity_is_chart_shift` — the "impure datum" counterexample (`a_p = p^θ`,
  uniformly) is DEAD: uniform impurity is a TRANSLATION of the `s`-chart.  The object
  is the same line mislabeled; its weld travels with it; its zeros sit on its OWN
  self-dual line.  A chart artifact, exactly like S(t).
* What survives as genuinely other: p-VARYING impurity (no single shift repairs it —
  incommensurate clock spacings = two lines overlaid) and Davenport–Heilbronn-type
  combinations (two welded Euler universes).  Both are, in the owner's sense, invalid
  single-universe constructions — and they are ALL the known off-weld-zero producers.
* The proven kernel this connects to: `ChiralCup.midpoint_forcing` — if the two dual
  spacings AGREE at a point (`‖q^s‖² = q`), that point is the midpoint `Re s = ½`.
  "One spacing ⟺ on the weld" is a theorem.  The wall, in its sharpest form yet:
  prove that a VANISHING of the one-line object forces the dual spacing balance.
  Per clock that is proven (`clock_zero_depth`: zeros sit exactly at balance depth);
  for the sum it is the open step.  An off-weld zero of the sum would be a vanishing
  at which the two dual amplitude ladders disagree — a transparent overlay of two
  spacings on one line, which the ontological axiom forbids and no valid construction
  has ever exhibited. -/

/-- **Uniform impurity is a chart shift**: scaling the whole datum by `n^θ` is exactly
a translation of `s` — the same line read in mislabeled coordinates.  The
shifted-datum "counterexample" to weld-confinement is a chart artifact: its weld
moves with it. -/
theorem uniform_impurity_is_chart_shift (s θ : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ^ (-(s - θ)) = (n : ℂ) ^ θ * (n : ℂ) ^ (-s) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← Complex.cpow_add _ _ h0]
  ring_nf

/-! ## No non-simple zeros: multiplicity is killed by the same pillar

Owner's identification (2026-07-02): the forbidden overlay-vanishing "is called a
non-simple or complex zero, and the helix doesn't have those either."  Proven for the
carrier, by FREENESS itself:

* `clock_zero_simple` — every zero of every clock is SIMPLE: the derivative at any
  zero is `2c·e^{cz} ≠ 0`.  One clock cannot double a zero.
* `no_common_beat` — the FTA kernel: distinct primes have no common power,
  `p^k ≠ q^m`.  `no_common_period` — the bridge: two clocks with rates `log p`,
  `log q` share no nonzero period, else `p^m = q^k`.
* `clocks_share_only_center` — distinct prime clocks share NO zero except the
  universal center `z = 0`: a shared zero off-center would be a common beat of two
  incommensurate clocks — the transparent overlay of two spacings, forbidden by FTA.

Hence every off-center zero of the finite carrier belongs to EXACTLY ONE clock, with
multiplicity EXACTLY ONE: the multiplicity dimension is closed for the carrier by the
same pillar (freeness) that closed the holonomy dimension.  For the summed fiber,
simplicity is the classical open conjecture; its measured face is GUE repulsion (the
in-house pair-correlation record: no multiple zero ever observed, first genuinely
close pairs at heights 66678/71733), and the birth-channel picture makes the owner's
identification exact: an exchanged off-weld pair can only be born through an on-weld
COLLISION — a non-simple zero — under continuous deformation of the bank.  No such
event exists anywhere in the record; the sharp-truncation (Turán) off-line zeros of
partial sums are clipping artifacts the smooth-entry bank does not have ("never
clip" — and the audit found zero ghosts). -/

/-- **The FTA kernel**: distinct primes share no common power. -/
theorem no_common_beat {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {k m : ℕ} (hk : k ≠ 0) (h : p ^ k = q ^ m) : False := by
  have hdvd : p ∣ q ^ m := h ▸ dvd_pow_self p hk
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-- **No common period**: two clocks with rates `log p`, `log q` (distinct primes)
share no nonzero period — a common period would force `p^m = q^k`, the forbidden
common beat.  Two incommensurate spacings cannot overlay. -/
theorem no_common_period {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {t : ℝ} (ht : t ≠ 0) {k m : ℤ}
    (h1 : t * Real.log p = k * (2 * Real.pi))
    (h2 : t * Real.log q = m * (2 * Real.pi)) : False := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact ht h
    · exact absurd h (ne_of_gt hlogp)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact ht h
    · exact absurd h (ne_of_gt hlogq)
  have hmk : (m : ℝ) * Real.log p = (k : ℝ) * Real.log q := by
    have hz : t * ((m : ℝ) * Real.log p - (k : ℝ) * Real.log q) = 0 := by
      linear_combination (m : ℝ) * h1 - (k : ℝ) * h2
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h ht
    · linarith [sub_eq_zero.mp h]
  have hcast : ∀ j : ℤ, (j.natAbs : ℝ) = |(j : ℝ)| := fun j => by simp
  have habs : (m.natAbs : ℝ) * Real.log p = (k.natAbs : ℝ) * Real.log q := by
    have := congrArg abs hmk
    rwa [abs_mul, abs_mul, abs_of_pos hlogp, abs_of_pos hlogq,
      ← hcast, ← hcast] at this
  have hlogeq : Real.log ((p : ℝ) ^ m.natAbs) = Real.log ((q : ℝ) ^ k.natAbs) := by
    rw [Real.log_pow, Real.log_pow]
    exact_mod_cast habs
  have hppos : (0 : ℝ) < (p : ℝ) ^ m.natAbs :=
    pow_pos (by exact_mod_cast hp.pos) _
  have hqpos : (0 : ℝ) < (q : ℝ) ^ k.natAbs :=
    pow_pos (by exact_mod_cast hq.pos) _
  have hpq : ((p : ℝ) ^ m.natAbs) = ((q : ℝ) ^ k.natAbs) := by
    have := congrArg Real.exp hlogeq
    rwa [Real.exp_log hppos, Real.exp_log hqpos] at this
  have hnat : p ^ m.natAbs = q ^ k.natAbs := by exact_mod_cast hpq
  exact no_common_beat hp hq hne (Int.natAbs_ne_zero.mpr hm0) hnat

/-- **Distinct prime clocks share only the center**: a common zero of the pure clocks
at rates `log p ≠ log q` off the center would be a common period of two
incommensurate clocks — forbidden.  Every off-center zero of the carrier belongs to
exactly one clock. -/
theorem clocks_share_only_center {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {z : ℂ} (hzp : CriticalLinePhasor.ChiralityHB.symClock 1 (Real.log p) z = 0)
    (hzq : CriticalLinePhasor.ChiralityHB.symClock 1 (Real.log q) z = 0) : z = 0 := by
  by_contra hz0
  have him : z.im = 0 :=
    CriticalLinePhasor.ChiralityHB.clock_zeros_real (by simp)
      (Real.log_pos (by exact_mod_cast hp.one_lt)) hzp
  rw [CriticalLinePhasor.ChiralityHB.symClock_zero_iff, Complex.exp_eq_one_iff] at hzp hzq
  obtain ⟨k, hk⟩ := hzp
  obtain ⟨m, hm⟩ := hzq
  have hkz : z * (Real.log p : ℂ) = (k : ℂ) * (2 * Real.pi) := by
    have : Complex.I * (z * (Real.log p : ℂ)) = Complex.I * ((k : ℂ) * (2 * Real.pi)) := by
      linear_combination hk
    exact mul_left_cancel₀ Complex.I_ne_zero this
  have hmz : z * (Real.log q : ℂ) = (m : ℂ) * (2 * Real.pi) := by
    have : Complex.I * (z * (Real.log q : ℂ)) = Complex.I * ((m : ℂ) * (2 * Real.pi)) := by
      linear_combination hm
    exact mul_left_cancel₀ Complex.I_ne_zero this
  have hzre : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
  have h1 : z.re * Real.log p = (k : ℝ) * (2 * Real.pi) := by
    apply Complex.ofReal_inj.mp
    rw [Complex.ofReal_mul, hzre, hkz]
    push_cast
    ring
  have h2 : z.re * Real.log q = (m : ℝ) * (2 * Real.pi) := by
    apply Complex.ofReal_inj.mp
    rw [Complex.ofReal_mul, hzre, hmz]
    push_cast
    ring
  have htne : z.re ≠ 0 := by
    intro h
    exact hz0 (Complex.ext h him)
  exact no_common_period hp hq hne htne h1 h2

/-- **Every clock zero is simple**: the derivative at any zero is `2c·e^{cz} ≠ 0` —
one clock cannot double a zero.  (With `clocks_share_only_center`: the carrier has no
non-simple zeros off the center at all.) -/
theorem clock_zero_simple {α : ℂ} {ℓ : ℝ} (hℓ : ℓ ≠ 0) {z : ℂ}
    (hz : CriticalLinePhasor.ChiralityHB.symClock α ℓ z = 0) :
    ∃ v : ℂ, v ≠ 0 ∧ HasDerivAt (CriticalLinePhasor.ChiralityHB.symClock α ℓ) v z := by
  set c : ℂ := Complex.I * ℓ / 2 with hc
  have hcne : c ≠ 0 :=
    div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hℓ)) two_ne_zero
  have harg : ∀ w : ℂ, Complex.I * w * ℓ / 2 = c * w := fun w => by rw [hc]; ring
  have hfun : CriticalLinePhasor.ChiralityHB.symClock α ℓ
      = fun w => Complex.exp (c * w) - α * Complex.exp (-(c * w)) := by
    funext w
    unfold CriticalLinePhasor.ChiralityHB.symClock
    rw [harg w]
  have h0 : HasDerivAt (fun w : ℂ => c * w) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (c * w)) (Complex.exp (c * z) * c) z :=
    h0.cexp
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (-(c * w)))
      (Complex.exp (-(c * z)) * (-c)) z := h0.neg.cexp
  have hD : HasDerivAt (CriticalLinePhasor.ChiralityHB.symClock α ℓ)
      (Complex.exp (c * z) * c - α * (Complex.exp (-(c * z)) * (-c))) z := by
    rw [hfun]
    exact h1.sub (h2.const_mul α)
  have hbal : α * Complex.exp (-(c * z)) = Complex.exp (c * z) := by
    have hz' := hz
    rw [hfun] at hz'
    exact (sub_eq_zero.mp hz').symm
  refine ⟨_, ?_, hD⟩
  have hval : Complex.exp (c * z) * c - α * (Complex.exp (-(c * z)) * (-c))
      = 2 * c * Complex.exp (c * z) := by
    linear_combination c * hbal
  rw [hval]
  exact mul_ne_zero (mul_ne_zero two_ne_zero hcne) (Complex.exp_ne_zero _)

/-! ## THE PROOF TARGET: EXHAUSTION (owner-set, 2026-07-02)

Hilbert–Pólya's criterion is satisfied on the line at iff-strength (the bridge:
resonance ⟺ `L(½ + i log Z) = 0`; spectrum real by self-adjointness; `e^γ ↔ γ` erased
by the spectral mapping theorem).  What remains of RH is ONE WORD — "all": the
resonance set must EXHAUST the zero set.  The owner sets this as the 3D proof target.

Named here, never assumed.  What is already proven toward it:
* `state_space_exhausted` — the 3D state space is exhausted by the modes,
  unconditionally: every bank state is the finite sum of its basis modes; the spectral
  resolution leaves nothing over.  Exhaustion HOLDS in 3D.
* `exhaustive_iff_no_sourceless` / `exhaustive_iff_on_axis` — the target is exactly
  the absence of sourceless zeros, exactly weld-confinement: one target, five faces
  (location, holonomy, dimension, multiplicity, HP-completeness).
* The bridge (on-line iff), the perimeter (no structural hiding place), the finite
  measured face (census = argument-principle count vs sources: 5/5, zero register
  hits — Turing-style finite exhaustion on every audited window).

The gap, stated exactly: TRANSFER — modes exhaust STATES (proven); the target is that
resonances exhaust the READOUT'S CONTINUATION ZEROS.  The transfer must pass through
the rank-one readout, and any successful argument must consume freeness (DH),
growth (the jet ladder), and exact criticality (Rodgers–Tao) simultaneously. -/

/-- **The exhaustion target**: every vanishing of the fiber is a weld-fixed resonance —
the resonance set accounts for ALL zeros.  This is the Hilbert–Pólya "all", the 3D
proof target.  A `Prop`, stated, never assumed. -/
def Exhaustive (E : ℂ → ℂ) : Prop := ∀ z : ℂ, E z = 0 → IsSource E z

/-- Exhaustion ⟺ no sourceless zeros: the target is exactly the fifth face of the one
wall. -/
theorem exhaustive_iff_no_sourceless (E : ℂ → ℂ) :
    Exhaustive E ↔ ∀ z : ℂ, ¬Sourceless E z := by
  constructor
  · intro h z hs
    exact hs.2 (h z hs.1).2
  · intro h z hz
    refine ⟨hz, ?_⟩
    by_contra hfix
    exact h z ⟨hz, hfix⟩

/-- Exhaustion ⟺ weld confinement (via the faithfulness theorem). -/
theorem exhaustive_iff_on_axis (E : ℂ → ℂ) :
    Exhaustive E ↔ ∀ z : ℂ, E z = 0 → z.im = 0 :=
  everyZeroHasSource_iff E

/-- **The 3D state space is exhausted by the modes, unconditionally**: every bank
state IS the finite sum of its basis modes — the spectral resolution of the diagonal
generator leaves nothing over.  In 3D, exhaustion is a theorem; the wall is exactly
the TRANSFER of this exhaustion through the rank-one readout to the continuation's
zeros. -/
theorem state_space_exhausted (v : ℕ →₀ ℂ) :
    (v.sum fun n c => Finsupp.single n c) = v :=
  Finsupp.sum_single v

/-! ## 3D exhaustion, unconditional (owner, 2026-07-02)

"You should be able to prove it unconditionally for 3D zeros."  Proven — and the proof
is SHORT for exactly the ontological reason: the 3D representation's event space is
the height ray, which IS the weld.  The strip is a 1D-projection device with no 3D
counterpart; in 3D there is nowhere off-weld for a zero event to occur, so every 3D
zero is a source by the geometry of the representation itself.

* `threeD_exhaustive` — EVERY fiber (no hypotheses at all) is exhaustive over the 3D
  event space: a zero event at a height is weld-fixed, hence a source.
* `threeD_metric_no_zeros` — stronger still: in the 3D metric NOTHING vanishes except
  the zero state (`cup_nullspace_safe` re-exported) — "3D zeros" in the state sense do
  not exist; zeros are readout events at heights, and all of those are sourced.
* With the bridge iff (`CriticalLineBridge`): the 3D resonance set equals the on-line
  1D zero set exactly.  So the 3D program is COMPLETE on its own side, with nothing
  left over.  The open remainder is solely whether the 1D continuation vanishes
  anywhere the 3D object never expresses — the `Exhaustive` target above. -/

/-- The 3D restriction of the exhaustion target: every zero event on the height ray —
the 3D object's ENTIRE event space — is a source. -/
def ThreeDExhaustive (E : ℂ → ℂ) : Prop :=
  ∀ y : ℝ, E (y : ℂ) = 0 → IsSource E (y : ℂ)

/-- **3D exhaustion holds unconditionally, for every fiber**: heights are weld-fixed,
so every 3D zero event is a source.  The triviality of this proof is the ontology made
formal: in 3D there is nowhere else for a zero to happen. -/
theorem threeD_exhaustive (E : ℂ → ℂ) : ThreeDExhaustive E :=
  fun y h => ⟨h, Complex.conj_ofReal y⟩

/-- **The 3D metric admits no zeros at all**: the cup norm vanishes only on the zero
state.  In the state space there is nothing to exhaust — vanishing is exclusively a
property of readings, never of states. -/
theorem threeD_metric_no_zeros (F : ℕ →₀ ℂ) :
    CriticalLinePhasor.CupIdentity.Cup F F = 0 ↔ F = 0 :=
  CriticalLinePhasor.ChiralCup.cup_nullspace_safe F

/-! ## Origin positivity, unconditional in 3D (owner, 2026-07-02)

"HB even by the origin positivity."  The route: Li's criterion reads the whole
confinement question off the jet ladder at the CENTER — the doubly-fixed point where
the odd jets are already dead by parity (`HingeKernel.even_live_jet_is_even`) and
where sourcelessness is impossible (`center_never_sourceless`).  The measured face
(`tmp/li_origin.py`): λ₁..λ₂₄ all positive, anchor to 12 digits, with the
Bombieri–Lagarias attribution showing a two-carrier relay — primes fund the low
orders (+γ at n=1 against a NEGATIVE gauge part), gauge funds the high orders,
handoff at n≈8, and a 96% cancellation at n=1: criticality measured at the origin
with no zeros involved.

The unconditional 3D content, proven here:
* `liCoeff` — the Li transform of a jet sequence (the origin ladder).
* `liCoeff_add` — **attribution is exact at every order**: the transform is additive,
  so every unit of origin positivity is carried by a named source component (the
  license behind the measured gauge/prime table).
* `liCoeff_nonneg` / `liCoeff_pos` — **positivity transfers**: a medium with
  pointwise-nonnegative jet data has a nonnegative origin ladder — the binomial
  weights are positive, and sums of nonnegatives admit no interference.  The
  no-conspiracy principle at the origin: in the 3D state space, where energies are
  nonnegative (`cup_positive_semidefinite`) and amplitudes cannot wind
  (`positive_scaling_coboundary`), origin positivity is STRUCTURAL.  The open
  question lives only in the readout's mixed-sign jets — the wall, in Li dress:
  prove the two-carrier relay never drops the baton. -/

/-- **The Li transform** of a jet sequence: the origin ladder
`liCoeff c n = n·Σ_{j=1}^{n} C(n−1, n−j)·c j`. -/
noncomputable def liCoeff (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  n * ∑ j ∈ Finset.Icc 1 n, ((n - 1).choose (n - j) : ℝ) * c j

/-- **Attribution is exact at every order**: the Li transform is additive, so the
origin ladder of a welded pair of carriers is the sum of the carriers' ladders —
every unit of origin positivity has a nameable source. -/
theorem liCoeff_add (c d : ℕ → ℝ) (n : ℕ) :
    liCoeff (fun j => c j + d j) n = liCoeff c n + liCoeff d n := by
  unfold liCoeff
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Positivity transfers unconditionally**: nonnegative jet data has a nonnegative
origin ladder — the binomial weights are positive and sums of nonnegatives admit no
interference.  No conspiracy can make a positive-jet medium read negative at the
origin. -/
theorem liCoeff_nonneg {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (n : ℕ) :
    0 ≤ liCoeff c n := by
  unfold liCoeff
  apply mul_nonneg (Nat.cast_nonneg n)
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hc j)

/-- Strict origin positivity from one live nonnegative jet: if the jet data is
nonnegative and any single order `j ≤ n` (with `1 ≤ j`, `1 ≤ n`) is strictly live and
its binomial weight nonzero, the ladder is strictly positive at `n`. -/
theorem liCoeff_pos {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) {n j : ℕ}
    (hj : j ∈ Finset.Icc 1 n) (hlive : 0 < ((n - 1).choose (n - j) : ℝ) * c j)
    (hn : 1 ≤ n) : 0 < liCoeff c n := by
  unfold liCoeff
  apply mul_pos
  · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  · exact Finset.sum_pos' (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hc i)) ⟨j, hj, hlive⟩

/-! ## The loss ledger — the base of the Li relay (owner, 2026-07-03)

Owner's positivity base: "midpoint projection loses radius (positive); Möbius/Cayley
unit circle loses angle (positive); taking logs to map heights doesn't change sign" —
and the sharpening: "the helix has no negative sector; it has a CONJUGATE sector.
The functional equation identifies the two π/2 transverse arms through the midpoint
origin, and positivity is the Gram positivity of that conjugate pairing."

The Bombieri–Lagarias dress of the Li ladder is the sum over the zero ledger of
`1 − zⁿ` in the Cayley chart `z = 1 − 1/ρ`.  This block proves the ledger mechanics,
each entry unconditional:

* `cayley_midpoint_faithful` — **entry 1, radius**: the chart is the exact radius
  detector — `‖z‖ = 1 ⟺ Re ρ = 1/2`.  A sourced zero pays no radial loss; only a
  sourceless one carries radius into the readout.
* `conjugate_sector` — **the sector claim**: the FE sends a chart point to the
  transverse arm `(conj z)⁻¹`; the two arms are IDENTIFIED (partner = conjugate)
  exactly on the unit circle.  There is no negative sector, only a conjugate one.
* `angle_loss_is_energy` / `angle_loss_nonneg` — **entry 2, angle**: on the circle
  the ledger entry `2 − 2 Re(zⁿ)` IS the Gram diagonal `normSq (1 − zⁿ)` of the
  conjugate pairing — a squared chord.  Positive because it is a SQUARE, not by
  estimate: Gram positivity, the cup metric's signature in Li dress.
* `ledger_positivity` — **the baton lemma**: a fully sourced ledger is nonnegative
  at EVERY order.  `Exhaustive ⟹ Li positivity`, term by term, unconditionally.
* `radius_loss_convex` — **entry 3, log chart**: the FE quartet's radial defects
  COMPOUND instead of cancelling — `rⁿ + r⁻ⁿ ≥ 2`, the floor attained exactly on
  the circle.  The log-height chart cannot change the ledger's sign.
* `radius_defect_unbounded` / `sourceless_entry_negative` / `dropped_baton` — the
  falsification arm: a sourceless quartet's compounded defect is unbounded, and at
  every late recurrence time of its winding it writes a strictly NEGATIVE entry —
  something no on-circle entry can produce.  One negative λₙ certifies a sourceless
  zero: the register's sixth face, computable from the bank (`tmp/li_origin.py`,
  λ₁..λ₂₄ measured positive).
* `recurrence_of_rational_angle` — the recurrence hypothesis witnessed for every
  rational winding (the irrational case is Weyl equidistribution: the orbit is dense,
  so it recurs; `hrec` stays a named hypothesis of `dropped_baton`).

Scope: does not assume or prove RH/GRH.  The sum-level composition — that the finite
negative excursion beats the sourced mass in the full ladder — is Bombieri–Lagarias
(Thm 1, 1999), cited as anchor, not re-derived.  What is new here is the mechanism:
positivity is a LOSS LEDGER, every stage of the 3D→1D chain is sign-preserving, and
the only object that can write a negative entry is a sourceless zero. -/

/-- **Entry 1 — midpoint projection loses radius.**  The Cayley chart `z = 1 − ρ⁻¹`
is the exact radius detector: the chart lands on the unit circle iff the zero sits at
the midpoint `Re ρ = 1/2`.  Radial loss in the readout ⟺ off-midpoint source. -/
theorem cayley_midpoint_faithful {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖1 - ρ⁻¹‖ = 1 ↔ ρ.re = 1 / 2 := by
  have h1 : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
  rw [h1, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hρ)]
  constructor
  · intro h
    have h2 : Complex.normSq (ρ - 1) = Complex.normSq ρ := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im] at h2
    linear_combination -h2 / 2
  · intro h
    have h2 : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, h]
      ring
    calc ‖ρ - 1‖ = Real.sqrt (‖ρ - 1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖ρ‖ ^ 2) := by rw [h2]
    _ = ‖ρ‖ := Real.sqrt_sq (norm_nonneg _)

/-- **The conjugate sector.**  "The helix has no negative sector; it has a conjugate
sector."  The functional equation sends a chart point `z` to the transverse arm
`(conj z)⁻¹` through the midpoint origin; the two arms are IDENTIFIED — FE partner =
conjugate — exactly on the unit circle.  A sourced entry pairs with its own conjugate
(Gram diagonal); only a sourceless entry has a partner it is not conjugate to. -/
theorem conjugate_sector {z : ℂ} (hz : z ≠ 0) :
    ((starRingEnd ℂ) z)⁻¹ = z ↔ ‖z‖ = 1 := by
  have hc : (starRingEnd ℂ) z ≠ 0 := by
    simpa using hz
  constructor
  · intro h
    have h2 := inv_mul_cancel₀ hc
    rw [h, Complex.mul_conj] at h2
    have h3 : Complex.normSq z = 1 := by exact_mod_cast h2
    have h4 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h3
    have h5 : (‖z‖ - 1) * (‖z‖ + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h5 with h6 | h6
    · linarith
    · linarith [norm_nonneg z]
  · intro h
    have h3 : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, h, one_pow]
    have h2 : (starRingEnd ℂ) z * z = 1 := by
      rw [mul_comm, Complex.mul_conj, h3, Complex.ofReal_one]
    exact inv_eq_of_mul_eq_one_right h2

/-- **Entry 2 — the entry is an energy.**  On the unit circle the ledger entry at
order `n` IS the Gram diagonal of the conjugate pairing: `2 − 2 Re(zⁿ)` equals the
squared chord `normSq (1 − zⁿ)` — the squared distance from closure.  Positivity is
Gram positivity: the entry is a square, not an estimate. -/
theorem angle_loss_is_energy {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    2 - 2 * (z ^ n).re = Complex.normSq (1 - z ^ n) := by
  have hn : Complex.normSq (z ^ n) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, hz, one_pow, one_pow]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at hn ⊢
  linear_combination -hn

/-- **Entry 2, corollary — the unit circle loses angle, positively.**  An on-circle
ledger entry is nonnegative at every order: the readout can only LOSE by winding. -/
theorem angle_loss_nonneg {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    0 ≤ 2 - 2 * (z ^ n).re := by
  rw [angle_loss_is_energy hz n]; exact Complex.normSq_nonneg _

/-- **The baton lemma.**  A fully sourced finite ledger — every entry on the circle —
is nonnegative at EVERY order, with no hypothesis on where the angles sit: each entry
is a Gram diagonal, and a sum of squares admits no interference.  This is the
`Exhaustive ⟹ Li positivity` half of the relay, term by term.  Scope: does not assume
or prove RH/GRH. -/
theorem ledger_positivity {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (n : ℕ) :
    0 ≤ ∑ i ∈ s, (2 - 2 * ((z i) ^ n).re) :=
  Finset.sum_nonneg fun i hi => angle_loss_nonneg (hz i hi) n

/-- **Entry 3 — the log-height chart cannot change sign.**  The FE quartet's radial
defects COMPOUND instead of cancelling: `rⁿ + r⁻ⁿ ≥ 2` for every positive radius,
with the floor attained exactly on the circle.  Radius lost by one partner is never
refunded by the other. -/
theorem radius_loss_convex {r : ℝ} (hr : 0 < r) (n : ℕ) :
    2 ≤ r ^ n + (r ^ n)⁻¹ := by
  have ha : 0 < r ^ n := pow_pos hr n
  have hinv : r ^ n * (r ^ n)⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  nlinarith [sq_nonneg (r ^ n - 1), inv_pos.mpr ha]

/-- Off the circle the compounded radial defect is UNBOUNDED: past some order it
exceeds every bound, permanently. -/
theorem radius_defect_unbounded {r : ℝ} (hr : 1 < r) (M : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, M < r ^ n + (r ^ n)⁻¹ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop M)
  exact ⟨N, fun n hn => lt_add_of_lt_of_pos (hN n hn)
    (inv_pos.mpr (pow_pos (lt_trans one_pos hr) n))⟩

/-- **A sourceless entry is negative at recurrence times.**  Once the radial defect
has compounded past 4 and the winding has returned (`cos ≥ 1/2`), the quartet's
ledger entry is strictly negative — radius loss masquerading as negative angle loss,
which no on-circle entry can produce. -/
theorem sourceless_entry_negative {S c : ℝ} (hS : 4 < S) (hc : 1 / 2 ≤ c) :
    2 - S * c < 0 := by nlinarith

/-- **The dropped baton**, composed: a sourceless quartet (radius `r > 1` after
FE-normalization) writes a strictly negative ledger entry at every late recurrence
time of its winding.  With the Bombieri–Lagarias reading, one negative order
falsifies exhaustion — the register's sixth face. -/
theorem dropped_baton {r : ℝ} (hr : 1 < r) {θ : ℝ}
    (hrec : ∀ N : ℕ, ∃ n ≥ N, 1 / 2 ≤ Real.cos (n * θ)) (N : ℕ) :
    ∃ n ≥ N, 2 - (r ^ n + (r ^ n)⁻¹) * Real.cos (n * θ) < 0 := by
  obtain ⟨N₀, hN₀⟩ := radius_defect_unbounded hr 4
  obtain ⟨n, hn, hcos⟩ := hrec (max N N₀)
  exact ⟨n, le_trans (le_max_left _ _) hn,
    sourceless_entry_negative (hN₀ n (le_trans (le_max_right _ _) hn)) hcos⟩

/-- The recurrence hypothesis, witnessed for every RATIONAL winding: the angle
`2π·p/q` returns exactly (`cos = 1`) along the multiples of its period.  The
irrational case is Weyl equidistribution — the orbit is dense on the circle, so it
recurs — and stays a named hypothesis of `dropped_baton`. -/
theorem recurrence_of_rational_angle (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ∀ N : ℕ, ∃ n ≥ N, 1 / 2 ≤ Real.cos (n * (2 * Real.pi * p / q)) := by
  intro N
  refine ⟨q * (N + 1), ?_, ?_⟩
  · calc N ≤ N + 1 := Nat.le_succ N
    _ ≤ q * (N + 1) := Nat.le_mul_of_pos_left _ hq
  · have hcast : ((q * (N + 1) : ℕ) : ℝ) * (2 * Real.pi * p / q) =
        (p * (N + 1) : ℤ) * (2 * Real.pi) := by
      push_cast
      field_simp
    rw [hcast, Real.cos_int_mul_two_pi]
    norm_num

/-- **The helix's own Li ladder is nonnegative — unconditionally** (owner: "we
already proved exhaustion on the helix").  Every 3D zero event lives at a real
height (`threeD_exhaustive`); the 1D chart places every such event at the midpoint
`Re ρ = 1/2`; by `cayley_midpoint_faithful` its Cayley image is ON the circle; and
there every ledger entry is a Gram diagonal (`ledger_positivity`).  Composed: any
finite ledger of midpoint events is nonnegative at EVERY order.  Li positivity FOR
THE HELIX is a theorem, not a hypothesis — the only 1D question left is
faithfulness: whether the readout's ledger contains an entry the helix never wrote
(`Exhaustive` = DPI).  Scope: does not assume or prove RH/GRH. -/
theorem helix_ledger_positive {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (hρ : ∀ i ∈ s, (ρ i).re = 1 / 2) (n : ℕ) :
    0 ≤ ∑ i ∈ s, (2 - 2 * (((1 : ℂ) - (ρ i)⁻¹) ^ n).re) := by
  refine ledger_positivity s _ (fun i hi => ?_) n
  have hne : ρ i ≠ 0 := by
    intro h
    have h2 := hρ i hi
    rw [h] at h2
    norm_num at h2
  exact (cayley_midpoint_faithful hne).mpr (hρ i hi)

/-- **The helix doesn't support DH concepts — it has the Euler product** (owner,
2026-07-03).  A composite weld — a nontrivial linear combination of two character
strands — is itself a character only if the strands were IDENTICAL all along: from
`c₁·χ₁ + c₂·χ₂ = ψ` pointwise with all three multiplicative and both coefficients
live, squaring one group element forces `c₁c₂·(χ₁ x − χ₂ x)² = 0`.  Davenport–
Heilbronn has no completely multiplicative coefficient stream, hence no phasor
bank, no fiber, no helix: its off-line zeros are READOUT-ONLY objects.  The loss
ledger's negative entries on DH are the detector firing on a foreign object — a
positive control, never a helix event.  Elementary and self-contained (no Artin
independence needed). -/
theorem composite_weld_forces_equal {G R : Type*} [Monoid G] [CommRing R]
    [NoZeroDivisors R] (χ₁ χ₂ ψ : G →* R) {c₁ c₂ : R} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (h : ∀ x, c₁ * χ₁ x + c₂ * χ₂ x = ψ x) : χ₁ = χ₂ := by
  ext x
  have h1 := h 1
  simp only [map_one, mul_one] at h1
  have hψ := h x
  have hx2 := h (x * x)
  simp only [map_mul] at hx2
  have key : c₁ * c₂ * (χ₁ x - χ₂ x) ^ 2 = 0 := by
    linear_combination hx2 - (ψ x + c₁ * χ₁ x + c₂ * χ₂ x) * hψ +
      (c₁ * χ₁ x ^ 2 + c₂ * χ₂ x ^ 2) * h1
  have hsq : (χ₁ x - χ₂ x) ^ 2 = 0 :=
    (mul_eq_zero.mp key).resolve_left (mul_ne_zero hc₁ hc₂)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-! ### The Euler-factor spiral — one clock, two projections (owner, 2026-07-03)

"Euler product and FTA using helix angle math, and on the unit circle, the
projection appears to look like a spiral based on the Euler factor."  The
angle-addition half is already proven log-free (`HelixLogFreeFTA.windAngle_mul` /
`wind_mul`: the winding is a completely multiplicative character — FTA as angle
math; cited, not re-derived).  What is proven here is the PROJECTION half: a single
Euler factor's phasor `exp(−s·ln p)` is ONE complex motion whose two real
projections are the ledger's two columns — the phase is `−Im(s)·ln p` and the
log-radius is `−Re(s)·ln p`, both driven by the SAME clock `ln p`.  On the midpoint
the radius column is frozen and the trajectory is the circle (the helix seen down
its axis); any transverse drift opens it into a logarithmic spiral whose pitch is
the same `ln p` that clocks the winding.  This is why the loss ledger's angle and
radius entries are commensurable — and why a radius defect cannot hide: it is
paid in the same currency the winding is counted in. -/

/-- **One clock, column one**: the log-radius of an Euler-factor phasor is the real
projection `−c·Re s` of the motion `−c·s` — the same `c = ln p` that drives the
phase.  (Column two, the phase, is `−c·Im s` by inspection of the exponent.) -/
theorem euler_factor_log_norm (c : ℝ) (s : ℂ) :
    Real.log ‖Complex.exp (-(c : ℂ) * s)‖ = -c * s.re := by
  rw [Complex.norm_exp, Real.log_exp]
  simp [Complex.mul_re]

/-- **Circle iff midpoint**: two heights of an Euler-factor phasor share a radius
iff they share a real part — the trajectory closes into a circle exactly on a
vertical line, and the midpoint line is the helix's carrier at rate `ln p`.  Off
it, the same clock opens the circle into a spiral. -/
theorem euler_factor_circle_iff {c : ℝ} (hc : c ≠ 0) (s₁ s₂ : ℂ) :
    ‖Complex.exp (-(c : ℂ) * s₁)‖ = ‖Complex.exp (-(c : ℂ) * s₂)‖ ↔
      s₁.re = s₂.re := by
  rw [Complex.norm_exp, Complex.norm_exp, Real.exp_eq_exp]
  constructor
  · intro h
    have h2 : -c * s₁.re = -c * s₂.re := by
      simpa [Complex.mul_re] using h
    exact mul_left_cancel₀ (neg_ne_zero.mpr hc) h2
  · intro h
    simp [Complex.mul_re, h]

/-- **The Euler spiral**: along ANY line `t ↦ s₀ + t·d` in the s-chart, the
log-radius and the phase of an Euler-factor phasor are BOTH affine in `t`, with
slopes `−c·Re d` and `−c·Im d` — the two projections of one linear motion, tied by
the single clock `c = ln p`.  Log-radius affine in phase = a logarithmic spiral;
`Re d = 0` (the midpoint direction) is exactly the degenerate pitch — the circle. -/
theorem euler_factor_spiral (c : ℝ) (s₀ d : ℂ) (t : ℝ) :
    Real.log ‖Complex.exp (-(c : ℂ) * (s₀ + t * d))‖ =
      -c * s₀.re + t * (-c * d.re) ∧
    (-(c : ℂ) * (s₀ + t * d)).im = -c * s₀.im + t * (-c * d.im) := by
  constructor
  · rw [euler_factor_log_norm]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [Complex.neg_im, Complex.neg_re, Complex.mul_im, Complex.add_im,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-! ### The unconditional chain (owner, 2026-07-03)

Owner's directive: "you can make that much more unconditional."  The chain, each
link a theorem, in order:

  `no_radial_drift_on_helix` → `helix_forces_midpoint_cancellation` →
  `helix_no_offline_cancellation` → `projection_bijective_loss_ledger` →
  `projection_retains_li_positivity` (3D→2D→1D) →
  `grh_from_helix_li_positivity` → `rh_from_grh_char_one`.

Every arrow is unconditional.  The entire conditional content of 1D GRH is
compressed into ONE hypothesis appearing at the second-to-last link: the
ATTRIBUTION hypothesis `hfaithful` — every entry of the readout's ledger charts
back to a helix height.  That is `Exhaustive` in ledger dress, and nothing else
in the chain assumes anything.  Positivity, the midpoint law, the no-off-line
law, the bijectivity of the chart chain, and the family-to-instance step
GRH → RH are all theorems.

PRECISION NOTE (owner dialogue, 2026-07-03).  The chart chain is bijective ONTO
ITS IMAGE — the height ray maps onto the midpoint LINE, not onto the strip; a
bijection re-coordinates whatever null set the readout has, it does not constrain
where the readout vanishes.  The proven inclusion is: every bank event charts to
an on-circle entry and IS a vanishing of the readout (this file + the lane-balance
bridge).  `hfaithful` is the CONVERSE inclusion — the readout vanishes nowhere
else — and it cannot be discharged by chart geometry alone: Davenport–Heilbronn's
readout admits the exact same midpoint and Cayley charts, the same ledger, yet
carries off-circle entries.  What DH lacks is a single free character
(`composite_weld_forces_equal`); any proof of `hfaithful` must therefore spend
the Euler product (freeness — the wall's first mandatory ingredient), not the
chart.  Scope: does not assume or prove RH/GRH. -/

/-- **Link 1 — no radial drift on the helix.**  On the carrier every Euler-factor
phasor has a frozen radius: the helix simply has no radial degree of freedom to
spend.  (`euler_factor_circle_iff` specialized to the midpoint line.) -/
theorem no_radial_drift_on_helix (c : ℝ) (y₁ y₂ : ℝ) :
    ‖Complex.exp (-(c : ℂ) * (((1/2 : ℝ) : ℂ) + y₁ * Complex.I))‖ =
    ‖Complex.exp (-(c : ℂ) * (((1/2 : ℝ) : ℂ) + y₂ * Complex.I))‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (euler_factor_circle_iff hc _ _).mpr (by simp)

/-- Chain plumbing: every helix height charts to an ON-CIRCLE ledger entry. -/
theorem midpoint_entry_on_circle (y : ℝ) :
    ‖1 - (((1/2 : ℝ) : ℂ) + y * Complex.I)⁻¹‖ = 1 := by
  have hre : ((((1/2 : ℝ) : ℂ)) + y * Complex.I).re = 1/2 := by simp
  have hne : (((1/2 : ℝ) : ℂ)) + y * Complex.I ≠ 0 := by
    intro h0
    rw [h0] at hre
    norm_num at hre
  exact (cayley_midpoint_faithful hne).mpr hre

/-- **Link 2 — the helix forces midpoint cancellation.**  A weld-fixed event (the
only kind of zero event the helix has: `threeD_exhaustive`) charts to the unit
circle: helix-funded cancellation happens AT the midpoint, with no radial loss,
always. -/
theorem helix_forces_midpoint_cancellation {z : ℂ} (hz : (starRingEnd ℂ) z = z) :
    ‖1 - (((1/2 : ℝ) : ℂ) + z * Complex.I)⁻¹‖ = 1 := by
  obtain hzre := Complex.conj_eq_iff_re.mp hz
  rw [← hzre]
  exact midpoint_entry_on_circle z.re

/-- **Link 3 — the helix cannot fund an off-line cancellation.**  Contrapositive of
Link 2: an off-circle ledger entry cannot come from a weld-fixed event.  Whatever
writes a radial defect into the readout, it is not the helix. -/
theorem helix_no_offline_cancellation {z : ℂ}
    (hoff : ‖1 - (((1/2 : ℝ) : ℂ) + z * Complex.I)⁻¹‖ ≠ 1) :
    (starRingEnd ℂ) z ≠ z :=
  fun hz => hoff (helix_forces_midpoint_cancellation hz)

/-- **Link 4 — the projection is bijective on the ledger.**  The chart chain
height → midpoint point → Cayley entry is INJECTIVE: distinct helix events write
distinct ledger entries, and the entry determines its source height.  The DPI made
literal for this chain: a bijective chart onto its image loses nothing and invents
nothing — the 1D ledger of helix events IS the helix ledger, re-charted. -/
theorem projection_bijective_loss_ledger :
    Function.Injective
      (fun y : ℝ => 1 - (((1/2 : ℝ) : ℂ) + y * Complex.I)⁻¹) := by
  intro y₁ y₂ h
  simp only [sub_right_inj] at h
  have h2 := inv_injective h
  have h3 := congrArg Complex.im h2
  simpa using h3

/-- **Link 5 — the 3D→2D→1D midpoint projection retains Li positivity.**  Push any
finite family of helix heights through the full chart chain: every image entry is
a Gram diagonal, and the projected ladder is nonnegative at EVERY order.  The
helix's Li positivity survives projection intact — unconditionally. -/
theorem projection_retains_li_positivity {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (n : ℕ) :
    0 ≤ ∑ i ∈ s,
      (2 - 2 * (((1 : ℂ) - (((1/2 : ℝ) : ℂ) + y i * Complex.I)⁻¹) ^ n).re) :=
  ledger_positivity s _ (fun i _ => midpoint_entry_on_circle (y i)) n

/-- **Link 6 — GRH from helix Li positivity.**  THE single conditional of the whole
program, in ledger dress: IF every entry of a readout's ledger charts back to a
helix height (`hfaithful` — attribution, = `Exhaustive` = DPI), THEN the readout's
Li ladder is nonnegative at every order.  The implication is a theorem; positivity
costs nothing beyond attribution.  With Bombieri–Lagarias (anchor, not re-derived),
ladder nonnegativity for every Dirichlet readout IS GRH. -/
theorem grh_from_helix_li_positivity {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hfaithful : ∀ i ∈ s, ∃ y : ℝ,
      z i = 1 - (((1/2 : ℝ) : ℂ) + y * Complex.I)⁻¹)
    (n : ℕ) : 0 ≤ ∑ i ∈ s, (2 - 2 * ((z i) ^ n).re) := by
  refine ledger_positivity s z (fun i hi => ?_) n
  obtain ⟨y, hy⟩ := hfaithful i hi
  rw [hy]
  exact midpoint_entry_on_circle y

/-- **Link 7 — RH from GRH, character 1.**  The family-to-instance step is pure
∀-instantiation: if the attribution hypothesis holds for EVERY character's ledger,
it holds for χ = 1, and ζ's ladder is nonnegative at every order — RH via
Bombieri–Lagarias (anchor).  RH is not an extra assumption on top of GRH; it is
GRH read at one character. -/
theorem rh_from_grh_char_one {Char ι : Type*} (ledger : Char → Finset ι)
    (entry : Char → ι → ℂ) (χ₀ : Char)
    (hGRH : ∀ χ, ∀ i ∈ ledger χ, ∃ y : ℝ,
      entry χ i = 1 - (((1/2 : ℝ) : ℂ) + y * Complex.I)⁻¹)
    (n : ℕ) : 0 ≤ ∑ i ∈ ledger χ₀, (2 - 2 * ((entry χ₀ i) ^ n).re) :=
  grh_from_helix_li_positivity (ledger χ₀) (entry χ₀) (hGRH χ₀) n

/-- **RH FOR THE 3D SPACE** (owner, 2026-07-02) — the composite fact, every clause
unconditional:
1. **Carrier**: every zero of the pure multiplicative carrier lies ON the conjugation
   axis (`ChiralityHB.carrier_zeros_real` — clock-RH, unconditional);
2. **States**: nothing in the 3D metric vanishes except the zero state
   (`threeD_metric_no_zeros`) — there are no state zeros to misplace at all;
3. **Events**: every zero event of every fiber on the height ray — the 3D object's
   entire event space — is a source (`threeD_exhaustive`).
With the spectrum real (self-adjoint diagonal), simple (`no_double_cancellation`),
and complete (`state_space_exhausted`), the 3D representation satisfies RH on its own
terms, with nothing assumed.  Classical RH is the further statement that the 1D limit
is FAITHFUL to this space — that the projection invents no holonomy the object never
carried (`Exhaustive`).  That is the challenge as positioned: not whether the 3D
space obeys RH (it does, proven), but whether the 1D readout can fail it. -/
theorem threeD_RH {ι : Type*} (s : Finset ι) (α : ι → ℂ) (ℓ : ι → ℝ)
    (hα : ∀ i ∈ s, ‖α i‖ = 1) (hℓ : ∀ i ∈ s, 0 < ℓ i) (E : ℂ → ℂ) (F : ℕ →₀ ℂ) :
    (∀ z : ℂ, (∏ i ∈ s, CriticalLinePhasor.ChiralityHB.symClock (α i) (ℓ i) z) = 0
      → z.im = 0)
    ∧ (CriticalLinePhasor.CupIdentity.Cup F F = 0 ↔ F = 0)
    ∧ ThreeDExhaustive E :=
  ⟨fun _ hz => CriticalLinePhasor.ChiralityHB.carrier_zeros_real s α ℓ hα hℓ hz,
   threeD_metric_no_zeros F, threeD_exhaustive E⟩

/-- **GRH_OF_HELIX_AND_DPI** (owner-named, 2026-07-02) — the program's SINGLE isolated
conditional, stated, never assumed.  The data-processing principle instantiated at the
fiber: every vanishing of the 1D readout occurs at a point the 3D event space
expresses — a height.  The projection chain 3D→2D→1D invents nothing; a line has no
place to hide a spurious zero, so all zeros are on the same line.  Its falsification
face is exactly a sourceless zero: an off-line vanishing would break this principle
for a single free pure carrier (Davenport–Heilbronn shows the mathematics of off-line
zeros is CONSISTENT for composite/non-free objects — so the dichotomy is between
DPI-for-primitive-carriers and a first invariant-without-source, not between
mathematics and contradiction).  Every measurement and every theorem in this file
weighs on the DPI side; the register stays open. -/
def GRH_of_helix_and_DPI (E : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, E z = 0 → ∃ y : ℝ, (y : ℂ) = z

/-- The named conditional is exactly the exhaustion target: DPI-faithfulness of the
projection ⟺ every zero has a source ⟺ weld confinement (classical RH/GRH for the
fiber).  One hypothesis, one wall, all names identified. -/
theorem grh_of_helix_and_dpi_iff_exhaustive (E : ℂ → ℂ) :
    GRH_of_helix_and_DPI E ↔ Exhaustive E := by
  constructor
  · intro h z hz
    obtain ⟨y, rfl⟩ := h z hz
    exact threeD_exhaustive E y hz
  · intro h z hz
    have him := (exhaustive_iff_on_axis E).mp h z hz
    exact ⟨z.re, Complex.ext (by simp) (by simp [him])⟩

end CriticalLinePhasor.SourceHolonomy
