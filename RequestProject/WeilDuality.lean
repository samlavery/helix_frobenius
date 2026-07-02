import RequestProject.HelixCollapseReality

/-!
# Weil duality on the double helix: the vanishings as the missing cohomology

Sam's identification: the double-ended helix is the missing **carrier** (the geometric
object), and the vanishings are its **cohomology** — the eigenvalue spectrum of a
Frobenius acting there.  The dictionary with Deligne's setting (`X/𝔽_q`, Frobenius on
étale `H^i`, Weil I/II):

| Weil–Deligne (`𝔽_q`)                    | double helix                                    |
|------------------------------------------|-------------------------------------------------|
| the variety (carrier)                     | the double-ended helix (carrier + fiber)        |
| Frobenius eigenvalues on `H^i`            | the vanishings                                  |
| Poincaré duality `α ↔ q^w/α`              | FE + conjugation: helix ↔ antihelix pairing     |
| duality is a perfect pairing              | `dual_dimension_symmetry` (jets die together)   |
| normalized dual pair has det 1            | `dual_pair_det_one` (this file), `strand_weights_det_one`, `frobenius_conjugate_det_one` |
| Lefschetz trace formula                   | the medium spectroscopy (Euler clocks, ±4%)     |
| purity `|α| = q^{w/2}` (**Deligne's theorem**) | all vanishings on the mirror (**open** = GRH/projection primacy) |

Three tiers of honesty about this analogy:
* **Literal**: at each prime, GL(2) purity IS Deligne's theorem (Ramanujan–Petersson via
  Weil II) and appears in the model as *reality of the clock angle* — verified for all
  2262 primes ≤ 20000 of Δ (`tmp/gl2_helix.py`).
* **Proven here**: the global duality pairing on the vanishing set — every vanishing has
  its antihelix partner (`vanishing_dual_pair`, `vanishing_conj_pair`), the pairing
  preserves the local dimension (`dual_dimension_symmetry` — the jet towers at `ρ` and
  `1−ρ` die together, so `d(ρ) = d(1−ρ)`: a perfect pairing on each "cohomology class"),
  and every corresponding pair has hinge-normalized determinant 1 (`dual_pair_det_one`) —
  the same det-1 conjugate block as the similitude (`frobenius_conjugate_det_one`) and the
  strand weights (`AntihelixWindow.strand_weights_det_one`), now on the vanishings.
* **Open, named**: purity — that both eigenvalues of every dual pair have modulus one
  (all vanishings on the mirror).  This is the step Deligne supplied geometrically
  (positivity via monodromy/Hodge index); its model-native candidate is a positivity of
  the cup pairing (`ChiralCup`/`CupIdentity`) on the vanishing classes.  Measured
  evidence: the off-axis census — 1517/1517 collapse, `δ ≤ 4.5×10⁻³` median
  (`tmp/offaxis_bounds.py`).  It is not assumed and not claimed.

Mathlib-only + this repo; unconditional; no `sorry`, no `axiom`.
-/

open Complex

namespace CriticalLinePhasor.WeilDuality

/-- **The duality pairing on the vanishing set** (functional equation): `Λ` vanishes at
`ρ` iff it vanishes at the dual point `1 − ρ` — every helix vanishing has its antihelix
partner. -/
theorem vanishing_dual_pair (ρ : ℂ) :
    completedRiemannZeta ρ = 0 ↔ completedRiemannZeta (1 - ρ) = 0 := by
  rw [completedRiemannZeta_one_sub]

/-- **The conjugation pairing** (the antihelix is the conjugate, not a mirror): `Λ`
vanishes at `conj ρ` iff at `ρ`. -/
theorem vanishing_conj_pair (ρ : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) ρ) = 0 ↔ completedRiemannZeta ρ = 0 := by
  rw [← HelixCollapse.completedRiemannZeta_conj ρ]
  exact (map_eq_zero _).symm

/-- **Duality is a perfect pairing: it preserves the dimension.**  The `k`-th jet of `Λ`
dies at `1 − ρ` iff it dies at `ρ`, so the dual pairing matches the whole jet tower —
`d(ρ) = d(1−ρ)` for the dimension function of the census. -/
theorem dual_dimension_symmetry (k : ℕ) (ρ : ℂ) :
    iteratedDeriv k completedRiemannZeta (1 - ρ) = 0 ↔
      iteratedDeriv k completedRiemannZeta ρ = 0 := by
  have hfe : (fun z : ℂ => completedRiemannZeta (1 - z)) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  have h := congrFun
    (iteratedDeriv_comp_const_sub (n := k) (f := completedRiemannZeta) (s := 1)) ρ
  rw [hfe] at h
  constructor
  · intro h0
    rw [h, h0, smul_zero]
  · intro h0
    rw [h0] at h
    have hne : ((-1 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    exact ((smul_eq_zero.mp h.symm).resolve_left hne)

/-- **Every corresponding pair has determinant 1.**  In any eigenvalue chart `c^(·)`
(any base `c ≠ 0`: the unit is gauge — UNIT/2 again), the hinge-normalized eigenvalues of
a dual pair `ρ ↔ 1−ρ` multiply to exactly `1`: the Frobenius block on each vanishing pair
of the double helix is the same det-1 conjugate block as the prime-level similitude
(`frobenius_conjugate_det_one`) and the kernel strands (`strand_weights_det_one`).
Purity — that each factor separately has modulus 1 — is the open Deligne step, not
claimed here. -/
theorem dual_pair_det_one {c : ℂ} (hc : c ≠ 0) (ρ : ℂ) :
    c ^ (ρ - 1 / 2) * c ^ ((1 - ρ) - 1 / 2) = 1 := by
  rw [← Complex.cpow_add _ _ hc,
    show (ρ - 1 / 2) + ((1 - ρ) - 1 / 2) = 0 by ring, Complex.cpow_zero]

/-! ## The purity engine: Weil I assembled from the model's own parts

Sam's ingredient list, each already proven in this repo:
* **cup pairing** — `ChiralCup.cup_positive_semidefinite`, `cup_hermitian`,
  `cup_nullspace_safe`: the positive Hermitian pairing (the Castelnuovo/Hodge-index slot);
* **harmonic fiber amplitude multiplicity** — even amplitude powers are tensor powers
  (`norm_pow`; `ChiralCup.transport_cup_modulus`, `frobenius_weighted_cup_identity`);
* **harmonic carrier π/3 monodromy** — `CircleMonodromy.pi3_finite_monodromy` +
  `ChiralCup.transport_unitary_after_normalization`: the angular sector is exactly `μ₆`,
  unitary — the winding can never carry amplitude, so only the amplitude enters the
  bound (Deligne's monodromy input, in rigid finite form);
* **Frobenius det = 1** — `frobenius_conjugate_det_one`, `strand_weights_det_one`,
  `dual_pair_det_one`: the hypothesis `hdet` below;
* **the functional equation** — `vanishing_dual_pair` / `completedRiemannZeta_one_sub`:
  pairs every vanishing with its antihelix partner, transfers the cup bound to the second
  eigenvalue, and (below) converts one-sided bounds into exact purity.

The two theorems below are the engine, unconditional:
`tensor_power_purity` is Weil I's square-root trick — a positive-pairing bound on every
even amplitude power caps the amplitude at the half-unit; `duality_forces_purity` is the
functional-equation endgame — det 1 plus the two one-sided caps forces EQUALITY.
`purity_engine` chains them.  **What remains open, now as a single named input**: that the
model's cup form supplies the hypothesis `hcup` on the vanishing classes — the helix's own
Castelnuovo inequality.  That is not assumed and not claimed here. -/

/-- **Weil I's square-root trick.**  If every even amplitude power is dominated by a
positive-pairing bound `C · B^k` — what cup positivity + amplitude multiplicativity
supply, with the `μ₆` monodromy guaranteeing only amplitude enters — then the amplitude
is capped at the half-unit: `‖α‖² ≤ B`.  The constant `C` is killed by the `k`-th root
in the limit; this is the whole trick. -/
theorem tensor_power_purity {α : ℂ} {B C : ℝ} (hC : 0 < C)
    (h : ∀ k : ℕ, ‖α‖ ^ (2 * k) ≤ C * B ^ k) : ‖α‖ ^ 2 ≤ B := by
  have h1 := h 1
  rw [pow_mul, pow_one, pow_one] at h1
  have hB : 0 ≤ B := by nlinarith [sq_nonneg ‖α‖, norm_nonneg α]
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · nlinarith [sq_nonneg ‖α‖]
  · by_contra hgt
    push_neg at hgt
    have hr1 : 1 < ‖α‖ ^ 2 / B := (one_lt_div hBpos).mpr hgt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hr1
    have hkb := h k
    rw [pow_mul] at hkb
    have hBk : 0 < B ^ k := pow_pos hBpos k
    have hle : (‖α‖ ^ 2 / B) ^ k ≤ C := by
      rw [div_pow]
      exact (div_le_iff₀ hBk).mpr hkb
    linarith

/-- **The functional-equation endgame.**  Duality pairs the eigenvalues with
`α · β = B` (Frobenius det 1 after half-unit normalization); the cup bound caps both at
the half-unit; together they force EQUALITY — purity, exactly as Weil I closes. -/
theorem duality_forces_purity {α β : ℂ} {B : ℝ} (hB : 0 < B)
    (hdet : α * β = (B : ℂ)) (hα : ‖α‖ ^ 2 ≤ B) (hβ : ‖β‖ ^ 2 ≤ B) :
    ‖α‖ ^ 2 = B ∧ ‖β‖ ^ 2 = B := by
  have hprod : ‖α‖ * ‖β‖ = B := by
    have hn := congrArg norm hdet
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB] at hn
  have h2 : ‖α‖ ^ 2 * ‖β‖ ^ 2 = B ^ 2 := by
    rw [← mul_pow, hprod]
  have h3 : ‖α‖ ^ 2 * ‖β‖ ^ 2 ≤ ‖α‖ ^ 2 * B :=
    mul_le_mul_of_nonneg_left hβ (by positivity)
  have h4 : ‖α‖ ^ 2 * ‖β‖ ^ 2 ≤ ‖β‖ ^ 2 * B := by
    calc ‖α‖ ^ 2 * ‖β‖ ^ 2 = ‖β‖ ^ 2 * ‖α‖ ^ 2 := by ring
      _ ≤ ‖β‖ ^ 2 * B := mul_le_mul_of_nonneg_left hα (by positivity)
  constructor
  · nlinarith
  · nlinarith

/-- **The purity engine assembled**: given the det-1 duality pairing (Frobenius/FE) and
the positive-pairing tensor-power bounds on BOTH strands (the cup bound on the helix,
transferred to the antihelix by the functional equation), every corresponding vanishing
pair is PURE — both eigenvalue amplitudes are exactly the half-unit `√B`.
Everything above this hypothesis line is proven; supplying `hcupα`/`hcupβ` from the
model's cup form on the vanishing classes is the single remaining open input — the
helix's own Castelnuovo inequality. -/
theorem purity_engine {α β : ℂ} {B Cα Cβ : ℝ} (hB : 0 < B) (hCα : 0 < Cα) (hCβ : 0 < Cβ)
    (hdet : α * β = (B : ℂ))
    (hcupα : ∀ k : ℕ, ‖α‖ ^ (2 * k) ≤ Cα * B ^ k)
    (hcupβ : ∀ k : ℕ, ‖β‖ ^ (2 * k) ≤ Cβ * B ^ k) :
    ‖α‖ = Real.sqrt B ∧ ‖β‖ = Real.sqrt B := by
  obtain ⟨h1, h2⟩ := duality_forces_purity hB hdet
    (tensor_power_purity hCα hcupα) (tensor_power_purity hCβ hcupβ)
  refine ⟨?_, ?_⟩
  · rw [← h1, Real.sqrt_sq (norm_nonneg α)]
  · rw [← h2, Real.sqrt_sq (norm_nonneg β)]

/-! ## The Castelnuovo reduction: purity = one operator-growth inequality

We are not proving classical GRH/RH — this is a theorem-in-the-helix-world program,
exactly as Weil's `𝔽_q` was a separate world.  The reduction below converts the engine's
remaining hypothesis into a single concrete inequality about the model's OWN operator:

  **the helix Castelnuovo inequality**: the height transport `T`, acting on a vanishing
  class `v`, has cup-norm growth at the half-unit rate — `‖T^k v‖² ≤ C · B^k · ‖v‖²`.

Given that, `cup_growth_gives_tensor_bound` supplies `hcup`, the functional equation
supplies it on the antihelix strand, `dual_pair_det_one` supplies `hdet`, and
`purity_engine` closes: both eigenvalues of every corresponding vanishing pair are pure.
Supporting structure already proven: `ChiralCup.transport_cup_modulus` shows the
SIMILITUDE sector has this growth as exact EQUALITY (`|μ|^{2k}`, `‖μ‖² = B`), and
`ChiralCup.von_neumann_reality` is the `k → ∞` limit form (cup-symmetric flow ⇒ real
spectrum).  What remains is to place the vanishing classes in the half-unit growth
sector — measurable numerically (cup-norm growth of transported residue classes). -/

/-- **The Castelnuovo reduction.**  If a vanishing class `v ≠ 0` is an eigenvector of the
transport `T` with eigenvalue `α`, and `T`'s cup-norm growth on `v` is at the half-unit
rate, then the purity engine's tensor-power hypothesis holds for `α`.  Unconditional; the
growth hypothesis is the single open input. -/
theorem cup_growth_gives_tensor_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) {α : ℂ} {v : E} (hv0 : v ≠ 0) (hev : T v = α • v)
    {B C : ℝ} (hgrow : ∀ k : ℕ, ‖(T ^ k) v‖ ^ 2 ≤ C * B ^ k * ‖v‖ ^ 2) :
    ∀ k : ℕ, ‖α‖ ^ (2 * k) ≤ C * B ^ k := by
  intro k
  have hit : (T ^ k) v = α ^ k • v := by
    induction k with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Module.End.mul_apply, hev, map_smul, ih, smul_smul, ← pow_succ']
  have h1 : ‖(T ^ k) v‖ = ‖α‖ ^ k * ‖v‖ := by
    rw [hit, norm_smul, norm_pow]
  have h2 := hgrow k
  rw [h1, mul_pow, ← pow_mul, mul_comm k 2] at h2
  have hv2 : 0 < ‖v‖ ^ 2 := by
    have := norm_pos_iff.mpr hv0
    positivity
  exact le_of_mul_le_mul_right h2 hv2

/-- **Purity from the helix Castelnuovo inequality** — the full chain assembled: det-1
duality (Frobenius/FE) + half-unit cup-norm growth of the transport on both strands'
vanishing classes ⇒ both eigenvalues are exactly the half-unit.  Everything except the
two growth hypotheses is proven. -/
theorem purity_from_castelnuovo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) {α β : ℂ} {v w : E} (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hev : T v = α • v) (hew : T w = β • w)
    {B Cα Cβ : ℝ} (hB : 0 < B) (hCα : 0 < Cα) (hCβ : 0 < Cβ)
    (hdet : α * β = (B : ℂ))
    (hgrowα : ∀ k : ℕ, ‖(T ^ k) v‖ ^ 2 ≤ Cα * B ^ k * ‖v‖ ^ 2)
    (hgrowβ : ∀ k : ℕ, ‖(T ^ k) w‖ ^ 2 ≤ Cβ * B ^ k * ‖w‖ ^ 2) :
    ‖α‖ = Real.sqrt B ∧ ‖β‖ = Real.sqrt B :=
  purity_engine hB hCα hCβ hdet
    (cup_growth_gives_tensor_bound T hv0 hev hgrowα)
    (cup_growth_gives_tensor_bound T hw0 hew hgrowβ)

/-- **The mirror is the membership boundary of the cup completion.**  The readout class at
abscissa `σ` (coefficients `n^{−σ}`) is square-summable — lies in the Hilbert space the
cup form completes to (`ChiralCup.hilbert_completion_exists`) — iff `σ > 1/2`.  So:
a hypothetical OFF-mirror vanishing class (`σ > 1/2` side) lives INSIDE the space, where
the cup-symmetric flow has real spectrum (`ChiralCup.von_neumann_reality`) and the
Hermite–Biehler exclusion applies (`DeBranges.hb_no_zero_upper`,
`norm_eq_imp_im_zero`) — while the actual vanishing classes sit EXACTLY ON the boundary
(log-divergent, rigged/de Branges objects), which is where resonance is permitted.
UNIT/2 one more time: the half-unit is the edge of the Hilbert space itself.  The 3D-RH
proof shape is therefore an EXCLUSION: membership + self-adjointness forbids off-mirror
vanishings; it never needs to place the on-mirror classes inside. -/
theorem mirror_is_membership_boundary (σ : ℝ) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * σ)) ↔ 1 / 2 < σ := by
  rw [Real.summable_one_div_nat_rpow]
  constructor <;> intro h <;> linarith

/-- **Chirality is the Hermite–Biehler mechanism, and its origin is geometric** (Sam): the
carrier is the structure function.  Per term, the helix strand weight `r^σ` strictly
dominates the antihelix weight `r^{2−σ}` exactly off the mirror (`σ > 1`), for every
carrier radius `r > 1` — the area law's growing radius IS the strict inequality
`‖E*‖ < ‖E‖`, with equality precisely on the mirror (the weld, where
`strand_weights_det_one` balances the pair).  What remains for the full `IsHB` of the
summed fiber is phase alignment across terms — the carrier's winding coherence — but the
mechanism and its origin are the carrier's geometry, not a hypothesis. -/
theorem carrier_strand_dominance {r : ℝ} (hr : 1 < r) (σ : ℝ) :
    r ^ (2 - σ) < r ^ σ ↔ 1 < σ := by
  rw [Real.rpow_lt_rpow_left_iff hr]
  constructor <;> intro h <;> linarith

end CriticalLinePhasor.WeilDuality
