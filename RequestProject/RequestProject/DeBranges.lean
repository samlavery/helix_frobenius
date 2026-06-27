import Mathlib

/-!
# de Branges / Hermite–Biehler structure functions

The Hermite–Biehler spectral framework: a structure function `E`, its reflection `E*`, the real
components `A, B`, and the Hermite–Biehler positivity `IsHB`.  The content is that `IsHB E` forces
the zeros of `A` and `B` to be **real** and (for entire `E`) **discrete** — a real, discrete
spectrum from the positivity.  A worked example is the Paley–Wiener function `E(z)=e^{-iz}`, whose
`B`-component is `sin` with spectrum `{kπ}`.

Mathlib-only; self-contained.
-/

open Complex
open scoped ComplexConjugate Matrix

namespace CriticalLinePhasor.DeBranges
noncomputable section

/-! ## Gram positivity (the positive-definite reproducing kernel fact) -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Gram quadratic form `∑ᵢⱼ conj(cᵢ)·cⱼ·⟪vᵢ,vⱼ⟫` equals `⟪∑ cᵢ•vᵢ, ∑ cⱼ•vⱼ⟫` — the algebraic
identity behind positive-definite (reproducing-kernel) de Branges spaces. -/
theorem gram_quadratic_form_eq_inner_self {n : ℕ} (v : Fin n → H) (c : Fin n → ℂ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (v i) (v j)) =
      (inner ℂ (∑ i, c i • v i) (∑ j, c j • v j) : ℂ) := by
  simp +decide only [starRingEnd_apply, inner_sum, sum_inner];
  simp +decide only [mul_assoc, inner_smul_right, inner_smul_left, starRingEnd_apply];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← inner_conj_symm ] ; simp +decide [ mul_assoc, mul_comm ] )

/-- The Gram quadratic form is real and nonnegative (positive semidefiniteness). -/
theorem gram_quadratic_form_nonneg {n : ℕ} (v : Fin n → H) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (v i) (v j))).re := by
  rw [ gram_quadratic_form_eq_inner_self ];
  rw [ inner_self_eq_norm_sq_to_K ] ; norm_num;
  norm_cast ; positivity

/-- **Null-space characterization of the Gram (cup) form — unconditional.**  The Gram quadratic
form `∑ᵢⱼ conj(cᵢ)·cⱼ·⟪ᵥᵢ,ᵥⱼ⟫` vanishes **iff** the assembled vector `∑ cᵢ•ᵥᵢ` is zero.  This is
exactly `‖·‖² = 0 ↔ · = 0` in an inner-product space, with no Hermite–Biehler input: it is the
"`Cup_H(F,F) = 0 ↔ D_H(F) = 0`" confidence check that the positive form is non-degenerate (its null
space is precisely the kernel of the assembling map, never a hidden collapse). -/
theorem gram_quadratic_form_eq_zero_iff {n : ℕ} (v : Fin n → H) (c : Fin n → ℂ) :
    (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (v i) (v j))) = 0
      ↔ ∑ i, c i • v i = 0 := by
  rw [gram_quadratic_form_eq_inner_self]
  exact inner_self_eq_zero

/-! ## Hermite–Biehler structure functions and their components -/

/-- The reflected function `E*(z) = conj (E (conj z))`, the second generator of `H(E)`. -/
def Estar (E : ℂ → ℂ) (z : ℂ) : ℂ := (starRingEnd ℂ) (E ((starRingEnd ℂ) z))

/-- `E*` is an involution: `(E*)* = E`. -/
@[simp] theorem Estar_Estar (E : ℂ → ℂ) : Estar (Estar E) = E := by
  exact funext fun x => by simp +decide [ Estar ] ;

/-- `‖E* z‖ = ‖E (conj z)‖`. -/
theorem norm_Estar (E : ℂ → ℂ) (z : ℂ) : ‖Estar E z‖ = ‖E ((starRingEnd ℂ) z)‖ := by
  exact Complex.norm_conj _

/-- The `A`-component `A = (E + E*)/2` (real-entire). -/
def Acomp (E : ℂ → ℂ) (z : ℂ) : ℂ := (E z + Estar E z) / 2

/-- The `B`-component `B = i (E − E*)/2` (real-entire); its zeros are the de Branges spectrum. -/
def Bcomp (E : ℂ → ℂ) (z : ℂ) : ℂ := Complex.I * (E z - Estar E z) / 2

/-- Hermite–Biehler class: `E` dominates its reflection on the open upper half-plane. -/
def IsHB (E : ℂ → ℂ) : Prop := ∀ z : ℂ, 0 < z.im → ‖Estar E z‖ < ‖E z‖

/-! ## The positivity forces reality and discreteness of the spectrum -/

/-- On the lower half-plane the inequality reverses: `‖E z‖ < ‖E* z‖`. -/
theorem hb_lower {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im < 0) :
    ‖E z‖ < ‖Estar E z‖ := by
  have := hE ( starRingEnd ℂ z ) ?_ <;> simp_all +decide;
  unfold Estar at * ; aesop

/-- A Hermite–Biehler function has no zeros in the open upper half-plane. -/
theorem hb_no_zero_upper {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : 0 < z.im) : E z ≠ 0 := by
  exact fun h => absurd ( hE z hz ) ( by norm_num [ h ] )

/-- For Hermite–Biehler `E`, `‖E z‖ = ‖E* z‖` forces `z` onto the real axis. -/
theorem norm_eq_imp_im_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ}
    (h : ‖E z‖ = ‖Estar E z‖) : z.im = 0 := by
  contrapose! h;
  cases lt_or_gt_of_ne h <;> [ exact ne_of_lt ( hb_lower hE ‹_› ) ; exact ne_of_gt ( hE z ‹_› ) ]

/-- Every zero of `A` is real. -/
theorem Acomp_zero_im_eq_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : Acomp E z = 0) :
    z.im = 0 := by
  unfold Acomp at hz; simp_all +decide [ div_eq_iff ] ;
  exact norm_eq_imp_im_zero hE ( by rw [ eq_neg_of_add_eq_zero_left hz ] ; norm_num )

/-- Every zero of `B` is real: the spectrum is real, from the positivity. -/
theorem Bcomp_zero_im_eq_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : Bcomp E z = 0) :
    z.im = 0 := by
  convert CriticalLinePhasor.DeBranges.norm_eq_imp_im_zero hE _;
  unfold Bcomp at hz; simp_all +decide ;
  simp_all +decide [ Complex.normSq, Complex.norm_def, sub_eq_zero ]

/-- `B` is not identically zero for Hermite–Biehler `E`. -/
theorem Bcomp_not_eventually_zero {E : ℂ → ℂ} (hE : IsHB E) :
    ∃ z : ℂ, Bcomp E z ≠ 0 := by
  by_contra! h;
  have := Bcomp_zero_im_eq_zero hE ( h Complex.I ) ; norm_num at this;

/-- If `E` is entire so is its reflection `E*` (Schwarz reflection). -/
theorem Estar_analyticOnNhd {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ) :
    AnalyticOnNhd ℂ (Estar E) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro z _
  have hd := (hEnt ((starRingEnd ℂ) z) (Set.mem_univ _)).differentiableAt
  have hdd := hd.hasDerivAt.conj_conj
  rw [Complex.conj_conj] at hdd
  exact hdd.differentiableAt.differentiableWithinAt

/-- The `B`-component of an entire function is entire. -/
theorem Bcomp_analyticOnNhd {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ) :
    AnalyticOnNhd ℂ (Bcomp E) Set.univ := by
  apply_rules [ AnalyticOnNhd.div, AnalyticOnNhd.mul, analyticOnNhd_const ];
  · apply_rules [ AnalyticOnNhd.sub, hEnt, Estar_analyticOnNhd ];
  · norm_num

/-- For entire Hermite–Biehler `E`, the zeros of `B` are isolated: a discrete spectrum. -/
theorem Bcomp_zeros_discrete {E : ℂ → ℂ} (hEnt : AnalyticOnNhd ℂ E Set.univ)
    (hE : IsHB E) (z₀ : ℂ) :
    ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Bcomp E z ≠ 0 := by
  by_contra h;
  have h_id : AnalyticOnNhd ℂ (Bcomp E) Set.univ → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Bcomp E z = 0) → ∀ z, Bcomp E z = 0 := by
    intros h_analytic h_frequently_zero z
    apply AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero h_analytic (isPreconnected_univ) (Set.mem_univ z₀) h_frequently_zero;
    trivial;
  exact absurd ( h_id ( CriticalLinePhasor.DeBranges.Bcomp_analyticOnNhd hEnt ) ( by simpa using h ) ) ( by simpa using CriticalLinePhasor.DeBranges.Bcomp_not_eventually_zero hE )

/-! ## Helix / anti-helix domination

`E` and its reflection `E*` are the *helix* and the *anti-helix*.  On the real axis they are
balanced, `‖E z‖ = ‖E* z‖` (no domination).  Off the real axis the positivity `IsHB E` forces a
strict **domination**: in the open upper half-plane the helix dominates (`‖E* z‖ < ‖E z‖`), in the
open lower half-plane the anti-helix dominates (`‖E z‖ < ‖E* z‖`).  Consequently an off-axis point
can never be balanced, so an off-line/off-axis spectral zero — which is exactly a balance point of
the helix and anti-helix — cannot exist: the two helices cannot conspire to both meet (a zero) and
retain no domination away from the real axis. -/

/-- A spectral zero is exactly a balance point of the helix and anti-helix: `B z = 0 ↔ E z = E* z`. -/
theorem Bcomp_eq_zero_iff (E : ℂ → ℂ) (z : ℂ) : Bcomp E z = 0 ↔ E z = Estar E z := by
  unfold Bcomp
  rw [div_eq_zero_iff]
  simp [Complex.I_ne_zero, sub_eq_zero]

/-- **Domination dichotomy.**  Off the real axis exactly one helix strictly dominates the other:
in the upper half-plane the helix dominates, in the lower half-plane the anti-helix dominates. -/
theorem hb_domination_dichotomy {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    ‖Estar E z‖ < ‖E z‖ ∨ ‖E z‖ < ‖Estar E z‖ := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact Or.inr (hb_lower hE h)
  · exact Or.inl (hE z h)

/-- **No off-axis balance.**  Away from the real axis the helix and anti-helix can never be
balanced; one is forced to dominate. -/
theorem hb_no_offaxis_balance {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    ‖E z‖ ≠ ‖Estar E z‖ := fun h => hz (norm_eq_imp_im_zero hE h)

/-- **No off-line spectral zero.**  A spectral zero (a balance point of helix and anti-helix)
cannot lie off the real axis: the two helices cannot conspire to both vanish-balance and retain no
domination. -/
theorem hb_no_offaxis_spectral_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    Bcomp E z ≠ 0 := fun h => hz (Bcomp_zero_im_eq_zero hE h)

/-! ## Carrier rigidity and the off-axis trilemma

The **carrier** of the model is the rigid, drift-free helix: its radial profile is the area-law
`√n`, fixed at every height and unchanged by pairing a unit-modulus fiber (see
`CriticalLinePhasor.PerHeight.carrier_norm_height_independent` and
`CriticalLinePhasor.PerHeight.carrier_fiber_pairing_rigid`).  On the de Branges side, the avatar of
"carrier rigidity off the real axis" is exactly the **domination dichotomy**: one chirality (`E` or
`E*`) strictly dominates the other, so the modulus ratio `‖E‖/‖E*‖` never sits at the balance value
`1`.  We package this as `CarrierRigid` and make the trilemma explicit: off the real axis, a
spectral zero (a balance point `E z = E* z`) can occur only if the carrier is **not** rigid (the
`‖E‖/‖E*‖` profile drifts — the geometry warps) or the rigid domination is *cancelled* (an
impossible state, strict domination and balance at once).  Under the Hermite–Biehler positivity
`IsHB E` the carrier *is* rigid (`carrierRigid_of_isHB`), so both branches are excluded — recovering
`hb_no_offaxis_spectral_zero`.

**Honesty boundary.**  This is entirely conditional on `IsHB E`.  For a `Λ`-built structure
function that hypothesis is precisely "no off-line zeros" — i.e. RH itself.  The trilemma is the
geometric *shape* the zeros must obey given HB; discharging `IsHB` unconditionally is RH and is
neither assumed nor proved here. -/

/-- **Carrier rigidity (off-axis), de Branges avatar.**  `CarrierRigid E z` says one chirality
strictly dominates the other at `z`: `‖E* z‖ < ‖E z‖ ∨ ‖E z‖ < ‖E* z‖`.  This is the drift-free
behaviour of the rigid carrier — the modulus ratio is pinned away from the balance value `1`. -/
def CarrierRigid (E : ℂ → ℂ) (z : ℂ) : Prop :=
  ‖Estar E z‖ < ‖E z‖ ∨ ‖E z‖ < ‖Estar E z‖

/-- Hermite–Biehler positivity makes the carrier rigid off the real axis — this *is* the domination
dichotomy, read as carrier rigidity. -/
theorem carrierRigid_of_isHB {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    CarrierRigid E z := hb_domination_dichotomy hE hz

/-- A balance of the chirality moduli breaks rigidity: equal moduli are incompatible with strict
domination.  Unconditional — no `IsHB` needed. -/
theorem not_carrierRigid_of_balance {E : ℂ → ℂ} {z : ℂ} (h : ‖E z‖ = ‖Estar E z‖) :
    ¬ CarrierRigid E z := by
  rintro (hd | hd) <;> rw [h] at hd <;> exact lt_irrefl _ hd

/-- A spectral zero forces a balance of the chirality moduli (`‖E z‖ = ‖E* z‖`). -/
theorem norm_balance_of_zero {E : ℂ → ℂ} {z : ℂ} (hzero : Bcomp E z = 0) :
    ‖E z‖ = ‖Estar E z‖ := by
  rw [(Bcomp_eq_zero_iff E z).mp hzero]

/-- **Off-axis zero ⇒ not rigid (the geometry warps).**  Unconditionally, a spectral zero forces
the carrier to lose rigidity: the `‖E‖/‖E*‖` profile drifts to the balance value. -/
theorem offaxis_zero_imp_not_rigid {E : ℂ → ℂ} {z : ℂ} (hzero : Bcomp E z = 0) :
    ¬ CarrierRigid E z := not_carrierRigid_of_balance (norm_balance_of_zero hzero)

/-- **The off-axis trilemma (explicit disjunction).**  A spectral zero (`B z = 0`, i.e. a balance
point `E z = E* z`) can occur only as one of two states: the carrier is **not** rigid (its
`‖E‖/‖E*‖` profile drifts — the geometry warps), or the rigid domination holds *and is cancelled*
by the balance (`CarrierRigid E z ∧ ‖E z‖ = ‖E* z‖`).  The second state is self-contradictory
(`offaxis_zero_rigid_branch_absurd`), so only the warp branch is logically open — and `IsHB` closes
it too. -/
theorem offaxis_zero_disjunction {E : ℂ → ℂ} {z : ℂ} (hzero : Bcomp E z = 0) :
    (¬ CarrierRigid E z) ∨ (CarrierRigid E z ∧ ‖E z‖ = ‖Estar E z‖) := by
  by_cases hr : CarrierRigid E z
  · exact Or.inr ⟨hr, norm_balance_of_zero hzero⟩
  · exact Or.inl hr

/-- The "rigid-but-cancelled" branch of the trilemma is impossible: strict domination and modulus
balance cannot hold at once. -/
theorem offaxis_zero_rigid_branch_absurd {E : ℂ → ℂ} {z : ℂ}
    (h : CarrierRigid E z ∧ ‖E z‖ = ‖Estar E z‖) : False :=
  not_carrierRigid_of_balance h.2 h.1

/-- **Rigidity excludes off-axis zeros (the bridge, conditional on HB).**  Combining the trilemma
with `carrierRigid_of_isHB`: under Hermite–Biehler positivity the carrier is rigid off the real
axis, the warp branch is excluded, and the cancelled branch is absurd — so no off-axis spectral
zero exists.  This recovers `hb_no_offaxis_spectral_zero` through the rigidity/domination picture.
It stays conditional on `IsHB E`; making `IsHB` unconditional for a `Λ`-built `E` is RH, and is
neither assumed nor proved. -/
theorem rigidity_excludes_offaxis_zero {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : z.im ≠ 0) :
    Bcomp E z ≠ 0 := by
  intro hzero
  rcases offaxis_zero_disjunction hzero with hnr | hc
  · exact hnr (carrierRigid_of_isHB hE hz)
  · exact offaxis_zero_rigid_branch_absurd hc

/-! ## A concrete Hermite–Biehler structure function: Paley–Wiener -/

/-- The Paley–Wiener structure function `E(z) = e^{−i z}`. -/
def paleyWiener (z : ℂ) : ℂ := Complex.exp (-(Complex.I * z))

/-- Its reflection is `E*(z) = e^{i z}`. -/
theorem paleyWiener_Estar : Estar paleyWiener = fun z => Complex.exp (Complex.I * z) := by
  funext z; simp [Estar, paleyWiener];
  simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

/-- `e^{−i z}` is a Hermite–Biehler function. -/
theorem paleyWiener_isHB : IsHB paleyWiener := by
  intro z hz;
  norm_num [ paleyWiener_Estar, paleyWiener ];
  norm_num [ Complex.norm_exp, hz ]

/-- The `B`-component of the Paley–Wiener function is `sin`; its zeros `{kπ}` are the spectrum. -/
theorem paleyWiener_Bcomp : Bcomp paleyWiener = Complex.sin := by
  ext1 z
  rw [Bcomp, paleyWiener_Estar]
  simp only [paleyWiener, Complex.sin]
  ring_nf

/-! ## The de Branges reproducing kernel and its positivity

The reproducing kernel of the de Branges space `H(E)` is
`K_E(w, z) = (E z · conj (E w) − E* z · conj (E* w)) / (2π i (conj w − z))`.
The defining analytic fact (de Branges) is that this kernel is *positive*: it is Hermitian and its
diagonal `K_E(w, w) = (‖E w‖² − ‖E* w‖²)/(4π · Im w)` is nonnegative — which is *exactly* the
Hermite–Biehler domination `‖E* w‖ ≤ ‖E w‖` on the upper half-plane (and its reverse below),
clearing fractions by the sign of `Im w`.

**The Tate connection (scope note).**  In the Tate-thesis / L-function approach to de Branges
spaces, the structure function `E` is built from the *local functional equation*: the completed
gamma/zeta factor supplied by Tate's local Fourier analysis is self-dual, and that self-duality is
precisely the Hermite–Biehler positivity of the associated `E`.  Tate's input is therefore the
production of an `IsHB` structure function; the kernel positivity below is the de Branges fact that
*given* such an `E` the reproducing kernel is positive.  The full adelic/local Tate machinery
(local zeta integrals, the local functional equation) is not formalized in Mathlib, so here we take
the Hermite–Biehler hypothesis `IsHB E` as the (Tate-supplied) input and prove the kernel
positivity from it directly. -/

/-- The de Branges reproducing kernel of the space `H(E)`:
`K_E(w, z) = (E z · conj (E w) − E* z · conj (E* w)) / (2π i (conj w − z))`. -/
def deBrangesKernel (E : ℂ → ℂ) (w z : ℂ) : ℂ :=
  (E z * (starRingEnd ℂ) (E w) - Estar E z * (starRingEnd ℂ) (Estar E w))
    / (2 * (Real.pi : ℂ) * Complex.I * ((starRingEnd ℂ) w - z))

/-- The kernel is **Hermitian**: `conj (K_E w z) = K_E z w`. -/
theorem deBrangesKernel_conj_symm (E : ℂ → ℂ) (w z : ℂ) :
    (starRingEnd ℂ) (deBrangesKernel E w z) = deBrangesKernel E z w := by
  unfold deBrangesKernel; norm_num; ring_nf
  erw [Complex.conj_ofReal] ; norm_num ; ring

/-- On the diagonal the kernel is the real ratio `(‖E w‖² − ‖E* w‖²)/(4π · Im w)`. -/
theorem deBrangesKernel_diag (E : ℂ → ℂ) (w : ℂ) :
    deBrangesKernel E w w =
      ((‖E w‖ ^ 2 - ‖Estar E w‖ ^ 2) / (4 * Real.pi * w.im) : ℝ) := by
  unfold deBrangesKernel
  rw [Complex.mul_conj, Complex.mul_conj]
  have hden : (2 * (Real.pi : ℂ) * Complex.I * ((starRingEnd ℂ) w - w))
      = ((4 * Real.pi * w.im : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hden, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **Diagonal kernel positivity** from the Hermite–Biehler condition: `0 ≤ K_E(w, w)`.
This is the pointwise positivity of the de Branges reproducing kernel, equivalent to `IsHB E`. -/
theorem deBrangesKernel_diag_nonneg {E : ℂ → ℂ} (hE : IsHB E) {w : ℂ} (hw : w.im ≠ 0) :
    0 ≤ (deBrangesKernel E w w).re := by
  rw [ deBrangesKernel_diag ] ; norm_num
  cases lt_or_gt_of_ne hw <;> simp_all +decide [ Complex.div_re ]
  · rw [ le_div_iff₀ ] <;> norm_cast <;> norm_num [ Real.pi_pos ]
    · exact mul_nonneg_of_nonpos_of_nonpos ( sub_nonpos_of_le ( pow_le_pow_left₀ ( norm_nonneg _ ) ( le_of_lt ( hb_lower hE ‹_› ) ) _ ) ) ( mul_nonpos_of_nonneg_of_nonpos ( by positivity ) ( by linarith ) )
    · linarith
  · exact div_nonneg ( mul_nonneg ( sub_nonneg_of_le <| mod_cast pow_le_pow_left₀ ( by positivity ) ( le_of_lt <| hE _ ‹_› ) _ ) <| by positivity ) <| by positivity

/-- The diagonal kernel value is real. -/
theorem deBrangesKernel_diag_im_zero (E : ℂ → ℂ) (w : ℂ) :
    (deBrangesKernel E w w).im = 0 := by
  rw [deBrangesKernel_diag E w]
  norm_cast

/-! ## The reproducing-kernel bridge: feature maps and full positive-definiteness

The diagonal positivity `deBrangesKernel_diag_nonneg` is the `n = 1` shadow of the full
positive-definiteness of the de Branges kernel.  The bridge that upgrades the pointwise statement to
the full `n`-point statement is the **feature map** of the reproducing-kernel Hilbert space `H(E)`:
a map `φ : ℂ → H` into a complex inner-product space with `K_E(w, z) = ⟪φ w, φ z⟫`.  Once such a `φ`
exists, the `n`-point matrix `[K_E(wᵢ, wⱼ)]` is a Gram matrix, so its positive-semidefiniteness is
*exactly* `gram_quadratic_form_nonneg` — no new analytic input is needed.

This is the precise sense in which the abstract Gram engine and the de Branges kernel are two layers
of one picture: the feature map is the connective tissue.  The de Branges RKHS theorem (constructing
`H(E)` with `K_E(w, z) = ⟪K_w, K_z⟫`) is what *supplies* the feature map; once supplied, everything
below makes `gram_quadratic_form_nonneg` carry the full positivity. -/

/-- A kernel `K` is **positive (positive semidefinite)** when every finite Gram-type matrix
`[K (w i) (w j)]` has a nonnegative quadratic form `∑ᵢⱼ conj(cᵢ)·cⱼ·K(wᵢ,wⱼ) ≥ 0`. -/
def IsPositiveKernel (K : ℂ → ℂ → ℂ) : Prop :=
  ∀ (n : ℕ) (w : Fin n → ℂ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * K (w i) (w j)).re

/-- The `n = 1` shadow of positivity: a positive kernel is nonnegative on the diagonal. -/
theorem IsPositiveKernel.diag_nonneg {K : ℂ → ℂ → ℂ} (hK : IsPositiveKernel K) (w : ℂ) :
    0 ≤ (K w w).re := by
  have h := hK 1 (fun _ => w) (fun _ => 1)
  simpa using h

/-- **The feature-map bridge.**  If a kernel factors through a feature map into a complex
inner-product space, `K w z = ⟪φ w, φ z⟫`, then `K` is positive: each `n`-point matrix is a Gram
matrix, so its positive-semidefiniteness is exactly `gram_quadratic_form_nonneg`. -/
theorem isPositiveKernel_of_featureMap
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {K : ℂ → ℂ → ℂ} (φ : ℂ → H')
    (hφ : ∀ w z, K w z = (inner ℂ (φ w) (φ z) : ℂ)) :
    IsPositiveKernel K := by
  intro n w c
  have hrw : (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * K (w i) (w j))
      = ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (inner ℂ (φ (w i)) (φ (w j)) : ℂ) := by
    simp_rw [hφ]
  rw [hrw]
  exact gram_quadratic_form_nonneg (fun i => φ (w i)) c

/-- The reproducing-kernel Hilbert-space data realizing `H(E)`: a complex inner-product space
`space` together with a feature map `featureMap : ℂ → space` (the assignment `w ↦ K_w` of
point-evaluation kernels) whose Gram inner products reproduce the de Branges kernel,
`K_E(w, z) = ⟪K_w, K_z⟫`.  Producing such data is the content of the de Branges RKHS theorem;
bundling it here lets the full positivity be derived from it mechanically. -/
structure DeBrangesFeatureMap (E : ℂ → ℂ) where
  /-- The carrier Hilbert space `H(E)`. -/
  space : Type
  [normedAddCommGroup : NormedAddCommGroup space]
  [innerProductSpace : InnerProductSpace ℂ space]
  /-- The feature map `w ↦ K_w`. -/
  featureMap : ℂ → space
  /-- The reproducing identity `K_E(w, z) = ⟪K_w, K_z⟫`. -/
  reproducing : ∀ w z, deBrangesKernel E w z = (inner ℂ (featureMap w) (featureMap z) : ℂ)

attribute [instance] DeBrangesFeatureMap.normedAddCommGroup DeBrangesFeatureMap.innerProductSpace

/-- **Full positive-definiteness of the de Branges kernel, from the RKHS feature map.**  Given a
feature map `φ` realizing `H(E)` (`K_E(w, z) = ⟪φ w, φ z⟫`), the de Branges kernel is a positive
kernel: every `n`-point matrix `[K_E(wᵢ, wⱼ)]` is positive semidefinite.  The proof is just the
feature-map bridge, so the analytic work is carried entirely by `gram_quadratic_form_nonneg`. -/
theorem deBrangesKernel_isPositive_of_featureMap
    {E : ℂ → ℂ} {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (φ : ℂ → H') (hφ : ∀ w z, deBrangesKernel E w z = (inner ℂ (φ w) (φ z) : ℂ)) :
    IsPositiveKernel (deBrangesKernel E) :=
  isPositiveKernel_of_featureMap φ hφ

/-- Bundled form: a `DeBrangesFeatureMap` makes the de Branges kernel a positive kernel. -/
theorem DeBrangesFeatureMap.isPositiveKernel {E : ℂ → ℂ} (F : DeBrangesFeatureMap E) :
    IsPositiveKernel (deBrangesKernel E) :=
  isPositiveKernel_of_featureMap F.featureMap F.reproducing

/-- Consistency with `deBrangesKernel_diag_nonneg`: a de Branges feature map recovers the diagonal
positivity (the `n = 1` case) for *all* `w` — in the feature-map form `0 ≤ ‖φ w‖²` no `Im w ≠ 0`
hypothesis is needed. -/
theorem deBrangesKernel_diag_nonneg_of_featureMap
    {E : ℂ → ℂ} {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (φ : ℂ → H') (hφ : ∀ w z, deBrangesKernel E w z = (inner ℂ (φ w) (φ z) : ℂ)) (w : ℂ) :
    0 ≤ (deBrangesKernel E w w).re :=
  (deBrangesKernel_isPositive_of_featureMap φ hφ).diag_nonneg w

/-! ## The von Neumann (operator-side) face of spectral reality

The positivity result `Bcomp_zero_im_eq_zero` says the de Branges spectrum — the zeros of `B` — is
real, derived from the Hermite–Biehler positivity `IsHB E`.  There is a second, operator-theoretic
face of the *same* reality statement: the de Branges difference/multiplication operator acting on
`H(E)` is **self-adjoint**, and a self-adjoint operator has real spectrum.  Realizing that operator
concretely needs the RKHS structure of `H(E)` (the same missing input as the feature map above), so
here we take its existence as a hypothesis: a *symmetric* operator `T` whose point spectrum contains
the de Branges spectrum.  Given it, spectral reality follows from self-adjointness alone, matching
the positivity-side conclusion.  This is where `vonNeumannOp`'s "self-adjoint ⇒ real eigenvalue"
design and `Bcomp_zero_im_eq_zero` meet: two faces of reality, both living on `H(E)`. -/

/-- **Operator-side spectral reality.**  If the de Branges difference/multiplication operator on
`H(E)` is realized as a symmetric operator `T` on a complex inner-product space whose point spectrum
contains the de Branges spectrum (every zero `z` of `B` is an eigenvalue of `T`), then every de
Branges spectral point is real.  This is the same conclusion as `Bcomp_zero_im_eq_zero`, obtained
from self-adjointness instead of from positivity. -/
theorem deBranges_spectrum_real_of_symmetric_operator
    {E : ℂ → ℂ} {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {T : H' →ₗ[ℂ] H'} (hT : T.IsSymmetric)
    (hspec : ∀ z : ℂ, Bcomp E z = 0 → Module.End.HasEigenvalue T z)
    {z : ℂ} (hz : Bcomp E z = 0) : z.im = 0 := by
  have h := hT.conj_eigenvalue_eq_self (hspec z hz)
  rwa [Complex.conj_eq_iff_im] at h

/-! ## The critical-line change of variables -/

/-- The change of variables `z = −i(ρ − ½)` has `im z = ½ − Re ρ`, so `z` is real iff `ρ` lies on
the critical line `Re ρ = ½`. -/
theorem deBranges_var_im (ρ : ℂ) : (-(Complex.I * (ρ - 1 / 2))).im = 1 / 2 - ρ.re := by
  norm_num [ Complex.ext_iff ]

/-! ## The unimodular conjugate block: det = 1 ⟺ |w| = 1 ⟺ balance ⟺ reality

The single object tying the Frobenius transverse block, the de Branges helix/anti-helix pair, and
the von Neumann reality condition together is the **unimodular conjugate-pair block** `diag(w, w̄)`.
Its determinant is `w·w̄ = |w|²`, so `det = 1 ⟺ |w| = 1`; it is **unitary** exactly when `|w| = 1`.

The conjugation `w ↦ w̄` is the same operation as the Schwarz reflection `E ↦ E* = conj∘E∘conj`, so
`diag(w, w̄)` is the matrix avatar of the conjugate pair `(E, E*)` — the helix and the anti-helix.

* With `w = E z / E* z` the unimodularity `det = 1` is exactly the de Branges **balance**
  `‖E z‖ = ‖E* z‖` (`conjPairBlock_quotient_det_one_iff_balance`).  For Hermite–Biehler `E` that
  balance holds iff `z` is on the real axis (`deBranges_balance_iff_real`), and it is forced at every
  spectral zero `B z = 0` (`Bcomp_eq_zero_imp_balance`).  Off-axis the modulus determinant fails to
  be `1` (`conjPairBlock_quotient_det_ne_one_offaxis`) — one chirality dominates its conjugate (the
  Hermite–Biehler domination).
* With any unimodular eigenphase `w` (e.g. `w = spin y n`, the height-`y` eigenstate value) the block
  is `det = 1` and unitary unconditionally (`conjPairBlock_det_one_of_norm_one`,
  `conjPairBlock_unitary`) — the algebraic shadow of the real ordinate.

So `conjugate det = 1 ⟺ |w| = 1 ⟺ balance ‖E‖ = ‖E*‖ ⟺ real locus`
(`conjugate_det_one_iff_reality`). -/

/-- The **unimodular conjugate-pair block** `diag(w, w̄)`: the matrix avatar of a conjugate
(chiral) pair `(w, w̄)`. -/
def conjPairBlock (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![w, (starRingEnd ℂ) w]

/-
The determinant of the conjugate-pair block is the squared modulus `|w|²`.
-/
theorem conjPairBlock_det (w : ℂ) : (conjPairBlock w).det = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  -- The determinant of a diagonal matrix is the product of its diagonal entries.
  simp [conjPairBlock, Matrix.det_diagonal];
  simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ]

/-
**`det = 1 ⟺ |w| = 1`.**  The conjugate-pair block is unimodular exactly when its entry has
unit modulus.
-/
theorem conjPairBlock_det_eq_one_iff (w : ℂ) : (conjPairBlock w).det = 1 ↔ ‖w‖ = 1 := by
  rw [ conjPairBlock_det, Complex.ext_iff ] ; norm_num;
  norm_cast;
  exact ⟨ fun h => by nlinarith [ norm_nonneg w ], fun h => ⟨ by norm_num [ h ], by norm_num ⟩ ⟩

/-- A unimodular entry gives a unimodular block: `det = 1`. -/
theorem conjPairBlock_det_one_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) :
    (conjPairBlock w).det = 1 :=
  (conjPairBlock_det_eq_one_iff w).mpr hw

/-- The conjugate-pair block is **unitary** (`Bᴴ B = 1`) when its entry is unimodular. -/
theorem conjPairBlock_unitary {w : ℂ} (hw : ‖w‖ = 1) :
    (conjPairBlock w)ᴴ * conjPairBlock w = 1 := by
  have hns : (Complex.normSq w : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hw]; norm_num
  rw [conjPairBlock, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;>
    simp only [Pi.star_apply, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← starRingEnd_apply, Complex.conj_conj]
  · rw [mul_comm, Complex.mul_conj]; exact hns
  · rw [Complex.mul_conj]; exact hns

/-- For Hermite–Biehler `E`, the helix/anti-helix **balance** `‖E z‖ = ‖E* z‖` holds exactly on the
real axis. -/
theorem deBranges_balance_iff_real {E : ℂ → ℂ} (hE : IsHB E) (z : ℂ) :
    ‖E z‖ = ‖Estar E z‖ ↔ z.im = 0 := by
  exact ⟨ fun h => norm_eq_imp_im_zero hE h, fun h => by rw [ show z = ( z.re : ℂ ) by simp +decide [ Complex.ext_iff, h ] ] ; simp +decide [ Estar ] ⟩

/-- Every de Branges spectral zero `B z = 0` lies on the balance locus `‖E z‖ = ‖E* z‖`. -/
theorem Bcomp_eq_zero_imp_balance (E : ℂ → ℂ) {z : ℂ} (h : Bcomp E z = 0) :
    ‖E z‖ = ‖Estar E z‖ := by
  rw [(Bcomp_eq_zero_iff E z).mp h]

/-
The chiral-quotient block `diag(E z / E* z, conj(E z / E* z))` is unimodular exactly at the
balance `‖E z‖ = ‖E* z‖`: `det = 1 ⟺ ‖E z‖ = ‖E* z‖`.
-/
theorem conjPairBlock_quotient_det_one_iff_balance (E : ℂ → ℂ) {z : ℂ} (h : Estar E z ≠ 0) :
    (conjPairBlock (E z / Estar E z)).det = 1 ↔ ‖E z‖ = ‖Estar E z‖ := by
  rw [ conjPairBlock_det_eq_one_iff, norm_div, div_eq_one_iff_eq ] ; aesop

/-- **Conjugate det = 1 ⟺ on the reality locus.**  For Hermite–Biehler `E` at a point `z` with
`E* z ≠ 0`, the chiral-quotient block is unimodular iff `z` lies on the real axis:
`det diag(E z/E* z, conj(E z/E* z)) = 1 ⟺ z.im = 0`.  This is the algebraic shadow of the
critical-line / real-axis reality condition. -/
theorem conjugate_det_one_iff_reality {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (h : Estar E z ≠ 0) :
    (conjPairBlock (E z / Estar E z)).det = 1 ↔ z.im = 0 := by
  rw [conjPairBlock_quotient_det_one_iff_balance E h, deBranges_balance_iff_real hE]

/-- **Off-axis the modulus determinant fails to be 1.**  For Hermite–Biehler `E`, away from the real
axis the chiral-quotient block is *not* unimodular — one chirality strictly dominates its conjugate
(the Hermite–Biehler domination). -/
theorem conjPairBlock_quotient_det_ne_one_offaxis {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ}
    (h : Estar E z ≠ 0) (hz : z.im ≠ 0) :
    (conjPairBlock (E z / Estar E z)).det ≠ 1 :=
  fun hd => hz ((conjugate_det_one_iff_reality hE h).mp hd)

/-- **The unimodular conjugate block unifies the three layers.**  For Hermite–Biehler `E` at `z`
with `E* z ≠ 0`, the determinant-one condition of the chiral-quotient block is simultaneously the
balance of the helix/anti-helix and the reality of `z`, and any spectral zero sits on that locus:

1. (algebra ⟺ balance ⟺ reality) `det diag(E z/E* z, ·) = 1 ⟺ ‖E z‖ = ‖E* z‖ ⟺ z.im = 0`;
2. (spectrum ⊆ reality locus) `B z = 0 → ‖E z‖ = ‖E* z‖`;
3. (off-axis domination) `z.im ≠ 0 → det ≠ 1`. -/
theorem unimodular_block_unifies {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (h : Estar E z ≠ 0) :
    ((conjPairBlock (E z / Estar E z)).det = 1 ↔ ‖E z‖ = ‖Estar E z‖)
      ∧ ((conjPairBlock (E z / Estar E z)).det = 1 ↔ z.im = 0)
      ∧ (Bcomp E z = 0 → ‖E z‖ = ‖Estar E z‖)
      ∧ (z.im ≠ 0 → (conjPairBlock (E z / Estar E z)).det ≠ 1) :=
  ⟨conjPairBlock_quotient_det_one_iff_balance E h,
    conjugate_det_one_iff_reality hE h,
    Bcomp_eq_zero_imp_balance E,
    fun hz => conjPairBlock_quotient_det_ne_one_offaxis hE h hz⟩

end
end CriticalLinePhasor.DeBranges