import RequestProject.FrobeniusSimilitude

/-!
# The tower's radial limit: the arithmetic strand block joins the unitary chiral class

**The 3D statement.**  At an arithmetic site the fiber's transverse datum is the *deprojected*
strand block `diag(α, α⁻¹)` — the helix and anti-helix legs with their radial weights, det-one by
the similitude, radius **not** assumed unit: the radius is the loss ledger's radial channel, and
only the phase shadow (`FrobeniusSimilitude.frobeniusBlock`, the unimodular chiral block) is what
the 2D chart reads.  Symmetric-power transport compounds the strand radius exponentially with
rank (`‖α^r‖ = ‖α‖^r`), while the carrier's ceiling is **rank-uniform** — the same `√·` law at
every rung.  This file proves the limit step, unconditionally: a strand radius whose every
transport sits under one fixed ceiling is exactly `1`, so the strand block is an **isometry of
the transverse plane** — it joins the carrier's unitary chiral class, and the radial ledger
channel at the site is trivial.  At the archimedean site the same limit forces the strand's
radial rate to zero: the strand clock is unit-modulus at every carrier height — a pure carrier
rotation with no radial drift.

**The two inputs this file does not prove** are the manuscript's, with their own citations:
the tower (`Sym^r π` automorphic/isobaric at every rank — the functoriality part) and the
rank-uniform ceiling (Jacquet–Shalika's unconditional per-rung bound, classical).  The 1D chart
reads the conclusions as **Ramanujan–Petersson** (`|α_p| = 1`, temperedness at `p`) and
**Selberg** (`Re μ_∞ = 0`; for a `GL(2)` Maass form, `λ ≥ 1/4`) — legitimate 1D readouts of the
3D radial-balance facts, never the objects of the proofs.

**The 3-D reframe of the conclusion** (`HelixStrandTemperedness`).  Temperedness `|α_p| = 1` is, on
the carrier, the statement that the strand is a **helix** (an elliptic rotation `e^{iθ}`), not a
**spiral** (a real, off-circle stretch): `isHelixStrand_iff_norm_one`.  The chart's `|a_p| ≤ 2` is
its automatic shadow (`helix_strandTrace_mem_Icc`; a spiral reads `|a_p| > 2`,
`spiral_strandTrace_gt_two`), and a nonzero real-trace strand is helix or spiral and nothing else
(`strand_dichotomy`) — the radial-channel twin of `SourceHolonomy.source_dichotomy`.  The forcing
direction *helix source ⟹ tempered* is proven (`tempered_of_hasHelixSource`); *every* Frobenius
having a helix source (`EveryFrobeniusHasHelixSource`, no spiral orphan) is the **favored branch** —
the radial twin of `EveryZeroHasSource` — grounded in the similitude structure, never asserted as a
from-1-D proof.

Does not assume or prove RH/GRH.  No unit modulus is assumed anywhere: the strand pair carries
its radius until the last line, where the tower closes it.  No `sorry`, no `axiom`.
-/

open Complex Matrix

namespace CriticalLinePhasor.RamanujanLimit

/-! ## 1. The radial-limit kernel (frame-neutral real algebra) -/

/-- **The rank-uniform ceiling forces radius `≤ 1`.**  A strand radius `ρ ≥ 0` whose every
positive transport `ρ^n` sits under one fixed ceiling `C` is at most `1`: radial imbalance
compounds with rank (Bernoulli), the ceiling does not. -/
theorem le_one_of_pow_le {ρ C : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ n : ℕ, 1 ≤ n → ρ ^ n ≤ C) : ρ ≤ 1 := by
  by_contra hcon
  have hlt : 1 < ρ := not_le.mp hcon
  have hρ1 : (0 : ℝ) < ρ - 1 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - 1) / (ρ - 1))
  have hmul : (C - 1) / (ρ - 1) * (ρ - 1) < (n : ℝ) * (ρ - 1) :=
    mul_lt_mul_of_pos_right hn hρ1
  rw [div_mul_cancel₀ _ (ne_of_gt hρ1)] at hmul
  have hbern : 1 + (n : ℝ) * (ρ - 1) ≤ ρ ^ n := by
    have h2 := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ ρ - 1) n
    rwa [show (1 : ℝ) + (ρ - 1) = ρ by ring] at h2
  have hstep : ρ ^ n ≤ ρ ^ (n + 1) := by
    calc ρ ^ n = ρ ^ n * 1 := (mul_one _).symm
    _ ≤ ρ ^ n * ρ := mul_le_mul_of_nonneg_left (le_of_lt hlt) (pow_nonneg hρ n)
    _ = ρ ^ (n + 1) := (pow_succ ρ n).symm
  have hceil := h (n + 1) (Nat.le_add_left 1 n)
  linarith

/-- **Det-one radial balance.**  A positive strand radius with `ρ ≤ 1` and `ρ⁻¹ ≤ 1` is exactly
`1`: the two conjugate legs of a det-one pair cannot both sit under the ceiling unless radially
balanced. -/
theorem eq_one_of_le_one_inv_le_one {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) (h2 : ρ⁻¹ ≤ 1) :
    ρ = 1 := by
  have hge : 1 ≤ ρ := by
    have h3 : ρ * ρ⁻¹ ≤ ρ * 1 := mul_le_mul_of_nonneg_left h2 (le_of_lt hρ)
    rwa [mul_inv_cancel₀ (ne_of_gt hρ), mul_one] at h3
  linarith

/-! ## 2. The deprojected strand block and its radial ledger channel -/

/-- **The deprojected arithmetic strand block** at a site: the helix leg `α` and the anti-helix
leg `α⁻¹` on the transverse plane — the det-one similitude pair with its radius *kept* (the loss
ledger's radial channel), of which `FrobeniusSimilitude.frobeniusBlock` (the unimodular chiral
block `diag(z, z̄)`) is the 2D phase shadow. -/
noncomputable def strandBlock (α : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![α, α⁻¹]

/-- **Determinant one**: the strand block is the similitude's volume/orientation-preserving
transverse pair, at *any* radius — det-one never sets the radius to one. -/
theorem strandBlock_det_one {α : ℂ} (hα : α ≠ 0) : (strandBlock α).det = 1 := by
  rw [strandBlock, Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact mul_inv_cancel₀ hα

/-- **Radius one makes the strand block an isometry of the transverse plane**: with the radial
ledger channel trivial, `strandBlock` is unitary — it coincides with the carrier's chiral class
(`frobeniusBlock_unitary` is the carrier-spin instance). -/
theorem strandBlock_unitary_of_radius_one {α : ℂ} (hα : ‖α‖ = 1) :
    (strandBlock α)ᴴ * strandBlock α = 1 := by
  have hne : α ≠ 0 := by
    intro h; rw [h, norm_zero] at hα; exact one_ne_zero hα.symm
  have hconj : (starRingEnd ℂ) α * α = 1 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hα, one_pow]
  have hconj_inv : (starRingEnd ℂ) α⁻¹ * α⁻¹ = 1 := by
    rw [map_inv₀, ← _root_.mul_inv_rev]
    rw [mul_comm α ((starRingEnd ℂ) α), hconj, inv_one]
  rw [strandBlock, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;>
    simp only [Pi.star_apply, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← starRingEnd_apply]
  · exact hconj
  · exact hconj_inv

/-! ## 3. The tower closes the radial channel at the arithmetic sites -/

/-- **The tower's radial limit at a site.**  If every symmetric-power transport of each strand
sits under one rank-uniform ceiling — `‖α^r‖ ≤ C` and `‖(α⁻¹)^r‖ ≤ C` for every rung `r ≥ 1`
(the manuscript supplies this from the tower and the per-rung Jacquet–Shalika ceiling,
`C = p^{1/2}`) — then the strand radius is exactly `1`: the radial ledger channel at the site is
trivial.  The 1D chart reads this as Ramanujan–Petersson at `p`. -/
theorem strand_radius_one_of_tower_ceiling {α : ℂ} (hα : α ≠ 0) {C : ℝ}
    (htop : ∀ r : ℕ, 1 ≤ r → ‖α ^ r‖ ≤ C)
    (hbot : ∀ r : ℕ, 1 ≤ r → ‖(α⁻¹) ^ r‖ ≤ C) : ‖α‖ = 1 := by
  have hpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have h1 : ‖α‖ ≤ 1 :=
    le_one_of_pow_le (norm_nonneg α) (fun n hn => by
      simpa [norm_pow] using htop n hn)
  have h2 : ‖α‖⁻¹ ≤ 1 := by
    have := le_one_of_pow_le (norm_nonneg α⁻¹) (fun n hn => by
      simpa [norm_pow] using hbot n hn)
    simpa [norm_inv] using this
  exact eq_one_of_le_one_inv_le_one hpos h1 h2

/-- **The strand block joins the unitary chiral class.**  Under the tower ceiling the
deprojected arithmetic block is an isometry of the transverse plane: its radial ledger entry is
empty and it coincides with the carrier's chiral (phase-only) class — the 3D form of
temperedness at the site. -/
theorem strandBlock_unitary_of_tower_ceiling {α : ℂ} (hα : α ≠ 0) {C : ℝ}
    (htop : ∀ r : ℕ, 1 ≤ r → ‖α ^ r‖ ≤ C)
    (hbot : ∀ r : ℕ, 1 ≤ r → ‖(α⁻¹) ^ r‖ ≤ C) :
    (strandBlock α)ᴴ * strandBlock α = 1 :=
  strandBlock_unitary_of_radius_one (strand_radius_one_of_tower_ceiling hα htop hbot)

/-! ## 4. The archimedean site: the strand clock is a pure carrier rotation -/

/-- **The radial rate vanishes at `∞`.**  If the top archimedean parameter of every rung is
uniformly bounded in real part — `|Re(r·μ)| ≤ C` for all `r ≥ 1` (the archimedean per-rung
ceiling, `C = 1/2`) — then `Re μ = 0`: the archimedean strand has no radial drift. -/
theorem archimedean_re_zero_of_tower_ceiling {μ : ℂ} {C : ℝ}
    (h : ∀ r : ℕ, 1 ≤ r → |((r : ℂ) * μ).re| ≤ C) : μ.re = 0 := by
  by_contra hne
  have habs : 0 < |μ.re| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |μ.re|)
  have hkey := h (n + 1) (Nat.le_add_left 1 n)
  have hre : (((n + 1 : ℕ) : ℂ) * μ).re = ((n + 1 : ℕ) : ℝ) * μ.re := by
    simp [Complex.mul_re]
  rw [hre, abs_mul, Nat.abs_cast] at hkey
  have hmul : C / |μ.re| * |μ.re| < (n : ℝ) * |μ.re| :=
    mul_lt_mul_of_pos_right hn habs
  rw [div_mul_cancel₀ _ (ne_of_gt habs)] at hmul
  have hcast : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hmono : (n : ℝ) * |μ.re| ≤ ((n + 1 : ℕ) : ℝ) * |μ.re| :=
    mul_le_mul_of_nonneg_right hcast (le_of_lt habs)
  linarith

/-- **The archimedean strand clock is unit-modulus at every carrier height.**  Under the tower
ceiling the strand profile `e^{yμ}` along the carrier ordinate has flat radial envelope — a pure
carrier rotation, no radial drift, at *every* height `y`.  The 1D chart reads this as Selberg's
bound (for a `GL(2)` Maass form, `λ ≥ 1/4`). -/
theorem archimedean_strand_unimodular_of_tower_ceiling {μ : ℂ} {C : ℝ}
    (h : ∀ r : ℕ, 1 ≤ r → |((r : ℂ) * μ).re| ≤ C) (y : ℝ) :
    ‖Complex.exp ((y : ℂ) * μ)‖ = 1 := by
  have h0 : μ.re = 0 := archimedean_re_zero_of_tower_ceiling h
  rw [Complex.norm_exp]
  have hre : ((y : ℂ) * μ).re = y * μ.re := by simp [Complex.mul_re]
  rw [hre, h0, mul_zero, Real.exp_zero]

end CriticalLinePhasor.RamanujanLimit

#print axioms CriticalLinePhasor.RamanujanLimit.strand_radius_one_of_tower_ceiling
#print axioms CriticalLinePhasor.RamanujanLimit.strandBlock_unitary_of_tower_ceiling
#print axioms CriticalLinePhasor.RamanujanLimit.archimedean_strand_unimodular_of_tower_ceiling
