import Mathlib

/-!
# Lattice self-duality upstairs of J (ledger 924)

The corpus's `J` on the fiber (`fiber3D_vanishes_at_partner`) is Mathlib's functional equation carried to the zero set;
its dependency closure contains Poisson summation over `ℤ` (`Real.tsum_eq_tsum_fourier`), where the dual of `ℤ` is `ℤ`.
This file restores the lattice level before that information is discarded.

* `latticeTheta_inv`: Poisson on `cℤ` — `θ_c(1/t) = (√t/c)·θ_{1/c}(t)`, i.e. `(cℤ)* = (1/c)ℤ`.
* `jInternal_iff`: `J` fixes the lattice theta (`θ_c(1/t) = √t·θ_c(t)` for all `t > 0`) iff `c = 1` — iff the lattice is
  self-dual.  **This is `NativeSelfDualJCompatibility` for one lattice.**
* R107's control `a θ_1 + b θ_p + (b/p) θ_{1/p}`: `J`-symmetric as a sum (`controlTheta_J`), with the components `pℤ`
  and `(1/p)ℤ` exchanged by `J` and not fixed by it (`control_components_external`).
* Its site series is `B(s)·ζ(s)` with the mixing factor `B(s) = a + b p^{−s} + (b/p) p^{s}` (`controlSeries_eq`).
  `B` realises a same-height off-carrier pair at any prescribed offset (`mixing_offCarrier_pair`), so the control's
  extra zeros are exactly the zeros of its `J`-external mixing factor.
* `mixing_of_compatible`: for a lattice combination all of whose components are `J`-internal, the mixing factor is the
  constant `Σ w_j`.  The site series is then `(Σ w_j)·ζ`, so its zeros are `ζ`'s zeros.

No `sorry`, no `axiom`.
-/

open Real Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.LatticeJ

/-! ## 1. Poisson on `cℤ` and `J`-internality -/

/-- The theta function of the lattice `cℤ ⊂ ℝ`: `θ_c(t) = Σ_{n ∈ ℤ} e^{−π c² t n²}`. -/
def latticeTheta (c t : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-Real.pi * (c ^ 2 * t) * (n : ℝ) ^ 2)

theorem latticeTheta_scale (c t : ℝ) : latticeTheta c t = latticeTheta 1 (c ^ 2 * t) := by
  unfold latticeTheta
  simp

theorem summable_theta_terms {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * T * (n : ℝ) ^ 2)) := by
  have h := (HurwitzZeta.hasSum_int_evenKernel 0 hT).summable
  refine h.congr (fun n => ?_)
  congr 1
  ring

theorem one_le_latticeTheta (c : ℝ) {t : ℝ} (h : 0 < c ^ 2 * t) : 1 ≤ latticeTheta c t := by
  unfold latticeTheta
  have hs := summable_theta_terms h
  have := hs.le_tsum 0 (fun j _ => (Real.exp_pos _).le)
  simpa using this

/-- **Poisson on `cℤ`**: `θ_c(1/t) = (√t/c)·θ_{1/c}(t)`; the dual lattice of `cℤ` is `(1/c)ℤ`. -/
theorem latticeTheta_inv {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    latticeTheta c (1 / t) = Real.sqrt t / c * latticeTheta (1 / c) t := by
  unfold latticeTheta
  have ha : 0 < c ^ 2 * (1 / t) := by positivity
  rw [Real.tsum_exp_neg_mul_int_sq ha]
  have h1 : (c ^ 2 * (1 / t)) ^ (1 / 2 : ℝ) = c / Real.sqrt t := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, one_div, Real.sqrt_inv]
    exact (div_eq_mul_inv c (Real.sqrt t)).symm
  have h2 : ∀ n : ℤ, -Real.pi / (c ^ 2 * (1 / t)) * (n : ℝ) ^ 2
      = -Real.pi * ((1 / c) ^ 2 * t) * (n : ℝ) ^ 2 := by
    intro n
    field_simp
  simp_rw [h2]
  rw [h1]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  field_simp

/-- `J` fixes the lattice's theta: `θ_c(1/t) = √t·θ_c(t)` for every `t > 0`. -/
def JInternal (c : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → latticeTheta c (1 / t) = Real.sqrt t * latticeTheta c t

/-- A self-similarity `θ_1(u) = e·θ_1(e⁴u)` with `e > 1` is impossible (`θ_1 ≥ 1`). -/
theorem not_selfSimilar {e : ℝ} (he : 1 < e)
    (h : ∀ u : ℝ, 0 < u → latticeTheta 1 u = e * latticeTheta 1 (e ^ 4 * u)) : False := by
  have he0 : 0 < e := by linarith
  have hk : ∀ k : ℕ, latticeTheta 1 1 = e ^ k * latticeTheta 1 (e ^ (4 * k) * 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, h (e ^ (4 * k) * 1) (by positivity),
        show e ^ 4 * (e ^ (4 * k) * 1) = e ^ (4 * (k + 1)) * 1 by ring]
      ring
  have hge : ∀ k : ℕ, e ^ k ≤ latticeTheta 1 1 := by
    intro k
    have h1 := one_le_latticeTheta 1 (t := e ^ (4 * k) * 1) (by positivity)
    rw [hk k]
    have := pow_pos he0 k
    nlinarith
  obtain ⟨k, hk'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt he).eventually_gt_atTop
    (latticeTheta 1 1)).exists
  linarith [hge k]

/-- **`NativeSelfDualJCompatibility` for one lattice**: `J` fixes the theta of `cℤ` iff `c = 1`, i.e. iff the lattice
equals its dual. -/
theorem jInternal_iff {c : ℝ} (hc : 0 < c) : JInternal c ↔ c = 1 := by
  constructor
  · intro hJ
    have key : ∀ u : ℝ, 0 < u → latticeTheta 1 u = c * latticeTheta 1 (c ^ 4 * u) := by
      intro u hu
      have ht : 0 < c ^ 2 * u := by positivity
      have h1 := hJ (c ^ 2 * u) ht
      rw [latticeTheta_inv hc ht] at h1
      have hst : 0 < Real.sqrt (c ^ 2 * u) := Real.sqrt_pos.2 ht
      have h2 : latticeTheta (1 / c) (c ^ 2 * u) = c * latticeTheta c (c ^ 2 * u) := by
        field_simp at h1
        linarith
      rw [latticeTheta_scale (1 / c), latticeTheta_scale c] at h2
      rw [show (1 / c) ^ 2 * (c ^ 2 * u) = u by field_simp,
        show c ^ 2 * (c ^ 2 * u) = c ^ 4 * u by ring] at h2
      exact h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `c < 1`: the relation read at `u/c⁴` is a self-similarity with `e = 1/c > 1`
      refine not_selfSimilar (e := 1 / c) (by rw [lt_div_iff₀ hc]; linarith) (fun u hu => ?_)
      have := key ((1 / c) ^ 4 * u) (by positivity)
      rw [show c ^ 4 * ((1 / c) ^ 4 * u) = u by field_simp] at this
      rw [this]
      field_simp
    · exact not_selfSimilar hgt key
  · rintro rfl t ht
    rw [latticeTheta_inv one_pos ht]
    simp

/-! ## 2. R107's control: `J`-symmetric as a sum, `J`-external in its components -/

/-- R107's control carrier theta at `p`: `a θ_1 + b θ_p + (b/p) θ_{1/p}`. -/
def controlTheta (a b p t : ℝ) : ℝ :=
  a * latticeTheta 1 t + b * latticeTheta p t + b / p * latticeTheta (1 / p) t

/-- The control is `J`-symmetric as a sum. -/
theorem controlTheta_J (a b : ℝ) {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    controlTheta a b p (1 / t) = Real.sqrt t * controlTheta a b p t := by
  unfold controlTheta
  rw [latticeTheta_inv one_pos ht, latticeTheta_inv hp ht, latticeTheta_inv (one_div_pos.2 hp) ht,
    one_div_one_div]
  simp only [div_one]
  field_simp
  ring

/-- `J` exchanges the control's components `pℤ ↔ (1/p)ℤ` and fixes neither. -/
theorem control_components_external {p : ℝ} (hp : 1 < p) :
    ¬ JInternal p ∧ ¬ JInternal (1 / p) := by
  have hp0 : 0 < p := by linarith
  constructor
  · rw [jInternal_iff hp0]
    exact ne_of_gt hp
  · rw [jInternal_iff (one_div_pos.2 hp0)]
    intro h
    rw [div_eq_one_iff_eq hp0.ne'] at h
    linarith

/-! ## 3. The control's site series: the `J`-external mixing factor -/

/-- The site series of `cℤ` (positive sites) is `c^{−s} ζ(s)` on `Re s > 1`. -/
theorem latticeSeries {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (((c * ((n : ℝ) + 1) : ℝ)) : ℂ) ^ (-s) = (c : ℂ) ^ (-s) * riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← tsum_mul_left]
  congr 1
  funext n
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le (by positivity), Complex.cpow_neg,
    Complex.cpow_neg]
  push_cast
  field_simp

/-- The control's mixing factor `B(s) = a + b p^{−s} + (b/p) p^{s}`. -/
def mixingFactor (a b p : ℝ) (s : ℂ) : ℂ :=
  (a : ℂ) + (b : ℂ) * (p : ℂ) ^ (-s) + ((b / p : ℝ) : ℂ) * (p : ℂ) ^ s

/-- **The control's site series is `B(s)·ζ(s)`** on `Re s > 1` (sites `ℤ`, `pℤ`, `(1/p)ℤ`, weights `a, b, b/p`). -/
theorem controlSeries_eq (a b : ℝ) {p : ℝ} (hp : 0 < p) {s : ℂ} (hs : 1 < s.re) :
    (a : ℂ) * ∑' n : ℕ, (((1 * ((n : ℝ) + 1) : ℝ)) : ℂ) ^ (-s)
      + (b : ℂ) * ∑' n : ℕ, (((p * ((n : ℝ) + 1) : ℝ)) : ℂ) ^ (-s)
      + ((b / p : ℝ) : ℂ) * ∑' n : ℕ, ((((1 / p) * ((n : ℝ) + 1) : ℝ)) : ℂ) ^ (-s)
      = mixingFactor a b p s * riemannZeta s := by
  rw [latticeSeries one_pos hs, latticeSeries hp hs, latticeSeries (one_div_pos.2 hp) hs, mixingFactor]
  have hinv : (((1 / p : ℝ)) : ℂ) ^ (-s) = (p : ℂ) ^ s := by
    rw [show ((1 / p : ℝ) : ℂ) = ((p : ℂ))⁻¹ by push_cast; ring,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hp.le]; exact Real.pi_ne_zero.symm),
      Complex.cpow_neg, inv_inv]
  rw [hinv]
  push_cast
  simp
  ring

/-- **The `J`-external mixing factor realises a same-height off-carrier pair at any prescribed offset.** For
`p > 0`, any `b`, and any real `w`, choosing `a = −(b p^{−(½+w)} + (b/p) p^{½+w})` gives `B(½ + w) = B(½ − w) = 0`:
two vanishings at height `0`, at abscissae `½ ± w`. -/
theorem mixing_offCarrier_pair (b : ℝ) {p : ℝ} (hp : 0 < p) (w : ℝ) :
    let a : ℝ := -(b * p ^ (-(1 / 2 + w)) + b / p * p ^ (1 / 2 + w))
    mixingFactor a b p ((1 / 2 + w : ℝ) : ℂ) = 0 ∧ mixingFactor a b p ((1 / 2 - w : ℝ) : ℂ) = 0 := by
  intro a
  have hre : ∀ x : ℝ, mixingFactor a b p (x : ℂ) = ((a + b * p ^ (-x) + b / p * p ^ x : ℝ) : ℂ) := by
    intro x
    rw [mixingFactor, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hp.le, ← Complex.ofReal_cpow hp.le]
    push_cast
    ring
  have hsplit : ∀ x : ℝ, b / p * p ^ x = b * p ^ (x - 1) := by
    intro x
    rw [Real.rpow_sub_one hp.ne']
    ring
  refine ⟨?_, ?_⟩
  · rw [hre]
    simp only [a]
    push_cast
    ring
  · rw [hre]
    simp only [a]
    rw [hsplit (1 / 2 + w), hsplit (1 / 2 - w),
      show -(1 / 2 - w) = 1 / 2 + w - 1 by ring, show 1 / 2 - w - 1 = -(1 / 2 + w) by ring]
    push_cast
    ring

/-! ## 4. Compatibility collapses the mixing factor -/

/-- A lattice-combination carrier `Σ_j w_j δ_{c_j ℤ}`, as a list of `(w_j, c_j)`; its mixing factor is
`Σ_j w_j c_j^{−s}`, and its site series is `mixing·ζ` (as `controlSeries_eq`, term by term). -/
def mixing (L : List (ℝ × ℝ)) (s : ℂ) : ℂ := (L.map fun x => (x.1 : ℂ) * (x.2 : ℂ) ^ (-s)).sum

/-- **`NativeSelfDualJCompatibility`**: every component lattice has a positive scale and is `J`-internal. -/
def SelfDualCompatible (L : List (ℝ × ℝ)) : Prop := ∀ x ∈ L, 0 < x.2 ∧ JInternal x.2

/-- R107's control is not compatible (its `pℤ` component is `J`-external). -/
theorem control_not_compatible (a b : ℝ) {p : ℝ} (hp : 1 < p) :
    ¬ SelfDualCompatible [(a, 1), (b, p), (b / p, 1 / p)] := by
  intro h
  exact (control_components_external hp).1 (h (b, p) (by simp)).2

/-- The control's list mixing factor is `B`. -/
theorem mixing_control (a b p : ℝ) (hp : 0 < p) (s : ℂ) :
    mixing [(a, 1), (b, p), (b / p, 1 / p)] s = mixingFactor a b p s := by
  have hinv : (((1 / p : ℝ)) : ℂ) ^ (-s) = (p : ℂ) ^ s := by
    rw [show ((1 / p : ℝ) : ℂ) = ((p : ℂ))⁻¹ by push_cast; ring,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hp.le]; exact Real.pi_ne_zero.symm),
      Complex.cpow_neg, inv_inv]
  simp only [mixing, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Complex.ofReal_one,
    Complex.one_cpow, mul_one, add_zero, mixingFactor, hinv]
  ring

/-- **Compatibility collapses the mixing factor to the constant `Σ w_j`**: a `J`-internal lattice combination has site
series `(Σ w_j)·ζ`, so its zeros are exactly `ζ`'s. -/
theorem mixing_of_compatible {L : List (ℝ × ℝ)} (h : SelfDualCompatible L) (s : ℂ) :
    mixing L s = ((L.map Prod.fst).sum : ℂ) := by
  induction L with
  | nil => simp [mixing]
  | cons x L ih =>
    have hx := h x (List.mem_cons_self ..)
    have hc1 : x.2 = 1 := (jInternal_iff hx.1).1 hx.2
    have hL : SelfDualCompatible L := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ihL := ih hL
    simp only [mixing, List.map_cons, List.sum_cons] at ihL ⊢
    rw [ihL, hc1]
    push_cast
    simp

/-- **Step (4), compiled: compatibility plus focal vanishing returns `D` verbatim.**  A compatible carrier with nonzero
total weight has fiber `mixing·ζ` vanishing exactly where `ζ` does, so a one-vanishing-per-height statement for it is
the statement for `ζ`. -/
theorem compatible_fiber_zero_iff {L : List (ℝ × ℝ)} (h : SelfDualCompatible L)
    (hw : (L.map Prod.fst).sum ≠ 0) (s : ℂ) :
    mixing L s * riemannZeta s = 0 ↔ riemannZeta s = 0 := by
  rw [mixing_of_compatible h, mul_eq_zero]
  constructor
  · rintro (h0 | h0)
    · exact absurd (Complex.ofReal_eq_zero.1 h0) hw
    · exact h0
  · exact Or.inr

/-- The control's fiber `B·ζ` vanishes at both `½ + w` and `½ − w` (height `0`), for the prescribed `a`. -/
theorem control_fiber_pair (b : ℝ) {p : ℝ} (hp : 0 < p) (w : ℝ) :
    let a : ℝ := -(b * p ^ (-(1 / 2 + w)) + b / p * p ^ (1 / 2 + w))
    mixingFactor a b p ((1 / 2 + w : ℝ) : ℂ) * riemannZeta ((1 / 2 + w : ℝ) : ℂ) = 0 ∧
      mixingFactor a b p ((1 / 2 - w : ℝ) : ℂ) * riemannZeta ((1 / 2 - w : ℝ) : ℂ) = 0 := by
  intro a
  obtain ⟨h1, h2⟩ := mixing_offCarrier_pair b hp w
  exact ⟨by rw [h1, zero_mul], by rw [h2, zero_mul]⟩

end CriticalLinePhasor.LatticeJ

#print axioms CriticalLinePhasor.LatticeJ.latticeTheta_inv
#print axioms CriticalLinePhasor.LatticeJ.jInternal_iff
#print axioms CriticalLinePhasor.LatticeJ.controlTheta_J
#print axioms CriticalLinePhasor.LatticeJ.control_components_external
#print axioms CriticalLinePhasor.LatticeJ.controlSeries_eq
#print axioms CriticalLinePhasor.LatticeJ.mixing_offCarrier_pair
#print axioms CriticalLinePhasor.LatticeJ.control_not_compatible
#print axioms CriticalLinePhasor.LatticeJ.mixing_control
#print axioms CriticalLinePhasor.LatticeJ.mixing_of_compatible
#print axioms CriticalLinePhasor.LatticeJ.compatible_fiber_zero_iff
#print axioms CriticalLinePhasor.LatticeJ.control_fiber_pair
