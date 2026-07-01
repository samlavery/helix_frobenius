import RequestProject.GeometricPhasorClosure
import RequestProject.HarmonicPencilCell

/-!
# The finite harmonic pencil: the pencil test on the 3-D bank, with `L` only as final verification

This file re-houses the harmonic pencil test on the **finite** side of the dictionary.  The
ontology is: the 3-D object (the finite phasor bank riding the carrier) is primary; the
1-D `L`-value is its **projection** — so the pencil channels and the pencil test itself must be
defined from the finite bank, and `DirichletCharacter.LFunction` may appear **only** in the
final-verification bridge that identifies the projection.

Contrast with `HarmonicPencilCell.Achan`/`Bchan`, which are *defined* as `L`-values: here

* `AchanFin χ Z N` — the finite unsigned channel: the bank of the first `N` phasors read at the
  absolute-convergence abscissa, `∑_{n<N} χ(n)·n^{-(3/2 + i·log Z)}`.  A finite sum; no
  continuation, no `L`.
* `BchanFin χ Z N` — the finite cell-normalized signed channel: the π/3-cell unit times the
  bank read on the critical abscissa, `(π/3)·∑_{n<N} χ(n)·n^{-(1/2 + i·log Z)}`.  Again a
  finite sum.
* `pencilFin A B μ λ = !![A, B; μ·A, λ·B]` — the 2×2 harmonic pencil of two channel values.

**The pencil test is proved entirely on the finite objects:**

* `pencilFin_det` — `det = (λ−μ)·A·B` exactly (finite algebra, no limit);
* `pencilFin_det_eq_zero_iff` — for `A ≠ 0`, `λ ≠ μ`: rank-drop `⇔` the signed channel closes;
* `pencilFin_gram_det` — the Gram determinant is `|det|²`, so the Gram rank-drop is the same
  event.

**Final verification (the 3-D → 1-D projection; the only place `L` enters):**

* `AchanFin_tendsto`, `BchanFin_tendsto` — the finite channels converge to the analytic
  channels `Achan`/`Bchan` of `HarmonicPencilCell` (via the already-proved strip convergence
  `dirichlet_strip_tendsto_LFunction`; non-principal `χ`);
* `BchanFin_closure_iff_L_zero` — the finite signed channel closes in the growth limit **iff**
  `Lχ(1/2 + i·log Z) = 0`: the `L`-zero is the projection of the finite closure event;
* `pencilFin_det_tendsto` — the finite pencil determinants converge to the analytic pencil
  determinant `(λ−μ)·Achan·Bchan`;
* `finite_pencil_rank_drop_iff_L_zero` — the headline: asymptotic rank-drop of the finite
  pencil is **equivalent** to the `L`-zero, using the unconditional admissibility
  `Achan_ne_zero` (the unsigned channel never vanishes).

**Indexing, the bank origin, and the strip.**  (Vocabulary: the **1-D object is the Dirichlet
L-function**; the **phasor representation is the 3-D bank** — there is no "1-D phasor
representation", only the 1-D readout of the 3-D one.)  The 1-D L-function partial sums are
indexed by `Finset.range N` (`n = 0, 1, …, N−1`): they start at `0`, not `1`, but the `n = 0`
site is the carrier origin and contributes nothing (`0 ^ (-s) = 0`, and `χ(0) = 0` for
`q > 1`) — the bank lives at heights `> 0`.  In the 3-D fiber each phasor enters **continuously**: zero magnitude
when the head reaches its site, growing until it is finished (the growth window of the Python
locator; the partial-absorption law of the carrier/fiber harness).  The finite channels here
are the completed-magnitude snapshot of that bank at head `N`; snapshot and grown bank have
the same growth limit, since the window is `1` on completed phasors.  The "strip" `0 < Re s`
through which the 1-D representation is carried by Abel summation
(`dirichlet_strip_tendsto_LFunction`) is a feature of the **projection only** — an
analytic-continuation device of the 1-D readout.  It has no 3-D counterpart: the geometry has
no free abscissa (`σ = 1/2` is the scale-balanced amplitude forced by the area law; `σ = 3/2`
is just the absolutely-convergent `A`-channel readout), so the strip appears in this file
exclusively inside the final-verification bridge.

Honest scope: the equivalences are per-height (`Z` fixed) and say nothing about *where* the
zeros are; completeness of the closure events over all nontrivial zeros is projection primacy
(GRH) and is neither assumed nor proved.  Mathlib-only; no `sorry`, no `axiom`.
-/

open Complex Filter Topology Matrix
open scoped BigOperators

namespace CriticalLinePhasor.FinitePencil

open CriticalLinePhasor CriticalLinePhasor.LFunctionPhasor CriticalLinePhasor.Bridge
open CriticalLinePhasor.Geometric CriticalLinePhasor.HarmonicCell

variable {q : ℕ} [NeZero q]

/-! ## 1. The finite channels (the 3-D side; no `L`, no continuation) -/

/-- **Finite unsigned channel**: the first `N` phasors of the bank read at the
absolute-convergence abscissa `σ = 3/2`, at source height `Z` (readout `log Z`).
A finite sum of phasor terms — nothing analytic is invoked. -/
noncomputable def AchanFin (χ : DirichletCharacter ℂ q) (Z : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, χ (n : ZMod q) * (n : ℂ) ^ (-((3 / 2 : ℂ) + (Real.log Z : ℂ) * I))

/-- **Finite cell-normalized signed channel**: the π/3 cell unit times the first `N` phasors
of the bank read on the critical abscissa `σ = 1/2` at source height `Z`.  A finite sum. -/
noncomputable def BchanFin (χ : DirichletCharacter ℂ q) (Z : ℝ) (N : ℕ) : ℂ :=
  ((Real.pi / 3 : ℝ) : ℂ) *
    ∑ n ∈ Finset.range N, χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (Real.log Z : ℂ) * I))

/-- **The finite harmonic pencil** of two channel values. -/
noncomputable def pencilFin (A B mu lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![A, B; mu * A, lam * B]

/-! ## 2. The pencil test, entirely on finite objects -/

/-- The finite pencil determinant factors exactly: `det = (λ−μ)·(A·B)`.  Finite algebra;
no limit, no remainder. -/
theorem pencilFin_det (A B mu lam : ℂ) :
    (pencilFin A B mu lam).det = (lam - mu) * (A * B) := by
  simp [pencilFin, Matrix.det_fin_two_of]; ring

/-- **The finite pencil test**: with the unsigned channel alive (`A ≠ 0`) and a nondegenerate
pencil (`λ ≠ μ`), rank-drop of the finite pencil is exactly closure of the signed channel. -/
theorem pencilFin_det_eq_zero_iff {A mu lam : ℂ} (hA : A ≠ 0) (hml : lam ≠ mu) (B : ℂ) :
    (pencilFin A B mu lam).det = 0 ↔ B = 0 := by
  rw [pencilFin_det]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hml
    · rcases mul_eq_zero.mp h2 with h3 | h4
      · exact absurd h3 hA
      · exact h4
  · intro h; rw [h, mul_zero, mul_zero]

/-- The Gram determinant of the finite pencil is `|det|²`: the Gram rank-drop detects the same
finite closure event. -/
theorem pencilFin_gram_det (A B mu lam : ℂ) :
    ((pencilFin A B mu lam)ᴴ * pencilFin A B mu lam).det
      = ((Complex.normSq ((pencilFin A B mu lam).det) : ℝ) : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  simp [Complex.normSq_eq_conj_mul_self]

/-! ## 3. Final verification: the 1-D projection (`L` enters here and only here) -/

/-- The finite unsigned channel converges to the analytic channel `Achan` (the 1-D projection
of the bank at `σ = 3/2`). -/
theorem AchanFin_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : ℝ) :
    Tendsto (AchanFin χ Z) atTop (𝓝 (Achan χ Z)) := by
  have hre : ((3 / 2 : ℂ) + (Real.log Z : ℂ) * I).re = 3 / 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hpos : 0 < ((3 / 2 : ℂ) + (Real.log Z : ℂ) * I).re := by rw [hre]; norm_num
  have h := CriticalLinePhasor.LFunctionPhasor.dirichlet_strip_tendsto_LFunction χ hχ hpos
  exact h

/-- The analytic signed channel is the π/3-scaled `L`-value (definitional unfolding of
`Bchan = Ucell · Phi`). -/
theorem Bchan_eq_Ucell_mul_L (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Bchan χ Z
      = ((Real.pi / 3 : ℝ) : ℂ)
        * DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (Real.log Z : ℂ) * I) := rfl

/-- The finite signed channel converges to the analytic channel `Bchan` (the 1-D projection
of the bank at `σ = 1/2`, carrying the π/3 cell normalization). -/
theorem BchanFin_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : ℝ) :
    Tendsto (BchanFin χ Z) atTop (𝓝 (Bchan χ Z)) := by
  have hre : ((1 / 2 : ℂ) + (Real.log Z : ℂ) * I).re = 1 / 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hpos : 0 < ((1 / 2 : ℂ) + (Real.log Z : ℂ) * I).re := by rw [hre]; norm_num
  have h := CriticalLinePhasor.LFunctionPhasor.dirichlet_strip_tendsto_LFunction χ hχ hpos
  have h2 := h.const_mul (((Real.pi / 3 : ℝ) : ℂ))
  rw [Bchan_eq_Ucell_mul_L]
  exact h2

/-- **Closure ⇔ `L`-zero (final verification).**  The finite signed channel closes in the
growth limit exactly when the projected `L`-value vanishes: residue-free vanishing, packaged
per height. -/
theorem BchanFin_closure_iff_L_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : ℝ) :
    DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (Real.log Z : ℂ) * I) = 0
      ↔ Tendsto (BchanFin χ Z) atTop (𝓝 0) := by
  have hc : (((Real.pi / 3 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero Real.pi_ne_zero (by norm_num))
  have base :=
    CriticalLinePhasor.Bridge.criticalLine_phasor_closure_iff_L_zero χ hχ (Real.log Z)
  constructor
  · intro hL
    have h0 := (base.mp hL).const_mul (((Real.pi / 3 : ℝ) : ℂ))
    rw [mul_zero] at h0
    exact h0
  · intro hB
    have h1 := hB.const_mul ((((Real.pi / 3 : ℝ) : ℂ))⁻¹)
    rw [mul_zero] at h1
    refine base.mpr (h1.congr fun N => ?_)
    simp only [BchanFin, inv_mul_cancel_left₀ hc]

/-- The finite pencil determinants converge to the analytic pencil determinant: the pencil
test's growth limit is the 1-D projection `(λ−μ)·Achan·Bchan`. -/
theorem pencilFin_det_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : ℝ)
    (mu lam : ℂ) :
    Tendsto (fun N : ℕ => (pencilFin (AchanFin χ Z N) (BchanFin χ Z N) mu lam).det)
      atTop (𝓝 ((lam - mu) * (Achan χ Z * Bchan χ Z))) := by
  have h := ((AchanFin_tendsto χ hχ Z).mul (BchanFin_tendsto χ hχ Z)).const_mul (lam - mu)
  simpa [pencilFin_det] using h

/-- **Headline: asymptotic finite-pencil rank-drop ⇔ `L`-zero.**  For a nondegenerate pencil,
the determinants of the finite pencils tend to `0` exactly when the projected `L`-value
vanishes.  The reverse direction uses the unconditional admissibility `Achan_ne_zero` (the
unsigned channel is alive), so no zero can hide in the `A`-channel. -/
theorem finite_pencil_rank_drop_iff_L_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : ℝ) {mu lam : ℂ} (hml : lam ≠ mu) :
    DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (Real.log Z : ℂ) * I) = 0
      ↔ Tendsto (fun N : ℕ => (pencilFin (AchanFin χ Z N) (BchanFin χ Z N) mu lam).det)
          atTop (𝓝 0) := by
  constructor
  · intro hL
    have hB0 : Bchan χ Z = 0 := by rw [Bchan_eq_Ucell_mul_L, hL, mul_zero]
    have h := pencilFin_det_tendsto χ hχ Z mu lam
    rw [hB0, mul_zero, mul_zero] at h
    exact h
  · intro hdet
    have hAne : Achan χ Z ≠ 0 := Achan_ne_zero χ Z
    have hden : Tendsto (fun N : ℕ => (lam - mu) * AchanFin χ Z N) atTop
        (𝓝 ((lam - mu) * Achan χ Z)) := (AchanFin_tendsto χ hχ Z).const_mul _
    have hdenne : (lam - mu) * Achan χ Z ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hml) hAne
    have hinv := hden.inv₀ hdenne
    have hq := hinv.mul hdet
    rw [mul_zero] at hq
    have hev : ∀ᶠ N in atTop, (lam - mu) * AchanFin χ Z N ≠ 0 :=
      hden.eventually_ne hdenne
    have heq : (fun N : ℕ => ((lam - mu) * AchanFin χ Z N)⁻¹
          * (pencilFin (AchanFin χ Z N) (BchanFin χ Z N) mu lam).det)
        =ᶠ[atTop] fun N : ℕ => BchanFin χ Z N := by
      filter_upwards [hev] with N hN
      rw [pencilFin_det]
      have hfac : (lam - mu) * (AchanFin χ Z N * BchanFin χ Z N)
          = ((lam - mu) * AchanFin χ Z N) * BchanFin χ Z N := by ring
      rw [hfac, inv_mul_cancel_left₀ hN]
    exact (BchanFin_closure_iff_L_zero χ hχ Z).mpr (Filter.Tendsto.congr' heq hq)

end CriticalLinePhasor.FinitePencil
