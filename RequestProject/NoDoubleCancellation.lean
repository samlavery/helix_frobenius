import RequestProject.SelfAdjointGeneratorReadout
import RequestProject.SpectralSignFlip

/-!
# No double cancellation: one growing phasor at a time

This file records, **unconditionally**, three facts about the fixed self-adjoint generator `Aχ` (the
real-diagonal operator with strictly increasing eigen-heights `logGen n = log(n+1)`) and the harmonic
Gram pencil, formalizing the physical statements:

* **The fiber's phasors cannot align to cancel at two places during the same cancellation event.**
  At a fixed spectral parameter `s`, at most one basis mode `single n 1` can be a kernel vector of the
  resolvent operator `specOp Aχ s`: if two basis modes both cancel, they are the same mode
  (`no_double_cancellation`); equivalently the set of cancelling modes is a subsingleton
  (`cancellation_modes_subsingleton`).  This is forced by the eigen-heights being **distinct**
  (`logGen_injective`), which in turn is "only one phasor growing continuously at a time"
  (`logGen_strictMono`: the heights `log(n+1)` are strictly increasing).

* **The Gram harmonic pencil does not support a double cancellation.**  The Hermitian PSD harmonic
  Gram matrix `specGram` is never the zero matrix (`specGram_ne_zero`): its `(0,0)` entry is
  `1 + |μ|² ≥ 1` (`specGram_apply00`).  A rank-drop is governed by the *single* signed mode
  (`SelfAdjointGenerator.specGram_det_zero_iff`), so the pencil can drop rank by **one** (a single
  cancellation) but never to the zero matrix (a simultaneous double cancellation).

* **You cannot divide the total phasor energy exactly in half.**  Because the eigen-heights are
  strictly monotone (distinct), a cancellation concentrates on a *single* mode; the cancelled
  energy cannot be split between two distinct modes (`cancellation_energy_not_split`, a restatement of
  the subsingleton fact).  Only one phasor is the resonant/growing one at any spectral parameter.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.SelfAdjointGenerator

open CriticalLinePhasor CriticalLinePhasor.UnconditionalFrobenius

/-! ## 1. The eigen-heights are strictly increasing (one phasor growing at a time) -/

/-- **Only one phasor is growing continuously at a time.**  The eigen-heights `logGen n = log(n+1)`
are strictly increasing in `n`. -/
theorem logGen_strictMono : StrictMono logGen := by
  intro a b hab
  unfold logGen
  apply Real.log_lt_log
  · positivity
  · have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith

/-- The eigen-heights are pairwise distinct. -/
theorem logGen_injective : Function.Injective logGen := logGen_strictMono.injective

/-- Distinct sites carry distinct eigen-heights. -/
theorem heights_distinct {m n : ℕ} (hmn : m ≠ n) : logGen m ≠ logGen n :=
  fun h => hmn (logGen_injective h)

/-! ## 2. A basis mode cancels iff its height matches the spectral parameter -/

/-- The action of the resolvent operator on a basis mode: `specOp Aχ s (single m 1)
= single m (logGen m − specHeight s)`. -/
theorem Aχ_specOp_single (m : ℕ) (s : ℂ) :
    specOp Aχ s (Finsupp.single m 1) = Finsupp.single m ((logGen m : ℂ) - specHeight s) := by
  rw [specOp_apply, Aχ, diagOp_single, mul_one, Finsupp.smul_single, smul_eq_mul, mul_one,
    ← Finsupp.single_sub]

/-- A basis mode `single m 1` is a kernel vector of `specOp Aχ s` **iff** its eigen-height matches
the spectral parameter: `(logGen m : ℂ) = specHeight s`. -/
theorem Aχ_single_kernel_iff (m : ℕ) (s : ℂ) :
    specOp Aχ s (Finsupp.single m 1) = 0 ↔ (logGen m : ℂ) = specHeight s := by
  rw [Aχ_specOp_single, Finsupp.single_eq_zero, sub_eq_zero]

/-! ## 3. No double cancellation -/

/--
**The fiber's phasors cannot align to cancel at two places during the same cancellation event.**

At a fixed spectral parameter `s`, if two basis modes `single m 1` and `single n 1` are both kernel
vectors of `specOp Aχ s`, then they are the *same* mode (`m = n`): a single cancellation event
cannot occur at two distinct sites simultaneously.  (Both forces `logGen m = specHeight s = logGen n`,
and the eigen-heights are distinct.)
-/
theorem no_double_cancellation (s : ℂ) {m n : ℕ}
    (hm : specOp Aχ s (Finsupp.single m 1) = 0) (hn : specOp Aχ s (Finsupp.single n 1) = 0) :
    m = n := by
  rw [Aχ_single_kernel_iff] at hm hn
  have hC : (logGen m : ℂ) = (logGen n : ℂ) := by rw [hm, hn]
  have hR : logGen m = logGen n := by exact_mod_cast hC
  exact logGen_injective hR

/-- **The set of cancelling modes is a subsingleton.**  At any spectral parameter `s`, at most one
basis mode lies in the kernel of `specOp Aχ s`. -/
theorem cancellation_modes_subsingleton (s : ℂ) :
    {n : ℕ | specOp Aχ s (Finsupp.single n 1) = 0}.Subsingleton :=
  fun _ ha _ hb => no_double_cancellation s ha hb

/--
**You cannot divide the total phasor energy exactly in half.**  A cancellation concentrates on a
single mode: there is no spectral parameter `s` at which two *distinct* basis modes both cancel, so
the cancelled energy cannot be split between two modes.  (Restates `no_double_cancellation`: only one
phasor is the resonant/growing one at a time.)
-/
theorem cancellation_energy_not_split (s : ℂ) {m n : ℕ} (hmn : m ≠ n) :
    ¬ (specOp Aχ s (Finsupp.single m 1) = 0 ∧ specOp Aχ s (Finsupp.single n 1) = 0) := by
  rintro ⟨hm, hn⟩
  exact hmn (no_double_cancellation s hm hn)

/-! ## 4. The Gram harmonic pencil does not support a double cancellation -/

open CriticalLinePhasor.HarmonicCell Matrix

/-- The `(0,0)` entry of the spectral harmonic Gram matrix is `1 + |μ|²` (`= 1 + conj μ · μ`),
coming from the unsigned mode `1`. -/
theorem specGram_apply00 (γ : ℝ) (s : ℂ) (μ lam : ℂ) :
    specGram γ s μ lam 0 0 = 1 + (starRingEnd ℂ) μ * μ := by
  simp only [specGram, specHarmonicPencil, HarmonicCell.harmonicPencil, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply]
  simp

/--
**The Gram harmonic pencil does not support a double cancellation.**

The Hermitian positive-semidefinite spectral harmonic Gram matrix `specGram γ s μ lam` is **never**
the zero matrix: its `(0,0)` entry is `1 + |μ|² ≥ 1 ≠ 0`.  Hence, although it can rank-drop by one at
a single signed-mode cancellation (`SelfAdjointGenerator.specGram_det_zero_iff`), it can never
collapse to the zero matrix — there is no simultaneous double cancellation.
-/
theorem specGram_ne_zero (γ : ℝ) (s : ℂ) (μ lam : ℂ) : specGram γ s μ lam ≠ 0 := by
  intro h
  have h00 : specGram γ s μ lam 0 0 = 0 := by rw [h]; rfl
  rw [specGram_apply00] at h00
  have hre : (1 + (starRingEnd ℂ) μ * μ).re = 0 := by rw [h00]; simp
  rw [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hre
  nlinarith [sq_nonneg μ.re, sq_nonneg μ.im, hre]

end CriticalLinePhasor.SelfAdjointGenerator
