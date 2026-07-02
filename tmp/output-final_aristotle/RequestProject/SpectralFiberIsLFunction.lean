import RequestProject.Phasor3D

/-!
# The spectral 3-D fiber **is** the L-function it is configured from

This file proves, unconditionally, that the **spectral 3-D fiber** of a Dirichlet character `χ`
is the very same analytic object as the 1-D Dirichlet `L`-function it is configured from — the
*only* difference being the space it lives in:

* the **state space** of the spectral object is the 3-D phasor space `Vec3 = ℂ × ℝ`
  (`Phasor3D.phasor3D`): at each site `n` it stores a genuine 3-D vector (spin plane × mass axis);
* the **readout space** of the 1-D `L`-function is just `ℂ`: the spin-plane component
  (`Phasor3D.plane`) read off site by site.

The headline results:

* `spectralFiber_readout_tendsto_LFunction` — **the σ > 0 identity**: for a non-principal Dirichlet
  character `χ` and *every* point `s` with `Re s > 0`, the partial-sum readout of the spectral
  fiber converges to `DirichletCharacter.LFunction χ s` — the genuine analytic continuation, valid
  on the **whole** half-plane `Re s > 0` (not merely `Re s > 1`).  This is the precise sense in
  which the spectral object is **not a single-line sampler** but reproduces the *entire*
  zero-producing `L`-function across the strip, including the critical line `Re s = 1/2`.
* `spectralFiber_readout_tsum_eq_LSeries` — the absolutely-convergent special case `Re s > 1`,
  where the readout is literally the `tsum` of the spin-plane components and equals `LSeries χ s`.
* `state_space_strictly_dominates_readout` — the state space carries strictly more than the readout:
  at a neutral site the 1-D readout is `0` while the 3-D state has *positive* magnitude (the mass is
  stored on the mass axis), so the spectral object is genuinely 3-D, not the 1-D readout.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.SpectralFiber

open CriticalLinePhasor CriticalLinePhasor.Phasor3D CriticalLinePhasor.LFunctionPhasor

/-! ## 0. The spectral 3-D fiber and its 1-D readout -/

/-- **The spectral 3-D fiber** of a weight `χ` at the point `s = Re s + i·Im s`: the site-indexed
family of 3-D phasors `phasor3D χ (Re s) (Im s)`.  Its value at each site `n` is a genuine vector of
the 3-D state space `Vec3 = ℂ × ℝ`. -/
noncomputable def spectralFiber (χ : ℕ → ℂ) (s : ℂ) (n : ℕ) : Vec3 :=
  phasor3D χ s.re s.im n

/-- **The 1-D readout** of the spectral fiber at site `n`: the spin-plane component, a point of the
readout space `ℂ`.  Summing this over `n` is what reproduces the `L`-function. -/
noncomputable def readout (χ : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  plane (spectralFiber χ s n)

@[simp] theorem readout_eq_phasorTerm (χ : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    readout χ s n = phasorTerm χ s.re s.im n := rfl

/-! ## 1. The readout term is the Dirichlet coefficient `χ(n)·n^{-s}` -/

/-- **The readout at a site is the Dirichlet term `χ(n)·n^{-s}`.**  For `Re s > 0` (so `s ≠ 0`) the
spin-plane readout of the spectral fiber at site `n` is exactly the `n`-th Dirichlet coefficient. -/
theorem readout_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re)
    (n : ℕ) :
    readout (fun n => χ (n : ZMod q)) s n = (χ (n : ZMod q)) * (n : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hterm := term_eq_phasorTerm (fun n => χ (n : ZMod q)) s.re s.im n
  rw [Complex.re_add_im] at hterm
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [readout_eq_phasorTerm]
    simp [phasorTerm, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [readout_eq_phasorTerm, ← hterm,
      LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]

/-! ## 2. The σ > 0 identity: the readout converges to the entire `L`-function -/

/--
**The spectral fiber readout reproduces the entire `L`-function on `Re s > 0`.**

For a non-principal Dirichlet character `χ` and *every* `s` with `Re s > 0`, the partial-sum readout
of the spectral 3-D fiber converges to `DirichletCharacter.LFunction χ s`.  The convergence holds on
the **whole** open half-plane `Re s > 0` — the genuine analytic continuation, **not** just the
absolutely-convergent region `Re s > 1`.  Hence the spectral object is not a sampler of a single
vertical line: it reproduces the entire zero-producing `L`-function across the strip, the critical
line `Re s = 1/2` included.
-/
theorem spectralFiber_readout_tendsto_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, readout (fun n => χ (n : ZMod q)) s n)
      Filter.atTop (nhds (DirichletCharacter.LFunction χ s)) := by
  refine (dirichlet_strip_tendsto_LFunction χ hχ hs).congr (fun N => ?_)
  exact (Finset.sum_congr rfl fun n _ => (readout_term χ hs n)).symm

/-! ## 3. The absolutely-convergent special case `Re s > 1` (tsum readout) -/

/--
**The readout `tsum` equals `LSeries χ s`** on the entire complex plane (where it converges
absolutely, i.e. `Re s > 1`): the spin-plane components, summed unconditionally, reproduce the
Dirichlet `L`-series.  The mass axis carries no part of `L`.
-/
theorem spectralFiber_readout_tsum_eq_LSeries (χ : ℕ → ℂ) (s : ℂ) :
    ∑' n, readout χ s n = LSeries χ s := by
  have h := phasor3D_plane_tsum χ s.re s.im
  rw [Complex.re_add_im] at h
  simpa [readout, spectralFiber] using h

/-! ## 3b. The principal-character case: the spectral fiber reproduces `ζ` on the strip -/

/-- **General readout term.**  For any weight `w` and any `s ≠ 0`, the spin-plane readout at site
`n` is `w(n)·n^{-s}`. -/
theorem readout_term_gen (w : ℕ → ℂ) {s : ℂ} (hs0 : s ≠ 0) (n : ℕ) :
    readout w s n = w n * (n : ℂ) ^ (-s) := by
  have hterm := term_eq_phasorTerm w s.re s.im n
  rw [Complex.re_add_im] at hterm
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [readout_eq_phasorTerm]
    simp [phasorTerm, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [readout_eq_phasorTerm, ← hterm,
      LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]

/-- **The alternating (eta) weight** `(-1)^{n+1}` — the spectral fiber's configuration for the
principal character, where there is no Dirichlet-bucket cancellation to reach `Re s > 0`. -/
noncomputable def etaW : ℕ → ℂ := fun n => (-1) ^ (n + 1)

/--
**Principal-character σ > 0 identity (eta form).**  For every `s` with `Re s > 0` and `s ≠ 1`, the
partial-sum readout of the eta-configured spectral fiber converges to the Dirichlet eta value
`(1 − 2^{1−s})·ζ(s)` — the analytic continuation on the punctured strip `{Re s > 0} \ {1}`.  This is
the principal-character analogue of `spectralFiber_readout_tendsto_LFunction`.
-/
theorem etaSpectralFiber_readout_tendsto_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, readout etaW s n)
      Filter.atTop (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  refine (eta_strip_tendsto hs hs1).congr (fun N => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [readout_term_gen etaW hs0 n, etaW]

/--
**Principal-character L-function recovered.**  Wherever the elementary factor `1 − 2^{1−s}` is
nonzero (in particular throughout the open critical strip `0 < Re s < 1`), the rescaled readout of
the eta-configured spectral fiber converges to `riemannZeta s` itself — and `riemannZeta` *is* the
principal (mod-`1`) Dirichlet L-function (`riemannZeta_eq_principal_LFunction`).  So the spectral
object reproduces the principal-character L-function on the strip exactly as it does the
non-principal ones.
-/
theorem etaSpectralFiber_readout_recovers_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hfac : (1 : ℂ) - (2 : ℂ) ^ (1 - s) ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => ((1 - (2 : ℂ) ^ (1 - s))⁻¹) * ∑ n ∈ Finset.range N, readout etaW s n)
      Filter.atTop (nhds (riemannZeta s)) := by
  have h := (etaSpectralFiber_readout_tendsto_zeta hs hs1).const_mul ((1 - (2 : ℂ) ^ (1 - s))⁻¹)
  rwa [inv_mul_cancel_left₀ hfac] at h

/-- **`riemannZeta` is the principal (mod-`1`) Dirichlet L-function.** -/
theorem riemannZeta_eq_principal_LFunction (χ : DirichletCharacter ℂ 1) :
    riemannZeta = DirichletCharacter.LFunction χ :=
  DirichletCharacter.LFunction_modOne_eq.symm

/-! ## 4. State space vs. readout space: the spectral object is genuinely 3-D -/

/--
**The state space strictly dominates the readout.**  At a neutral site (`χ(n) = 0`, `n ≥ 1`) the
1-D readout vanishes, yet the 3-D state has strictly positive magnitude: the magnitude is stored on
the mass axis, invisible to the readout.  So the spectral object lives in a strictly larger space
than its 1-D `L`-readout — they differ only by this state-vs-readout space, not as analytic objects.
-/
theorem state_space_strictly_dominates_readout (χ : ℕ → ℂ) (s : ℂ) (n : ℕ) (h : χ n = 0)
    (hn : 0 < n) :
    readout χ s n = 0 ∧ 0 < mag3 (spectralFiber χ s n) := by
  refine ⟨phasor3D_neutral_plane_zero χ s.re s.im n h, ?_⟩
  rw [spectralFiber, phasor3D_neutral χ s.re s.im n h, mag3]
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  rw [Real.sqrt_pos]
  positivity

/-! ## 5. Capstone -/

/--
**The spectral 3-D fiber is the `L`-function it is configured from.**  For a non-principal Dirichlet
character `χ`:

1. **σ > 0 identity (entire object, not a line sampler).**  On every point of the half-plane
   `Re s > 0`, the partial-sum readout converges to the genuine analytic `L`-function
   `LFunction χ s` — the whole zero-producing object, the critical line included.
2. **Absolute regime.**  On `Re s > 1` the readout `tsum` is literally `LSeries χ s`.
3. **Different space, same object.**  The two differ only by the space they operate in: the 3-D
   state space carries strictly more than the 1-D readout (positive magnitude on neutral sites where
   the readout is `0`).
-/
theorem spectral_fiber_is_Lfunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (∀ s : ℂ, 0 < s.re →
        Filter.Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range N, readout (fun n => χ (n : ZMod q)) s n)
          Filter.atTop (nhds (DirichletCharacter.LFunction χ s)))
      ∧ (∀ s : ℂ, ∑' n, readout (fun n => χ (n : ZMod q)) s n
          = LSeries (fun n => χ (n : ZMod q)) s)
      ∧ (∀ (s : ℂ) (n : ℕ), χ (n : ZMod q) = 0 → 0 < n →
          readout (fun n => χ (n : ZMod q)) s n = 0
            ∧ 0 < mag3 (spectralFiber (fun n => χ (n : ZMod q)) s n)) := by
  refine ⟨fun s hs => spectralFiber_readout_tendsto_LFunction χ hχ hs,
    fun s => spectralFiber_readout_tsum_eq_LSeries _ s,
    fun s n h hn => state_space_strictly_dominates_readout _ s n h hn⟩

end CriticalLinePhasor.SpectralFiber
