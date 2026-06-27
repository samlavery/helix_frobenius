import RequestProject.FrobeniusSimilitude

/-!
# Per-height convergence: the cancellation machine on the whole critical line

This file states the **honest, convergence-layer** form of the "cancellation machine".  The
non-trivial content lives entirely in the convergence layer: for every height `y` a convergent
phasor channel converges to a *nonvanishing factor* times the `L`-value `L(½+iy, χ)`, so the
`L`-value vanishes exactly when the channel cancels in the limit.  Nothing here asserts *where*
the zeros are — only that every zero on the line is subject to the cancellation machine.

## Carrier vs. fiber (two distinct objects)

The **carrier** is the fiber-independent helix `helixPt θ n = √n · wind θ n`.  Its modulus is
exactly `√n` (`HelixLogFree.norm_helixPt`) — a fact of the geometry that depends only on the site
`n` and the fixed winding `θ`, *not* on the height `y` or the character `χ`
(`carrier_norm_height_independent`).  The carrier never vanishes off the origin
(`carrier_ne_zero`): it is a *no-radial-drift* source and is not mutable across heights.  The
**fiber** is what one pairs *against* the carrier: the unit-modulus spin `spin y n`
(`fiber_spin_unimodular`) times the arithmetic data `χ(n)·n^{-½}`.  Attaching the fiber only
rotates the carrier; it cannot change the `√n` radial profile.  Hence any vanishing of an
accumulation is a **fiber/pairing** cancellation (orthogonality), never a collapse of the carrier.

## The two convergent channels

* **Non-principal `χ`** (`finiteCarrier_critical_tendsto`): the raw weighted phasor partial sums
  `∑_{n<N} χ(n)·n^{-(½+iy)}` themselves converge to `L(½+iy, χ)` (Dirichlet/Abel summation past
  `Re = 1`, the strip-convergence engine).  The nonvanishing factor is `1`.
* **Principal / trivial character (Riemann `ζ`)** (`eta_critical_tendsto`): the raw series does
  *not* converge; the convergent channel is the alternating (eta) sum
  `∑_{n<N} (-1)^{n+1}·n^{-s}`, which converges to `(1 − 2^{1−s})·ζ(s)`.  The correction factor
  `1 − 2^{1−s}` is nonzero on the line (`zeta_eta_factor_ne_zero`), so the channel still detects
  the zeros exactly.

The "`= 0 ⇔ channel cancels`" corollaries
(`LFunction_critical_eq_zero_iff_pairing_tendsto_zero`,
`riemannZeta_critical_eq_zero_iff_eta_tendsto_zero`) and the unified packaging
(`perHeight_channel_nonprincipal`, `perHeight_channel_zeta`) are the precise, defensible form of
"every zero on the line is subject to the cancellation machine."
-/

open Complex Filter Topology
open CriticalLinePhasor

namespace CriticalLinePhasor.PerHeight

noncomputable section

/-! ## 1. Carrier vs. fiber: the geometry is fixed and height-independent -/

/-- **The carrier radius is `√n`, independent of the height `y`.**  The carrier modulus depends
only on the site `n` and the fixed winding `θ` — never on the height at which a fiber is laid on
top.  The carrier is immutable across heights. -/
theorem carrier_norm_height_independent (θ : ℕ → ℝ) (n : ℕ) (_y : ℝ) :
    ‖HelixLogFree.helixPt θ n‖ = Real.sqrt n :=
  HelixLogFree.norm_helixPt θ n

/-- **The carrier never vanishes off the origin.**  For `n ≥ 1`, `helixPt θ n ≠ 0`: there is no
radial drift to zero, so a vanishing accumulation is a fiber cancellation, not a carrier
collapse. -/
theorem carrier_ne_zero (θ : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    HelixLogFree.helixPt θ n ≠ 0 := by
  rw [← norm_ne_zero_iff, HelixLogFree.norm_helixPt]
  exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))

/-- **The fiber spin is unimodular.**  Attaching the fiber only rotates the carrier, preserving
its `√n` radial profile. -/
theorem fiber_spin_unimodular (y : ℝ) (n : ℕ) : ‖LFunctionPhasor.spin y n‖ = 1 :=
  LFunctionPhasor.spin_norm y n

/-- **Carrier rigidity: pairing a fiber cannot change the radial profile.**  Multiplying the
carrier by the unit-modulus spin (the fiber) only rotates it; the modulus stays `‖helixPt θ n‖`.
The only way the `√n` profile could change is to abandon the area-law geometry itself — the carrier
is rigid (drift-free), not mutable by the fiber. -/
theorem carrier_fiber_pairing_rigid (θ : ℕ → ℝ) (y : ℝ) (n : ℕ) :
    ‖LFunctionPhasor.spin y n * HelixLogFree.helixPt θ n‖ = ‖HelixLogFree.helixPt θ n‖ := by
  rw [norm_mul, LFunctionPhasor.spin_norm, one_mul]

/-- **Carrier rigidity, explicit form.**  Pairing any fiber `spin y n` against the carrier leaves
the radial profile at the area-law baseline `√n`, for every height `y`. -/
theorem carrier_fiber_pairing_norm_sqrt (θ : ℕ → ℝ) (y : ℝ) (n : ℕ) :
    ‖LFunctionPhasor.spin y n * HelixLogFree.helixPt θ n‖ = Real.sqrt n := by
  rw [carrier_fiber_pairing_rigid, HelixLogFree.norm_helixPt]

/-! ## 2. The fiber pairing equals the finite phasor carrier -/

/-- **The fiber pairing is the finite Dirichlet phasor sum.**  The ℓ² pairing
`⟪waveVec y N, dataVec χ N⟫` equals the finite phasor carrier
`∑_{n<N} χ(n)·n^{-(½+iy)}`. -/
theorem pairing_eq_finiteCarrier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) (N : ℕ) :
    (inner ℂ (FrobeniusSimilitude.waveVec y N) (FrobeniusSimilitude.dataVec χ N) : ℂ)
      = DirichletPhasorCarrier.finiteCarrier χ ((1 / 2 : ℂ) + (y : ℂ) * Complex.I) N :=
  FrobeniusSimilitude.inner_eq_finiteCarrier χ y N

/-! ## 3. Raw channel: per-height convergence for non-principal characters -/

/-- **Per-height raw convergence (non-principal `χ`).**  For every height `y` the finite phasor
carrier `∑_{n<N} χ(n)·n^{-(½+iy)}` converges to `L(½+iy, χ)`.  This is the raw channel: the bare
weighted phasor partial sums themselves converge, with nonvanishing factor `1`. -/
theorem finiteCarrier_critical_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (y : ℝ) :
    Tendsto (fun N => DirichletPhasorCarrier.finiteCarrier χ ((1 / 2 : ℂ) + (y : ℂ) * I) N)
      atTop (nhds (DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I))) := by
  have hs : 0 < ((1 / 2 : ℂ) + (y : ℂ) * I).re := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  have h := LFunctionPhasor.dirichlet_strip_tendsto_LFunction χ hχ hs
  simpa only [DirichletPhasorCarrier.finiteCarrier, DirichletPhasorCarrier.phasorTerm] using h

/-- **Zero ⇔ asymptotic orthogonality (non-principal `χ`).**  On the line, `L(½+iy, χ) = 0` iff the
fiber pairing `⟪waveVec y N, dataVec χ N⟫` tends to `0` — i.e. the real-frequency eigenwave becomes
asymptotically orthogonal to the arithmetic data. -/
theorem LFunction_critical_eq_zero_iff_pairing_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y : ℝ) :
    DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I) = 0
      ↔ Tendsto (fun N => (inner ℂ (FrobeniusSimilitude.waveVec y N)
          (FrobeniusSimilitude.dataVec χ N) : ℂ)) atTop (nhds 0) := by
  have hconv := finiteCarrier_critical_tendsto χ hχ y
  rw [show (fun N => (inner ℂ (FrobeniusSimilitude.waveVec y N)
        (FrobeniusSimilitude.dataVec χ N) : ℂ))
      = (fun N => DirichletPhasorCarrier.finiteCarrier χ ((1 / 2 : ℂ) + (y : ℂ) * I) N) from
    funext fun N => pairing_eq_finiteCarrier χ y N]
  constructor
  · intro hz; rw [hz] at hconv; exact hconv
  · intro hzero; exact tendsto_nhds_unique hconv hzero

/-! ## 4. Eta channel: per-height convergence for the principal / trivial character (`ζ`) -/

/-- **The eta correction factor `1 − 2^{1−s}` is nonzero on the critical line.**  On `Re s = ½` we
have `‖2^{1−s}‖ = 2^{½} = √2 ≠ 1`, so the factor cannot vanish.  This is what keeps the eta route
honest — without it the twist could manufacture or hide a zero. -/
theorem zeta_eta_factor_ne_zero {s : ℂ} (hs : s.re = 1 / 2) : (1 - (2 : ℂ) ^ (1 - s)) ≠ 0 := by
  intro h
  have h2 : (1 : ℂ) = (2 : ℂ) ^ (1 - s) := sub_eq_zero.mp h
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ ((1 - s).re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hre : (1 - s).re = 1 / 2 := by rw [Complex.sub_re, Complex.one_re, hs]; norm_num
  rw [hre, ← h2, norm_one] at hnorm
  have hgt : (1 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, by norm_num⟩)
  linarith

/-- **Per-height eta convergence (`ζ`).**  The alternating phasor partial sums
`∑_{n<N} (-1)^{n+1}·n^{-(½+iy)}` converge to `(1 − 2^{1−(½+iy)})·ζ(½+iy)`.  This is the convergent
channel that carries the line for the principal / trivial character, where the raw series diverges. -/
theorem eta_critical_tendsto (y : ℝ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I)))
      atTop (nhds ((1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))) *
        riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I))) := by
  have hs : 0 < ((1 / 2 : ℂ) + (y : ℂ) * I).re := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  have hs1 : ((1 / 2 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im] at this
  exact LFunctionPhasor.eta_strip_tendsto hs hs1

/-- **Zero ⇔ eta cancellation (`ζ`).**  `ζ(½+iy) = 0` iff the alternating phasor channel cancels in
the limit.  Because the eta factor is nonzero on the line, the channel detects the zeros exactly. -/
theorem riemannZeta_critical_eq_zero_iff_eta_tendsto_zero (y : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) = 0
      ↔ Tendsto (fun N => ∑ n ∈ Finset.range N,
          (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))) atTop (nhds 0) := by
  have hconv := eta_critical_tendsto y
  have hfac : (1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))) ≠ 0 := by
    refine zeta_eta_factor_ne_zero ?_
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  constructor
  · intro hz; rw [hz] at hconv; simpa using hconv
  · intro hzero
    have huniq := tendsto_nhds_unique hconv hzero
    rcases mul_eq_zero.mp huniq with h | h
    · exact absurd h hfac
    · exact h

/-! ## 5. The unified per-height statement (the cancellation machine the zeros must obey) -/

/-- **Unified per-height convergence — non-principal `χ`.**  For every non-principal Dirichlet
character and every height `y` there is a convergent phasor channel `chan` and a *nonzero* factor
`c` with `chan N → c·L(½+iy, χ)`, and `L(½+iy, χ) = 0 ⇔ chan N → 0`.  Here the channel is the raw
weighted phasor sum and `c = 1`. -/
theorem perHeight_channel_nonprincipal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (y : ℝ) :
    ∃ (chan : ℕ → ℂ) (c : ℂ), c ≠ 0 ∧
      Tendsto chan atTop (nhds (c * DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I))) ∧
      (DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I) = 0
        ↔ Tendsto chan atTop (nhds 0)) := by
  refine ⟨fun N => DirichletPhasorCarrier.finiteCarrier χ ((1 / 2 : ℂ) + (y : ℂ) * I) N, 1,
    one_ne_zero, ?_, ?_⟩
  · simpa using finiteCarrier_critical_tendsto χ hχ y
  · have h := LFunction_critical_eq_zero_iff_pairing_tendsto_zero χ hχ y
    rw [show (fun N => (inner ℂ (FrobeniusSimilitude.waveVec y N)
          (FrobeniusSimilitude.dataVec χ N) : ℂ))
        = (fun N => DirichletPhasorCarrier.finiteCarrier χ ((1 / 2 : ℂ) + (y : ℂ) * I) N) from
      funext fun N => pairing_eq_finiteCarrier χ y N] at h
    exact h

/-- **Unified per-height convergence — principal / trivial character (`ζ`).**  For every height `y`
there is a convergent phasor channel `chan` (the alternating/eta sum) and a *nonzero* factor `c`
with `chan N → c·ζ(½+iy)`, and `ζ(½+iy) = 0 ⇔ chan N → 0`.  Here `c = 1 − 2^{1−(½+iy)}`. -/
theorem perHeight_channel_zeta (y : ℝ) :
    ∃ (chan : ℕ → ℂ) (c : ℂ), c ≠ 0 ∧
      Tendsto chan atTop (nhds (c * riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I))) ∧
      (riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) = 0 ↔ Tendsto chan atTop (nhds 0)) := by
  refine ⟨fun N => ∑ n ∈ Finset.range N,
      (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I)),
    1 - (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (y : ℂ) * I)), ?_, eta_critical_tendsto y,
    riemannZeta_critical_eq_zero_iff_eta_tendsto_zero y⟩
  refine zeta_eta_factor_ne_zero ?_
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]

/-- **Unified per-height convergence — principal character mod `q` (`q ≥ 1`).**  The principal
character has no bucket cancellation, so the raw series diverges; but its `L`-function is the
entire Euler-factor product `∏_{p∣q}(1 − p^{-s})` times `ζ(s)`
(`DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`).  Scaling the convergent eta channel by
that fixed (in `N`) product gives a convergent phasor channel `chan` and a nonzero factor
`c = 1 − 2^{1−(½+iy)}` with `chan N → c·L(½+iy, 1)` and `L(½+iy, 1) = 0 ⇔ chan N → 0`.  This routes
the principal/trivial case through `ζ`, exactly the mechanism the per-modulus eta twist cannot
supply on its own. -/
theorem perHeight_channel_principal {q : ℕ} [NeZero q] (y : ℝ) :
    ∃ (chan : ℕ → ℂ) (c : ℂ), c ≠ 0 ∧
      Tendsto chan atTop (nhds (c * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        ((1 / 2 : ℂ) + (y : ℂ) * I))) ∧
      (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (y : ℂ) * I) = 0
        ↔ Tendsto chan atTop (nhds 0)) := by
  set s : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I with hs_def
  have hsre : s.re = 1 / 2 := by
    rw [hs_def]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hsre; norm_num at hsre
  set P : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) with hP
  set c : ℂ := 1 - (2 : ℂ) ^ (1 - s) with hc
  have hc0 : c ≠ 0 := zeta_eta_factor_ne_zero hsre
  have hLeq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s = P * riemannZeta s :=
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1
  have hchan : Tendsto (fun N => P * ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s))
      atTop (nhds (P * (c * riemannZeta s))) :=
    (eta_critical_tendsto y).const_mul P
  refine ⟨fun N => P * ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-s), c, hc0, ?_, ?_⟩
  · rw [hLeq, show c * (P * riemannZeta s) = P * (c * riemannZeta s) by ring]
    exact hchan
  · rw [hLeq]
    constructor
    · intro hz
      have hval : P * (c * riemannZeta s) = 0 := by
        rw [show P * (c * riemannZeta s) = c * (P * riemannZeta s) by ring, hz, mul_zero]
      rw [hval] at hchan; exact hchan
    · intro hzero
      have huniq := tendsto_nhds_unique hchan hzero
      have : c * (P * riemannZeta s) = 0 := by
        rw [show c * (P * riemannZeta s) = P * (c * riemannZeta s) by ring]; exact huniq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc0
      · exact h

/-! ## 6. One uniform statement over **all** Dirichlet characters at once

The three packagings above (`perHeight_channel_nonprincipal`, `perHeight_channel_zeta`,
`perHeight_channel_principal`) are here folded into a *single* theorem that quantifies over every
Dirichlet character `χ` mod `q` and branches internally on principal vs. non-principal.  This is the
"whole line, all characters" claim as one object: for **every** `χ` and **every** height `y` there is
a convergent phasor channel `chan` and a nonzero factor `c` with `chan N → c·L(½+iy, χ)`, and the
`L`-value vanishes exactly when the channel cancels in the limit. -/

/-- **The uniform cancellation machine over all Dirichlet characters.**  For every Dirichlet
character `χ` mod `q` (principal or not) and every height `y`, there is a convergent phasor channel
`chan` and a *nonzero* factor `c` with `chan N → c·L(½+iy, χ)`, and `L(½+iy, χ) = 0 ⇔ chan N → 0`.
The proof branches internally: the principal character routes through the eta channel scaled by the
Euler-factor product (`perHeight_channel_principal`), every non-principal character uses the raw
weighted phasor sum with `c = 1` (`perHeight_channel_nonprincipal`). -/
theorem perHeight_channel_uniform {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) :
    ∃ (chan : ℕ → ℂ) (c : ℂ), c ≠ 0 ∧
      Tendsto chan atTop (nhds (c * DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I))) ∧
      (DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I) = 0
        ↔ Tendsto chan atTop (nhds 0)) := by
  by_cases hχ : χ = 1
  · subst hχ; exact perHeight_channel_principal y
  · exact perHeight_channel_nonprincipal χ hχ y

/-! ## 7. The limit function **is** the L-function restricted to the critical line

The per-height limits of §3 are not a disconnected family: as the height `y` varies they assemble
into a single function `LOnLine χ : ℝ → ℂ`, the `L`-function restricted to the critical line
`s = ½ + iy`.  This is "the same helix sampled at every height" as **one** analytic object:
* `LOnLine χ` is continuous (indeed it is the restriction of the analytic `LFunction χ` to the
  line, on which `s ≠ 1`, so it is differentiable at every height) — `continuous_LOnLine`;
* for a non-principal `χ` the finite phasor carriers converge to it *pointwise in the height*
  — `finiteCarrier_tendsto_LOnLine`;
* and `LOnLine χ` is *uniquely* characterised as that pointwise limit — any function that the
  carriers converge to, at every height, equals `LOnLine χ` (`LOnLine_eq_of_pointwise_tendsto`),
  the limit/identity-theorem packaging.
`LOnLine_is_analytic_limit` bundles the three facts into the single "analytic limit object" claim. -/

/-- **The L-function restricted to the critical line**, `LOnLine χ y = L(½ + iy, χ)`: the single
analytic object obtained by sampling the helix at every height `y`. -/
noncomputable def LOnLine {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  fun y => DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I)

/-- The point `½ + iy` is never `1` (its real part is `½`), so the `L`-function is differentiable
there for **every** character. -/
theorem critical_ne_one (y : ℝ) : ((1 / 2 : ℂ) + (y : ℂ) * I) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im] at this

/-- **`LOnLine χ` is continuous, for every character.**  On the line `s ≠ 1`, so `LFunction χ` is
differentiable — hence continuous — at every sampled point, and the sampling map `y ↦ ½ + iy` is
continuous; the restriction to the line is therefore a single continuous (analytic) object. -/
theorem continuous_LOnLine {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (LOnLine χ) := by
  rw [continuous_iff_continuousAt]
  intro y
  show ContinuousAt (DirichletCharacter.LFunction χ ∘ fun y : ℝ => (1 / 2 : ℂ) + (y : ℂ) * I) y
  have hline : ContinuousAt (fun y : ℝ => (1 / 2 : ℂ) + (y : ℂ) * I) y := by
    fun_prop
  have hdiff : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) ((1 / 2 : ℂ) + (y : ℂ) * I) :=
    DirichletCharacter.differentiableAt_LFunction χ _ (Or.inl (critical_ne_one y))
  exact ContinuousAt.comp (g := DirichletCharacter.LFunction χ)
    (f := fun y : ℝ => (1 / 2 : ℂ) + (y : ℂ) * I) hdiff.continuousAt hline

/-- **Per-height convergence, in limit-function form (non-principal `χ`).**  For every height `y`
the finite phasor carriers converge to the value of the single line-function `LOnLine χ` at `y`. -/
theorem finiteCarrier_tendsto_LOnLine {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (y : ℝ) :
    Tendsto (fun N => DirichletPhasorCarrier.finiteCarrier χ ((1 / 2 : ℂ) + (y : ℂ) * I) N)
      atTop (nhds (LOnLine χ y)) := by
  unfold LOnLine
  exact finiteCarrier_critical_tendsto χ hχ y

/-- **Identity/uniqueness packaging (non-principal `χ`).**  `LOnLine χ` is *the* pointwise limit of
the finite phasor carriers: any function `g` to which the carriers converge at every height equals
`LOnLine χ`.  This is the limit-uniqueness (identity-theorem) statement that pins the line-function
down as a single analytic object, not merely a family of per-height values. -/
theorem LOnLine_eq_of_pointwise_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (g : ℝ → ℂ)
    (hg : ∀ y : ℝ, Tendsto (fun N => DirichletPhasorCarrier.finiteCarrier χ
        ((1 / 2 : ℂ) + (y : ℂ) * I) N) atTop (nhds (g y))) :
    g = LOnLine χ := by
  funext y
  exact tendsto_nhds_unique (hg y) (finiteCarrier_tendsto_LOnLine χ hχ y)

/-- **The line-function as a single analytic limit object (non-principal `χ`).**  Bundles the three
facts: `LOnLine χ` is continuous; the finite phasor carriers converge to it at every height; and it
vanishes at a height exactly when the carriers cancel there.  Together these say "the same helix
sampled at every height" is one continuous analytic object whose zeros are exactly the heights at
which the convergent channel cancels. -/
theorem LOnLine_is_analytic_limit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Continuous (LOnLine χ) ∧
      (∀ y : ℝ, Tendsto (fun N => DirichletPhasorCarrier.finiteCarrier χ
          ((1 / 2 : ℂ) + (y : ℂ) * I) N) atTop (nhds (LOnLine χ y))) ∧
      (∀ y : ℝ, LOnLine χ y = 0 ↔ Tendsto (fun N => DirichletPhasorCarrier.finiteCarrier χ
          ((1 / 2 : ℂ) + (y : ℂ) * I) N) atTop (nhds 0)) := by
  refine ⟨continuous_LOnLine χ, fun y => finiteCarrier_tendsto_LOnLine χ hχ y, fun y => ?_⟩
  constructor
  · intro hz
    have h := finiteCarrier_tendsto_LOnLine χ hχ y
    rwa [hz] at h
  · intro h0
    exact tendsto_nhds_unique (finiteCarrier_tendsto_LOnLine χ hχ y) h0

end

end CriticalLinePhasor.PerHeight
