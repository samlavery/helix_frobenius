import RequestProject.LFunctionPhasor

/-!
# True 3-D phasors: three channels (positive / negative / neutral) with magnitude as mass

This file upgrades the planar L-function phasor model of `LFunctionPhasor.lean` to a **genuinely
three-dimensional phasor model**.  In the planar model the `n`-th term is the complex number
`phasorTerm χ σ y n = χ(n)·n^{-σ}·exp(-(y·log n)·i)`, a 2-D arrow whose length is the magnitude
`|χ(n)|·n^{-σ}` — so on the **neutral** channel `χ(n)=0` the arrow collapses to `0` and *the
magnitude is lost*.

Here every term becomes a vector in `ℝ³ = (spin plane ℝ²) × (mass axis ℝ)`, modelled as `ℂ × ℝ`:

```
phasor3D χ σ y n = ( phasorTerm χ σ y n ,  (1 - ‖χ(n)‖)·n^{-σ} ).
```

* the **spin plane** (first, complex, coordinate) carries the rotating arrow of the *charged*
  channels `χ(n) = ±1`; this is exactly the old planar phasor, so the **L-series representation is
  unchanged** (`phasor3D_plane`, `phasor3D_plane_tsum`);
* the **mass axis** (third, real, coordinate) carries the magnitude `n^{-σ}` of the *neutral*
  channel `χ(n) = 0` as a real, non-rotating **mass**.

The three channels (`Channel`, `channel`) and their geometry:

| channel  | `χ(n)` | spin plane                     | mass axis | spins? | mass? |
|----------|--------|--------------------------------|-----------|--------|-------|
| positive | `+1`   | `+n^{-σ}·exp(-(y·log n)·i)`     | `0`       | yes    | no    |
| negative | `-1`   | `-n^{-σ}·exp(-(y·log n)·i)`     | `0`       | yes    | no    |
| neutral  | `0`    | `0`                            | `n^{-σ}`  | no     | yes   |

The headline upgrade is **magnitude conservation across all three channels**: the genuine 3-D
Euclidean length `mag3` of every term is exactly `n^{-σ}`, *including the neutral channel*
(`phasor3D_mag3`), whereas the planar arrow length was `‖χ(n)‖·n^{-σ}` and vanished there.

* **No intrinsic spin for the neutral channel.** Its 3-D phasor is independent of the frequency `y`
  (`phasor3D_neutral_no_spin`): it is a *standing* (resonant) mode, not a travelling one.  The
  charged channels, by contrast, rotate at rate `log n` as `y` advances (`phasor3D_charged_spin`).
* **Mass for absorption and resonance.** On the neutral channel the magnitude is *absorbed* off the
  radiating spin plane (`phasor3D_neutral_plane_zero`: it contributes `0` to the L-series) and
  *stored* on the mass axis as a positive amplitude `n^{-σ}` (`phasor3D_neutral_mass_pos`).  This
  standing mass resonates at frequency `resonantFreq n = log n` and height `resonantHeight n = n`
  with `resonantHeight n = exp (resonantFreq n)` (`resonantHeight_eq_exp_resonantFreq`), matching
  the carrier height law `z_n = n = e^{y_n}` of the geometric model.

No `axiom`, no `sorry`.
-/
open Complex
open scoped BigOperators
namespace CriticalLinePhasor.Phasor3D
open CriticalLinePhasor CriticalLinePhasor.LFunctionPhasor

/-! ## 0. The 3-D phasor space `ℝ³ = ℂ × ℝ` and its Euclidean magnitude -/

/-- A **3-D phasor**: a vector in `ℝ³`, modelled as `(spin plane : ℂ) × (mass axis : ℝ)`.
The first (complex) coordinate is the rotating arrow living in the spin plane `ℝ²`; the second
(real) coordinate is the non-rotating mass axis. -/
abbrev Vec3 := ℂ × ℝ

/-- The **spin-plane** (radiating) component of a 3-D phasor: a point of the plane `ℝ² ≅ ℂ`. -/
def plane (p : Vec3) : ℂ := p.1

/-- The **mass-axis** component of a 3-D phasor: a real amplitude (the "mass"). -/
def massAxis (p : Vec3) : ℝ := p.2

/-- The **3-D Euclidean magnitude** (true length in `ℝ³`) of a 3-D phasor:
`mag3 (z, m) = √(‖z‖² + m²)`. -/
noncomputable def mag3 (p : Vec3) : ℝ := Real.sqrt (‖p.1‖ ^ 2 + p.2 ^ 2)

/-- The 3-D Euclidean magnitude is nonnegative. -/
theorem mag3_nonneg (p : Vec3) : 0 ≤ mag3 p := Real.sqrt_nonneg _

/-! ## 1. The 3-D phasor term and the three channels -/

/-- The **3-D phasor term** of the Dirichlet series with weight `χ` on the line `s = σ + i y`:
`( χ(n)·n^{-σ}·exp(-(y·log n)·i) , (1 - ‖χ(n)‖)·n^{-σ} )`.  The spin-plane coordinate is the
planar phasor `phasorTerm`; the mass-axis coordinate stores the magnitude `n^{-σ}` exactly when
the channel is neutral (`‖χ(n)‖ = 0`). -/
noncomputable def phasor3D (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) : Vec3 :=
  (phasorTerm χ σ y n, (1 - ‖χ n‖) * ((n : ℝ) ^ (-σ)))

/-- The **three phasor channels**: positive, negative, neutral. -/
inductive Channel
  | positive
  | negative
  | neutral
  deriving DecidableEq, Repr

/-- The channel of index `n` for a quadratic weight `χ`: `+1 ↦ positive`, `-1 ↦ negative`,
everything else (`0`) `↦ neutral`. -/
noncomputable def channel (χ : ℕ → ℂ) (n : ℕ) : Channel :=
  if χ n = 1 then Channel.positive else if χ n = -1 then Channel.negative else Channel.neutral

/-! ## 2. The spin plane recovers the planar model (L-series unchanged) -/

/-- **The spin-plane component is the old planar phasor.** -/
@[simp] theorem phasor3D_plane (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) :
    plane (phasor3D χ σ y n) = phasorTerm χ σ y n := rfl

/-- **The mass-axis component.** -/
@[simp] theorem phasor3D_massAxis (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) :
    massAxis (phasor3D χ σ y n) = (1 - ‖χ n‖) * ((n : ℝ) ^ (-σ)) := rfl

/--
**The L-series representation survives the upgrade.**  Summing the spin-plane components over
all `n` still reproduces the Dirichlet `L`-series: the mass axis carries no part of `L`.
-/
theorem phasor3D_plane_tsum (χ : ℕ → ℂ) (σ y : ℝ) :
    ∑' n, plane (phasor3D χ σ y n) = LSeries χ ((σ : ℂ) + (y : ℂ) * I) := by
  simp only [phasor3D_plane]
  exact (LSeries_phasor_representation χ σ y).symm

/-! ## 3. Magnitude conservation: every channel has length `n^{-σ}` -/

/--
**Magnitude included in every channel (magnitude conservation).**  For a real (quadratic)
character `χ` and `n ≥ 1`, the genuine 3-D length of the `n`-th phasor is exactly the magnitude
`n^{-σ}` — *on all three channels*, including the neutral one where the planar arrow vanished.  This
is the precise sense in which "the magnitude is included in the phasors model".
-/
theorem phasor3D_mag3 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic)
    (σ y : ℝ) (n : ℕ) (hn : 0 < n) :
    mag3 (phasor3D (fun k => χ k) σ y n) = (n : ℝ) ^ (-σ) := by
  -- By definition of `phasor3D`, we have `mag3 (phasor3D χ σ y n) = sqrt(|phasorTerm χ σ y n|^2 + ((1 - |χ n|) * n^-σ)^2)`.
  simp [mag3, phasor3D];
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> norm_num [ phasorTerm_norm _ _ _ _ hn ];
  · have := phasorTerm_bucket_trichotomy χ hq n; rcases this with ( h | h | h ) <;> norm_num [ h ] ; ring;
    · ring;
    · ring;
  · positivity;
  · positivity

/-! ## 4. The neutral channel: mass, no spin, absorption, resonance -/

/--
**Neutral 3-D phasor.**  When `χ(n) = 0` the term is `(0, n^{-σ})`: pure mass, no arrow.
-/
theorem phasor3D_neutral (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (h : χ n = 0) :
    phasor3D χ σ y n = (0, (n : ℝ) ^ (-σ)) := by
  unfold phasor3D; simp +decide [ h, phasorTerm ] ;

/--
**The neutral channel has no intrinsic spin.**  Its 3-D phasor does not depend on the frequency
`y`: it is a standing mode, not a rotating one.
-/
theorem phasor3D_neutral_no_spin (χ : ℕ → ℂ) (σ y y' : ℝ) (n : ℕ) (h : χ n = 0) :
    phasor3D χ σ y n = phasor3D χ σ y' n := by
  rw [ phasor3D_neutral χ σ y n h, phasor3D_neutral χ σ y' n h ]

/--
**Absorption.**  The neutral channel contributes nothing to the radiating spin plane (hence
nothing to the `L`-series): its magnitude is absorbed off the plane.
-/
theorem phasor3D_neutral_plane_zero (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (h : χ n = 0) :
    plane (phasor3D χ σ y n) = 0 := by
  unfold phasor3D; simp +decide [ h, phasorTerm ] ;
  rfl

/--
**The neutral channel carries mass `n^{-σ}`.**
-/
theorem phasor3D_neutral_mass (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (h : χ n = 0) :
    massAxis (phasor3D χ σ y n) = (n : ℝ) ^ (-σ) := by
  unfold phasor3D massAxis; aesop;

/--
**The neutral mass is strictly positive** for `n ≥ 1`, `σ` arbitrary: the absorbed magnitude is
a genuine, nonzero mass on the mass axis.
-/
theorem phasor3D_neutral_mass_pos (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (h : χ n = 0) (hn : 0 < n) :
    0 < massAxis (phasor3D χ σ y n) := by
  rw [ phasor3D_neutral_mass χ σ y n h ] ; exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn ) _

/-! ## 5. The charged channels: spin, no mass -/

/--
**The charged channels are massless** (`χ(n) = ±1`): all of their magnitude is in the spinning
plane, none on the mass axis.
-/
theorem phasor3D_charged_massless (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (h : χ n = 1 ∨ χ n = -1) :
    massAxis (phasor3D χ σ y n) = 0 := by
  cases h <;> simp [massAxis, phasor3D, ‹_›]

/--
**The charged channels carry the full magnitude in the spin plane.**
-/
theorem phasor3D_charged_plane_norm (χ : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (hn : 0 < n)
    (h : χ n = 1 ∨ χ n = -1) :
    ‖plane (phasor3D χ σ y n)‖ = (n : ℝ) ^ (-σ) := by
  simp only [phasor3D_plane]
  rw [phasorTerm_norm χ σ y n hn]
  rcases h with h | h <;> simp [h]

/--
**The charged channels spin at rate `log n`.**  As the frequency advances `y ↦ y + t`, the
spin-plane arrow rotates by the angle `-(t·log n)` — an *intrinsic spin* at rate `log n`.  (This
rotation law in fact holds for every `χ`; the point is that on the neutral channel the arrow is `0`,
so the rotation is invisible — no intrinsic spin.)
-/
theorem phasor3D_charged_spin (χ : ℕ → ℂ) (σ y t : ℝ) (n : ℕ) :
    plane (phasor3D χ σ (y + t) n)
      = Complex.exp (-(t * Real.log n) * I) * plane (phasor3D χ σ y n) := by
  by_cases hn : n = 0
  · simp [phasor3D_plane, phasorTerm, hn]
  · simp only [phasor3D_plane, phasorTerm, if_neg hn, spin]
    have hexp : Complex.exp (-(↑(y + t) * ↑(Real.log ↑n)) * I)
        = Complex.exp (-(↑t * ↑(Real.log ↑n)) * I) * Complex.exp (-(↑y * ↑(Real.log ↑n)) * I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [hexp]; ring

/-! ## 6. Resonance: the neutral mass sits at its resonant frequency / height -/

/-- The **resonant frequency** of index `n`: the spin rate `log n` (the frequency at which the
`n`-th phasor resonates). -/
noncomputable def resonantFreq (n : ℕ) : ℝ := Real.log n

/-- The **resonant height** of index `n` on the carrier: `z_n = n` (the geometric height law). -/
def resonantHeight (n : ℕ) : ℝ := (n : ℝ)

/--
**Resonance condition `height = exp(frequency)`.**  For `n ≥ 1` the resonant height `n` is the
exponential of the resonant frequency `log n`: `resonantHeight n = exp (resonantFreq n)`.  This is
the carrier height law `z_n = n = e^{y_n}` realised on the neutral channel's standing mass.
-/
theorem resonantHeight_eq_exp_resonantFreq (n : ℕ) (hn : 0 < n) :
    resonantHeight n = Real.exp (resonantFreq n) := by
  exact_mod_cast Eq.symm ( Real.exp_log ( Nat.cast_pos.mpr hn ) )

/-! ## 7. Capstone: the full 3-D three-channel picture for a quadratic L-function -/

/--
**3-D three-channel phasor form (full picture).**  For a real (quadratic) Dirichlet character
`χ` modulo `q`, on the vertical line `s = σ + i y`:
1. **L-series unchanged** — the spin-plane components still sum to `L(χ, s)`;
2. **magnitude conservation** — every term, in *all three channels*, has 3-D length `n^{-σ}`;
3. **neutral has mass, no spin** — for `χ(n) = 0` the phasor is `(0, n^{-σ})`, `y`-independent, with
   `plane = 0` (absorption) and `mass = n^{-σ} > 0`;
4. **charged channels spin, no mass** — for `χ(n) = ±1` the mass axis is `0`, the full magnitude
   `n^{-σ}` lives in the spin plane, rotating at rate `log n`;
5. **resonance** — the neutral mass resonates at height `resonantHeight n = exp (resonantFreq n)`.
-/
theorem phasor3D_three_channel_form {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (σ y : ℝ) :
    (∑' n, plane (phasor3D (fun n => χ n) σ y n) = LSeries (fun n => χ n) ((σ : ℂ) + (y : ℂ) * I))
      ∧ (∀ n : ℕ, 0 < n → mag3 (phasor3D (fun n => χ n) σ y n) = (n : ℝ) ^ (-σ))
      ∧ (∀ n : ℕ, χ n = 0 →
          phasor3D (fun n => χ n) σ y n = (0, (n : ℝ) ^ (-σ))
            ∧ plane (phasor3D (fun n => χ n) σ y n) = 0
            ∧ (0 < n → 0 < massAxis (phasor3D (fun n => χ n) σ y n)))
      ∧ (∀ n : ℕ, (χ n = 1 ∨ χ n = -1) →
          massAxis (phasor3D (fun n => χ n) σ y n) = 0
            ∧ (0 < n → ‖plane (phasor3D (fun n => χ n) σ y n)‖ = (n : ℝ) ^ (-σ)))
      ∧ (∀ n : ℕ, 0 < n → resonantHeight n = Real.exp (resonantFreq n)) := by
  refine ⟨phasor3D_plane_tsum (fun n => χ n) σ y,
    fun n hn => phasor3D_mag3 χ hq σ y n hn,
    fun n h => ⟨phasor3D_neutral _ σ y n h, phasor3D_neutral_plane_zero _ σ y n h,
      fun hn => phasor3D_neutral_mass_pos _ σ y n h hn⟩,
    fun n h => ⟨phasor3D_charged_massless _ σ y n h,
      fun hn => phasor3D_charged_plane_norm _ σ y n hn h⟩,
    fun n hn => resonantHeight_eq_exp_resonantFreq n hn⟩

end CriticalLinePhasor.Phasor3D