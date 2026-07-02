import Mathlib
import RequestProject.GeometricPhasorClosure

/-!
# The helix **focal eigenheight**: projective focal-centroid coincidence

This file records the *projective / focal* version of the helix eigenheight event, as the
clean replacement for the two earlier (rejected) primitives:

* **too strong** — raw 3D moment equality `P₃D(t) = M₃D(t)` (dominated by large carrier
  height/radius), and
* **too crude** — raw cumulative endpoint equality `endpoint₊(Z) = endpoint₋(Z)` (ignores the
  projective normalisation by the scalar channel readout).

The right primitive is the **normalised** (projective) one:
`P₃D(t) / P(t) = M₃D(t) / M(t)`, i.e. the positive and negative weighted fibres point to the
**same normalised carrier focus**.

## The model

For a character/sign split of the source slots `n` we use the tested amplitude
`aₙ(t) = (π/3)·n^{-1/2}·exp(-i·t·log n)` (`aTerm`), and the scalar channel sums
```
P(t) = Σ_{χ(n)=+1} aₙ(t)      (Pchan)
M(t) = Σ_{χ(n)=-1} aₙ(t)      (Mchan)
```
The carrier points are `Cₙ = (rₙ cos θₙ, rₙ sin θₙ, n)` with `θₙ = (π/3)·n`, `rₙ = (4/3)·θₙ`
and height `Zₙ = n` (`carrier`).  The weighted 3D moments are
```
P₃D(t) = Σ_{χ(n)=+1} aₙ(t)·Cₙ   (Pmom, component-wise)
M₃D(t) = Σ_{χ(n)=-1} aₙ(t)·Cₙ   (Mmom, component-wise)
```
and the focal centroids are `F_P = P₃D / P`, `F_M = M₃D / M` (`focalP`, `focalM`).

## The eigenheight conditions

With the readout dictionary `t = log Z`:

* `IsFocalEigenheight χ N Z` — full projective coincidence `F_P(log Z) = F_M(log Z)`;
* `IsZFocalEigenheight χ N Z` — the strongest observed component, the **z-focal height**
  `P_z(log Z)/P(log Z) = M_z(log Z)/M(log Z)`.

The focal coincidence equation is the **kernel**
`Kχ(Z) = P_z(log Z)·M(log Z) − M_z(log Z)·P(log Z)` (`Kz`); cross-multiplication gives the
clean division-free characterisation `IsZFocalEigenheight χ N Z ↔ Kz χ N Z = 0`
(`isZFocalEigenheight_iff_Kz`).

## What is proved

* `isZFocalEigenheight_iff_Kz` — the projective z-focal condition is exactly `Kχ(Z) = 0`.
* `isFocalEigenheight_zFocal` — full focal coincidence implies the z-focal one.
* `channel_diff` — the scalar **channel difference** is the readout phasor:
  `P(log Z) − M(log Z) = (π/3)·Σ readoutTerm`.
* `channel_diff_tendsto` — its Abel limit is `(π/3)·Φχ(Z) = (π/3)·Lχ(1/2 + i log Z)`.
* `channel_closure_iff_L_zero` — **scalar channel closure ⇔ L-zero**: the channel difference
  tends to `0` iff `Φχ(Z) = Lχ(1/2 + i log Z) = 0`.

The sharper handoff target — that *focal coincidence* `Kχ(Z) = 0` is itself equivalent to the
scalar L-zero closure (and can only happen on the critical readout line) — is **not** asserted;
it is only *named* as `FocalCoincidenceTarget`, the next pencil's actual kernel.

Everything proved here is `Mathlib`-only and `sorry`/`axiom`-free.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace CriticalLinePhasor.Focal

open CriticalLinePhasor CriticalLinePhasor.Geometric

open Classical

variable {q : ℕ} [NeZero q]

/-! ## 1. The amplitude and the carrier geometry -/

/-- **The tested amplitude** `aₙ(t) = (π/3)·n^{-1/2}·exp(-i·t·log n)`.  This is the common
magnitude carried by *both* channels; the character only enters through the channel split. -/
noncomputable def aTerm (t : ℝ) (n : ℕ) : ℂ :=
  ((Real.pi / 3 : ℝ) : ℂ) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    * Complex.exp (-(t * Real.log n) * I)

/-- **The cell angle** `θₙ = (π/3)·n` — the **geometric carrier spin** (linear in `n`, the μ6 cell
placement winding); it carries **no logarithm**.  (The log-`n` phase that appears in `aTerm`/the
readout is the *analytic Mellin readout* spin, pulled back from the dilation readout geometry by
`helix_phase_pullback`, not the geometric carrier spin.) -/
noncomputable def cellAngle (n : ℕ) : ℝ := (Real.pi / 3) * (n : ℝ)

/-- **The carrier radius** `rₙ = (4/3)·θₙ`. -/
noncomputable def carrierRadius (n : ℕ) : ℝ := (4 / 3 : ℝ) * cellAngle n

/-- **The carrier point** `Cₙ = (rₙ cos θₙ, rₙ sin θₙ, n)`; the height (z) component is `Zₙ = n`. -/
noncomputable def carrier (n : ℕ) : Fin 3 → ℝ :=
  ![carrierRadius n * Real.cos (cellAngle n),
    carrierRadius n * Real.sin (cellAngle n),
    (n : ℝ)]

/-- The carrier height (z) component is exactly the geometric height `Zₙ = n`. -/
theorem carrier_z (n : ℕ) : carrier n 2 = (n : ℝ) := by
  simp [carrier]

/-! ## 2. The scalar channel sums and the 3D moments -/

/-- **Positive scalar channel** `P(t) = Σ_{χ(n)=+1} aₙ(t)` (finite truncation to `n ≤ N`). -/
noncomputable def Pchan (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, if χ (n : ZMod q) = 1 then aTerm t n else 0

/-- **Negative scalar channel** `M(t) = Σ_{χ(n)=-1} aₙ(t)` (finite truncation to `n ≤ N`). -/
noncomputable def Mchan (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, if χ (n : ZMod q) = -1 then aTerm t n else 0

/-- **Positive weighted 3D moment** `P₃D(t) = Σ_{χ(n)=+1} aₙ(t)·Cₙ`, component `i`. -/
noncomputable def Pmom (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) (i : Fin 3) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, if χ (n : ZMod q) = 1 then aTerm t n * ((carrier n i : ℝ) : ℂ) else 0

/-- **Negative weighted 3D moment** `M₃D(t) = Σ_{χ(n)=-1} aₙ(t)·Cₙ`, component `i`. -/
noncomputable def Mmom (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) (i : Fin 3) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, if χ (n : ZMod q) = -1 then aTerm t n * ((carrier n i : ℝ) : ℂ) else 0

/-- **Positive focal centroid** `F_P(t) = P₃D(t)/P(t)`, component `i`. -/
noncomputable def focalP (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) (i : Fin 3) : ℂ :=
  Pmom χ N t i / Pchan χ N t

/-- **Negative focal centroid** `F_M(t) = M₃D(t)/M(t)`, component `i`. -/
noncomputable def focalM (χ : DirichletCharacter ℂ q) (N : ℕ) (t : ℝ) (i : Fin 3) : ℂ :=
  Mmom χ N t i / Mchan χ N t

/-! ## 3. The focal eigenheight conditions (readout `t = log Z`) -/

/-- **Helix focal eigenheight.**  `Z > 0` is a focal eigenheight iff, with `t = log Z`, the
positive and negative weighted channel centroids agree in every component:
`P₃D(t)/P(t) = M₃D(t)/M(t)`. -/
def IsFocalEigenheight (χ : DirichletCharacter ℂ q) (N : ℕ) (Z : ℝ) : Prop :=
  ∀ i : Fin 3, focalP χ N (Real.log Z) i = focalM χ N (Real.log Z) i

/-- **z-focal eigenheight** (the strongest observed component): the focal *heights* agree,
`P_z(log Z)/P(log Z) = M_z(log Z)/M(log Z)`. -/
def IsZFocalEigenheight (χ : DirichletCharacter ℂ q) (N : ℕ) (Z : ℝ) : Prop :=
  focalP χ N (Real.log Z) 2 = focalM χ N (Real.log Z) 2

/-- **The focal (z) coincidence kernel** `Kχ(Z) = P_z(log Z)·M(log Z) − M_z(log Z)·P(log Z)`:
the division-free form of the focal-height coincidence equation `F_P,z = F_M,z`. -/
noncomputable def Kz (χ : DirichletCharacter ℂ q) (N : ℕ) (Z : ℝ) : ℂ :=
  Pmom χ N (Real.log Z) 2 * Mchan χ N (Real.log Z)
    - Mmom χ N (Real.log Z) 2 * Pchan χ N (Real.log Z)

/-! ## 4. The clean characterisations -/

/-
**The projective z-focal condition is exactly `Kχ(Z) = 0`.**  Cross-multiplication of
`P_z/P = M_z/M` (valid since both channels are non-degenerate).
-/
omit [NeZero q] in
theorem isZFocalEigenheight_iff_Kz (χ : DirichletCharacter ℂ q) (N : ℕ) (Z : ℝ)
    (hP : Pchan χ N (Real.log Z) ≠ 0) (hM : Mchan χ N (Real.log Z) ≠ 0) :
    IsZFocalEigenheight χ N Z ↔ Kz χ N Z = 0 := by
  simp only [IsZFocalEigenheight, focalP, focalM, Kz]
  rw [div_eq_div_iff hP hM, sub_eq_zero]

omit [NeZero q] in
/-- **Full focal coincidence implies the z-focal coincidence.** -/
theorem isFocalEigenheight_zFocal {χ : DirichletCharacter ℂ q} {N : ℕ} {Z : ℝ}
    (h : IsFocalEigenheight χ N Z) : IsZFocalEigenheight χ N Z :=
  h 2

/-! ## 5. The scalar channel difference is the readout phasor -/

/-
**The scalar channel difference is the readout phasor.**  For a character with values in
`{-1, 0, +1}`, the positive minus negative channel is `(π/3)` times the cell-free readout sum:
`P(log Z) − M(log Z) = (π/3)·Σ_{n=1}^N readoutTerm χ Z n`.
-/
theorem channel_diff (χ : DirichletCharacter ℂ q) (N : ℕ) (Z : ℝ)
    (hsign : ∀ n : ℕ, χ (n : ZMod q) = 1 ∨ χ (n : ZMod q) = -1 ∨ χ (n : ZMod q) = 0) :
    Pchan χ N (Real.log Z) - Mchan χ N (Real.log Z)
      = ((Real.pi / 3 : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, readoutTerm χ Z n := by
  rw [ Finset.mul_sum _ _ _ ];
  unfold Pchan Mchan readoutTerm;
  rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun n hn => _ ; rcases hsign n with h | h | h <;> norm_num [ h, aTerm ] ; ring;
  ring

/-
**The Abel limit of the scalar channel difference is `(π/3)·Φχ(Z)`.**  Hence the scalar
focal readout is `(π/3)·Lχ(1/2 + i log Z)`.
-/
theorem channel_diff_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hsign : ∀ n : ℕ, χ (n : ZMod q) = 1 ∨ χ (n : ZMod q) = -1 ∨ χ (n : ZMod q) = 0) (Z : ℝ) :
    Tendsto (fun N : ℕ => Pchan χ N (Real.log Z) - Mchan χ N (Real.log Z)) atTop
      (nhds (((Real.pi / 3 : ℝ) : ℂ) * Phi χ Z)) := by
  convert Filter.Tendsto.mul tendsto_const_nhds ( readout_partialSum_tendsto χ hχ Z |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 ) using 2 ; ring;
  convert channel_diff χ _ _ hsign using 1 ; norm_num [ add_comm, Finset.sum_range_succ' ];
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ; ring;
  unfold readoutTerm; norm_num;

/-
**Scalar channel closure ⇔ L-zero.**  The scalar channel difference tends to `0` iff
`Φχ(Z) = Lχ(1/2 + i log Z) = 0`.
-/
theorem channel_closure_iff_L_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hsign : ∀ n : ℕ, χ (n : ZMod q) = 1 ∨ χ (n : ZMod q) = -1 ∨ χ (n : ZMod q) = 0) (Z : ℝ) :
    Tendsto (fun N : ℕ => Pchan χ N (Real.log Z) - Mchan χ N (Real.log Z)) atTop (nhds 0)
      ↔ Phi χ Z = 0 := by
  constructor <;> intro h;
  · contrapose! h;
    convert channel_diff_tendsto χ hχ hsign Z |> fun h' => h'.not_tendsto _ using 1;
    simp +decide [ h, Real.pi_ne_zero ];
  · convert channel_diff_tendsto χ hχ hsign Z using 2 ; aesop

/-! ## 6. The helix phase-pullback (where `log n` comes from)

The Dirichlet phase `n^{-it} = exp(-it·log n)` is **not** an independent assumption: it is the
pullback of the *multiplicative dilation* readout geometry.  Source atoms are placed at positive
heights `Zₙ = n`; the readout modes are the dilation eigenfunctions `ψ_t(Z) = Z^{it}`; and the
relative phase of atom `n` seen from readout height `Z` is exactly `n^{-it}`.  The integer cell
spin `θₙ = Hn` is the carrier *placement/routing* law, while the observed analytic phase is the
induced multiplicative (Mellin) character. -/

/-- **The dilation readout mode** `ψ_t(Z) = Z^{it} = exp(i·t·log Z)`. -/
noncomputable def readoutMode (t Z : ℝ) : ℂ := Complex.exp (I * ((t : ℂ) * (Real.log Z : ℂ)))

/-- **The real log-dilation phase identity.**  Comparing the readout clock `t·log(Z/n)` with the
base clock `t·log Z` gives the relative delay `-t·log n`. -/
theorem log_dilation_phase (n : ℕ) (hn : 0 < n) (Z t : ℝ) (hZ : 0 < Z) :
    t * Real.log (Z / n) - t * Real.log Z = -t * Real.log n := by
  rw [Real.log_div (ne_of_gt hZ) (by exact_mod_cast hn.ne')]
  ring

/-
**The helix phase-pullback (exponential form).**  The relative readout factor of source atom
`n` under dilation `Z ↦ Z/n` is the Dirichlet/Mellin character `n^{-it} = exp(-i·t·log n)`:
`ψ_t(Z/n) / ψ_t(Z) = exp(-(t·log n)·i)`.  The `log n` phase is *derived*, not assumed.
-/
theorem helix_phase_pullback (n : ℕ) (hn : 0 < n) (t Z : ℝ) (hZ : 0 < Z) :
    readoutMode t (Z / n) / readoutMode t Z = Complex.exp (-((t : ℂ) * (Real.log n : ℂ)) * I) := by
  rw [ div_eq_iff ];
  · unfold readoutMode; rw [ ← Complex.exp_add ] ; ring;
    rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_inv ] ; push_cast ; ring;
  · exact Complex.exp_ne_zero _

/-- **The relative readout factor.**  The phase pulled back from the dilation `Z ↦ Z/n`. -/
noncomputable def relativeReadout (t Z : ℝ) (n : ℕ) : ℂ :=
  readoutMode t (Z / n) / readoutMode t Z

/-
**The amplitude is the pullback of the readout geometry.**  At readout height `Z` (so
`t = log Z` in the dictionary) the weighted atom factorises as
`aₙ(t) = (π/3)·n^{-1/2}·relativeReadout`, i.e. its Dirichlet phase is exactly the relative
dilation readout factor — not an independent `log n` assumption.
-/
theorem aTerm_eq_pullback (n : ℕ) (hn : 0 < n) (t Z : ℝ) (hZ : 0 < Z) :
    aTerm t n = ((Real.pi / 3 : ℝ) : ℂ) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      * relativeReadout t Z n := by
  -- Substitute the definition of `relativeReadout` and simplify using `helix_phase_pullback`.
  rw [relativeReadout, helix_phase_pullback n hn t Z hZ]
  -- Now use `push_cast` to convert the real numbers to complex numbers.
  simp [aTerm]

/-! ## 7. The handoff target (named, not asserted) -/

/-- **The next pencil's actual kernel.**  The sharper conjecture is that focal (z) coincidence
`Kχ(Z) = 0` is equivalent to the scalar L-zero closure `Φχ(Z) = 0`.  This is *not* proved here;
it is only named as the handoff target. -/
def FocalCoincidenceTarget (χ : DirichletCharacter ℂ q) (N : ℕ) : Prop :=
  ∀ Z : ℝ, 0 < Z → (Kz χ N Z = 0 ↔ Phi χ Z = 0)

end CriticalLinePhasor.Focal