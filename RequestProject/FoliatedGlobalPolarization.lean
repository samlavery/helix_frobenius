import RequestProject.FoliatedPolarization
import RequestProject.HelixLedgerPairing
import RequestProject.ZetaContourArgument

/-!
# The global polarization on the actual zero multiset

`FoliatedPolarization` built the functional-equation pairing on a single
reflection block and proved the generator self-adjoint there.  This file
globalizes both statements to the *actual* zero multiset, window by window,
and compiles the target of the foliated route as a single proposition.

New analytic input: `xiOrderNat_conj` — the analytic multiplicity of `ξ` is
invariant under conjugation, by transporting the local factorization through
the Schwarz reflection `z ↦ conj (g (conj z))` (mathlib's
`DifferentiableAt.conj_conj` plus `analyticAt_iff_eventually_differentiableAt`).
Combined with the compiled `xiOrderNat_one_sub`, the multiplicity is invariant
under the full FE reflection `ρ ↦ 1 - conj ρ`, which is what makes the global
pairing Hermitian.

Objects, over any FE-closed finite window `s` of zeros:

* `diagFormOn s c d = Σ_ρ m_ρ c(ρ) conj(d(ρ))` — the multiplicity-weighted
  diagonal form, positive semidefinite outright;
* `feFormOn s c d = Σ_ρ m_ρ c(ρ) conj(d(ρ*))` — the functional-equation
  pairing, `ρ* = 1 - conj ρ`.

Compiled, unconditionally:

* `feFormOn_hermitian` — the FE pairing is Hermitian on every FE-closed window;
* `feFormOn_theta` — the flow generator (multiplication by the spectral
  coordinate `t_ρ`) is self-adjoint for the FE pairing, termwise, with no
  window hypothesis;
* `feFormOn_eq_diagFormOn_of_online` — on-line windows: the FE pairing *is*
  the diagonal form;
* `feFormOn_nonneg_iff` / `feForm_global_nonneg_iff` — **the target, pinned**:
  the FE pairing is positive semidefinite on every FE-closed window iff every
  nontrivial zero lies on the critical line.

The iffs state the target; nothing here proves its left side.  The off-line
witness in the reverse direction is the explicit hyperbolic vector
`e_ρ − e_{ρ*}` of the block model, now instantiated on the actual multiset.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.FoliatedGlobalPolarization

open CriticalLinePhasor.FoliatedPolarization
open CriticalLinePhasor.CaptureInterfaceAudit (xiOrderNat_one_sub)
open CriticalLinePhasor.ContourArgument (riemannXi_conj riemannXi_one_sub_conj)

/-! ## Multiplicity is conjugation- and FE-invariant -/

/-- **Conjugation invariance of the ξ-multiplicity**, at every point of the
plane: the local factorization `ξ(z) = (z-ρ)ⁿ g(z)` transports through the
Schwarz reflection of the unit. -/
theorem xiOrderNat_conj (z : ℂ) :
    ZD.xiOrderNat ((starRingEnd ℂ) z) = ZD.xiOrderNat z := by
  show analyticOrderNatAt ZD.riemannXi ((starRingEnd ℂ) z)
      = analyticOrderNatAt ZD.riemannXi z
  have hana : ∀ w : ℂ, AnalyticAt ℂ ZD.riemannXi w := fun w =>
    ZD.riemannXi_differentiable.analyticAt w
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere
  obtain ⟨g, hg, hg0, hev⟩ :=
    ((hana z).analyticOrderNatAt_eq_iff (hne z)).mp rfl
  have hct : Tendsto (fun w : ℂ => (starRingEnd ℂ) w)
      (𝓝 ((starRingEnd ℂ) z)) (𝓝 z) := by
    have h := continuous_conj.tendsto ((starRingEnd ℂ) z)
    simpa using h
  refine ((hana ((starRingEnd ℂ) z)).analyticOrderNatAt_eq_iff
      (hne ((starRingEnd ℂ) z))).mpr
    ⟨fun w => (starRingEnd ℂ) (g ((starRingEnd ℂ) w)), ?_, ?_, ?_⟩
  · -- analyticity of the Schwarz reflection at `conj z`
    rw [analyticAt_iff_eventually_differentiableAt]
    have hgev : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g w :=
      hg.eventually_analyticAt.mono fun _ hw => hw.differentiableAt
    filter_upwards [hct.eventually hgev] with w hw
    have h2 : DifferentiableAt ℂ
        ((starRingEnd ℂ) ∘ g ∘ (starRingEnd ℂ)) w := by
      rw [differentiableAt_conj_conj_iff]
      exact hw
    exact h2
  · simpa using hg0
  · filter_upwards [hct.eventually hev] with w hw
    have hxi : ZD.riemannXi w = (starRingEnd ℂ) (ZD.riemannXi ((starRingEnd ℂ) w)) := by
      rw [riemannXi_conj]
      simp
    rw [hxi, hw]
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

/-- **FE-reflection invariance of the ξ-multiplicity.** -/
theorem xiOrderNat_feReflect (z : ℂ) :
    ZD.xiOrderNat (feReflect z) = ZD.xiOrderNat z := by
  unfold feReflect
  rw [xiOrderNat_one_sub, xiOrderNat_conj]

/-- The FE reflection preserves the nontrivial-zero set:
`ξ(1 - conj ρ) = conj (ξ ρ) = 0`. -/
theorem feReflect_mem {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    feReflect ρ ∈ ZD.NontrivialZeros := by
  apply (ZD.riemannXi_eq_zero_iff _).mp
  unfold feReflect
  rw [riemannXi_one_sub_conj, (ZD.riemannXi_eq_zero_iff ρ).mpr hρ, map_zero]

/-! ## The zero index, the reflection equivalence, the weight -/

/-- The zero index type: the actual nontrivial-zero set. -/
abbrev Zero : Type := {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}

/-- The FE reflection as a self-equivalence of the zero set. -/
def feReflectZ : Zero ≃ Zero where
  toFun ρ := ⟨feReflect ρ.val, feReflect_mem ρ.2⟩
  invFun ρ := ⟨feReflect ρ.val, feReflect_mem ρ.2⟩
  left_inv ρ := Subtype.ext (feReflect_involutive ρ.val)
  right_inv ρ := Subtype.ext (feReflect_involutive ρ.val)

@[simp] theorem feReflectZ_val (ρ : Zero) :
    (feReflectZ ρ).val = feReflect ρ.val := rfl

@[simp] theorem feReflectZ_feReflectZ (ρ : Zero) :
    feReflectZ (feReflectZ ρ) = ρ :=
  Subtype.ext (feReflect_involutive ρ.val)

/-- The multiplicity weight of a zero. -/
def mwt (ρ : Zero) : ℝ := (ZD.xiOrderNat ρ.val : ℝ)

theorem mwt_pos (ρ : Zero) : 0 < mwt ρ := by
  unfold mwt
  exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ.2

theorem mwt_feReflectZ (ρ : Zero) : mwt (feReflectZ ρ) = mwt ρ := by
  unfold mwt
  rw [feReflectZ_val, xiOrderNat_feReflect]

/-- An FE-closed window of zeros. -/
def FEClosed (s : Finset Zero) : Prop := ∀ ρ ∈ s, feReflectZ ρ ∈ s

/-! ## The two forms -/

/-- The multiplicity-weighted diagonal form on a window. -/
def diagFormOn (s : Finset Zero) (c d : Zero → ℂ) : ℂ :=
  ∑ ρ ∈ s, (mwt ρ : ℂ) * c ρ * (starRingEnd ℂ) (d ρ)

/-- The functional-equation pairing on a window: each zero couples to its FE
reflection, with its multiplicity as weight. -/
def feFormOn (s : Finset Zero) (c d : Zero → ℂ) : ℂ :=
  ∑ ρ ∈ s, (mwt ρ : ℂ) * c ρ * (starRingEnd ℂ) (d (feReflectZ ρ))

/-- The diagonal form is positive semidefinite outright. -/
theorem diagFormOn_nonneg (s : Finset Zero) (c : Zero → ℂ) :
    0 ≤ (diagFormOn s c c).re := by
  unfold diagFormOn
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun ρ _ => ?_
  rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (mwt_pos ρ).le (Complex.normSq_nonneg _)

/-- **The FE pairing is Hermitian on every FE-closed window** — the global
form of the block Hermitian structure, using the compiled multiplicity
invariance. -/
theorem feFormOn_hermitian {s : Finset Zero} (hs : FEClosed s) (c d : Zero → ℂ) :
    feFormOn s c d = (starRingEnd ℂ) (feFormOn s d c) := by
  unfold feFormOn
  rw [map_sum]
  refine Finset.sum_nbij' (fun ρ => feReflectZ ρ) (fun ρ => feReflectZ ρ)
    (fun ρ hρ => hs ρ hρ) (fun ρ hρ => hs ρ hρ)
    (fun ρ _ => feReflectZ_feReflectZ ρ) (fun ρ _ => feReflectZ_feReflectZ ρ)
    ?_
  intro ρ _
  rw [mwt_feReflectZ, feReflectZ_feReflectZ]
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Complex.conj_ofReal]
  ring

/-- **The generator is self-adjoint for the FE pairing on the actual zero
multiset** — termwise, with no window hypothesis: multiplication by the
spectral coordinate `t_ρ` passes across the pairing because the FE reflection
conjugates the coordinate. -/
theorem feFormOn_theta (s : Finset Zero) (c d : Zero → ℂ) :
    feFormOn s (fun ρ => spectralCoord ρ.val * c ρ) d
      = feFormOn s c (fun ρ => spectralCoord ρ.val * d ρ) := by
  unfold feFormOn
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have ht : (starRingEnd ℂ) (spectralCoord (feReflectZ ρ).val)
      = spectralCoord ρ.val := by
    rw [feReflectZ_val, spectralCoord_feReflect]
    simp
  rw [map_mul, ht]
  ring

/-- On an on-line window the FE pairing **is** the diagonal form. -/
theorem feFormOn_eq_diagFormOn_of_online {s : Finset Zero}
    (hon : ∀ ρ ∈ s, (ρ : Zero).val.re = 1 / 2) (c d : Zero → ℂ) :
    feFormOn s c d = diagFormOn s c d := by
  unfold feFormOn diagFormOn
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hfix : feReflectZ ρ = ρ :=
    Subtype.ext ((feReflect_eq_self_iff ρ.val).mpr (hon ρ hρ))
  rw [hfix]

/-- The hyperbolic witness: at an off-line zero the vector
`e_ρ − e_{ρ*}` has strictly negative FE norm. -/
def offlineWitness (ρ₀ : Zero) : Zero → ℂ :=
  fun ρ => if ρ = ρ₀ then 1 else if ρ = feReflectZ ρ₀ then -1 else 0

/-- **Negative energy at an off-line zero.**  If `ρ₀ ∈ s` is off the line and
`s` is FE-closed, the witness vector has FE norm `−2 m_{ρ₀} < 0`. -/
theorem feFormOn_offlineWitness {s : Finset Zero} (hs : FEClosed s)
    {ρ₀ : Zero} (hρ₀ : ρ₀ ∈ s) (hoff : ρ₀.val.re ≠ 1 / 2) :
    (feFormOn s (offlineWitness ρ₀) (offlineWitness ρ₀)).re = -2 * mwt ρ₀ := by
  have hne : feReflectZ ρ₀ ≠ ρ₀ := by
    intro h
    exact hoff ((feReflect_eq_self_iff ρ₀.val).mp (congrArg Subtype.val h))
  have hpair : ({ρ₀, feReflectZ ρ₀} : Finset Zero) ⊆ s := by
    intro ρ hρ
    rcases Finset.mem_insert.mp hρ with h | h
    · exact h ▸ hρ₀
    · exact (Finset.mem_singleton.mp h) ▸ hs ρ₀ hρ₀
  have hzero : ∀ ρ ∈ s, ρ ∉ ({ρ₀, feReflectZ ρ₀} : Finset Zero) →
      (mwt ρ : ℂ) * offlineWitness ρ₀ ρ
        * (starRingEnd ℂ) (offlineWitness ρ₀ (feReflectZ ρ)) = 0 := by
    intro ρ _ hρ
    have h1 : ρ ≠ ρ₀ := fun h => hρ (by simp [h])
    have h2 : ρ ≠ feReflectZ ρ₀ := fun h => hρ (by simp [h])
    simp [offlineWitness, h1, h2]
  unfold feFormOn
  rw [← Finset.sum_subset hpair hzero]
  rw [Finset.sum_pair hne.symm]
  have hw1 : offlineWitness ρ₀ ρ₀ = 1 := by simp [offlineWitness]
  have hw2 : offlineWitness ρ₀ (feReflectZ ρ₀) = -1 := by
    simp [offlineWitness, hne]
  rw [feReflectZ_feReflectZ, hw1, hw2, mwt_feReflectZ]
  simp
  ring

/-- **The window target, pinned.**  On every FE-closed window, positive
semidefiniteness of the FE pairing is *exactly* the statement that every zero
of the window lies on the critical line. -/
theorem feFormOn_nonneg_iff {s : Finset Zero} (hs : FEClosed s) :
    (∀ c : Zero → ℂ, 0 ≤ (feFormOn s c c).re)
      ↔ ∀ ρ ∈ s, (ρ : Zero).val.re = 1 / 2 := by
  constructor
  · intro hpos ρ₀ hρ₀
    by_contra hoff
    have h := hpos (offlineWitness ρ₀)
    rw [feFormOn_offlineWitness hs hρ₀ hoff] at h
    nlinarith [mwt_pos ρ₀]
  · intro hon c
    rw [feFormOn_eq_diagFormOn_of_online hon]
    exact diagFormOn_nonneg s c

/-- **The global target, pinned: the foliated route's remaining statement as
one compiled proposition.**  The FE polarization is positive semidefinite on
every FE-closed window of the actual zero multiset iff every nontrivial zero
lies on the critical line.

The left side is the definiteness of the Krein polarization for which the
flow generator is self-adjoint (`feFormOn_theta`); nothing here proves it. -/
theorem feForm_global_nonneg_iff :
    (∀ s : Finset Zero, FEClosed s → ∀ c : Zero → ℂ, 0 ≤ (feFormOn s c c).re)
      ↔ ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  constructor
  · intro hpos ρ hρ
    set ρ₀ : Zero := ⟨ρ, hρ⟩
    have hsclosed : FEClosed {ρ₀, feReflectZ ρ₀} := by
      intro σ hσ
      rcases Finset.mem_insert.mp hσ with h | h
      · subst h; simp
      · rw [Finset.mem_singleton.mp h]
        simp [feReflectZ_feReflectZ]
    exact (feFormOn_nonneg_iff hsclosed).mp (hpos _ hsclosed) ρ₀ (by simp)
  · intro hon s _ c
    rw [feFormOn_eq_diagFormOn_of_online (fun ρ _ => hon ρ.val ρ.2)]
    exact diagFormOn_nonneg s c

/-! ## The Hankel bridge

On real-polynomial evaluations in the spectral coordinate, the FE pairing is
the paper's window Hankel quadratic form `Σ_ρ m_ρ P(t_ρ)²` — the object whose
negative inertia is the census `q(W)` (`hp_pencil`, Theorem `thm:inertia`).
The mechanism is one line: real coefficients commute with conjugation, and the
FE reflection conjugates the spectral coordinate. -/

/-- Real-polynomial conjugation commutes with evaluation. -/
theorem conj_aeval_real (P : Polynomial ℝ) (z : ℂ) :
    (starRingEnd ℂ) (Polynomial.aeval z P) = Polynomial.aeval ((starRingEnd ℂ) z) P := by
  have h := Polynomial.aeval_algHom_apply
    (Complex.conjAe.toAlgHom : ℂ →ₐ[ℝ] ℂ) z P
  simpa using h.symm

/-- Evaluation of a real polynomial in the spectral coordinate. -/
def polyEval (P : Polynomial ℝ) : Zero → ℂ :=
  fun ρ => Polynomial.aeval (spectralCoord ρ.val) P

/-- **The Hankel bridge**: the FE-pairing energy of a real-polynomial
evaluation is the multiplicity-weighted sum of squares `Σ_ρ m_ρ P(t_ρ)²` —
the window Hankel form of the pencil paper, with no conjugation left. -/
theorem feFormOn_polyEval (s : Finset Zero) (P : Polynomial ℝ) :
    feFormOn s (polyEval P) (polyEval P)
      = ∑ ρ ∈ s, (mwt ρ : ℂ) * (Polynomial.aeval (spectralCoord ρ.val) P) ^ 2 := by
  unfold feFormOn polyEval
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [feReflectZ_val, spectralCoord_feReflect, ← conj_aeval_real,
    Complex.conj_conj]
  ring

/-- The FE-pairing self-energy is real on FE-closed windows. -/
theorem feFormOn_self_im_zero {s : Finset Zero} (hs : FEClosed s) (c : Zero → ℂ) :
    (feFormOn s c c).im = 0 := by
  have h := feFormOn_hermitian hs c c
  exact Complex.conj_eq_iff_im.mp h.symm

/-! ## The negative family: the informative half of the Pontryagin lever

One witness vector per off-line reflection pair, pairwise `feFormOn`-orthogonal
and strictly negative.  This is the `q ≤ κ` direction: every off-line pair
contributes an independent negative direction, so any *external* upper bound
on the number of pairwise-orthogonal negative directions of the FE pairing
bounds the off-line census — and a bound of zero is the critical line. -/

/-- Distinct off-line reflection orbits have disjoint witness supports, so the
witnesses are `feFormOn`-orthogonal. -/
theorem feFormOn_offlineWitness_orthogonal {s : Finset Zero}
    {ρ σ : Zero} (hρσ : ρ ≠ σ) (hσρ : σ ≠ feReflectZ ρ) :
    feFormOn s (offlineWitness ρ) (offlineWitness σ) = 0 := by
  have hd1 : feReflectZ ρ ≠ σ := fun h => hσρ h.symm
  have hd2 : feReflectZ ρ ≠ feReflectZ σ := fun h =>
    hρσ (by simpa using congrArg feReflectZ h)
  have hd3 : ρ ≠ feReflectZ σ := fun h =>
    hσρ (by simpa using (congrArg feReflectZ h).symm)
  unfold feFormOn
  refine Finset.sum_eq_zero fun τ _ => ?_
  by_cases h1 : τ = ρ
  · subst h1
    simp [offlineWitness, hd1, hd2]
  · by_cases h2 : τ = feReflectZ ρ
    · subst h2
      simp [offlineWitness, feReflectZ_feReflectZ, hρσ, hd3]
    · simp [offlineWitness, h1, h2]

/-- **The negative family.**  For any set `R` of off-line orbit
representatives inside an FE-closed window (one zero per reflection pair,
`hrep`), the witness vectors are strictly negative and pairwise orthogonal
for the FE pairing.  Consequently every off-line pair contributes an
independent negative square: the census `q` is a lower bound for the
polarization's negative index. -/
theorem feFormOn_negFamily {s : Finset Zero} (hs : FEClosed s)
    {R : Finset Zero} (hR : R ⊆ s)
    (hoff : ∀ ρ ∈ R, (ρ : Zero).val.re ≠ 1 / 2)
    (hrep : ∀ ρ ∈ R, ∀ σ ∈ R, ρ ≠ σ → σ ≠ feReflectZ ρ) :
    (∀ ρ ∈ R, (feFormOn s (offlineWitness ρ) (offlineWitness ρ)).re < 0) ∧
    (∀ ρ ∈ R, ∀ σ ∈ R, ρ ≠ σ →
      feFormOn s (offlineWitness ρ) (offlineWitness σ) = 0) := by
  constructor
  · intro ρ hρ
    rw [feFormOn_offlineWitness hs (hR hρ) (hoff ρ hρ)]
    nlinarith [mwt_pos ρ]
  · intro ρ hρ σ hσ hne
    exact feFormOn_offlineWitness_orthogonal hne (hrep ρ hρ σ hσ hne)

end CriticalLinePhasor.FoliatedGlobalPolarization

section AxiomAudit
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_conj
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_feReflect
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.feFormOn_hermitian
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.feFormOn_theta
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.feFormOn_nonneg_iff
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.feForm_global_nonneg_iff
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.feFormOn_polyEval
#print axioms CriticalLinePhasor.FoliatedGlobalPolarization.feFormOn_negFamily
end AxiomAudit
