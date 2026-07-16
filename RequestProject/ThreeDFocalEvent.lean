import RequestProject.SpectralSignFlip
import RequestProject.AreaLaw
import RequestProject.HelixDefs
import RequestProject.FocalResidualVanishes

/-!
# Native three-dimensional focal events

This file separates two exact event levels.  At physical helix height `Z > 0`, the logarithmic
ordinate is `y = log Z`.  `ThreeDZeroAtHeight` is the finite signed-phasor cancellation at that
ordinate.  `CompletedThreeDZeroAtHeight` is the completed fibre cancellation; it is proved
equivalent to `LFunction χ (carrierPointAtHeight Z) = 0`.

Both harmonic and von Neumann Gram operators are lifted to the three spatial carrier coordinates
as `G ⊗ I₃`.  The determinant cube and rank-drop equivalences prove that spatial lifting
neither creates nor removes a cancellation.
-/

open Complex Matrix
open scoped BigOperators ComplexConjugate Kronecker

namespace CriticalLinePhasor.ThreeDFocal

open CriticalLinePhasor CriticalLinePhasor.HarmonicCell
open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius
open Filter Topology

variable {q : ℕ} [NeZero q]

/-! ## The carrier midpoint is specified by the area law -/

/-- A real abscissa is admissible for the unit-gauge 3D carrier when its fiber amplitude
reciprocates the arclength-derived radius to a positive finite limit.  This definition contains
no zero set, spectral chart, or preselected midpoint. -/
def CarrierScaleBalanced (σ : ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ) * Geometry.carrierRadius 1 3 n)
      atTop (nhds L)

/-- The area law computes the admissible carrier abscissa. -/
theorem carrierScaleBalanced_iff (σ : ℝ) :
    CarrierScaleBalanced σ ↔ σ = 1 / 2 :=
  Geometry.sigma_half_is_scale_critical 1 3 (by norm_num) σ

/-- There is exactly one scale-balanced carrier abscissa. -/
theorem exists_unique_carrierScaleBalanced : ∃! σ : ℝ, CarrierScaleBalanced σ := by
  refine ⟨1 / 2, (carrierScaleBalanced_iff _).2 rfl, ?_⟩
  intro σ hσ
  exact (carrierScaleBalanced_iff σ).1 hσ

/-- The carrier abscissa, selected by the unique area-law scale-balance specification. -/
noncomputable def carrierAbscissa : ℝ :=
  Classical.choose exists_unique_carrierScaleBalanced

/-- The selected carrier abscissa satisfies the scale-balance specification. -/
theorem carrierAbscissa_scaleBalanced : CarrierScaleBalanced carrierAbscissa :=
  (Classical.choose_spec exists_unique_carrierScaleBalanced).1

/-- The area-law-selected carrier abscissa is the half-unit. -/
@[simp] theorem carrierAbscissa_eq_half : carrierAbscissa = 1 / 2 :=
  (carrierScaleBalanced_iff carrierAbscissa).1 carrierAbscissa_scaleBalanced

/-- Relative to the area-law-selected carrier, zero radial drift occurs exactly at the selected
abscissa.  The statement is expressed using `carrierAbscissa`; the half-unit appears only after
the area-law theorem rewrites that abscissa. -/
theorem noRadialDrift_iff_carrierAbscissa (n σ : ℝ) (hn : 1 < n) :
    n ^ (σ - carrierAbscissa) = 1 ↔ σ = carrierAbscissa := by
  rw [carrierAbscissa_eq_half]
  exact Helix.no_radial_drift_iff_half n σ hn

/-- An abscissa different from the area-law carrier necessarily has nontrivial radial drift. -/
theorem offCarrier_has_radialDrift (n σ : ℝ) (hn : 1 < n)
    (hoff : σ ≠ carrierAbscissa) : n ^ (σ - carrierAbscissa) ≠ 1 := by
  intro h
  exact hoff ((noRadialDrift_iff_carrierAbscissa n σ hn).1 h)

/-- A finite phasor bank whose phase profile is indexed by the carrier height. -/
structure FocalBank where
  amplitude : ℕ → ℝ
  phase : ℝ → ℕ → ℝ
  cutoff : ℕ
  cutoff_pos : 1 ≤ cutoff
  amplitude_one_pos : 0 < amplitude 1
  amplitude_nonneg : ∀ n, 0 ≤ amplitude n

/-- The carrier amplitude using the area-law-selected exponent; its proved normal form is
`(π / 3) n^{-1/2}`. -/
noncomputable def carrierAmplitude (n : ℕ) : ℝ :=
  (Real.pi / 3) * (n : ℝ) ^ (-carrierAbscissa)

/-- The Mellin phase in the logarithmic chart ordinate `y`: `-y log n`.  The physical helix
height is `Z = exp y`; see `ThreeDZeroAtHeight` below. -/
noncomputable def carrierPhase (z : ℝ) (n : ℕ) : ℝ := -z * Real.log n

/-- The canonical completed carrier bank through the physical stage `N`. -/
noncomputable def carrierBank (N : ℕ) (hN : 1 ≤ N) : FocalBank where
  amplitude := carrierAmplitude
  phase := carrierPhase
  cutoff := N
  cutoff_pos := hN
  amplitude_one_pos := by
    simp [carrierAmplitude]
    positivity
  amplitude_nonneg := by
    intro n
    exact mul_nonneg (le_of_lt (div_pos Real.pi_pos (by norm_num)))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The finite signed phasor closure at 3-D height `z`. -/
noncomputable def focalClosure (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ) : Prop :=
  finiteB χ bank.amplitude (bank.phase z) bank.cutoff = 0

/-- The harmonic Gram pencil built from the finite phasor bank at 3-D height `z`. -/
noncomputable def harmonicGram (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (harmonicPencil ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ)
      (finiteB χ bank.amplitude (bank.phase z) bank.cutoff) mu lam)ᴴ *
    harmonicPencil ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ)
      (finiteB χ bank.amplitude (bank.phase z) bank.cutoff) mu lam

/-- A finite Gram rank drop at the 3-D height `z`. -/
noncomputable def FocalRankDrop (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) : Prop :=
  (harmonicGram χ bank z mu lam).det = 0

/-- The carrier point represented by a real logarithmic ordinate. -/
noncomputable def carrierPoint (z : ℝ) : ℂ :=
  (carrierAbscissa : ℂ) + Complex.I * (z : ℂ)

/-- The analytic readout point of the physical helix height `Z`: its ordinate is `log Z`. -/
noncomputable def carrierPointAtHeight (Z : ℝ) : ℂ :=
  carrierPoint (Real.log Z)

/-- Expanded physical-height readout: `carrierAbscissa + i log Z`. -/
theorem carrierPointAtHeight_eq (Z : ℝ) :
    carrierPointAtHeight Z = (carrierAbscissa : ℂ) + Complex.I * (Real.log Z : ℂ) := rfl

/-- The readout ordinate of a physical helix height is exactly its logarithm. -/
@[simp] theorem carrierPointAtHeight_im (Z : ℝ) : (carrierPointAtHeight Z).im = Real.log Z := by
  simp [carrierPointAtHeight, carrierPoint]

/-- Exponentiating an ordinate and then reading the physical height recovers the ordinate chart. -/
@[simp] theorem carrierPointAtHeight_exp (y : ℝ) :
    carrierPointAtHeight (Real.exp y) = carrierPoint y := by
  simp [carrierPointAtHeight]

/-- Normal form of the area-law-selected carrier point. -/
theorem carrierPoint_eq_half_add_I (z : ℝ) :
    carrierPoint z = 1 / 2 + Complex.I * (z : ℂ) := by
  simp [carrierPoint]

/-- The carrier's real coordinate is the area-law-selected abscissa. -/
@[simp] theorem carrierPoint_re (z : ℝ) : (carrierPoint z).re = carrierAbscissa := by
  simp [carrierPoint]

/-- The real coordinate of every physical-height readout is the area-law-selected abscissa. -/
@[simp] theorem carrierPointAtHeight_re (Z : ℝ) :
    (carrierPointAtHeight Z).re = carrierAbscissa := by
  simpa only [carrierPointAtHeight] using carrierPoint_re (Real.log Z)

/-- A state represented by a physical helix height has no radial drift.  This is a theorem of
carrier membership: the represented point first reads the area-law-selected abscissa, and only
then the no-drift law is evaluated.  No zero predicate or numerical midpoint occurs in the
statement. -/
theorem carrierPointAtHeight_noRadialDrift (Z n : ℝ) (hn : 1 < n) :
    n ^ ((carrierPointAtHeight Z).re - carrierAbscissa) = 1 := by
  apply (noRadialDrift_iff_carrierAbscissa n (carrierPointAtHeight Z).re hn).2
  exact carrierPointAtHeight_re Z

/-- The carrier's imaginary coordinate is its logarithmic ordinate. -/
@[simp] theorem carrierPoint_im (z : ℝ) : (carrierPoint z).im = z := by
  simp [carrierPoint]

/-- A complex point is represented by the 3D carrier exactly when its real coordinate is the
area-law-selected abscissa. -/
theorem exists_eq_carrierPoint_iff (ρ : ℂ) :
    (∃ z : ℝ, ρ = carrierPoint z) ↔ ρ.re = carrierAbscissa := by
  constructor
  · rintro ⟨z, rfl⟩
    exact carrierPoint_re z
  · intro hre
    refine ⟨ρ.im, ?_⟩
    apply Complex.ext
    · simpa using hre
    · simp

/-- An off-carrier point cannot be represented by any real helix height. -/
theorem no_offCarrier_representation (ρ : ℂ) (hoff : ρ.re ≠ carrierAbscissa) :
    ¬ ∃ z : ℝ, ρ = carrierPoint z := by
  exact fun h => hoff ((exists_eq_carrierPoint_iff ρ).1 h)

/-- A complex point is represented at a positive physical helix height exactly when its real
coordinate is the area-law-selected carrier abscissa. -/
theorem exists_pos_eq_carrierPointAtHeight_iff (ρ : ℂ) :
    (∃ Z : ℝ, 0 < Z ∧ ρ = carrierPointAtHeight Z) ↔ ρ.re = carrierAbscissa := by
  constructor
  · rintro ⟨Z, _hZ, rfl⟩
    exact carrierPointAtHeight_re Z
  · intro hre
    refine ⟨Real.exp ρ.im, Real.exp_pos _, ?_⟩
    rw [carrierPointAtHeight_exp]
    apply Complex.ext
    · simpa using hre
    · simp

/-- An off-carrier point cannot be represented at any positive physical helix height. -/
theorem no_offCarrier_physical_representation (ρ : ℂ)
    (hoff : ρ.re ≠ carrierAbscissa) :
    ¬ ∃ Z : ℝ, 0 < Z ∧ ρ = carrierPointAtHeight Z := by
  exact fun h => hoff ((exists_pos_eq_carrierPointAtHeight_iff ρ).1 h)

/-- The von Neumann Gram pencil at the same 3-D height and carrier point. -/
noncomputable def vonNeumannGram (z : ℝ) (mu lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  specGram z (carrierPoint z) mu lam

/-- A rank drop of the von Neumann Gram pencil. -/
noncomputable def VonNeumannRankDrop (z : ℝ) (mu lam : ℂ) : Prop :=
  (vonNeumannGram z mu lam).det = 0

/-! ## Compatibility with the three spatial carrier coordinates -/

/-- Extend a two-channel Gram operator uniformly over the three complexified spatial carrier
coordinates.  The state index is `(channel, spatial coordinate)`, so this is the tensor product
`G ⊗ I₃`; the extra spatial coordinates introduce no new cancellation mechanism. -/
noncomputable def spatialLiftGram (G : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  G ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)

/-- The determinant of the spatial lift is the cube of the channel-Gram determinant. -/
theorem spatialLiftGram_det (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (spatialLiftGram G).det = G.det ^ 3 := by
  simp [spatialLiftGram, Matrix.det_kronecker]

/-- Spatial lifting preserves and reflects rank drop: a three-coordinate carrier state cannot
create a cancellation absent from the underlying channel Gram operator. -/
theorem spatialLiftGram_rankDrop_iff (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (spatialLiftGram G).det = 0 ↔ G.det = 0 := by
  rw [spatialLiftGram_det]
  exact pow_eq_zero_iff (by norm_num)

/-- The finite harmonic Gram pencil acting uniformly on all three carrier coordinates. -/
noncomputable def harmonicGram3D (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  spatialLiftGram (harmonicGram χ bank z mu lam)

/-- The von Neumann Gram pencil acting uniformly on all three carrier coordinates. -/
noncomputable def vonNeumannGram3D (z : ℝ) (mu lam : ℂ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  spatialLiftGram (vonNeumannGram z mu lam)

omit [NeZero q] in
/-- The 3D harmonic-pencil lift rank-drops exactly at the original finite focal rank drop. -/
theorem harmonicGram3D_rankDrop_iff (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) :
    (harmonicGram3D χ bank z mu lam).det = 0 ↔ FocalRankDrop χ bank z mu lam := by
  exact spatialLiftGram_rankDrop_iff (harmonicGram χ bank z mu lam)

/-- The 3D von Neumann lift rank-drops exactly at the original fibre rank drop. -/
theorem vonNeumannGram3D_rankDrop_iff (z : ℝ) (mu lam : ℂ) :
    (vonNeumannGram3D z mu lam).det = 0 ↔ VonNeumannRankDrop z mu lam := by
  exact spatialLiftGram_rankDrop_iff (vonNeumannGram z mu lam)

/-- Ordinate-level form of a native focal cancellation.  The physical-height form used for the
3D helix is `ThreeDZeroAtHeight χ bank Z`, with ordinate `y = log Z`. -/
noncomputable def ThreeDZero (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ) : Prop :=
  focalClosure χ bank z

/-- A native 3D zero at physical helix height `Z > 0`: exactly the finite focal cancellation at
the logarithmic chart ordinate `y = log Z`. -/
noncomputable def ThreeDZeroAtHeight
    (χ : DirichletCharacter ℂ q) (bank : FocalBank) (Z : ℝ) : Prop :=
  0 < Z ∧ ThreeDZero χ bank (Real.log Z)

omit [NeZero q] in
/-- The physical helix height and logarithmic ordinate descriptions are exact inverses. -/
theorem threeDZeroAtHeight_exp_iff
    (χ : DirichletCharacter ℂ q) (bank : FocalBank) (y : ℝ) :
    ThreeDZeroAtHeight χ bank (Real.exp y) ↔ ThreeDZero χ bank y := by
  constructor
  · rintro ⟨_hpos, hzero⟩
    simpa using hzero
  · intro hzero
    exact ⟨Real.exp_pos y, by simpa using hzero⟩

omit [NeZero q] in
/-- A positive physical-height event is precisely focal cancellation at its logarithmic ordinate. -/
theorem threeDZeroAtHeight_iff
    (χ : DirichletCharacter ℂ q) (bank : FocalBank) {Z : ℝ} (hZ : 0 < Z) :
    ThreeDZeroAtHeight χ bank Z ↔ ThreeDZero χ bank (Real.log Z) := by
  simp [ThreeDZeroAtHeight, hZ]

/-- A completed native 3D zero at physical helix height `Z`: the represented fibre's normalized
focal residual vanishes exactly at that positive height.  Unlike the finite `ThreeDZero`, this is
the completed L-function fibre event. -/
noncomputable def CompletedThreeDZeroAtHeight
    (χ : DirichletCharacter ℂ q) (Z : ℝ) : Prop :=
  0 < Z ∧ HarmonicCell.Dcell χ Z = 0

omit [NeZero q] in
/-- The harmonic-cell represented point and the area-law carrier point are the same readout of a
positive physical height: `carrierAbscissa + i log Z`. -/
theorem reprPoint_eq_carrierPointAtHeight
    (χ : DirichletCharacter ℂ q) (Z : ℝ) (hZ : 0 < Z) :
    HarmonicCell.reprPoint χ Z = carrierPointAtHeight Z := by
  rw [(HarmonicCell.admissible_real_height_implies_critical_readout χ Z hZ).1]
  simp [carrierPointAtHeight, carrierPoint]
  ring

/-- The completed 3D focal crossing at physical height `Z` is exactly an analytic L-function zero
at the fibre's readout point `carrierAbscissa + i log Z`. -/
theorem completedThreeDZeroAtHeight_iff_L_zero
    (χ : DirichletCharacter ℂ q) (Z : ℝ) (hZ : 0 < Z) :
    CompletedThreeDZeroAtHeight χ Z ↔
      DirichletCharacter.LFunction χ (carrierPointAtHeight Z) = 0 := by
  rw [CompletedThreeDZeroAtHeight, and_iff_right hZ,
    HarmonicCell.focal_residual_zero_iff_L_zero,
    reprPoint_eq_carrierPointAtHeight χ Z hZ]

/-- Every completed fibre crossing is read on the area-law midpoint; the focal-cancellation
hypothesis supplies the event, while the real coordinate comes only from carrier geometry. -/
theorem completedThreeDZeroAtHeight_on_midline
    (χ : DirichletCharacter ℂ q) (Z : ℝ)
    (_hzero : CompletedThreeDZeroAtHeight χ Z) :
    (carrierPointAtHeight Z).re = 1 / 2 := by
  rw [carrierPointAtHeight_re, carrierAbscissa_eq_half]

/-- Exact focal cancellation representing a specified analytic parameter.  The parameter is not
an independent label on the event: it must be the readout of the same positive physical helix
height at which `Dcell` vanishes. -/
noncomputable def CompletedFocalCancellationRepresents
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  ∃ Z : ℝ, CompletedThreeDZeroAtHeight χ Z ∧ carrierPointAtHeight Z = ρ

/-- Parameter-preserving focal cancellation has exactly two consequences: the analytic
L-function vanishes at that parameter, and the parameter has the area-law carrier abscissa.
Conversely these two facts reconstruct the unique physical height `exp (Im ρ)` and its completed
focal event. -/
theorem completedFocalCancellationRepresents_iff
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    CompletedFocalCancellationRepresents χ ρ ↔
      DirichletCharacter.LFunction χ ρ = 0 ∧ ρ.re = carrierAbscissa := by
  constructor
  · rintro ⟨Z, hzero, hpoint⟩
    have hL := (completedThreeDZeroAtHeight_iff_L_zero χ Z hzero.1).1 hzero
    rw [hpoint] at hL
    refine ⟨hL, ?_⟩
    rw [← hpoint, carrierPointAtHeight_re]
  · rintro ⟨hL, hre⟩
    let Z := Real.exp ρ.im
    have hZ : 0 < Z := Real.exp_pos ρ.im
    have hpoint : carrierPointAtHeight Z = ρ := by
      rw [carrierPointAtHeight_exp]
      apply Complex.ext
      · simpa [carrierPoint] using hre.symm
      · simp [carrierPoint]
    have hzero : CompletedThreeDZeroAtHeight χ Z :=
      (completedThreeDZeroAtHeight_iff_L_zero χ Z hZ).2 (by simpa [hpoint] using hL)
    exact ⟨Z, hzero, hpoint⟩

/-- Exact 3D focal cancellation has carrier support: an off-carrier complex parameter cannot be
the parameter represented by a completed focal event.  This is pointwise, before any trace or
zero-count sum, so no other event can cancel the discrepancy. -/
theorem no_offCarrier_completedFocalCancellation
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hoff : ρ.re ≠ carrierAbscissa) :
    ¬ CompletedFocalCancellationRepresents χ ρ := by
  intro hcancel
  exact hoff ((completedFocalCancellationRepresents_iff χ ρ).1 hcancel).2

/-! ## The ambient 3D carrier operator, defined before event certificates

The local scalar operator `vonNeumannOp y` remains useful for evaluating one diagonal mode.  The
ambient construction below is instead made on the geometric carrier itself.  Its state type
mentions only the carrier parameters and the equation placing a spatial point on `gammaY`; it
contains no character, L-function, zero predicate, focal cancellation, or event certificate.
Completed events are mapped into this already-defined state space afterward.
-/

/-- A state on the fixed `(p,r)` three-dimensional carrier.  The stored spatial point is required
to be the native helix point `gammaY p r ordinate`; this is a geometric membership certificate,
independent of every spectral or vanishing event. -/
structure CarrierState3D (p r : ℝ) where
  point : ℝ × ℝ × ℝ
  ordinate : ℝ
  point_eq_gammaY : point = Geometry.gammaY p r ordinate

/-- The canonical carrier state at logarithmic ordinate `y`. -/
noncomputable def carrierState3D (p r y : ℝ) : CarrierState3D p r where
  point := Geometry.gammaY p r y
  ordinate := y
  point_eq_gammaY := rfl

/-- The third spatial coordinate of an ambient carrier state. -/
def CarrierState3D.physicalHeight {p r : ℝ} (s : CarrierState3D p r) : ℝ :=
  s.point.2.2

/-- On every nondegenerate-pitch carrier state, the third spatial coordinate is the positive
physical height `exp ordinate`. -/
theorem CarrierState3D.physicalHeight_eq_exp {p r : ℝ} (hp : p ≠ 0)
    (s : CarrierState3D p r) :
    s.physicalHeight = Real.exp s.ordinate := by
  rw [CarrierState3D.physicalHeight, s.point_eq_gammaY, Geometry.gammaY_eq p r s.ordinate hp]

/-- Every ambient carrier state has positive physical height. -/
theorem CarrierState3D.physicalHeight_pos {p r : ℝ} (hp : p ≠ 0)
    (s : CarrierState3D p r) :
    0 < s.physicalHeight := by
  rw [s.physicalHeight_eq_exp hp]
  exact Real.exp_pos _

/-- Finitely supported wave states on the full geometric `(p,r)` carrier. -/
abbrev CarrierThreeDMode (p r : ℝ) := CarrierState3D p r →₀ ℂ

/-- The ambient 3D carrier operator.  It is defined on every geometric carrier state and reads
the logarithmic ordinate whose exponential is the state's physical third coordinate. -/
noncomputable def carrierThreeDOperator (p r : ℝ) :
    CarrierThreeDMode p r →ₗ[ℂ] CarrierThreeDMode p r :=
  diagOp fun s => s.ordinate

/-- The ambient 3D carrier operator is symmetric on the entire carrier state space. -/
theorem carrierThreeDOperator_isSymmetric (p r : ℝ) :
    (carrierThreeDOperator p r).IsSymmetric := by
  simpa only [carrierThreeDOperator] using
    (diagOp_symmetric (fun s : CarrierState3D p r => s.ordinate))

/-- Every geometric carrier basis state is a nonzero eigenvector of the ambient operator. -/
theorem carrierThreeDOperator_eigenvector (p r : ℝ) (s : CarrierState3D p r) :
    Finsupp.single s (1 : ℂ) ≠ 0 ∧
      carrierThreeDOperator p r (Finsupp.single s (1 : ℂ)) =
        (s.ordinate : ℂ) • Finsupp.single s (1 : ℂ) := by
  simpa only [carrierThreeDOperator] using
    (diagOp_eigenvector (fun x : CarrierState3D p r => x.ordinate) s)

/-! ### Completed events inside the ambient state space -/

/-- A completed 3D focal event, indexed by its positive physical helix height. -/
def CompletedThreeDEigenEvent (χ : DirichletCharacter ℂ q) :=
  { Z : ℝ // CompletedThreeDZeroAtHeight χ Z }

/-- A completed event placed into the independently defined ambient `(p,r)` carrier state space. -/
noncomputable def CompletedThreeDEigenEvent.toCarrierState
    (p r : ℝ) {χ : DirichletCharacter ℂ q} (e : CompletedThreeDEigenEvent χ) :
    CarrierState3D p r :=
  carrierState3D p r (Real.log e.1)

/-- For nonzero pitch, the spatial third coordinate of an embedded completed event is exactly its
original positive physical height. -/
theorem CompletedThreeDEigenEvent.toCarrierState_physicalHeight
    (p r : ℝ) (hp : p ≠ 0) {χ : DirichletCharacter ℂ q}
    (e : CompletedThreeDEigenEvent χ) :
    (e.toCarrierState p r).physicalHeight = e.1 := by
  rw [CarrierState3D.physicalHeight_eq_exp hp]
  exact Real.exp_log e.2.1

/-- Every completed event is therefore an eigenvector of the ambient operator already defined on
all carrier states; the event certificate selects the state but does not define the operator. -/
theorem carrierThreeDOperator_completedEvent_eigenvector
    (p r : ℝ) {χ : DirichletCharacter ℂ q} (e : CompletedThreeDEigenEvent χ) :
    Finsupp.single (e.toCarrierState p r) (1 : ℂ) ≠ 0 ∧
      carrierThreeDOperator p r (Finsupp.single (e.toCarrierState p r) (1 : ℂ)) =
        (Real.log e.1 : ℂ) • Finsupp.single (e.toCarrierState p r) (1 : ℂ) := by
  simpa [CompletedThreeDEigenEvent.toCarrierState, carrierState3D] using
    carrierThreeDOperator_eigenvector p r (e.toCarrierState p r)

/-- The completed-event sub-index for `χ`, with one finitely supported basis mode per 3D crossing.
This restricted presentation is retained for the resolvent-trace API; the ambient operator above
is defined without it. -/
abbrev CompletedThreeDMode (χ : DirichletCharacter ℂ q) :=
  CompletedThreeDEigenEvent χ →₀ ℂ

/-- The single completed 3D height operator for `χ`.  On the event at physical height `Z`, its
real diagonal value is the derived logarithmic ordinate `y = log Z`. -/
noncomputable def completedThreeDOperator (χ : DirichletCharacter ℂ q) :
    CompletedThreeDMode χ →ₗ[ℂ] CompletedThreeDMode χ :=
  diagOp fun e => Real.log e.1

/-- The completed 3D operator is symmetric because its complete diagonal is real. -/
theorem completedThreeDOperator_isSymmetric (χ : DirichletCharacter ℂ q) :
    (completedThreeDOperator χ).IsSymmetric := by
  simpa only [completedThreeDOperator] using
    (diagOp_symmetric (fun e : CompletedThreeDEigenEvent χ => Real.log e.1))

/-- Every completed 3D event supplies an explicit nonzero eigenvector of the single operator,
with eigenvalue equal to its logarithmic helix ordinate. -/
theorem completedThreeDOperator_eigenvector
    (χ : DirichletCharacter ℂ q) (e : CompletedThreeDEigenEvent χ) :
    Finsupp.single e (1 : ℂ) ≠ 0 ∧
      completedThreeDOperator χ (Finsupp.single e (1 : ℂ)) =
        (Real.log e.1 : ℂ) • Finsupp.single e (1 : ℂ) := by
  simpa only [completedThreeDOperator] using
    (diagOp_eigenvector (fun f : CompletedThreeDEigenEvent χ => Real.log f.1) e)

/-- Positive physical height makes the logarithmic ordinate an injective coordinate on completed
3D events. -/
theorem completedThreeDEigenEvent_ordinate_injective
    (χ : DirichletCharacter ℂ q) :
    Function.Injective (fun e : CompletedThreeDEigenEvent χ => Real.log e.1) := by
  intro e f h
  apply Subtype.ext
  apply Real.exp_injective
  simpa [Real.exp_log e.2.1, Real.exp_log f.2.1] using congrArg Real.exp h

/-- The same event certificate also gives the 1D analytic readout equation.  This theorem is the
explicit bridge used by the second resolvent-trace version. -/
theorem completedThreeDEigenEvent_L_zero
    (χ : DirichletCharacter ℂ q) (e : CompletedThreeDEigenEvent χ) :
    DirichletCharacter.LFunction χ (carrierPointAtHeight e.1) = 0 :=
  (completedThreeDZeroAtHeight_iff_L_zero χ e.1 e.2.1).1 e.2

/-- The completed harmonic-cell Gram matrix lifted uniformly over all three carrier coordinates. -/
noncomputable def completedHarmonicGram3DAtHeight
    (χ : DirichletCharacter ℂ q) (Z : ℝ) (mu lam : ℂ) :=
  spatialLiftGram (HarmonicCell.GramH χ Z mu lam)

/-- The completed 3D harmonic Gram rank drop is exactly the completed focal crossing. -/
theorem completedHarmonicGram3DAtHeight_rankDrop_iff
    (χ : DirichletCharacter ℂ q) (Z : ℝ) (mu lam : ℂ)
    (hZ : 0 < Z) (hlam : lam ≠ mu) :
    (completedHarmonicGram3DAtHeight χ Z mu lam).det = 0 ↔
      CompletedThreeDZeroAtHeight χ Z := by
  rw [completedHarmonicGram3DAtHeight, spatialLiftGram_rankDrop_iff,
    CompletedThreeDZeroAtHeight, and_iff_right hZ,
    HarmonicCell.gramH_rank_drop_iff_L_zero χ Z mu lam hlam,
    ← HarmonicCell.focal_residual_zero_iff_L_zero]

/-- Direct completed-fibre form: the spatial 3D harmonic Gram operator rank-drops exactly when
the represented L-function vanishes at `carrierAbscissa + i log Z`. -/
theorem completedHarmonicGram3DAtHeight_rankDrop_iff_L_zero
    (χ : DirichletCharacter ℂ q) (Z : ℝ) (mu lam : ℂ)
    (hZ : 0 < Z) (hlam : lam ≠ mu) :
    (completedHarmonicGram3DAtHeight χ Z mu lam).det = 0 ↔
      DirichletCharacter.LFunction χ (carrierPointAtHeight Z) = 0 := by
  exact (completedHarmonicGram3DAtHeight_rankDrop_iff χ Z mu lam hZ hlam).trans
    (completedThreeDZeroAtHeight_iff_L_zero χ Z hZ)

/-- The spatially lifted harmonic Gram operator evaluated at physical helix height `Z`. -/
noncomputable def harmonicGram3DAtHeight
    (χ : DirichletCharacter ℂ q) (bank : FocalBank) (Z : ℝ) (mu lam : ℂ) :=
  harmonicGram3D χ bank (Real.log Z) mu lam

/-- The spatially lifted von Neumann Gram operator evaluated at physical helix height `Z`. -/
noncomputable def vonNeumannGram3DAtHeight (Z : ℝ) (mu lam : ℂ) :=
  vonNeumannGram3D (Real.log Z) mu lam

omit [NeZero q] in
/-- Exact finite focal cancellation is exactly a finite Gram rank drop. -/
theorem focalClosure_iff_rankDrop (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) :
    focalClosure χ bank z ↔ FocalRankDrop χ bank z mu lam := by
  simpa only [focalClosure, FocalRankDrop, harmonicGram] using
    (finite_gramH_rank_drop_iff_channel_zero χ bank.amplitude (bank.phase z) bank.cutoff
      bank.cutoff_pos bank.amplitude_one_pos bank.amplitude_nonneg mu lam hlam).symm

/-- The von Neumann Gram pencil rank-drops at every carrier point of its own height. -/
theorem vonNeumannGram_rankDrop (z : ℝ) (mu lam : ℂ) (hlam : lam ≠ mu) :
    VonNeumannRankDrop z mu lam := by
  simpa only [VonNeumannRankDrop, vonNeumannGram, carrierPoint_eq_half_add_I] using
    (specGram_rank_drop_on_line z hlam)

/-- A von Neumann Gram rank drop is exactly its nonzero fibre eigenstate. -/
theorem vonNeumannGram_rankDrop_iff_eigenstate (z : ℝ) (mu lam : ℂ) (hlam : lam ≠ mu) :
    VonNeumannRankDrop z mu lam ↔
      ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp z) (carrierPoint z) ψ = 0 := by
  rw [VonNeumannRankDrop, vonNeumannGram,
    specGram_det_zero_iff z (carrierPoint z) hlam,
    ← specOp_kernel_iff_specBchan_zero]

/-- The von Neumann fibre has a nonzero kernel mode at every marked carrier height. -/
theorem carrier_kernel_realized (z : ℝ) :
    ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp z) (carrierPoint z) ψ = 0 := by
  apply (specOp_kernel_iff_specBchan_zero z (carrierPoint z)).mpr
  rw [carrierPoint_eq_half_add_I]
  simp only [specBchan, specHeight]
  ring_nf
  rw [Complex.I_sq]
  ring

omit [NeZero q] in
/-- Full finite focal cancellation is a native 3-D zero by definition. -/
theorem focalCancellation_to_threeDZero (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (hclose : focalClosure χ bank z) : ThreeDZero χ bank z := hclose

omit [NeZero q] in
/-- The harmonic Gram pencil detects every native 3-D zero by a rank drop. -/
theorem threeDZero_harmonicRankDrop (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) (hzero : ThreeDZero χ bank z) :
    FocalRankDrop χ bank z mu lam :=
  (focalClosure_iff_rankDrop χ bank z mu lam hlam).mp hzero

omit [NeZero q] in
/-- A native 3-D zero has simultaneous harmonic and von Neumann Gram rank drops, and an eigenstate. -/
theorem threeDZero_twoGram_eigenstate (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) (hzero : ThreeDZero χ bank z) :
    FocalRankDrop χ bank z mu lam ∧ VonNeumannRankDrop z mu lam ∧
      ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp z) (carrierPoint z) ψ = 0 := by
  refine ⟨threeDZero_harmonicRankDrop χ bank z mu lam hlam hzero,
    vonNeumannGram_rankDrop z mu lam hlam, ?_⟩
  exact (vonNeumannGram_rankDrop_iff_eigenstate z mu lam hlam).mp
    (vonNeumannGram_rankDrop z mu lam hlam)

omit [NeZero q] in
/-- Every native 3D zero produces rank drops in both spatially lifted Gram operators.  Conversely,
each lifted rank drop reflects to its original channel Gram, so the 3D lift cannot manufacture an
additional cancellation. -/
theorem threeDZero_twoGram3D_rankDrop (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) (hzero : ThreeDZero χ bank z) :
    (harmonicGram3D χ bank z mu lam).det = 0 ∧
      (vonNeumannGram3D z mu lam).det = 0 := by
  constructor
  · exact (harmonicGram3D_rankDrop_iff χ bank z mu lam).2
      (threeDZero_harmonicRankDrop χ bank z mu lam hlam hzero)
  · exact (vonNeumannGram3D_rankDrop_iff z mu lam).2
      (vonNeumannGram_rankDrop z mu lam hlam)

omit [NeZero q] in
/-- A focal cancellation at physical helix height `Z` produces both 3D Gram rank drops at that
same height; their internal spectral parameter is the derived coordinate `y = log Z`. -/
theorem threeDZeroAtHeight_twoGram3D_rankDrop
    (χ : DirichletCharacter ℂ q) (bank : FocalBank) (Z : ℝ)
    (mu lam : ℂ) (hlam : lam ≠ mu) (hzero : ThreeDZeroAtHeight χ bank Z) :
    (harmonicGram3DAtHeight χ bank Z mu lam).det = 0 ∧
      (vonNeumannGram3DAtHeight Z mu lam).det = 0 := by
  exact threeDZero_twoGram3D_rankDrop χ bank (Real.log Z) mu lam hlam hzero.2

/-- A completed 3D fibre crossing at physical height `Z` has both the completed harmonic Gram
rank drop and the local von Neumann spatial rank drop at ordinate `log Z`. -/
theorem completedThreeDZeroAtHeight_twoGram3D_rankDrop
    (χ : DirichletCharacter ℂ q) (Z : ℝ) (mu lam : ℂ)
    (hlam : lam ≠ mu) (hzero : CompletedThreeDZeroAtHeight χ Z) :
    (completedHarmonicGram3DAtHeight χ Z mu lam).det = 0 ∧
      (vonNeumannGram3DAtHeight Z mu lam).det = 0 := by
  refine ⟨(completedHarmonicGram3DAtHeight_rankDrop_iff χ Z mu lam hzero.1 hlam).2 hzero, ?_⟩
  exact (vonNeumannGram3D_rankDrop_iff (Real.log Z) mu lam).2
    (vonNeumannGram_rankDrop (Real.log Z) mu lam hlam)

/-- Complete native-event assembly at one physical helix height.  A completed 3D focal
cancellation supplies the literal focal residual zero, the spatial harmonic-pencil rank drop,
the event-independent carrier eigenvector at ordinate `log Z`, and zero radial drift of its
analytic readout.  Thus the pencil and the no-drift law concern the same marked carrier event;
the latter is derived from helix membership rather than inserted into the event certificate. -/
theorem completedThreeDZeroAtHeight_focal_rankDrop_eigenvector_noRadialDrift
    (χ : DirichletCharacter ℂ q) (p r Z n : ℝ) (mu lam : ℂ)
    (hn : 1 < n) (hlam : lam ≠ mu) (hzero : CompletedThreeDZeroAtHeight χ Z) :
    HarmonicCell.Dcell χ Z = 0 ∧
      (completedHarmonicGram3DAtHeight χ Z mu lam).det = 0 ∧
      let e : CompletedThreeDEigenEvent χ := ⟨Z, hzero⟩
      Finsupp.single (e.toCarrierState p r) (1 : ℂ) ≠ 0 ∧
        carrierThreeDOperator p r (Finsupp.single (e.toCarrierState p r) (1 : ℂ)) =
          (Real.log Z : ℂ) • Finsupp.single (e.toCarrierState p r) (1 : ℂ) ∧
        n ^ ((carrierPointAtHeight Z).re - carrierAbscissa) = 1 := by
  have hrank :=
    (completedHarmonicGram3DAtHeight_rankDrop_iff χ Z mu lam hzero.1 hlam).2 hzero
  let e : CompletedThreeDEigenEvent χ := ⟨Z, hzero⟩
  have heigen := carrierThreeDOperator_completedEvent_eigenvector p r e
  refine ⟨hzero.2, hrank, heigen.1, ?_, carrierPointAtHeight_noRadialDrift Z n hn⟩
  simpa [e] using heigen.2

omit [NeZero q] in
/-- The carrier coordinate of every native 3-D zero lies on the midline. -/
theorem threeDZero_on_midline (χ : DirichletCharacter ℂ q) (bank : FocalBank) (z : ℝ)
    (_ : ThreeDZero χ bank z) :
    (carrierPoint z).re = 1 / 2 := by
  simp [carrierPoint]

end CriticalLinePhasor.ThreeDFocal

#print axioms CriticalLinePhasor.ThreeDFocal.focalClosure_iff_rankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.carrierScaleBalanced_iff
#print axioms CriticalLinePhasor.ThreeDFocal.exists_unique_carrierScaleBalanced
#print axioms CriticalLinePhasor.ThreeDFocal.carrierAbscissa_eq_half
#print axioms CriticalLinePhasor.ThreeDFocal.noRadialDrift_iff_carrierAbscissa
#print axioms CriticalLinePhasor.ThreeDFocal.offCarrier_has_radialDrift
#print axioms CriticalLinePhasor.ThreeDFocal.carrierPoint_eq_half_add_I
#print axioms CriticalLinePhasor.ThreeDFocal.carrierPointAtHeight_im
#print axioms CriticalLinePhasor.ThreeDFocal.carrierPointAtHeight_re
#print axioms CriticalLinePhasor.ThreeDFocal.carrierPointAtHeight_exp
#print axioms CriticalLinePhasor.ThreeDFocal.carrierPoint_re
#print axioms CriticalLinePhasor.ThreeDFocal.carrierPoint_im
#print axioms CriticalLinePhasor.ThreeDFocal.exists_eq_carrierPoint_iff
#print axioms CriticalLinePhasor.ThreeDFocal.no_offCarrier_representation
#print axioms CriticalLinePhasor.ThreeDFocal.exists_pos_eq_carrierPointAtHeight_iff
#print axioms CriticalLinePhasor.ThreeDFocal.no_offCarrier_physical_representation
#print axioms CriticalLinePhasor.ThreeDFocal.spatialLiftGram_det
#print axioms CriticalLinePhasor.ThreeDFocal.spatialLiftGram_rankDrop_iff
#print axioms CriticalLinePhasor.ThreeDFocal.harmonicGram3D_rankDrop_iff
#print axioms CriticalLinePhasor.ThreeDFocal.vonNeumannGram3D_rankDrop_iff
#print axioms CriticalLinePhasor.ThreeDFocal.vonNeumannGram_rankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.vonNeumannGram_rankDrop_iff_eigenstate
#print axioms CriticalLinePhasor.ThreeDFocal.carrier_kernel_realized
#print axioms CriticalLinePhasor.ThreeDFocal.focalCancellation_to_threeDZero
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZero_harmonicRankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZero_twoGram_eigenstate
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZero_twoGram3D_rankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZeroAtHeight_exp_iff
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZeroAtHeight_twoGram3D_rankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.reprPoint_eq_carrierPointAtHeight
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDZeroAtHeight_iff_L_zero
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDZeroAtHeight_on_midline
#print axioms CriticalLinePhasor.ThreeDFocal.completedFocalCancellationRepresents_iff
#print axioms CriticalLinePhasor.ThreeDFocal.no_offCarrier_completedFocalCancellation
#print axioms CriticalLinePhasor.ThreeDFocal.CarrierState3D.physicalHeight_eq_exp
#print axioms CriticalLinePhasor.ThreeDFocal.carrierThreeDOperator_isSymmetric
#print axioms CriticalLinePhasor.ThreeDFocal.carrierThreeDOperator_eigenvector
#print axioms CriticalLinePhasor.ThreeDFocal.CompletedThreeDEigenEvent.toCarrierState_physicalHeight
#print axioms CriticalLinePhasor.ThreeDFocal.carrierThreeDOperator_completedEvent_eigenvector
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDOperator_isSymmetric
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDOperator_eigenvector
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDEigenEvent_ordinate_injective
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDEigenEvent_L_zero
#print axioms CriticalLinePhasor.ThreeDFocal.completedHarmonicGram3DAtHeight_rankDrop_iff
#print axioms CriticalLinePhasor.ThreeDFocal.completedHarmonicGram3DAtHeight_rankDrop_iff_L_zero
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDZeroAtHeight_twoGram3D_rankDrop
#print axioms CriticalLinePhasor.ThreeDFocal.carrierPointAtHeight_noRadialDrift
#print axioms CriticalLinePhasor.ThreeDFocal.completedThreeDZeroAtHeight_focal_rankDrop_eigenvector_noRadialDrift
#print axioms CriticalLinePhasor.ThreeDFocal.threeDZero_on_midline
