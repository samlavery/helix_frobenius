import RequestProject.CancellationEigenstatePair

/-!
# The focal spectral datum (M, Z), its two realizations, the anti-helix datum, and the readouts
(ledger 1166, corrected in 1167)

A focal event produces a spectral datum: a mass `M > 0` (the sum of the magnitudes of the cancelling
phasors) and the event's HEIGHT `Z > 0` (the third coordinate of its helix point). The logarithm is not
part of the datum: the signed eigenvalue `y = log Z` is derived from it.

* `SpectralDatum` (mass, height, both positive); `datum e` (mass `eigenMass e = headUnsigned`, height
  `e.height`, the projected height of the event's helix point); `eigenvalue d := log Z`;
  `datum_eigenvalue` (`= e.y`, derived through the log).
* Two realizations, both built from the datum: `standing d = standingMode M` and
  `wave d = massiveWave M (log Z)`. `realizations_same_datum`: each reads back `M`, and the wave reads
  back `log Z`; `wave_injective` (with `Z > 0`, the wave determines the datum).
* The reciprocal-height datum `J d = (M, Z⁻¹)`: `J_involutive`, `eigenvalue_J` (`log Z⁻¹ = −log Z`: the
  ± pair comes out of the log), `wave_J` (the conjugate wave), `standing_J`. DEMOTED-SEMANTICS (cleanup,
  ledger 1237): this `J` FLIPS HEIGHT. It is representation-specific, not canonical physical J (the
  same-height feet involution, `FocalFeetDatum`), and not the transverse partner `ρ ↦ 1 − conj ρ` or the FE
  reflection `ρ ↦ 1 − ρ`. The same applies to `logReadout_J`, `cayleyLog_J`, `cayleyHeight_J`, `pairedLog` and
  `pairedHeight`.
* The log readout `logReadout d = (M, log Z)` and its J law (`logReadout_J`).
* The two Cayley orders, as the repository has them (Sam, ledger 1168: `cayleyLog` is the native
  route; `log` is the multiplicative-height → signed-height coordinate change, not the 2D→1D
  projection; `cayleyHeight` is kept as the control):
  - `cayleyLog d = (M, cayley(log Z))` (NATIVE): Cayley consumes the logarithmic coordinate, as the
    compiled `GlobalHelix.circleReadout` does (`cayley` of the signed height `h`, with `exp h` the
    positive height). `cayleyLog_J`: J becomes conjugation.
  - `cayleyHeight d = (M, cayley Z)` (CONTROL): Cayley consumes the positive height, as
    GeometricReadout's header comment reads. No compiled Cayley in the repository takes the positive
    height. `cayleyHeight_J`: J becomes `w ↦ −conj w`.
  Both are injective (`cayleyLog_injective`, `cayleyHeight_injective`).
* The paired states of an event in each order: `pairedLog e`, `pairedHeight e`.

**REPRESENTATION-SPECIFIC, NOT THE FOCAL EIGENSTATE PAIR (ledger 1171, Sam 2026-10-10).** The `J`
of this file sends the height `Z` to `Z⁻¹`. The physical anti-helix foot stands at the same height
with the same weight; J reverses only the direction (`FocalFeet.J`, RequestProject/FocalFeetDatum.lean).
The reciprocal height was imported from `GlobalHelix.globalHelixInvolution`, which reverses the signed
height of the double carrier. Every statement here that uses `J` (`J`, `J_involutive`, `eigenvalue_J`,
`wave_J`, `antihelix_datum_wave`, `logReadout_J`, `cayleyLog_J`, `cayleyHeight_J`, `pairedLog`,
`pairedLog_eq`, `pairedHeight`, `pairedHeight_eq`) is a property of that representation. The datum
`(M, Z)`, its realizations and the readouts without `J` are unaffected. `Z` is the height in the 3D
state space; `log Z` is the chart height.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.FocalSpectral

open CriticalLinePhasor CriticalLinePhasor.Phasor3D CriticalLinePhasor.FocalCancellation
open CriticalLinePhasor.UnconditionalFrobenius CriticalLinePhasor.FocalEventProjection
open CriticalLinePhasor.CancellationEigenstatePair

/-! ## The datum -/

/-- **A focal spectral datum**: a positive mass and a positive height. -/
structure SpectralDatum where
  mass : ℝ
  mass_pos : 0 < mass
  height : ℝ
  height_pos : 0 < height

theorem SpectralDatum.ext' {d₁ d₂ : SpectralDatum} (hm : d₁.mass = d₂.mass)
    (hZ : d₁.height = d₂.height) : d₁ = d₂ := by
  cases d₁
  cases d₂
  simp only at hm hZ
  subst hm hZ
  rfl

/-- The signed eigenvalue, derived from the height by the log readout. -/
def eigenvalue (d : SpectralDatum) : ℝ := Real.log d.height

/-- **The datum a focal event produces**: mass = the sum of the magnitudes of the cancelling phasors,
height = the projected height of the event's helix point. -/
def datum (e : FocalEvent) : SpectralDatum where
  mass := eigenMass e
  mass_pos := eigenMass_pos e
  height := e.height
  height_pos := e.height_pos

theorem datum_mass (e : FocalEvent) :
    (datum e).mass = ∑ k ∈ Finset.range ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊,
      ‖cancellingPhasor e.w e.a e.y k‖ :=
  (cancellingMass_eq e.w e.a_pos e.y).symm

/-- The event's eigenvalue is its ordinate, obtained from its height through the log. -/
theorem datum_eigenvalue (e : FocalEvent) : eigenvalue (datum e) = e.y := by
  show Real.log e.height = e.y
  rw [e.height_eq, TwoEndedJState.eventHeight, Real.log_exp]

/-! ## Two realizations of the same datum -/

/-- The standing realization: the non-radiating, pure-mass 3D mode. -/
def standing (d : SpectralDatum) : Vec3 := standingMode d.mass

/-- The massive-wave realization: `M·e^{i(log Z)t}`. -/
def wave (d : SpectralDatum) : ℝ → ℂ := massiveWave d.mass (eigenvalue d)

/-- The standing realization's readout: its 3D magnitude. -/
def standingMass (v : Vec3) : ℝ := mag3 v

/-- The wave realization's mass readout: its modulus at `t = 0`. -/
def waveMass (f : ℝ → ℂ) : ℝ := ‖f 0‖

/-- The wave realization's eigenvalue readout: `−i f'(0) / f(0)`. -/
def waveEigenvalue (f : ℝ → ℂ) : ℂ := -Complex.I * deriv f 0 / f 0

theorem standing_plane (d : SpectralDatum) : plane (standing d) = 0 := rfl

theorem standing_mass (d : SpectralDatum) : standingMass (standing d) = d.mass :=
  mag3_standingMode d.mass_pos.le

theorem wave_mass (d : SpectralDatum) : waveMass (wave d) = d.mass :=
  massiveWave_norm _ _ d.mass_pos.le 0

theorem wave_ne_zero (d : SpectralDatum) (t : ℝ) : wave d t ≠ 0 := by
  intro h
  have := massiveWave_norm d.mass (eigenvalue d) d.mass_pos.le t
  rw [show massiveWave d.mass (eigenvalue d) t = wave d t from rfl, h, norm_zero] at this
  exact d.mass_pos.ne this

theorem wave_eigenvalue (d : SpectralDatum) : waveEigenvalue (wave d) = eigenvalue d := by
  unfold waveEigenvalue
  rw [show -Complex.I * deriv (wave d) 0 = (eigenvalue d : ℂ) * wave d 0 from
    massiveWave_eigen d.mass (eigenvalue d) 0]
  field_simp [wave_ne_zero d 0]

/-- **Both realizations read back the same datum**: the same mass from each, and `log Z` from the
wave. -/
theorem realizations_same_datum (d : SpectralDatum) :
    standingMass (standing d) = d.mass ∧ waveMass (wave d) = d.mass ∧
      waveEigenvalue (wave d) = Real.log d.height :=
  ⟨standing_mass d, wave_mass d, wave_eigenvalue d⟩

/-- The wave realization is faithful: with `Z > 0`, it determines the datum. -/
theorem wave_injective {d₁ d₂ : SpectralDatum} (h : wave d₁ = wave d₂) : d₁ = d₂ := by
  apply SpectralDatum.ext'
  · rw [← wave_mass d₁, ← wave_mass d₂, h]
  · have h1 := wave_eigenvalue d₁
    rw [h, wave_eigenvalue d₂] at h1
    have hlog : Real.log d₂.height = Real.log d₁.height := by exact_mod_cast h1
    exact (Real.log_injOn_pos d₁.height_pos d₂.height_pos hlog.symm)

/-! ## The reciprocal-height datum (representation-specific; ledger 1171)

The physical anti-helix foot keeps the height; see `FocalFeet.J`. -/

/-- **The reciprocal-height datum**: same mass, reciprocal height. Representation-specific (ledger
1171): this is not the physical anti-helix foot, which stands at the same height. -/
def J (d : SpectralDatum) : SpectralDatum where
  mass := d.mass
  mass_pos := d.mass_pos
  height := d.height⁻¹
  height_pos := inv_pos.mpr d.height_pos

theorem J_involutive : Function.Involutive J := fun _ =>
  SpectralDatum.ext' rfl (inv_inv _)

theorem J_mass (d : SpectralDatum) : (J d).mass = d.mass := rfl

/-- `log Z⁻¹ = −log Z`. Representation-specific (ledger 1171): the feet do not carry `±log Z`; both
read the chart height `log Z`, and the sign belongs to the direction. -/
theorem eigenvalue_J (d : SpectralDatum) : eigenvalue (J d) = -eigenvalue d :=
  Real.log_inv d.height

/-- The anti-helix wave is the conjugate wave. -/
theorem wave_J (d : SpectralDatum) (t : ℝ) : wave (J d) t = (starRingEnd ℂ) (wave d t) := by
  unfold wave
  rw [eigenvalue_J, massiveWave_conj]
  rfl

/-- The anti-helix standing mode is the same standing mode. -/
theorem standing_J (d : SpectralDatum) : standing (J d) = standing d := rfl

theorem antihelix_datum_mass (e : FocalEvent) :
    (J (datum e)).mass = ∑ k ∈ Finset.range ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊,
      ‖(starRingEnd ℂ) (cancellingPhasor e.w e.a e.y k)‖ :=
  (antihelix_mass e).symm

theorem antihelix_datum_wave (e : FocalEvent) (t : ℝ) :
    wave (J (datum e)) t = massiveWave (eigenMass e) (-e.y) t := by
  unfold wave
  rw [eigenvalue_J, datum_eigenvalue]
  rfl

/-! ## The log readout -/

/-- The 1D log readout: mass and `log Z`. -/
def logReadout (d : SpectralDatum) : ℝ × ℝ := (d.mass, Real.log d.height)

theorem logReadout_J (d : SpectralDatum) :
    logReadout (J d) = ((logReadout d).1, -(logReadout d).2) := by
  unfold logReadout J
  simp only [Real.log_inv]

/-! ## The two Cayley orders -/

theorem cayley_real_inj {a b : ℝ} (h : Readout.cayley (a : ℂ) = Readout.cayley (b : ℂ)) : a = b := by
  unfold Readout.cayley at h
  have ha : (a : ℂ) + Complex.I ≠ 0 := fun h0 => by simpa using congrArg Complex.im h0
  have hb : (b : ℂ) + Complex.I ≠ 0 := fun h0 => by simpa using congrArg Complex.im h0
  rw [div_eq_div_iff ha hb] at h
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- On real inputs the Cayley map sends reversal to conjugation. -/
theorem cayley_neg (y : ℝ) :
    Readout.cayley ((-y : ℝ) : ℂ) = (starRingEnd ℂ) (Readout.cayley (y : ℂ)) := by
  unfold Readout.cayley
  rw [map_div₀, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  rw [show -(y : ℂ) - Complex.I = -((y : ℂ) - -Complex.I) by ring,
    show -(y : ℂ) + Complex.I = -((y : ℂ) + -Complex.I) by ring, neg_div_neg_eq]

/-- On positive real inputs the Cayley map sends the reciprocal to minus the conjugate. -/
theorem cayley_inv {Z : ℝ} (hZ : 0 < Z) :
    Readout.cayley ((Z⁻¹ : ℝ) : ℂ) = -(starRingEnd ℂ) (Readout.cayley (Z : ℂ)) := by
  unfold Readout.cayley
  rw [map_div₀, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I]
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hd1 : ((Z⁻¹ : ℝ) : ℂ) + Complex.I ≠ 0 := fun h0 => by simpa using congrArg Complex.im h0
  have hd2 : (Z : ℂ) + -Complex.I ≠ 0 := fun h0 => by simpa using congrArg Complex.im h0
  rw [neg_div', div_eq_div_iff hd1 hd2]
  push_cast
  have hZZ : (Z : ℂ) * (Z : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hZc
  linear_combination 2 * hZZ + 2 * Complex.I_sq

/-- **Cayley of the logarithmic coordinate** (the compiled `circleReadout` order). -/
def cayleyLog (d : SpectralDatum) : ℝ × ℂ := (d.mass, Readout.cayley ((Real.log d.height : ℝ) : ℂ))

/-- **Cayley of the positive height** (GeometricReadout's stated chain order). -/
def cayleyHeight (d : SpectralDatum) : ℝ × ℂ := (d.mass, Readout.cayley ((d.height : ℝ) : ℂ))

/-- In the log order, J becomes conjugation. -/
theorem cayleyLog_J (d : SpectralDatum) :
    cayleyLog (J d) = ((cayleyLog d).1, (starRingEnd ℂ) (cayleyLog d).2) := by
  unfold cayleyLog J
  simp only [Real.log_inv]
  rw [cayley_neg]

/-- In the height order, J becomes `w ↦ −conj w`. -/
theorem cayleyHeight_J (d : SpectralDatum) :
    cayleyHeight (J d) = ((cayleyHeight d).1, -(starRingEnd ℂ) (cayleyHeight d).2) := by
  unfold cayleyHeight J
  simp only
  rw [cayley_inv d.height_pos]

theorem cayleyLog_injective {d₁ d₂ : SpectralDatum} (h : cayleyLog d₁ = cayleyLog d₂) : d₁ = d₂ := by
  apply SpectralDatum.ext'
  · exact congrArg Prod.fst h
  · exact Real.log_injOn_pos d₁.height_pos d₂.height_pos (cayley_real_inj (congrArg Prod.snd h))

theorem cayleyHeight_injective {d₁ d₂ : SpectralDatum} (h : cayleyHeight d₁ = cayleyHeight d₂) :
    d₁ = d₂ :=
  SpectralDatum.ext' (congrArg Prod.fst h) (cayley_real_inj (congrArg Prod.snd h))

theorem cayleyLog_norm_one (d : SpectralDatum) : ‖(cayleyLog d).2‖ = 1 :=
  Readout.cayley_real_norm_one _

theorem cayleyHeight_norm_one (d : SpectralDatum) : ‖(cayleyHeight d).2‖ = 1 :=
  Readout.cayley_real_norm_one _

/-! ## The paired 2D spectral states of an event, in each order -/

def pairedLog (e : FocalEvent) : (ℝ × ℂ) × (ℝ × ℂ) := (cayleyLog (datum e), cayleyLog (J (datum e)))

def pairedHeight (e : FocalEvent) : (ℝ × ℂ) × (ℝ × ℂ) :=
  (cayleyHeight (datum e), cayleyHeight (J (datum e)))

theorem pairedLog_eq (e : FocalEvent) :
    pairedLog e = ((eigenMass e, Readout.cayley (e.y : ℂ)),
      (eigenMass e, (starRingEnd ℂ) (Readout.cayley (e.y : ℂ)))) := by
  unfold pairedLog
  rw [cayleyLog_J]
  unfold cayleyLog
  rw [show Real.log (datum e).height = e.y from datum_eigenvalue e]
  rfl

theorem pairedHeight_eq (e : FocalEvent) :
    pairedHeight e = ((eigenMass e, Readout.cayley (e.height : ℂ)),
      (eigenMass e, -(starRingEnd ℂ) (Readout.cayley (e.height : ℂ)))) := by
  unfold pairedHeight
  rw [cayleyHeight_J]
  rfl

end CriticalLinePhasor.FocalSpectral

#print axioms CriticalLinePhasor.FocalSpectral.datum_eigenvalue
#print axioms CriticalLinePhasor.FocalSpectral.realizations_same_datum
#print axioms CriticalLinePhasor.FocalSpectral.wave_injective
#print axioms CriticalLinePhasor.FocalSpectral.eigenvalue_J
#print axioms CriticalLinePhasor.FocalSpectral.wave_J
#print axioms CriticalLinePhasor.FocalSpectral.antihelix_datum_wave
#print axioms CriticalLinePhasor.FocalSpectral.cayley_inv
#print axioms CriticalLinePhasor.FocalSpectral.cayleyLog_J
#print axioms CriticalLinePhasor.FocalSpectral.cayleyHeight_J
#print axioms CriticalLinePhasor.FocalSpectral.pairedLog_eq
#print axioms CriticalLinePhasor.FocalSpectral.pairedHeight_eq
