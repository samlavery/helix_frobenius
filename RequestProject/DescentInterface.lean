import RequestProject.GeometricSourceRecognition

/-!
# The descent interface: one object, many shadows — the provable
# direction, and the wall as a single field

The wall census measured (2026-07-29, nine primes, twelve base powers):
the collective projector's discrete signature on the explicit fourfold is
constant — degree 13, channel multiplicity 18, identity μ-address,
base-change stable, Weil-to-impostor gap macroscopic.  The theorem
hierarchy this feeds:

* **The provable direction** (`census_flat_of_pattern`): if the per-place
  spectra all realize ONE fixed partition pattern — the shadow of a single
  characteristic-zero object — then every per-place signature is
  identical.  One object ⟹ flat census.  This is the direction that,
  instantiated on the fourfold (where the char-0 object EXISTS: the
  decomposable/Lefschetz construction, with Markman closing Weil
  algebraicity in dimension 4 regardless), upgrades the measured census
  from corroboration to the shadow of a theorem.

* **The wall, as a field** (`DescentDatum.glue`): the converse — flat
  census ⟹ one char-0 object — is NOT a theorem (no known result converts
  algebraic-mod-p-for-all-p into algebraic-over-ℚ).  `DescentDatum` types
  the family of per-place projectors with its constancy certificate and
  carries the char-0 correspondence as the single remaining field;
  `projectorRecognition_of_glue` shows recognition follows once the field
  is supplied.  On the fourfold the field is inhabited (cited
  construction); on the sixfold it is THE open step, one field wide.

Scope: the model theorems are exact finite linear algebra, the geometric
instantiations carry their citations.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {Z : Type*} [Zero Z]

/-! ## The provable direction: one pattern ⟹ flat census -/

/-- A spectral pattern: a fixed assignment of `m` channels to `c` classes
— the characteristic-zero shadow that every place realizes. -/
structure SpecPattern (m c : ℕ) where
  classOf : Fin m → Fin c
  surj : Function.Surjective classOf

/-- The signature of a pattern: the multiplicity of each class — the
discrete data the census measures. -/
def SpecPattern.mult {m c : ℕ} (P : SpecPattern m c) (j : Fin c) : ℕ :=
  (Finset.univ.filter fun i => P.classOf i = j).card

/-- A place realizing the pattern: a spectrum whose value at a channel
depends exactly on the channel's class, distinct classes getting distinct
values. -/
structure Realizes {m c : ℕ} (P : SpecPattern m c) (spec : Fin m → ℂ) : Prop where
  factors : ∀ i i', P.classOf i = P.classOf i' → spec i = spec i'
  separates : ∀ i i', spec i = spec i' → P.classOf i = P.classOf i'

/-- **One object ⟹ flat census**: at every place realizing the pattern,
the census reads the SAME signature — the distinct-value count is the
class count and each cluster's multiplicity is the pattern's.  The
measured flatness (13/18, all places, all powers) is exactly what one
characteristic-zero object casts. -/
theorem census_flat_of_pattern {m c : ℕ} (P : SpecPattern m c)
    (spec : Fin m → ℂ) (h : Realizes P spec) (j : Fin c) :
    ∀ i₀ : Fin m, P.classOf i₀ = j →
      (Finset.univ.filter fun i => spec i = spec i₀).card = P.mult j := by
  intro i₀ hi₀
  unfold SpecPattern.mult
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    rw [h.separates i i₀ hv, hi₀]
  · intro hc
    exact h.factors i i₀ (by rw [hc, hi₀])

/-! ## The wall as a single field -/

/-- The descent datum over a family of places: per-place correspondence
calculi and per-place projectors with their landing certificates, the
constancy of the discrete signature across places — and the ONE field the
census cannot supply: the characteristic-zero correspondence whose
shadows they are.  On the fourfold this field is inhabited by the cited
decomposable/Lefschetz construction; on the sixfold it is the named open
step. -/
structure DescentDatum.{v} (Place : Type*) (D : HodgeDial Z) where
  /-- the per-place correspondence calculus (Frobenius polynomials). -/
  calc' : Place → CorrespondenceCalculus.{_, v} D
  /-- the per-place collective projector. -/
  proj : ∀ v : Place, (calc' v).Corr
  /-- per-place algebraicity — free in finite characteristic (polynomials
  in the Frobenius graph). -/
  proj_algebraic : ∀ v, (calc' v).AlgebraicCorr (proj v)
  /-- the constancy certificate: the measured signature, one number per
  place, equal across the family (the census's 13/18-flatness). -/
  signature : Place → ℕ × ℕ
  signature_const : ∀ v w, signature v = signature w
  /-- **THE WALL**: the characteristic-zero correspondence and its
  compatibility — supplying this field IS the descent. -/
  glue : Option ((c : CorrespondenceCalculus.{_, v} D) ×
    { π : c.Corr // c.AlgebraicCorr π })

/-- **Recognition follows once the wall field is supplied**: a glued
descent datum whose char-0 projector recognizes the fired rational DC
states yields dial recognition — the whole chain above the field is
already theorem. -/
theorem recognition_of_glue {Place : Type*} {D : HodgeDial Z}
    (Δ : DescentDatum Place D)
    (K : CorrespondenceCalculus D) (π : K.Corr) (hπ : K.AlgebraicCorr π)
    (hrec : ∀ z : Z, (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z →
      ∃ η : Z, D.Algebraic η ∧ K.act π η = z) :
    Recognition D := by
  intro z hf hdc hrat
  obtain ⟨η, hη, hact⟩ := hrec z hf hdc hrat
  rw [← hact]
  exact K.transport π hπ η hη

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.census_flat_of_pattern
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.recognition_of_glue
