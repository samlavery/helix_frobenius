import RequestProject.HodgeRealizationBridge

/-!
# The Néron–Severi rung: a faithful realization with a genuine pairing layer

The first realization instance whose no-kernel condition is carried by a
NONTRIVIAL intersection pairing, proved as exact integer linear algebra.

The cycle group is `NS(E × E)` for a non-CM elliptic curve `E`: rank three,
basis the two fiber classes `f₁, f₂` and the diagonal graph `Δ`, with the
classical intersection matrix

    G = [[0,1,1],[1,0,1],[1,1,0]],   det G = 2 ≠ 0.

(The geometric identification `NS(E×E) ≅ (ℤ³, G)` for `Hom(E,E) = ℤ` is the
cited classical input — Birkenhake–Lange V.§; the file proves everything
about the realization of that lattice.)  The realization sends a divisor
class to its PAIRING COORDINATES `⟨fᵢ, z⟩` placed on the frequency-zero
channel of the three-channel `H²`-bank (frequencies `(-2, 0, 2)`, the Hodge
channels of a surface), one pairing coordinate per layer:

* `noKernel` is a THEOREM: the Gram matrix is nondegenerate over ℤ (integer
  elimination — `omega`), so a class with vanishing pairing coordinates is
  zero;
* exact regulator compatibility is a THEOREM (`readout_is_pairing`): the
  moment-zero tower readout of layer `l` IS the intersection number
  `⟨f_l, z⟩`, on the nose — the model reads the regulator layer exactly;
* retention, depth preservation, and the executed terminus then transport
  through the proven bridge theorems; recognition on this rung is the
  statement that NS-classes are divisor classes — algebraic by provenance.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- The Néron–Severi lattice of `E × E` in the basis `(f₁, f₂, Δ)`. -/
abbrev NSClass := Fin 3 → ℤ

namespace NeronSeveriRung

/-- The pairing coordinates `⟨f_l, z⟩` against the basis divisors — the
intersection matrix `[[0,1,1],[1,0,1],[1,1,0]]` applied to `z`. -/
def pairCoord (z : NSClass) : Fin 3 → ℤ :=
  ![z 1 + z 2, z 0 + z 2, z 0 + z 1]

theorem pairCoord_add (z w : NSClass) :
    pairCoord (z + w) = pairCoord z + pairCoord w := by
  funext l
  fin_cases l <;> simp [pairCoord] <;> ring

/-- **Nondegeneracy of the intersection form** (det G = 2): vanishing
pairing coordinates force the zero class — exact integer elimination. -/
theorem pairCoord_eq_zero (z : NSClass) (h : ∀ l, pairCoord z l = 0) :
    z = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [pairCoord] at h0 h1 h2
  funext i
  fin_cases i <;> simp <;> omega

/-- The three `H²`-channels of a surface: frequencies `(q - p)` for
`(2,0), (1,1), (0,2)`. -/
def surfaceBank : IntFrequencyBank 3 where
  freq := ![-2, 0, 2]
  injective := by decide

/-- The realization: pairing coordinate `⟨f_l, z⟩` on the frequency-zero
channel at layer `l`; the nonzero-frequency channels are empty. -/
def toModelFun (z : NSClass) : GeneralExtensionData 2 3 :=
  fun l i => if i = 1 then ((pairCoord z l : ℤ) : ℂ) else 0

theorem toModelFun_add (z w : NSClass) :
    toModelFun (z + w) = toModelFun z + toModelFun w := by
  funext l i
  simp only [toModelFun, Pi.add_apply, pairCoord_add]
  by_cases hi : i = 1
  · simp only [if_pos hi]
    push_cast
    ring
  · simp [hi]

theorem toModelFun_zero : toModelFun 0 = 0 := by
  funext l i
  by_cases hi : i = 1
  · fin_cases l <;> simp [toModelFun, hi, pairCoord]
  · simp [toModelFun, hi]

/-- The NS dial: every class is type `(1,1)` (DC) and integral (rational);
algebraicity is provenance — NS is by definition the image of the divisor
group.  The tower readouts are the model moments of the pairing data. -/
noncomputable def nsDial : HodgeDial NSClass where
  DC _ := True
  Rational _ := True
  Algebraic _ := True
  T d z := generalExtensionTower surfaceBank.toClockBank d (toModelFun z)

/-- **The faithful realization for the Néron–Severi group** — the five
conditions, with `noKernel` proven from the nondegenerate intersection
form and `regCompat` definitionally exact. -/
noncomputable def nsRealization :
    FaithfulRealization nsDial 2 surfaceBank where
  toModel := AddMonoidHom.mk' toModelFun toModelFun_add
  regCompat _ _ := rfl
  ratCompat z _ _ := by
    intro l i
    by_cases hi : i = 1
    · subst hi
      refine ⟨(pairCoord z l : ℚ), ?_⟩
      show toModelFun z l 1 = _
      simp [toModelFun]
    · exact ⟨0, by simp [toModelFun, hi]⟩
  dcCompat z _ := by
    intro l i hfreq
    have hi : i ≠ 1 := by
      intro h
      subst h
      exact hfreq (by decide)
    simp [toModelFun, hi]
  noKernel z _ _ h0 := by
    apply pairCoord_eq_zero
    intro l
    have := congrFun (congrFun h0 l) 1
    simp [toModelFun] at this
    exact_mod_cast this

/-- **Exact regulator compatibility, as a theorem**: the moment-zero tower
readout of layer `l` is exactly the intersection number `⟨f_l, z⟩`.  The
model does not approximate the regulator layer; it reads it. -/
theorem readout_is_pairing (z : NSClass) (l : Fin 3) :
    nsDial.T (Nat.pair l 0) z = ((pairCoord z l : ℤ) : ℂ) := by
  show generalExtensionTower surfaceBank.toClockBank (Nat.pair l 0)
      (toModelFun z) = _
  rw [generalExtensionTower_pair surfaceBank.toClockBank l 0 (toModelFun z)]
  rw [Fin.sum_univ_three]
  simp [toModelFun]

/-- Retention holds on the NS rung (transported through the bridge). -/
theorem ns_retention : Retention nsDial :=
  nsRealization.retention

/-- Recognition on the divisor rung: NS-classes are divisor classes,
algebraic by provenance. -/
theorem ns_recognition : Recognition nsDial := fun _ _ _ _ => trivial

/-- The executed terminus on the Néron–Severi rung. -/
theorem ns_sourceExhaustion : SourceExhaustion nsDial :=
  hodge_of_retention_recognition ns_retention ns_recognition

end NeronSeveriRung

end CriticalLinePhasor.HodgeLedgerFiltration
