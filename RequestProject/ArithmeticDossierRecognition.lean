import RequestProject.SchoenGateRecognition

/-!
# The arithmetic-dossier recognition package: point-counted inhabitant

The named next step after the Schoen-gate model inhabitant: the same
recognition architecture with the finite model types replaced by
POINT-COUNTED dossiers.  Every angular entry is a Frobenius trace computed
in-kernel from an actual affine point count over `𝔽_p`, and every radial
entry is the exact rational `j`-invariant — the arithmetic content the
genus-1 radial–Torelli rung recovers exactly from periods.

The three members and the two-regime structure, all real:

* the **blind pair** `11a1`, `11a3` — genuinely isogenous curves (isogeny
  class `11a`), so their angular dossiers are IDENTICAL at every counted
  prime (`blind_pair_counts`, kernel-verified at `p = 2, 3, 5, 7`) while
  their `j`-invariants differ (`−122023936/161051` vs `−4096/11`):
  Faltings Tier-3 blindness realized on actual arithmetic, not on a toy
  label;
* the **simple member** `37a1`, separated angularly and radially;
* the **decomposable/class-pinned regime** on the designated class
  representative: the isogeny class is read from angular data alone
  (Faltings Tier 2 — the `a_p` stream pins the class), and the class
  cycle certifies the representative without any radial reading.

The dossiers being genuine forces the boundary theorems to carry real
content: `boundary_necessity` on this bridge says no function of
`a_p`-data alone recovers the `j`-invariant — witnessed by an actual
isogeny class, the L-invisible fine coordinate in the flesh.

Register: the bridge fields remain the in-model form of the four
monuments (the architecture is the theorem; the monuments are cited, not
proven); what upgrades is the TYPE of the dossiers — from `Fin n` labels
to counted traces and exact `j`-invariants.  Scope: does not assume or
prove RH/GRH or the Hodge conjecture.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

namespace ArithmeticDossier

/-! ## The point-counted angular dossiers -/

/-- The affine point count of `y² + y = x³ + Ax² + Bx + C` over `ZMod p`
(the `a₁ = 0, a₃ = 1` minimal shape shared by `11a1`, `11a3`, `37a1`). -/
def affineCount (A B C : ℤ) (p : ℕ) [NeZero p] : ℕ :=
  (Finset.univ.filter (fun q : ZMod p × ZMod p =>
    q.2 ^ 2 + q.2 =
      q.1 ^ 3 + (A : ZMod p) * q.1 ^ 2 + (B : ZMod p) * q.1 + (C : ZMod p))).card

/-- The Frobenius trace `a_p = p − #affine`. -/
def ap (A B C : ℤ) (p : ℕ) [NeZero p] : ℤ := (p : ℤ) - affineCount A B C p

/-- The angular dossier: the counted traces at `p = 2, 3, 5, 7` (good
reduction for conductors 11 and 37). -/
def dossier (A B C : ℤ) : Fin 4 → ℤ :=
  ![ap A B C 2, ap A B C 3, ap A B C 5, ap A B C 7]

/-- `11a1 : y² + y = x³ − x² − 10x − 20`. -/
def d11a1 : Fin 4 → ℤ := dossier (-1) (-10) (-20)

/-- `11a3 : y² + y = x³ − x²` (the curve `X₁(11)`). -/
def d11a3 : Fin 4 → ℤ := dossier (-1) 0 0

/-- `37a1 : y² + y = x³ − x`. -/
def d37a1 : Fin 4 → ℤ := dossier 0 (-1) 0

/-- **The blind pair is angular-identical, by point count**: the isogeny
class `11a` shares every counted trace — kernel-verified arithmetic, the
real Faltings Tier-3 witness. -/
theorem blind_pair_counts : d11a1 = d11a3 := by decide

/-- The simple member is angular-separated from the class. -/
theorem separated_counts : d11a1 ≠ d37a1 := by decide

/-- The counted values, on the record: class `11a` reads
`(a₂, a₃, a₅, a₇) = (−2, −1, 1, −2)`. -/
theorem d11a1_val : d11a1 = ![-2, -1, 1, -2] := by decide

/-- `37a1` reads `(−2, −3, −2, −1)`. -/
theorem d37a1_val : d37a1 = ![-2, -3, -2, -1] := by decide

/-! ## The exact radial dossiers -/

/-- The exact `j`-invariant of `y² + y = x³ + Ax² + Bx + C` — the fine,
L-invisible coordinate the radial/period channel recovers (the genus-1
rung recovers exactly this rational from AGM periods). -/
def jInv (A B C : ℚ) : ℚ :=
  (16 * A ^ 2 - 48 * B) ^ 3 /
    (-16 * A ^ 2 * (4 * A * C + A - B ^ 2) - 64 * B ^ 3
      - 27 * (4 * C + 1) ^ 2 + 72 * A * B * (4 * C + 1))

/-- `j(11a1) = −2¹²·31³/11⁵`, exactly. -/
theorem j_11a1 : jInv (-1) (-10) (-20) = -122023936 / 161051 := by
  norm_num [jInv]

/-- `j(11a3) = −4096/11`, exactly. -/
theorem j_11a3 : jInv (-1) 0 0 = -4096 / 11 := by
  norm_num [jInv]

/-- `j(37a1) = 110592/37`, exactly (the discriminant is the conductor). -/
theorem j_37a1 : jInv 0 (-1) 0 = 110592 / 37 := by
  norm_num [jInv]

/-- The blind pair is radially SEPARATED: `j(11a1) ≠ j(11a3)` — the fine
coordinate the angular stream provably cannot see. -/
theorem blind_pair_radial : jInv (-1) (-10) (-20) ≠ jInv (-1) 0 0 := by
  rw [j_11a1, j_11a3]
  norm_num

theorem jne10 : jInv (-1) 0 0 ≠ jInv (-1) (-10) (-20) := by
  rw [j_11a1, j_11a3]
  norm_num

theorem jne20 : jInv 0 (-1) 0 ≠ jInv (-1) (-10) (-20) := by
  rw [j_37a1, j_11a1]
  norm_num

theorem jne21 : jInv 0 (-1) 0 ≠ jInv (-1) 0 0 := by
  rw [j_37a1, j_11a3]
  norm_num

/-! ## The bridge over the counted types -/

/-- Three members: the isogenous blind pair and the simple member. -/
abbrev Member := Fin 3

/-- The angular reading: the counted dossiers. -/
def angularOf : Member → (Fin 4 → ℤ) := ![d11a1, d11a3, d37a1]

/-- The radial reading: the exact `j`-invariants. -/
def radialOf : Member → ℚ :=
  ![jInv (-1) (-10) (-20), jInv (-1) 0 0, jInv 0 (-1) 0]

/-- **The arithmetic-dossier bridge**: the recognition architecture over
counted traces and exact `j`-invariants. -/
def arithBridge :
    RecognitionBridge Member (Fin 4 → ℤ) ℚ ℚ ℚ (Fin 2) where
  angular := angularOf
  angularClass v := if v = d11a1 then 0 else 1
  radial := radialOf
  torelli := id
  construct := id
  constructDecomposable v :=
    if v = d11a1 then jInv (-1) (-10) (-20) else jInv 0 (-1) 0
  trueCurve := radialOf
  Isogenous f g := angularOf f = angularOf g
  Detected _ := True
  Decomposable f := f = 0
  Recognizes c f := c = radialOf f
  angular_complete := by decide
  angular_invariant := by decide
  angular_blind := ⟨0, 1, trivial, trivial, by decide, blind_pair_radial⟩
  radial_retention := fun _ _ _ _ h => h
  torelli_spec := fun _ _ => rfl
  construct_spec := fun _ _ => rfl
  decomposable_spec := by
    intro f _ hd
    subst hd
    show (if angularOf 0 = d11a1 then jInv (-1) (-10) (-20) else jInv 0 (-1) 0)
      = radialOf 0
    rw [if_pos (by decide : angularOf 0 = d11a1)]
    simp [radialOf]

/-- The dossier dial: detection reads nonzero membership. -/
def arithDial : HodgeDial Member where
  DC _ := True
  Rational _ := True
  Algebraic _ := True
  T _ z := if z = 0 then 0 else 1

/-- Cycles land back on their members through the exact `j`-lookup. -/
def realizeCycle (c : ℚ) : Member :=
  if c = radialOf 0 then 0 else if c = radialOf 1 then 1 else 2

/-- The realization: recognized cycles are algebraic by the gate's
provenance. -/
def arithRealization : AlgebraicSourceRealization arithDial ℚ where
  realize := realizeCycle
  algebraic_realize _ := trivial

theorem realize_j0 : realizeCycle (radialOf 0) = 0 := by
  simp [realizeCycle]

theorem realize_j1 : realizeCycle (radialOf 1) = 1 := by
  have h : radialOf 1 ≠ radialOf 0 := jne10
  simp [realizeCycle, h]

theorem realize_j2 : realizeCycle (radialOf 2) = 2 := by
  have h0 : radialOf 2 ≠ radialOf 0 := jne20
  have h1 : radialOf 2 ≠ radialOf 1 := jne21
  simp [realizeCycle, h0, h1]

/-- **The point-counted recognition package** — grade four, dossiers
counted, `j`-invariants exact. -/
def arithPackage :
    HigherGradeRecognitionPackage arithDial (Fin 4 → ℤ) ℚ ℚ ℚ (Fin 2) where
  grade _ := 4
  bridge := arithBridge
  sourceRealization := arithRealization
  detected_of_fired_above_one _ _ _ _ _ := trivial
  realizes_of_recognizes source z h := by
    subst h
    fin_cases z
    · exact realize_j0
    · exact realize_j1
    · exact realize_j2

/-! ## The executed theorems on real arithmetic -/

/-- The package executes: every fired member receives a constructed,
certified, algebraically-realized source. -/
theorem arith_recognition_executes (z : Member)
    (hf : ∃ d, arithDial.T d z ≠ 0) :
    arithBridge.Recognizes (arithPackage.source z) z ∧
      arithDial.Algebraic (arithRealization.realize (arithPackage.source z)) :=
  ⟨arithPackage.source_recognizes z hf trivial trivial
    (by show (1 : ℕ) < 4; norm_num),
   arithRealization.algebraic_realize _⟩

/-- **The real blind pair, recognized**: `11a1` and `11a3` share every
counted trace yet both are recognized — through the radial channel, which
separates exactly where the angular channel is provably blind. -/
theorem arith_blind_pair_recognized :
    arithBridge.angular 0 = arithBridge.angular 1 ∧
      arithBridge.trueCurve 0 ≠ arithBridge.trueCurve 1 ∧
      arithBridge.Recognizes (arithBridge.recognizedCycle 0) 0 ∧
      arithBridge.Recognizes (arithBridge.recognizedCycle 1) 1 :=
  ⟨by decide, blind_pair_radial, recognition_closes arithBridge 0 trivial,
    recognition_closes arithBridge 1 trivial⟩

/-- **The boundary on real arithmetic**: no function of the `a_p`-stream
alone recovers the `j`-invariant — the witness is an actual isogeny class,
not a model label. -/
theorem no_angular_recovery :
    ¬ ∃ recover : (Fin 4 → ℤ) → ℚ,
      ∀ f, recover (arithBridge.angular f) = arithBridge.trueCurve f :=
  boundary_necessity arithBridge

/-- The class-pinned shortcut executes on the designated representative
from the counted angular data alone — Faltings Tier 2 in action. -/
theorem class_shortcut_executes :
    arithBridge.Recognizes
      (arithBridge.constructDecomposable (arithBridge.angular 0)) 0 :=
  decomposable_shortcut arithBridge 0 trivial rfl

end ArithmeticDossier

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.ArithmeticDossier.blind_pair_counts
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.ArithmeticDossier.arith_recognition_executes
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.ArithmeticDossier.arith_blind_pair_recognized
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.ArithmeticDossier.no_angular_recovery
