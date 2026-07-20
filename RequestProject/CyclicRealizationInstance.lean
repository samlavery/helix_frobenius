import RequestProject.HodgeRealizationBridge

/-!
# The first genuine realization instance: the rational group algebra of ℤ/n

Constructs the first non-identity `FaithfulRealization` term, on a library-native object with
independent meaning: the rational group algebra `ℚ[ℤ/n]` (functions `ZMod n → ℚ`).  The
realization is the **finite winding-clock transform** `â(k) = Σ_j a_j ζ^{jk}` onto the integer
channel frequencies `k = 0, …, n-1`, `ζ` any primitive `n`-th root of unity.

Every field of the structure is exercised by a real proof:

* **(v) no kernel** = injectivity of the transform, and it reduces to the same layerwise
  Vandermonde separation that powers retention (`windingTransform_injective` consumes
  `momentTower_detects` at the nodes `ζ^j`, extended from `k < n` to all `k` by periodicity) —
  the geometric faithfulness and the model separation are one theorem;
* **DC compatibility** = the finite harmonic dictionary: translation invariance forces
  frequency-zero support (`winding_dc`: the shift identity `ζ^k · â(k) = â(k)` with `ζ^k ≠ 1`);
* **(iii) rationality on the DC locus**: an invariant class concentrates at `k = 0` where its
  amplitude is the rational mass `Σ_j a_j` (`winding_rational`);
* **Recognition is provable here**: an invariant rational class is a rational multiple of the
  diagonal element (`cyclic_recognition`), so the terminus pipeline executes end to end —
  `cyclic_sourceExhaustion` derives unrestricted `SourceExhaustion` for the cyclic dial from the
  realization and recognition, unconditionally.

Register, exact: this is the abelian character-level shadow — the group-algebra analogue of
Lefschetz (1,1) — not a cycle group; the arithmetic landings (Mordell–Weil, CM, Ceresa data)
remain the open constructions.  `Dg.Rational := True` is honest here, not a trivialization: the
geometric space is literally the ℚ-algebra, every class rational.  No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-! ## Root-of-unity exponent arithmetic -/

omit [NeZero n] in
theorem pow_mod_n (hζ : IsPrimitiveRoot ζ n) (a : ℕ) : ζ ^ (a % n) = ζ ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

omit [NeZero n] in
theorem pow_congr_mod (hζ : IsPrimitiveRoot ζ n) {a b : ℕ} (h : a ≡ b [MOD n]) :
    ζ ^ a = ζ ^ b := by
  have h' : a % n = b % n := h
  rw [← pow_mod_n hζ a, ← pow_mod_n hζ b, h']

/-! ## The bank and the transform -/

/-- The cyclic winding bank: channel `k` carries integer frequency `k`. -/
def cyclicBank (n : ℕ) : IntFrequencyBank n where
  freq k := (k.val : ℤ)
  injective _ _ h := Fin.ext (Nat.cast_injective h)

/-- The finite winding-clock transform, raw form: `â(k) = Σ_j a_j ζ^{j·k}`. -/
noncomputable def windingAmp (_hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℚ) :
    GeneralExtensionData 0 n :=
  fun _ k => ∑ j : ZMod n, (a j : ℂ) * ζ ^ (j.val * k.val)

/-- The transform is additive: the (iv-a) extension-compatibility field. -/
noncomputable def windingTransform (hζ : IsPrimitiveRoot ζ n) :
    (ZMod n → ℚ) →+ GeneralExtensionData 0 n where
  toFun := windingAmp hζ
  map_zero' := by
    funext l k
    simp [windingAmp]
  map_add' a b := by
    funext l k
    simp only [windingAmp, Pi.add_apply, Rat.cast_add, add_mul, Finset.sum_add_distrib]

/-! ## (v) No kernel: the transform is injective, by the house Vandermonde engine -/

theorem windingTransform_injective (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (windingTransform hζ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have ha' : windingAmp hζ a = 0 := ha
  have hzero : ∀ k : Fin n, ∑ j : ZMod n, (a j : ℂ) * ζ ^ (j.val * k.val) = 0 := by
    intro k
    exact congrFun (congrFun ha' 0) k
  set e : Fin n ≃ ZMod n := (Fintype.equivFinOfCardEq (ZMod.card n)).symm with he
  have hlaminj : Function.Injective fun i : Fin n => ζ ^ (e i).val := by
    intro i j hij
    exact e.injective (ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hij))
  have hmom : ∀ d : ℕ,
      ∑ i : Fin n, (a (e i) : ℂ) * (fun i : Fin n => ζ ^ (e i).val) i ^ d = 0 := by
    intro d
    have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have h0 : ∑ j : ZMod n, (a j : ℂ) * ζ ^ (j.val * (d % n)) = 0 :=
      hzero ⟨d % n, Nat.mod_lt _ hn0⟩
    rw [← Equiv.sum_comp e (fun j : ZMod n => (a j : ℂ) * ζ ^ (j.val * (d % n)))] at h0
    calc ∑ i : Fin n, (a (e i) : ℂ) * (ζ ^ (e i).val) ^ d
        = ∑ i : Fin n, (a (e i) : ℂ) * ζ ^ ((e i).val * (d % n)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← pow_mul,
            pow_congr_mod hζ ((Nat.ModEq.mul_left _ (Nat.mod_modEq d n)).symm)]
      _ = 0 := h0
  have hc := momentTower_detects (fun i : Fin n => ζ ^ (e i).val)
    (fun i => (a (e i) : ℂ)) hlaminj hmom
  funext j
  have hcast : (a j : ℂ) = 0 := by
    have h := congrFun hc (e.symm j)
    rwa [Equiv.apply_symm_apply] at h
  exact_mod_cast hcast

/-! ## DC compatibility: the finite harmonic dictionary -/

/-- **Translation invariance forces frequency-zero support** — the discrete form of the
harmonic dictionary (`modelDC_iff_angularFixed`), on a genuine object: the shift identity gives
`ζ^k · â(k) = â(k)`, and `ζ^k ≠ 1` for `0 < k < n`. -/
theorem winding_dc (hζ : IsPrimitiveRoot ζ n) {a : ZMod n → ℚ}
    (hdc : ∀ j : ZMod n, a (j + 1) = a j) :
    ModelDC (cyclicBank n) (windingAmp hζ a) := by
  intro l k hk
  have hkv : k.val ≠ 0 := by
    intro h
    exact hk (by simp [cyclicBank, h])
  have h1n : 1 < n := by have := k.isLt; omega
  have hval1 : (1 : ZMod n).val = 1 := by
    haveI : Fact (1 < n) := ⟨h1n⟩
    exact ZMod.val_one n
  set S := ∑ j : ZMod n, (a j : ℂ) * ζ ^ (j.val * k.val) with hS
  have key : ζ ^ k.val * S = S := by
    calc ζ ^ k.val * S
        = ∑ j : ZMod n, (a j : ℂ) * ζ ^ ((j + 1).val * k.val) := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hcong : (j + 1).val * k.val ≡ (j.val + 1) * k.val [MOD n] := by
            refine Nat.ModEq.mul_right k.val ?_
            rw [ZMod.val_add, hval1]
            exact Nat.mod_modEq _ n
          rw [pow_congr_mod hζ hcong, add_mul, one_mul, pow_add]
          ring
      _ = ∑ j : ZMod n, (a (j + 1) : ℂ) * ζ ^ ((j + 1).val * k.val) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hdc j]
      _ = S := by
          rw [hS]
          exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
            (fun j => (a (j + 1) : ℂ) * ζ ^ ((j + 1).val * k.val))
            (fun x => (a x : ℂ) * ζ ^ (x.val * k.val)) (fun j => rfl)
  have hne : ζ ^ k.val ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt hkv k.isLt
  have h0 : (ζ ^ k.val - 1) * S = 0 := by rw [sub_mul, one_mul, key, sub_self]
  have hS0 := (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  show windingAmp hζ a l k = 0
  simp only [windingAmp]
  exact hS ▸ hS0

/-! ## (iii) Rationality, read on the DC locus -/

/-- An invariant class concentrates at `k = 0`, where its amplitude is the rational mass
`Σ_j a_j`; all other channels vanish.  So the image is channel-wise rational — exactly on the
DC locus, which is where the interface reads it. -/
theorem winding_rational (hζ : IsPrimitiveRoot ζ n) {a : ZMod n → ℚ}
    (hdc : ∀ j : ZMod n, a (j + 1) = a j) :
    ModelRational (windingAmp hζ a) := by
  intro l k
  by_cases hk : k.val = 0
  · refine ⟨∑ j : ZMod n, a j, ?_⟩
    show ∑ j : ZMod n, (a j : ℂ) * ζ ^ (j.val * k.val) = _
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hk, Nat.mul_zero, pow_zero, mul_one]
  · exact ⟨0, by
      rw [Rat.cast_zero]
      exact winding_dc hζ hdc l k (by simp [cyclicBank, hk])⟩

/-! ## The geometric dial and the realization term -/

/-- The cyclic geometric dial: `DC` = translation invariance (the discrete torus action),
`Rational` = `True` (honest: the space is literally the ℚ-algebra), `Algebraic` = rational
multiple of the diagonal element, readouts = the winding tower. -/
noncomputable def cyclicDial (hζ : IsPrimitiveRoot ζ n) : HodgeDial (ZMod n → ℚ) where
  DC a := ∀ j : ZMod n, a (j + 1) = a j
  Rational _ := True
  Algebraic a := ∃ q : ℚ, a = fun _ => q
  T d a := generalExtensionTower (cyclicBank n).toClockBank d (windingTransform hζ a)

/-- **The first genuine realization term**: `ℚ[ℤ/n]` with the winding-clock transform satisfies
all five conditions of the bridge. -/
noncomputable def cyclicRealization (hζ : IsPrimitiveRoot ζ n) :
    FaithfulRealization (cyclicDial hζ) 0 (cyclicBank n) where
  toModel := windingTransform hζ
  regCompat _ _ := rfl
  ratCompat _ hdc _ := winding_rational hζ hdc
  dcCompat _ hdc := winding_dc hζ hdc
  noKernel _ _ _ h := windingTransform_injective hζ (h.trans (map_zero _).symm)

/-- Retention for the cyclic dial — supplied by the bridge, not re-proved. -/
theorem cyclic_retention (hζ : IsPrimitiveRoot ζ n) : Retention (cyclicDial hζ) :=
  (cyclicRealization hζ).retention

/-! ## Recognition, provable here, and the executed terminus -/

/-- **Recognition for the cyclic dial**: an invariant rational class is constant — a rational
multiple of the diagonal element. -/
theorem cyclic_recognition (hζ : IsPrimitiveRoot ζ n) : Recognition (cyclicDial hζ) := by
  rintro a - hdc -
  have hconst : ∀ t : ℕ, a ((t : ℕ) : ZMod n) = a 0 := by
    intro t
    induction t with
    | zero => simp
    | succ s ih =>
        have hcast : ((s + 1 : ℕ) : ZMod n) = ((s : ℕ) : ZMod n) + 1 := by push_cast; ring
        rw [hcast, hdc, ih]
  refine ⟨a 0, funext fun j => ?_⟩
  have hj : ((j.val : ℕ) : ZMod n) = j := ZMod.natCast_rightInverse j
  rw [← hj, hconst]

/-- **The terminus, executed end to end on a genuine object**: source exhaustion for the cyclic
dial, from the realization term and recognition, unconditionally. -/
theorem cyclic_sourceExhaustion (hζ : IsPrimitiveRoot ζ n) :
    SourceExhaustion (cyclicDial hζ) :=
  (cyclicRealization hζ).sourceExhaustion_of_recognition (cyclic_recognition hζ)

/-- Unpacked: every nonzero translation-invariant class in `ℚ[ℤ/n]` is a rational multiple of
the diagonal — the group-algebra shadow of Lefschetz (1,1), delivered by the pipeline. -/
theorem cyclic_diagonal_law (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℚ) (ha : a ≠ 0)
    (hdc : ∀ j : ZMod n, a (j + 1) = a j) : ∃ q : ℚ, a = fun _ => q :=
  cyclic_sourceExhaustion hζ a ha hdc trivial

/-- The concrete instantiation at `ζ = e^{2πi/n}`. -/
theorem cyclic_sourceExhaustion_exp (n : ℕ) [NeZero n] :
    SourceExhaustion (cyclicDial (Complex.isPrimitiveRoot_exp n (NeZero.ne n))) :=
  cyclic_sourceExhaustion _

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.windingTransform_injective
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.winding_dc
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.cyclic_recognition
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.cyclic_sourceExhaustion
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.cyclic_diagonal_law
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.cyclic_sourceExhaustion_exp
