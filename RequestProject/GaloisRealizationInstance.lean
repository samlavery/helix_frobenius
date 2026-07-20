import RequestProject.CyclicRealizationInstance

/-!
# The Artin-motive instance: cyclic Galois number fields on the carrier

Climbs one rung from the combinatorial shadow (`CyclicRealizationInstance`, the group algebra
`ℚ[ℤ/n]`) to a **genuine zero-dimensional variety**: `Spec K` for `K` a finite Galois extension
of `ℚ` with cyclic Galois group — the class covering the CM quadratic fields `ℚ(√-d)` and the
cyclotomic fields `ℚ(ζ_p)`.  The classes are the field elements (the `H^0`/Artin-motive cycle
data), and the pipeline executes end to end:

* **the realization is the classical Lagrange-resolvent transform**
  `R_k(z) = Σ_s ι(g^s z) · ω^{sk}` (`g` the Galois generator, `ι : K →+* ℂ` an embedding,
  `ω = e^{2πi/m}`, `m = |Gal|`), additive, with the winding bank of the cyclic instance reused;
* **(v) no kernel** is again the house Vandermonde engine: vanishing resolvents force all orbit
  coordinates to vanish (`finDFT_detects`, consuming `momentTower_detects`), and the `s = 0`
  coordinate is `ι z` with `ι` a field embedding — geometric faithfulness and model separation
  remain one theorem;
* **DC = the Galois-clock freeze** `g z = z`, and DC compatibility is the geometric-series
  identity: a frozen class has constant orbit coordinates, so every nonzero-frequency resolvent
  is `ι z · Σ_s (ω^k)^s = 0`;
* **Recognition is Artin descent, consumed from the library**: a frozen class is fixed by the
  full group (cyclicity), hence equals the average of its conjugates, hence descends to `ℚ` by
  `trace_eq_sum_automorphisms` — classical Galois theory doing the recognition step;
* `galois_sourceExhaustion` then derives unrestricted `SourceExhaustion`: **every nonzero frozen
  class of the Artin motive has a source in the base field.**

Register, exact: for zero-dimensional varieties the Hodge/Tate statement *is* Galois descent —
classically known, nothing new is claimed about it.  What is new is the executed pipeline: the
five-condition realization, the retention transport, and the recognition step all run on a
genuine arithmetic variety, one dimension up the ladder from the group algebra.  The open rungs
above remain named: `H^1` (Mordell–Weil, CM abelian varieties, Ceresa) awaits its realization
terms.  No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-! ## The general finite winding separation (Fin-indexed, complex coefficients) -/

/-- **Finite DFT separation**: complex coefficients at the winding nodes are determined by the
resolvent values — the Fin-indexed, arbitrary-coefficient form of the Vandermonde engine. -/
theorem finDFT_detects {m : ℕ} [NeZero m] {ω : ℂ} (hω : IsPrimitiveRoot ω m)
    (c : Fin m → ℂ) (h : ∀ k : Fin m, ∑ s : Fin m, c s * ω ^ (s.val * k.val) = 0) : c = 0 := by
  apply momentTower_detects (fun s : Fin m => ω ^ s.val) c
    (fun s t hst => Fin.ext (hω.pow_inj s.isLt t.isLt hst))
  intro d
  have hd : d % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have h0 : ∑ s : Fin m, c s * ω ^ (s.val * (d % m)) = 0 := h ⟨d % m, hd⟩
  calc ∑ s : Fin m, c s * (ω ^ s.val) ^ d
      = ∑ s : Fin m, c s * ω ^ (s.val * (d % m)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← pow_mul, pow_congr_mod hω ((Nat.ModEq.mul_left _ (Nat.mod_modEq d m)).symm)]
    _ = 0 := h0

section ArtinMotive

variable (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]

/-- The channel count: the order of the Galois group. -/
noncomputable def galoisChannels : ℕ := Fintype.card (K ≃ₐ[ℚ] K)

instance : NeZero (galoisChannels K) := ⟨Fintype.card_ne_zero⟩

/-- The winding root `ω = e^{2πi/m}` of the Galois clock. -/
noncomputable def galoisRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (galoisChannels K))

theorem galoisRoot_primitive : IsPrimitiveRoot (galoisRoot K) (galoisChannels K) :=
  Complex.isPrimitiveRoot_exp _ (NeZero.ne _)

variable {K}

/-- **The Lagrange-resolvent transform**, raw form: channel `k` reads
`R_k(z) = Σ_s ι(g^s z) · ω^{sk}` — the classical resolvent of the Galois orbit of `z`. -/
noncomputable def galoisAmp (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ) (z : K) :
    GeneralExtensionData 0 (galoisChannels K) :=
  fun _ k => ∑ s : Fin (galoisChannels K), ι ((g ^ s.val) z) * galoisRoot K ^ (s.val * k.val)

/-- The resolvent transform is additive: the (iv-a) extension-compatibility field. -/
noncomputable def galoisTransform (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ) :
    K →+ GeneralExtensionData 0 (galoisChannels K) where
  toFun := galoisAmp g ι
  map_zero' := by
    funext l k
    simp [galoisAmp]
  map_add' a b := by
    funext l k
    simp only [galoisAmp, map_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]

omit [FiniteDimensional ℚ K] in
/-- A frozen class has constant Galois orbit. -/
theorem frozen_orbit {g : K ≃ₐ[ℚ] K} {z : K} (hdc : g z = z) :
    ∀ s : ℕ, (g ^ s) z = z := by
  intro s
  induction s with
  | zero => simp
  | succ t ih => rw [pow_succ, AlgEquiv.mul_apply, hdc, ih]

/-! ## (v) No kernel: vanishing resolvents kill the class -/

theorem galoisTransform_injective (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ) :
    Function.Injective (galoisTransform g ι) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hz' : galoisAmp g ι z = 0 := hz
  have hc := finDFT_detects (galoisRoot_primitive K)
    (fun s : Fin (galoisChannels K) => ι ((g ^ s.val) z))
    (fun k => congrFun (congrFun hz' 0) k)
  have h0 : ι ((g ^ (0 : ℕ)) z) = 0 :=
    congrFun hc ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
  rw [pow_zero, AlgEquiv.one_apply] at h0
  exact (map_eq_zero ι).mp h0

/-! ## DC compatibility: the frozen class concentrates at frequency zero -/

/-- **Freeze forces frequency-zero support**: a frozen class has constant orbit coordinates, so
every nonzero-frequency resolvent is `ι z` times a full geometric sum of a nontrivial root of
unity — zero. -/
theorem galois_dc (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ) {z : K} (hdc : g z = z) :
    ModelDC (cyclicBank (galoisChannels K)) (galoisAmp g ι z) := by
  intro l k hk
  have hkv : k.val ≠ 0 := by
    intro h
    exact hk (by simp [cyclicBank, h])
  have hne : galoisRoot K ^ k.val ≠ 1 :=
    (galoisRoot_primitive K).pow_ne_one_of_pos_of_lt hkv k.isLt
  show galoisAmp g ι z l k = 0
  simp only [galoisAmp]
  have hterm : ∀ s : Fin (galoisChannels K),
      ι ((g ^ s.val) z) * galoisRoot K ^ (s.val * k.val)
        = ι z * (galoisRoot K ^ k.val) ^ s.val := by
    intro s
    rw [frozen_orbit hdc s.val, Nat.mul_comm, pow_mul]
  rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.mul_sum]
  have hgeom : ∑ s : Fin (galoisChannels K), (galoisRoot K ^ k.val) ^ s.val = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (galoisRoot K ^ k.val) ^ i),
      geom_sum_eq hne, ← pow_mul, Nat.mul_comm, pow_mul,
      (galoisRoot_primitive K).pow_eq_one, one_pow, sub_self, zero_div]
  rw [hgeom, mul_zero]

/-! ## Recognition: Artin descent by trace averaging, consumed from the library -/

/-- **A frozen class descends to the base field.**  Freeze under the generator propagates to the
full group by cyclicity; the class then equals the average of its conjugates, which is
`(1/m)·tr(z)` by `trace_eq_sum_automorphisms` — classical Galois theory as the recognition
step. -/
theorem galois_recognition_of_frozen [IsGalois ℚ K] (g : K ≃ₐ[ℚ] K)
    (hg : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers g) {z : K} (hdc : g z = z) :
    ∃ q : ℚ, z = algebraMap ℚ K q := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hall : ∀ σ : K ≃ₐ[ℚ] K, σ z = z := by
    intro σ
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hg σ)
    rw [← hs]
    obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg s
    · rw [zpow_natCast]
      exact frozen_orbit hdc t
    · rw [zpow_neg, zpow_natCast]
      have h2 : (g ^ t)⁻¹ ((g ^ t) z) = z := by
        rw [← AlgEquiv.mul_apply, inv_mul_cancel]
        exact AlgEquiv.one_apply z
      rw [frozen_orbit hdc t] at h2
      exact h2
  have hsum : ∑ σ : K ≃ₐ[ℚ] K, σ z = (galoisChannels K) • z := by
    rw [Finset.sum_congr rfl fun σ _ => hall σ, Finset.sum_const, Finset.card_univ]
    rfl
  have htr : algebraMap ℚ K (Algebra.trace ℚ K z) = (galoisChannels K) • z := by
    rw [trace_eq_sum_automorphisms, hsum]
  have hm : ((galoisChannels K : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hKne : ((galoisChannels K : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  refine ⟨Algebra.trace ℚ K z / (galoisChannels K : ℚ), ?_⟩
  apply mul_left_cancel₀ hKne
  calc ((galoisChannels K : ℕ) : K) * z
      = (galoisChannels K) • z := (nsmul_eq_mul _ _).symm
    _ = algebraMap ℚ K (Algebra.trace ℚ K z) := htr.symm
    _ = ((galoisChannels K : ℕ) : K)
          * algebraMap ℚ K (Algebra.trace ℚ K z / (galoisChannels K : ℚ)) := by
        rw [← map_natCast (algebraMap ℚ K) (galoisChannels K), ← map_mul]
        congr 1
        field_simp

/-! ## The rational structure, read on the DC locus -/

/-- A frozen class has all resolvent amplitudes rational: the nonzero-frequency channels vanish
and the DC channel carries `m · q`, the rational mass of the descended class. -/
theorem galois_rational [IsGalois ℚ K] (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ)
    (hg : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers g) {z : K} (hdc : g z = z) :
    ModelRational (galoisAmp g ι z) := by
  obtain ⟨q, rfl⟩ := galois_recognition_of_frozen g hg hdc
  intro l k
  by_cases hk : k.val = 0
  · refine ⟨galoisChannels K * q, ?_⟩
    show ∑ s : Fin (galoisChannels K),
        ι ((g ^ s.val) (algebraMap ℚ K q)) * galoisRoot K ^ (s.val * k.val) = _
    have hterm : ∀ s : Fin (galoisChannels K),
        ι ((g ^ s.val) (algebraMap ℚ K q)) * galoisRoot K ^ (s.val * k.val) = (q : ℂ) := by
      intro s
      rw [hk, Nat.mul_zero, pow_zero, mul_one, AlgEquiv.commutes,
        eq_ratCast (algebraMap ℚ K) q, map_ratCast]
    rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · exact ⟨0, by
      rw [Rat.cast_zero]
      exact galois_dc g ι hdc l k (by simp [cyclicBank, hk])⟩

/-! ## The dial, the realization term, and the executed terminus -/

/-- The Artin-motive dial: `DC` = the Galois-clock freeze under the generator, `Rational` =
`True` (honest: the classes are the elements of the rational vector space `K` itself),
`Algebraic` = descends to the base field, readouts = the resolvent tower. -/
noncomputable def galoisDial (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ) : HodgeDial K where
  DC z := g z = z
  Rational _ := True
  Algebraic z := ∃ q : ℚ, z = algebraMap ℚ K q
  T d z := generalExtensionTower (cyclicBank (galoisChannels K)).toClockBank d
    (galoisTransform g ι z)

/-- **The Artin-motive realization term**: a cyclic Galois number field with the
Lagrange-resolvent transform satisfies all five conditions of the bridge. -/
noncomputable def galoisRealization [IsGalois ℚ K] (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ)
    (hg : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers g) :
    FaithfulRealization (galoisDial g ι) 0 (cyclicBank (galoisChannels K)) where
  toModel := galoisTransform g ι
  regCompat _ _ := rfl
  ratCompat _ hdc _ := galois_rational g ι hg hdc
  dcCompat _ hdc := galois_dc g ι hdc
  noKernel _ _ _ h := galoisTransform_injective g ι (h.trans (map_zero _).symm)

/-- Retention for the Artin-motive dial — supplied by the bridge, not re-proved. -/
theorem galois_retention [IsGalois ℚ K] (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ)
    (hg : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers g) : Retention (galoisDial g ι) :=
  (galoisRealization g ι hg).retention

/-- Recognition for the Artin-motive dial: Artin descent. -/
theorem galois_recognition [IsGalois ℚ K] (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ)
    (hg : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers g) : Recognition (galoisDial g ι) :=
  fun _ _ hdc _ => galois_recognition_of_frozen g hg hdc

/-- **The terminus, executed on a genuine variety**: source exhaustion for the Artin-motive
dial of any cyclic Galois number field, from the realization term and Artin descent,
unconditionally. -/
theorem galois_sourceExhaustion [IsGalois ℚ K] (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ)
    (hg : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers g) : SourceExhaustion (galoisDial g ι) :=
  (galoisRealization g ι hg).sourceExhaustion_of_recognition (galois_recognition g ι hg)

/-- Unpacked: **every nonzero frozen class of the Artin motive descends to the base field** —
the zero-dimensional Hodge/Tate statement, delivered by the pipeline. -/
theorem galois_descent_law [IsGalois ℚ K] (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ)
    (hg : ∀ σ : K ≃ₐ[ℚ] K, σ ∈ Subgroup.zpowers g) (z : K) (hz : z ≠ 0) (hdc : g z = z) :
    ∃ q : ℚ, z = algebraMap ℚ K q :=
  galois_sourceExhaustion g ι hg z hz hdc trivial

/-- Any cyclic Galois number field admits the realization: the generator is supplied by
cyclicity. -/
theorem galois_sourceExhaustion_of_isCyclic [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
    (ι : K →+* ℂ) : ∃ g : K ≃ₐ[ℚ] K, SourceExhaustion (galoisDial g ι) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K ≃ₐ[ℚ] K)
  exact ⟨g, galois_sourceExhaustion g ι hg⟩

end ArtinMotive

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.finDFT_detects
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.galoisTransform_injective
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.galois_dc
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.galois_recognition_of_frozen
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.galois_sourceExhaustion
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.galois_descent_law
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.galois_sourceExhaustion_of_isCyclic
