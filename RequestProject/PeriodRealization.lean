import RequestProject.CeresaFamilyRetention
import RequestProject.HodgeRealizationBridge

/-!
# The period realization: the transcendental layer's interface, designed
# and instantiated on the Ceresa family

`CeresaFamilyRetention` proved the retention half at family level and
isolated the exact misfit: `FaithfulRealization.ratCompat` cannot hold for
a transcendental-valued readout — a Beilinson–Bloch height is not a
rational amplitude.  This file supplies the designed interface variant and
its Ceresa-family instantiation:

* `PeriodRational` — the correct rational structure at the transcendental
  layer: every amplitude is a RATIONAL MULTIPLE of its channel period
  (rank-one period lattice per channel; rationality of ratios, not of
  values).
* `PeriodRealization` — the five-condition realization with `ratCompat`
  replaced by `periodCompat`; retention transports along it unchanged
  (`PeriodRealization.retention`), and the terminus reduction specializes
  (`PeriodRealization.sourceExhaustion_of_recognition`).
* `ceresaPeriodRealization` — the instantiation on the Laga–Shnidman
  Ceresa bundle: the depth-three channel of a non-torsion member realizes
  `ℤ` with period the member's Beilinson–Bloch height; `noKernel` is the
  family bundle's no-silent-class theorem; the readout IS the height
  (`readout_is_bb_height`).
* `ratCompat_uninhabitable` — the misfit as a theorem: if the member's
  height is irrational, `ModelRational` FAILS on the generator's image, so
  the rationality field of `FaithfulRealization` is uninhabitable at this
  layer while `periodCompat` holds.  (Irrationality of Beilinson–Bloch
  heights is open; the statement is hypothesis-typed on purpose.)
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-! ## The interface -/

/-- Channelwise period data for a transcendental layer: one period per
layer/channel pair. -/
structure PeriodStructure (order m : ℕ) where
  period : Fin (order + 1) → Fin m → ℂ

/-- **Period-rationality** — the transcendental layer's replacement for
`ModelRational`: every amplitude is a rational multiple of its channel
period. -/
def PeriodRational {order m : ℕ} (P : PeriodStructure order m)
    (z : GeneralExtensionData order m) : Prop :=
  ∀ (l : Fin (order + 1)) (i : Fin m), ∃ q : ℚ, z l i = (q : ℂ) * P.period l i

/-- **The period-faithful realization**: the five-condition realization of
`HodgeRealizationBridge` with the rationality field replaced by the
period-lattice structure — the interface a transcendental readout can
actually inhabit. -/
structure PeriodRealization {Zg : Type*} [AddCommGroup Zg] (Dg : HodgeDial Zg)
    (order : ℕ) {m : ℕ} (B : IntFrequencyBank m) where
  /-- (iv-a) the realization is additive. -/
  toModel : Zg →+ GeneralExtensionData order m
  /-- the channel periods of the transcendental layer. -/
  periods : PeriodStructure order m
  /-- (iv-b) the geometric readouts are the paired layer/moment tower. -/
  regCompat : ∀ (d : ℕ) (z : Zg), Dg.T d z = generalExtensionTower B.toClockBank d (toModel z)
  /-- (iii-per) rational DC geometric classes land on the period lattice. -/
  periodCompat : ∀ z : Zg, Dg.DC z → Dg.Rational z → PeriodRational periods (toModel z)
  /-- (iii') DC geometric classes land on the frequency-zero locus. -/
  dcCompat : ∀ z : Zg, Dg.DC z → ModelDC B (toModel z)
  /-- (v) no kernel on the classes at issue. -/
  noKernel : ∀ z : Zg, Dg.DC z → Dg.Rational z → toModel z = 0 → z = 0

/-- **Retention transports along any period realization** — the same
Vandermonde firing as `FaithfulRealization.retention`; the rationality
replacement costs nothing on the detection leg. -/
theorem PeriodRealization.retention {Zg : Type*} [AddCommGroup Zg] {Dg : HodgeDial Zg}
    {order m : ℕ} {B : IntFrequencyBank m} (R : PeriodRealization Dg order B) :
    Retention Dg := by
  intro z hz hdc hrat
  have hmodel : R.toModel z ≠ 0 := fun h0 => hz (R.noKernel z hdc hrat h0)
  obtain ⟨d, hd⟩ := generalExtensionTower_exhaustive B.toClockBank (R.toModel z) hmodel
  exact ⟨d, by rw [R.regCompat]; exact hd⟩

/-- **The terminus reduction along a period realization**: a transcendental
geometric dial admitting the period interface needs `Recognition` alone. -/
theorem PeriodRealization.sourceExhaustion_of_recognition {Zg : Type*} [AddCommGroup Zg]
    {Dg : HodgeDial Zg} {order m : ℕ} {B : IntFrequencyBank m}
    (R : PeriodRealization Dg order B) (hrec : Recognition Dg) :
    SourceExhaustion Dg :=
  hodge_of_retention_recognition R.retention hrec

/-! ## The Ceresa-family instantiation -/

namespace CeresaPeriod

variable {T : Type*}

/-- The depth-three channel bank: frequencies `(−1, 0, 1)` flanking the
period channel at frequency zero. -/
def ceresaBank : IntFrequencyBank 3 where
  freq := ![-1, 0, 1]
  injective := by decide

/-- The model image of the member's Ceresa multiples: `n` lands as
`n · h` on the frequency-zero channel of the depth-three layer, where `h`
is the member's Beilinson–Bloch height. -/
noncomputable def ceresaModelFun (h : ℝ) (n : ℤ) : GeneralExtensionData 3 3 :=
  fun l i => if l = 3 ∧ i = 1 then (n : ℂ) * (h : ℂ) else 0

theorem ceresaModelFun_add (h : ℝ) (n k : ℤ) :
    ceresaModelFun h (n + k) = ceresaModelFun h n + ceresaModelFun h k := by
  funext l i
  simp only [ceresaModelFun, Pi.add_apply]
  by_cases hc : l = 3 ∧ i = 1
  · simp only [if_pos hc]
    push_cast
    ring
  · simp [hc]

/-- The member's Ceresa dial: the depth-three readout of the multiples of
the class.  Cycles by provenance; the open content is non-triviality, which
is exactly what the bundle's no-silent theorem reads. -/
noncomputable def ceresaDial (D : CeresaFamilyData T) (t : T) : HodgeDial ℤ where
  DC _ := True
  Rational _ := True
  Algebraic _ := True
  T d n := generalExtensionTower ceresaBank.toClockBank d
    (ceresaModelFun (D.bbHeight t) n)

/-- **The period realization of the Ceresa channel** — the transcendental
layer inhabited: period = the member's Beilinson–Bloch height, `noKernel`
= the family bundle's no-silent-class theorem. -/
noncomputable def ceresaPeriodRealization (D : CeresaFamilyData T) (t : T)
    (ht : ¬ D.IsTorsion t) :
    PeriodRealization (ceresaDial D t) 3 ceresaBank where
  toModel := AddMonoidHom.mk' (ceresaModelFun (D.bbHeight t))
    (ceresaModelFun_add (D.bbHeight t))
  periods := ⟨fun _ _ => ((D.bbHeight t : ℝ) : ℂ)⟩
  regCompat _ _ := rfl
  periodCompat n _ _ := by
    intro l i
    by_cases hc : l = 3 ∧ i = 1
    · obtain ⟨h3, h1⟩ := hc
      subst h3
      subst h1
      refine ⟨(n : ℚ), ?_⟩
      show ceresaModelFun (D.bbHeight t) n 3 1
        = ((n : ℚ) : ℂ) * ((D.bbHeight t : ℝ) : ℂ)
      rw [show ceresaModelFun (D.bbHeight t) n 3 1
        = (n : ℂ) * ((D.bbHeight t : ℝ) : ℂ) by simp [ceresaModelFun]]
      push_cast
      ring
    · exact ⟨0, by simp [ceresaModelFun, hc]⟩
  dcCompat n _ := by
    intro l i hfreq
    have hi : ¬ (l = 3 ∧ i = 1) := by
      rintro ⟨-, hi1⟩
      subst hi1
      exact hfreq (by decide)
    simp [ceresaModelFun, hi]
  noKernel n _ _ h0 := by
    have h1 := congrFun (congrFun h0 3) 1
    have h2 : (n : ℂ) * ((D.bbHeight t : ℝ) : ℂ) = 0 := by
      simpa [ceresaModelFun] using h1
    rcases mul_eq_zero.mp h2 with hn | hh
    · exact_mod_cast hn
    · exact absurd (Complex.ofReal_eq_zero.mp hh)
        (D.no_silent_ceresa t ht)

/-- **The readout is the height**: the moment-zero depth-three tower level
of `n` is exactly `n` times the member's Beilinson–Bloch height. -/
theorem readout_is_bb_height (D : CeresaFamilyData T) (t : T) (n : ℤ) :
    (ceresaDial D t).T (Nat.pair ((3 : Fin 4) : ℕ) 0) n
      = (n : ℂ) * ((D.bbHeight t : ℝ) : ℂ) := by
  show generalExtensionTower ceresaBank.toClockBank (Nat.pair ((3 : Fin 4) : ℕ) 0)
      (ceresaModelFun (D.bbHeight t) n) = _
  rw [generalExtensionTower_pair ceresaBank.toClockBank 3 0
    (ceresaModelFun (D.bbHeight t) n)]
  rw [Fin.sum_univ_three]
  simp [ceresaModelFun]

/-- **Family-level transcendental retention through the typed interface**:
every non-torsion member's channel retains — now as a transport theorem
along the period realization, upgrading the bundle-level statement of
`CeresaFamilyRetention` into the designed interface. -/
theorem ceresa_period_retention (D : CeresaFamilyData T) (t : T)
    (ht : ¬ D.IsTorsion t) : Retention (ceresaDial D t) :=
  (ceresaPeriodRealization D t ht).retention

/-! ## The misfit, as a theorem -/

/-- **Why the variant is necessary**: if the member's Beilinson–Bloch
height is irrational, the generator's model image is NOT rational-amplitude
— `ModelRational` fails, so `FaithfulRealization.ratCompat` is
uninhabitable at the transcendental layer, while `periodCompat` holds
(the realization above).  Hypothesis-typed: irrationality of
Beilinson–Bloch heights is open. -/
theorem ratCompat_uninhabitable (D : CeresaFamilyData T) (t : T)
    (hirr : ∀ q : ℚ, D.bbHeight t ≠ (q : ℝ)) :
    ¬ ModelRational (ceresaModelFun (D.bbHeight t) 1) := by
  intro hrat
  obtain ⟨q, hq⟩ := hrat 3 1
  have hq2 : ((D.bbHeight t : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by
    have hlhs : ceresaModelFun (D.bbHeight t) 1 3 1
        = ((D.bbHeight t : ℝ) : ℂ) := by
      simp [ceresaModelFun]
    rw [hlhs] at hq
    rw [hq]
    push_cast
    ring
  exact hirr q (Complex.ofReal_inj.mp hq2)

end CeresaPeriod

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.PeriodRealization.retention
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaPeriod.ceresa_period_retention
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaPeriod.readout_is_bb_height
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaPeriod.ratCompat_uninhabitable
