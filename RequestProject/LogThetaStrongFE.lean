import RequestProject.LogReadoutReflection
import RequestProject.CarrierMellinContinuation

/-!
# Strong Mellin functional-equation pairs from carrier exchange

The logarithmic readout already transports carrier conjugation to `x ↦ 1/x`.  This file packages
that result in Mathlib's `StrongFEPair` interface.  Continuity supplies local integrability; the exact
carrier exchange supplies the theta reflection; rapid decay at infinity on the primal and dual legs
then gives the entire, strip-bounded Mellin pair and its global functional equation.
-/

open Complex Set Filter Topology Asymptotics

namespace CriticalLinePhasor.StrandExchange

/-- A single carrier clock becomes a two-term real-power expression on the logarithmic readout. -/
theorem symClock_logReadout_eq (α : ℂ) (ℓ : ℝ) {x : ℝ} (hx : 0 < x) :
    CriticalLinePhasor.ChiralityHB.symClock α ℓ (logReadout x) =
      (x ^ (-ℓ / 2) : ℝ) - α * (x ^ (ℓ / 2) : ℝ) := by
  unfold CriticalLinePhasor.ChiralityHB.symClock logReadout
  have h1 : Complex.I * (Complex.I * (Real.log x : ℂ)) * (ℓ : ℂ) / 2 =
      (((-ℓ / 2) * Real.log x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have h2 : -((((-ℓ / 2) * Real.log x : ℝ) : ℂ)) =
      (((ℓ / 2) * Real.log x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [h1, h2, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx,
    Complex.ofReal_exp, Complex.ofReal_exp]
  congr 2 <;> push_cast <;> ring

/-- A single logarithmic carrier clock has polynomial growth. -/
theorem symClock_logTheta_isBigO (α : ℂ) (ℓ : ℝ) :
    logTheta (CriticalLinePhasor.ChiralityHB.symClock α ℓ) =O[atTop]
      (fun x : ℝ => x ^ max (-ℓ / 2) (ℓ / 2)) := by
  rw [isBigO_iff]
  refine ⟨1 + ‖α‖, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [logTheta, symClock_logReadout_eq α ℓ hx0]
  calc
    ‖(x ^ (-ℓ / 2) : ℝ) - α * (x ^ (ℓ / 2) : ℝ)‖
        ≤ ‖((x ^ (-ℓ / 2) : ℝ) : ℂ)‖ + ‖α * ((x ^ (ℓ / 2) : ℝ) : ℂ)‖ :=
      norm_sub_le _ _
    _ = x ^ (-ℓ / 2) + ‖α‖ * x ^ (ℓ / 2) := by
      simp [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    _ ≤ (1 + ‖α‖) * x ^ max (-ℓ / 2) (ℓ / 2) := by
      have hneg := Real.rpow_le_rpow_of_exponent_le hx.le
        (le_max_left (-ℓ / 2) (ℓ / 2))
      have hpos := Real.rpow_le_rpow_of_exponent_le hx.le
        (le_max_right (-ℓ / 2) (ℓ / 2))
      calc
        x ^ (-ℓ / 2) + ‖α‖ * x ^ (ℓ / 2)
            ≤ x ^ max (-ℓ / 2) (ℓ / 2) +
              ‖α‖ * x ^ max (-ℓ / 2) (ℓ / 2) :=
          add_le_add hneg (mul_le_mul_of_nonneg_left hpos (norm_nonneg α))
        _ = (1 + ‖α‖) * x ^ max (-ℓ / 2) (ℓ / 2) := by ring
    _ = (1 + ‖α‖) * ‖x ^ max (-ℓ / 2) (ℓ / 2)‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]

/-- Multiplication by the self-dual exponential envelope turns any polynomially growing
logarithmic carrier readout into a rapidly decaying theta. -/
theorem completedLogTheta_rapid_of_polynomial
    (E : ℂ → ℂ) (k A : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ A)) :
    ∀ r : ℝ, completedLogTheta E k =O[atTop] (fun x : ℝ => x ^ r) := by
  intro r
  rw [isBigO_iff'] at hpoly ⊢
  obtain ⟨C, hCpos, hC⟩ := hpoly
  have hdec := (isLittleO_exp_neg_mul_rpow_atTop (a := 1) one_pos
    (r - A + k / 2)).isBigO
  rw [isBigO_iff'] at hdec
  obtain ⟨D, hDpos, hD⟩ := hdec
  refine ⟨C * D, mul_pos hCpos hDpos, ?_⟩
  filter_upwards [hC, hD, eventually_gt_atTop (1 : ℝ)] with x hxC hxD hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hexp : Real.exp (-x - x⁻¹) ≤ Real.exp (-x) := by
    rw [Real.exp_le_exp]
    exact sub_le_self _ (inv_nonneg.mpr hx0.le)
  simp only [completedLogTheta, selfDualEnvelope, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
    abs_of_pos (Real.exp_pos _)]
  have hxa : ‖x ^ A‖ = x ^ A := Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)
  have hxD' : Real.exp (-x) ≤ D * x ^ (r - A + k / 2) := by
    simpa [Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] using hxD
  rw [hxa] at hxC
  calc
    x ^ (-k / 2) * Real.exp (-x - x⁻¹) * ‖logTheta E x‖
        ≤ x ^ (-k / 2) * Real.exp (-x) * (C * x ^ A) := by gcongr
    _ ≤ x ^ (-k / 2) * (D * x ^ (r - A + k / 2)) * (C * x ^ A) := by
      gcongr
    _ = (C * D) * x ^ r := by
      calc
        x ^ (-k / 2) * (D * x ^ (r - A + k / 2)) * (C * x ^ A)
            = (C * D) * ((x ^ (-k / 2) * x ^ (r - A + k / 2)) * x ^ A) := by ring
        _ = (C * D) * x ^ r := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          congr 2
          ring

/-- The same polynomial-growth hypothesis gives rapid decay of the dual completed theta, since
complex conjugation preserves norms. -/
theorem completedLogThetaDual_rapid_of_polynomial
    (E : ℂ → ℂ) (k A : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ A)) :
    ∀ r : ℝ, completedLogThetaDual E k =O[atTop] (fun x : ℝ => x ^ r) := by
  intro r
  have hp := completedLogTheta_rapid_of_polynomial E k A hpoly r
  rw [isBigO_iff] at hp ⊢
  obtain ⟨C, hC⟩ := hp
  refine ⟨C, hC.mono fun x hx => ?_⟩
  simpa [completedLogTheta, completedLogThetaDual, logTheta, logThetaDual,
    RCLike.norm_conj] using hx

/-- A continuous carrier with an exact conjugation exchange and rapidly decaying completed
logarithmic readouts defines a strong Riemann--Hecke pair. -/
noncomputable def strongFEPairOfLogExchange
    (E : ℂ → ℂ) (hcont : Continuous E)
    (ε : ℂ) (hε : ε ≠ 0)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k : ℝ) (hk : 0 < k)
    (hf_top : ∀ r : ℝ, completedLogTheta E k =O[atTop] (fun x : ℝ => x ^ r))
    (hg_top : ∀ r : ℝ, completedLogThetaDual E k =O[atTop] (fun x : ℝ => x ^ r)) :
    StrongFEPair ℂ where
  toWeakFEPair := {
    f := completedLogTheta E k
    g := completedLogThetaDual E k
    k := k
    ε := (starRingEnd ℂ) ε
    f₀ := 0
    g₀ := 0
    hf_int := (completedLogTheta_continuousOn E hcont k).locallyIntegrableOn measurableSet_Ioi
    hg_int := (completedLogThetaDual_continuousOn E hcont k).locallyIntegrableOn measurableSet_Ioi
    hk := hk
    hε := (map_ne_zero (starRingEnd ℂ)).2 hε
    h_feq := fun x hx => completedLogTheta_one_div E ε hE k hx
    hf_top := fun r => by simpa using hf_top r
    hg_top := fun r => by simpa using hg_top r
  }
  hf₀ := rfl
  hg₀ := rfl

/-- The complete analytic payload of a logarithmic carrier exchange: primal and dual Mellin
transforms are entire, both are uniformly bounded on every closed vertical strip, and they satisfy
the global functional equation. -/
theorem logExchange_twistedNiceness
    (E : ℂ → ℂ) (hcont : Continuous E)
    (ε : ℂ) (hε : ε ≠ 0)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k : ℝ) (hk : 0 < k)
    (hf_top : ∀ r : ℝ, completedLogTheta E k =O[atTop] (fun x : ℝ => x ^ r))
    (hg_top : ∀ r : ℝ, completedLogThetaDual E k =O[atTop] (fun x : ℝ => x ^ r)) :
    let P := strongFEPairOfLogExchange E hcont ε hε hE k hk hf_top hg_top
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖P.Λ s‖ ≤ C) ∧
    (∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ‖P.symm.Λ s‖ ≤ C) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := strongFEPairOfLogExchange E hcont ε hε hE k hk hf_top hg_top
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun a b => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P a b,
    fun a b => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P.symm a b,
    P.functional_equation⟩

end CriticalLinePhasor.StrandExchange

#print axioms CriticalLinePhasor.StrandExchange.strongFEPairOfLogExchange
#print axioms CriticalLinePhasor.StrandExchange.logExchange_twistedNiceness
#print axioms CriticalLinePhasor.StrandExchange.completedLogTheta_rapid_of_polynomial
#print axioms CriticalLinePhasor.StrandExchange.completedLogThetaDual_rapid_of_polynomial
#print axioms CriticalLinePhasor.StrandExchange.symClock_logReadout_eq
#print axioms CriticalLinePhasor.StrandExchange.symClock_logTheta_isBigO
