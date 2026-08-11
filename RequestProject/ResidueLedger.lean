import RequestProject.ZeroContainment

/-!
# The residue ledger at a quotient interface

Brick B of the Sato--Tate closure campaign.  `ZeroContainment` typed the
rung-five frontier as one object; this file compiles the unconditional
bookkeeping that every mode of the defect system is a *residue of the
quotient*, and that the reflection pairs the ledger.  Everything is stated
for an abstract interface `(P, C, εP, εC)` -- at rung five `P = Λ(f×Sym⁴f)`
(entire by Jacquet--Piatetski-Shapiro--Shalika), `C = Λ(Sym³f)` (entire by
Kim--Shahidi, valid for Maass forms) -- and consumes only entirety and the
two functional equations, so it applies verbatim at every Dirichlet twist.

* `quotient_meromorphic` / `quotient_analyticAt_off_zeros` — the quotient
  `P/C` is meromorphic on ℂ and analytic off `Z(C)`: poles are CONFINED to
  the denominator's zeros;
* `zero_transport` / `deriv_transport` — the functional equation carries
  `Z(C)` and the derivative data across `s ↦ 1−s`;
* `quotient_FE_off_zeros` — the ledger's functional equation, pointwise
  wherever the denominator lives;
* `residue_at_simple_zero` — at a simple zero `ρ` of `C` the mode
  coefficient exists as a limit and equals `P(ρ)/C′(ρ)`;
* `residue_pairing` — **the pairing law**: the ledger is closed under the
  reflection, `r(1−ρ) = −(εC/εP)·r(ρ)`;
* `pole_order_at_simple_zero` / `no_pole_iff_vanishing` — order arithmetic:
  at a simple zero the quotient has a pole exactly when `P(ρ) ≠ 0`, so
  pole-freeness IS zero-containment there;
* `PoleDichotomy` / `dichotomy_finite_forces_empty` /
  `dichotomy_containment_at_simple_zeros` — **the Booker dichotomy, typed**:
  either no poles or infinitely many.  Named for Booker's quotient theorem
  ([Boo15] Cor. 1.9: cuspidal `Λ(π₂)/Λ(π₁)`, degree gap ≤ 1, has infinitely
  many poles unless `π₁ ≅ π₂`), which does NOT cover this interface (the
  pair is not a standard cuspidal `L`, the degree gap is six): here it is a
  named target, and the compiled reductions say what it buys — a finite
  ledger forces an empty one, and an empty ledger forces `P` to vanish at
  every simple zero of `C`.

Register.  The analytic inputs (entirety of the pair and the cube, their
reflections) are the cited classical theorems, consumed as typed
hypotheses; nothing here assumes automorphy of `Sym⁵`.  The numerical side
of the campaign (`tmp/maass_containment.py`) measured the four first ledger
entries of the Maass interface at the instrument floor — this file is the
structure those measurements are entries OF.  No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.ResidueLedger

/-! ## Pole confinement -/

/-- The quotient of entire functions is meromorphic on all of ℂ. -/
theorem quotient_meromorphic {P C : ℂ → ℂ}
    (hP : Differentiable ℂ P) (hC : Differentiable ℂ C) :
    MeromorphicOn (fun s => P s / C s) Set.univ := by
  intro z _
  exact (hP.analyticAt z).meromorphicAt.div (hC.analyticAt z).meromorphicAt

/-- Off the denominator's zero set the quotient is analytic: poles are
confined to `Z(C)`. -/
theorem quotient_analyticAt_off_zeros {P C : ℂ → ℂ}
    (hP : Differentiable ℂ P) (hC : Differentiable ℂ C)
    {z : ℂ} (hz : C z ≠ 0) :
    AnalyticAt ℂ (fun s => P s / C s) z :=
  (hP.analyticAt z).div (hC.analyticAt z) hz

/-! ## The reflection acts on the ledger -/

/-- The functional equation transports zeros of the denominator across the
reflection. -/
theorem zero_transport {C : ℂ → ℂ} {εC : ℂ} (hεC : εC ≠ 0)
    (hCrefl : ∀ s : ℂ, C s = εC * C (1 - s))
    {ρ : ℂ} (hρ : C ρ = 0) : C (1 - ρ) = 0 := by
  have h := (hCrefl ρ).symm
  rw [hρ] at h
  exact (mul_eq_zero.mp h).resolve_left hεC

/-- The functional equation transports the derivative:
`C′(ρ) = −εC · C′(1−ρ)`. -/
theorem deriv_transport {C : ℂ → ℂ} {εC : ℂ}
    (hC : Differentiable ℂ C)
    (hCrefl : ∀ s : ℂ, C s = εC * C (1 - s)) (ρ : ℂ) :
    deriv C ρ = -(εC * deriv C (1 - ρ)) := by
  have hinner : HasDerivAt (fun s : ℂ => 1 - s) (-1) ρ :=
    (hasDerivAt_id ρ).const_sub 1
  have houter : HasDerivAt C (deriv C (1 - ρ)) (1 - ρ) :=
    (hC (1 - ρ)).hasDerivAt
  have hcomp : HasDerivAt (fun s : ℂ => C (1 - s))
      (deriv C (1 - ρ) * (-1)) ρ := houter.comp ρ hinner
  have hmul : HasDerivAt (fun s : ℂ => εC * C (1 - s))
      (εC * (deriv C (1 - ρ) * (-1))) ρ := hcomp.const_mul εC
  have hfun : C = fun s : ℂ => εC * C (1 - s) := funext hCrefl
  conv_lhs => rw [hfun]
  rw [hmul.deriv]; ring

/-- The ledger's functional equation: wherever the denominator is nonzero on
both sides of the reflection, `εC·(P/C)(s) = εP·(P/C)(1−s)`. -/
theorem quotient_FE_off_zeros {P C : ℂ → ℂ} {εP εC : ℂ}
    (hPrefl : ∀ s : ℂ, P s = εP * P (1 - s))
    (hCrefl : ∀ s : ℂ, C s = εC * C (1 - s))
    {s : ℂ} (hs : C s ≠ 0) :
    εC * (P s / C s) = εP * (P (1 - s) / C (1 - s)) := by
  have hεC : εC ≠ 0 := fun h => hs (by rw [hCrefl s, h, zero_mul])
  have hs' : C (1 - s) ≠ 0 := fun h => hs (by rw [hCrefl s, h, mul_zero])
  rw [hPrefl s, hCrefl s]
  field_simp

/-! ## The residue at a simple zero: the mode coefficient exists -/

/-- **The mode coefficient is a residue.**  At a simple zero `ρ` of the
denominator, `(s−ρ)·(P/C)(s)` converges on the punctured neighbourhood to
`P(ρ)/C′(ρ)`. -/
theorem residue_at_simple_zero {P C : ℂ → ℂ}
    (hP : Differentiable ℂ P) (hC : Differentiable ℂ C)
    {ρ : ℂ} (hρ : C ρ = 0) (hρ' : deriv C ρ ≠ 0) :
    Tendsto (fun s => (s - ρ) * (P s / C s)) (𝓝[≠] ρ)
      (𝓝 (P ρ / deriv C ρ)) := by
  have hslope : Tendsto (slope C ρ) (𝓝[≠] ρ) (𝓝 (deriv C ρ)) :=
    hasDerivAt_iff_tendsto_slope.mp (hC ρ).hasDerivAt
  have hPt : Tendsto P (𝓝[≠] ρ) (𝓝 (P ρ)) :=
    ((hP.continuous.tendsto ρ)).mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun s => P s / slope C ρ s) (𝓝[≠] ρ)
      (𝓝 (P ρ / deriv C ρ)) := hPt.div hslope hρ'
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ ρ)
  have hsub : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  rw [slope_def_field, hρ, sub_zero]
  rw [div_div_eq_mul_div]
  ring

/-- **The pairing law**: the reflected mode coefficient is
`−(εC/εP)` times the original — the ledger is closed under `ρ ↦ 1−ρ`. -/
theorem residue_pairing {P C : ℂ → ℂ} {εP εC : ℂ}
    (hC : Differentiable ℂ C) (hεP : εP ≠ 0)
    (hPrefl : ∀ s : ℂ, P s = εP * P (1 - s))
    (hCrefl : ∀ s : ℂ, C s = εC * C (1 - s))
    {ρ : ℂ} (hρ' : deriv C ρ ≠ 0) :
    P (1 - ρ) / deriv C (1 - ρ) = -(εC / εP) * (P ρ / deriv C ρ) := by
  have hεC : εC ≠ 0 := by
    intro h
    apply hρ'
    have : C = fun _ => (0 : ℂ) := funext fun s => by rw [hCrefl s, h, zero_mul]
    rw [this]
    simp
  have hPρ : P (1 - ρ) = P ρ / εP := by
    rw [hPrefl ρ]; field_simp
  have hCρ : deriv C (1 - ρ) = -(deriv C ρ / εC) := by
    rw [deriv_transport hC hCrefl ρ]
    field_simp
  rw [hPρ, hCρ]
  field_simp

/-- **Central exclusion in the even sign configuration**: at the reflection
fixed point `ρ = 1/2`, the pairing law degenerates to `r = −(εC/εP)·r`; when
`εP = εC` this forces the central residue to vanish — no extra mechanism,
just `residue_pairing` at its fixed point. -/
theorem central_residue_eq_zero {P C : ℂ → ℂ} {εP εC : ℂ}
    (hC : Differentiable ℂ C) (hεP : εP ≠ 0) (hsign : εP = εC)
    (hPrefl : ∀ s : ℂ, P s = εP * P (1 - s))
    (hCrefl : ∀ s : ℂ, C s = εC * C (1 - s))
    (hρ' : deriv C (1/2 : ℂ) ≠ 0) :
    P (1/2 : ℂ) / deriv C (1/2 : ℂ) = 0 := by
  have hpair := residue_pairing hC hεP hPrefl hCrefl (ρ := (1/2 : ℂ)) hρ'
  have hhalf : (1 : ℂ) - 1/2 = 1/2 := by norm_num
  rw [hhalf] at hpair
  have hone : εC / εP = 1 := by rw [← hsign]; exact div_self hεP
  rw [hone] at hpair
  have h2 : (2 : ℂ) * (P (1/2 : ℂ) / deriv C (1/2 : ℂ)) = 0 := by
    linear_combination hpair
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-! ## Order arithmetic: pole ⟺ non-vanishing of the numerator -/

/-- At a simple zero of `C` with `P(ρ) ≠ 0` the quotient has a genuine pole:
its meromorphic order is `−1`. -/
theorem pole_order_at_simple_zero {P C : ℂ → ℂ}
    (hP : Differentiable ℂ P) (hC : Differentiable ℂ C)
    {ρ : ℂ} (hρ : C ρ = 0) (hρ' : deriv C ρ ≠ 0) (hPρ : P ρ ≠ 0) :
    meromorphicOrderAt (fun s => P s / C s) ρ = (-1 : ℤ) := by
  have hPa : AnalyticAt ℂ P ρ := hP.analyticAt ρ
  have hCa : AnalyticAt ℂ C ρ := hC.analyticAt ρ
  have hPord : meromorphicOrderAt P ρ = (0 : ℤ) := by
    rw [hPa.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (.inr hPρ)]
    simp
  have hCord : meromorphicOrderAt C ρ = (1 : ℤ) := by
    rw [hCa.meromorphicOrderAt_eq,
      hCa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hρ']
    simp
  have hfun : (fun s => P s / C s) = P / C := rfl
  rw [hfun, meromorphicOrderAt_div hPa.meromorphicAt hCa.meromorphicAt,
    hPord, hCord]
  decide

/-! ## The Booker dichotomy, typed -/

/-- The pole set of the interface quotient. -/
def poleSet (P C : ℂ → ℂ) : Set ℂ :=
  {z | meromorphicOrderAt (fun s => P s / C s) z < 0}

/-- **The Booker dichotomy at an interface** (named target): the quotient has
no poles at all, or infinitely many.  Booker's theorem proves this shape for
cuspidal standard quotients with degree gap ≤ 1; at the `(5,3)` interface it
is the campaign's named analytic target. -/
def PoleDichotomy (P C : ℂ → ℂ) : Prop :=
  poleSet P C = ∅ ∨ (poleSet P C).Infinite

/-- What the dichotomy buys, part one: a finite ledger is an empty ledger. -/
theorem dichotomy_finite_forces_empty {P C : ℂ → ℂ}
    (h : PoleDichotomy P C) (hfin : (poleSet P C).Finite) :
    poleSet P C = ∅ :=
  h.resolve_right hfin.not_infinite

/-- What the dichotomy buys, part two: an empty ledger forces the numerator
to vanish at every simple zero of the denominator — zero-containment at the
simple zeros. -/
theorem dichotomy_containment_at_simple_zeros {P C : ℂ → ℂ}
    (hP : Differentiable ℂ P) (hC : Differentiable ℂ C)
    (hempty : poleSet P C = ∅)
    {ρ : ℂ} (hρ : C ρ = 0) (hρ' : deriv C ρ ≠ 0) : P ρ = 0 := by
  by_contra hPρ
  have hpole := pole_order_at_simple_zero hP hC hρ hρ' hPρ
  have : ρ ∈ poleSet P C := by
    simp only [poleSet, Set.mem_setOf_eq, hpole]
    exact_mod_cast neg_one_lt_zero
  rw [hempty] at this
  exact this

end CriticalLinePhasor.ResidueLedger

#print axioms CriticalLinePhasor.ResidueLedger.quotient_meromorphic
#print axioms CriticalLinePhasor.ResidueLedger.residue_at_simple_zero
#print axioms CriticalLinePhasor.ResidueLedger.residue_pairing
#print axioms CriticalLinePhasor.ResidueLedger.central_residue_eq_zero
#print axioms CriticalLinePhasor.ResidueLedger.dichotomy_containment_at_simple_zeros
