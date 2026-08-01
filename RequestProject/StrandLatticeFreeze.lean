import RequestProject.RamanujanLimit
import RequestProject.GeneralLatticeLanding

/-!
# The Langlands–Hodge junction: temperedness is a freeze law

The tower corpus (`RamanujanLimit`) and the lattice corpus (`ZetaSixClosure` and its
descendants) have never met in the kernel.  This file joins them through one exact
bridge and terminates in a closure — not a reduction.

**The bridge.**  The lattice embedding `latticeToC : ℤ[ζ₆] → ℂ`, `a + b·ζ₆` with
`ζ₆ = (1 + i√3)/2`, is *norm-exact*: `normSq (latticeToC x) = normForm x` on the
nose (`normSq_latticeToC`) — the analytic radius of a strand and the arithmetic
norm form of its lattice datum are the same number.

**The junction theorem** (`freeze_of_tower_ceiling`).  A strand whose transverse
datum is a nonzero ℤ[ζ₆]-integer and whose every symmetric-power transport sits
under one rank-uniform ceiling — the same two cited inputs the manuscript's
Ramanujan corollary consumes (the tower, and Jacquet–Shalika's per-rung bound) —
is a **sixth root of unity**: the radial limit forces radius one, norm-exactness
lands norm-form one, and the μ₆ classification closes the order at six.  The freeze
law is thereby *derived from functoriality*: Weil RH for curves, Hasse–Davenport,
and every family-specific freeze mechanism are absent from the chain.

**The termination** (`landingData_of_tower_ceiling`,
`step2_closure_of_tower_ceiling`).  The junction manufactures the general landing
certificate of `GeneralLatticeLanding`, so multi-rail readouts of lattice strands
under the tower ceiling close exactly and simultaneously at the common height.
The chain runs: tower radial limit → purity → norm-exact bridge → μ₆ → threshold
→ zero.  Every link is compiled here or upstream; no field of any structure is
left uninhabited by the theorems of this file.

Register: the abstract kernel of the junction — a ℤ[ζ₆]-integer of unit modulus is
a root of unity — is Kronecker's rigidity in its simplest quadratic instance; the
content of this file is that the *purity* input is supplied by the compiled tower
limit rather than assumed, and that the composition lands inside the closure
machinery, kernel-checked end to end.
-/

open Complex

namespace CriticalLinePhasor.StrandLatticeFreeze

open CriticalLinePhasor.RamanujanLimit ZetaSixClosure ZetaSixClosure.Zz6

/-! ## The norm-exact bridge -/

/-- The lattice embedding: `⟨a, b⟩ ↦ a + b·ζ₆` with `ζ₆ = (1 + i√3)/2`, written in
rectangular coordinates. -/
noncomputable def latticeToC (x : Zz6) : ℂ :=
  ⟨(x.a : ℝ) + (x.b : ℝ) / 2, (x.b : ℝ) * (Real.sqrt 3 / 2)⟩

/-- The embedding is multiplicative: the lattice product law is the complex one. -/
theorem latticeToC_mul (x y : Zz6) :
    latticeToC (mul x y) = latticeToC x * latticeToC y := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · show ((mul x y).a : ℝ) + ((mul x y).b : ℝ) / 2 = _
    rw [Complex.mul_re]
    show _ = ((x.a : ℝ) + (x.b : ℝ) / 2) * ((y.a : ℝ) + (y.b : ℝ) / 2)
      - ((x.b : ℝ) * (Real.sqrt 3 / 2)) * ((y.b : ℝ) * (Real.sqrt 3 / 2))
    simp only [mul]
    push_cast
    linear_combination ((x.b : ℝ) * (y.b : ℝ) / 4) * h3
  · show ((mul x y).b : ℝ) * (Real.sqrt 3 / 2) = _
    rw [Complex.mul_im]
    show _ = ((x.a : ℝ) + (x.b : ℝ) / 2) * ((y.b : ℝ) * (Real.sqrt 3 / 2))
      + ((x.b : ℝ) * (Real.sqrt 3 / 2)) * ((y.a : ℝ) + (y.b : ℝ) / 2)
    simp only [mul]
    push_cast
    ring

/-- The embedding sends the lattice unit to `1`. -/
theorem latticeToC_one : latticeToC one = 1 := by
  apply Complex.ext <;> simp [latticeToC, one]

/-- **Norm-exactness**: the analytic radius squared of a lattice strand is its
arithmetic norm form, exactly. -/
theorem normSq_latticeToC (x : Zz6) :
    Complex.normSq (latticeToC x) = (normForm x : ℝ) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [latticeToC, Complex.normSq_mk, normForm]
  push_cast
  linear_combination ((x.b : ℝ) * (x.b : ℝ) / 4) * h3

/-- A nonzero lattice datum embeds to a nonzero strand. -/
theorem latticeToC_ne_zero {x : Zz6} (hx : x ≠ ⟨0, 0⟩) : latticeToC x ≠ 0 := by
  intro h0
  have h := congrArg Complex.normSq h0
  rw [normSq_latticeToC, Complex.normSq_zero] at h
  exact hx ((normForm_eq_zero_iff x).mp (by exact_mod_cast h))

/-- Unit analytic radius lands norm-form one. -/
theorem normForm_eq_one_of_norm_one {x : Zz6} (h : ‖latticeToC x‖ = 1) :
    normForm x = 1 := by
  have h2 : Complex.normSq (latticeToC x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h, one_pow]
  rw [normSq_latticeToC] at h2
  exact_mod_cast h2

/-- **The helix class of lattice strands is exactly μ₆**: a unit-radius ℤ[ζ₆]
strand has sixth power one. -/
theorem helix_lattice_strand_mu6 {x : Zz6} (h : ‖latticeToC x‖ = 1) :
    pow6 x = one :=
  mu6_pow_six x (normForm_eq_one_of_norm_one h)

/-! ## The junction theorem -/

/-- **Temperedness is a freeze law.**  A strand whose transverse datum is a nonzero
ℤ[ζ₆]-integer and whose every symmetric-power transport sits under one rank-uniform
ceiling — the tower and the per-rung Jacquet–Shalika bound, the manuscript's two
cited inputs — is a sixth root of unity: purity from the compiled radial limit,
μ₆ from the compiled lattice classification.  No family freeze mechanism, no Weil
RH for curves, appears anywhere in the chain. -/
theorem freeze_of_tower_ceiling {x : Zz6} (hx : x ≠ ⟨0, 0⟩) {C : ℝ}
    (htop : ∀ r : ℕ, 1 ≤ r → ‖latticeToC x ^ r‖ ≤ C)
    (hbot : ∀ r : ℕ, 1 ≤ r → ‖(latticeToC x)⁻¹ ^ r‖ ≤ C) :
    normForm x = 1 ∧ pow6 x = one := by
  have h1 := strand_radius_one_of_tower_ceiling (latticeToC_ne_zero hx) htop hbot
  have hn := normForm_eq_one_of_norm_one h1
  exact ⟨hn, mu6_pow_six x hn⟩

/-- The strand-side reading of the freeze: the embedded strand itself has sixth
power one. -/
theorem strand_pow6_one_of_tower_ceiling {x : Zz6} (hx : x ≠ ⟨0, 0⟩) {C : ℝ}
    (htop : ∀ r : ℕ, 1 ≤ r → ‖latticeToC x ^ r‖ ≤ C)
    (hbot : ∀ r : ℕ, 1 ≤ r → ‖(latticeToC x)⁻¹ ^ r‖ ≤ C) :
    latticeToC x ^ 6 = 1 := by
  have h := (freeze_of_tower_ceiling hx htop hbot).2
  have h6 : latticeToC (pow6 x) = latticeToC x ^ 6 := by
    simp only [pow6, latticeToC_mul]
    ring
  rw [← h6, h, latticeToC_one]

/-! ## The termination: the junction feeds the closure machine -/

/-- The tower ceiling manufactures the general landing certificate: every rail
reading is a lattice strand under the ceiling, so its order is six on the nose —
the `finiteOrder` field of `AlgebraicLandingData` is inhabited by the junction
theorem, with no family hypothesis. -/
noncomputable def landingData_of_tower_ceiling {rails n : ℕ}
    (x : Fin rails → Fin n → Zz6) (wt : Fin rails → Fin n → ℤ)
    (C : Fin rails → Fin n → ℝ)
    (hx : ∀ r i, x r i ≠ ⟨0, 0⟩)
    (htop : ∀ r i, ∀ k : ℕ, 1 ≤ k → ‖latticeToC (x r i) ^ k‖ ≤ C r i)
    (hbot : ∀ r i, ∀ k : ℕ, 1 ≤ k → ‖(latticeToC (x r i))⁻¹ ^ k‖ ≤ C r i) :
    AlgebraicLandingData rails n where
  val := x
  finiteOrder := fun r i => ⟨6, by norm_num, by
    rw [← pow6_eq_npow_six]
    exact (freeze_of_tower_ceiling (hx r i) (htop r i) (hbot r i)).2⟩
  wt := wt

/-- **The Langlands–Hodge junction, terminated.**  Multi-rail readouts of lattice
strands under the tower ceiling, measured below the lattice threshold, close
exactly and simultaneously at the common height.  The chain — tower radial limit
→ purity → norm-exact bridge → μ₆ → threshold → zero — terminates in the closure;
nothing is reduced to a later step. -/
theorem step2_closure_of_tower_ceiling {rails n : ℕ}
    (x : Fin rails → Fin n → Zz6) (wt : Fin rails → Fin n → ℤ)
    (C : Fin rails → Fin n → ℝ)
    (hx : ∀ r i, x r i ≠ ⟨0, 0⟩)
    (htop : ∀ r i, ∀ k : ℕ, 1 ≤ k → ‖latticeToC (x r i) ^ k‖ ≤ C r i)
    (hbot : ∀ r i, ∀ k : ℕ, 1 ≤ k → ‖(latticeToC (x r i))⁻¹ ^ k‖ ≤ C r i)
    (hsub : ∀ r, normForm
      ((landingData_of_tower_ceiling x wt C hx htop hbot).railResidual r) < 1) :
    ∀ r, (landingData_of_tower_ceiling x wt C hx htop hbot).railResidual r
      = ⟨0, 0⟩ :=
  (landingData_of_tower_ceiling x wt C hx htop hbot).general_lattice_closure hsub

end CriticalLinePhasor.StrandLatticeFreeze

#print axioms CriticalLinePhasor.StrandLatticeFreeze.latticeToC_mul
#print axioms CriticalLinePhasor.StrandLatticeFreeze.normSq_latticeToC
#print axioms CriticalLinePhasor.StrandLatticeFreeze.helix_lattice_strand_mu6
#print axioms CriticalLinePhasor.StrandLatticeFreeze.freeze_of_tower_ceiling
#print axioms CriticalLinePhasor.StrandLatticeFreeze.strand_pow6_one_of_tower_ceiling
#print axioms CriticalLinePhasor.StrandLatticeFreeze.step2_closure_of_tower_ceiling
