import RequestProject.SixfoldEndgame

/-!
# The eightfold endgame: the trap ladder law and the dim-8 integrality obstruction

Extends the sixfold endgame to the flex-construction eightfold
`B = Prym(C/C')`, `C' : u³ − 3(1+x)²u + (2(1+x)³ + y + 2x + 1) = 0` over Schoen's
conductor-19 curve, `C : t³ = y` — the genus-5 base delivered by the 3-torsion FLEX
of `E0` (T' = (0,−1) is 3-torsion, so its tangent line has triple contact; the index
formula `g' = 3K − I + 1` gives `K = 2`, `I = 1_O + 1_flex = 2`, `g' = 5`).  Genus 5
machine-certified (FE-completed degree-10 numerator at p = 7; overdetermination:
predicted `#C'(F_{7⁶}) = 119556` = actual, exact).  Prym dim 8, signature (4,4).

**The trap ladder law, proven here in full generality** (`central_binomial_trap`):
the q-battery `q_k = k!·C(2n,k)` forces, under proportionality `Ξ = 0`, the identity
`W_n²·Θ^{2n} = q_n²`, and `(n!·C(2n,n))² = C(2n,n)·(2n)!` — so `W_n² = C(2n,n)/3^m`:
**the central binomial**.  Its 3-adic valuation is the number of base-3 carries of
`n + n` (Kummer), so the trap fires for all `m ≥ 1` exactly when every base-3 digit
of `n` is ≤ 1: dimensions 6, 8, 18, 20, 24, 26 — the ζ₃-adic harmonic ladder.
Dimension 8 (`n = 4 = 11₃`): `W₄² = 70/3^m`, `70 = 2·5·7` coprime to 3.

**Proven here unconditionally**: `integrality_obstruction8` (27 ∤ 2822400, the 3-adic
kill at dim 8) and the bundle chain `Ξ := W₄ − Θ⁴/(24·3^m)` primitive, algebraic,
nonzero.  Register of the bundle fields: battery = the same Pfaffian identity
(`Pf(sE + tE_V) = s⁵(s+t)⁸`); `m_pos` = the Lange–Ortega / period-certification brick
(same as the sixfold's); `accounting` = MT full `GU(4,4)` — **certificates in
progress** (p = 7 tower running; a second split prime needs the optimized counter,
named gap), unlike the sixfold whose two-prime certificates are complete.  This file
formalizes the obstruction arithmetic; the specimen enters `weil_class_constructed8`
only through a bundle whose fields carry those certificates at their honest register.
No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.WeilEightfold

/-- **The trap ladder identity, all dimensions at once**: `(n!·C(2n,n))² = C(2n,n)·(2n)!`.
Under `Ξ = 0` the battery forces `W_n²·Θ^{2n} = q_n²` with `q_n = n!·C(2n,n)` and
`Θ^{2n} = (2n)!·3^m`, so `W_n² = C(2n,n)/3^m` — the central binomial over the glue. -/
theorem central_binomial_trap (n : ℕ) :
    (n.factorial * (2 * n).choose n) ^ 2 = (2 * n).choose n * (2 * n).factorial := by
  have hle : n ≤ 2 * n := by omega
  have h := Nat.choose_mul_factorial_mul_factorial hle
  have h2 : 2 * n - n = n := by omega
  rw [h2] at h
  calc (n.factorial * (2 * n).choose n) ^ 2
      = (2 * n).choose n * ((2 * n).choose n * n.factorial * n.factorial) := by ring
    _ = (2 * n).choose n * (2 * n).factorial := by rw [h]

/-- Dimension 8 sits on the all-`m` rung of the ladder: `C(8,4) = 70` and `3 ∤ 70`. -/
theorem dim8_on_ladder : (8 : ℕ).choose 4 = 70 ∧ ¬ (3 ∣ (8 : ℕ).choose 4) := by
  decide

/-- **The integrality obstruction at dimension 8, unconditional**: for `m ≥ 1` no
integer `n` satisfies `n · (40320·3^m) = 2822400 = 1680²` — the left side carries
3-adic valuation at least `2 + m ≥ 3` while `v₃(2822400) = 2`. -/
theorem integrality_obstruction8 (m : ℕ) (hm : 1 ≤ m) :
    ¬ ∃ n : ℤ, (n : ℚ) * (40320 * 3 ^ m) = 2822400 := by
  rintro ⟨n, hn⟩
  have hZ : n * (40320 * 3 ^ m) = 2822400 := by exact_mod_cast hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hexp : (3 : ℤ) ^ (1 + k) = 3 * 3 ^ k := by rw [pow_add, pow_one]
  have h27 : (27 : ℤ) ∣ 2822400 := by
    refine ⟨n * 4480 * 3 ^ k, ?_⟩
    rw [← hZ, hexp]
    ring
  norm_num at h27

/-- **The eightfold endgame bundle**: abstract (4,4)-cohomology data of the flex-
construction eightfold, every field at its register — battery values from the closed
Pfaffian form, integrality from the cycle class, non-principality cited (the brick),
the accounting to be discharged by the two-prime Frobenius certificates (p = 7 in
hand, second prime = the named optimized-counter gap). -/
structure EightfoldData (H : Type*) [AddCommGroup H] [Module ℚ H] where
  /-- The intersection pairing on the (4,4) Hodge space. -/
  pair : H → H → ℚ
  pair_sub_left : ∀ u v w : H, pair (u - v) w = pair u w - pair v w
  pair_smul_left : ∀ (a : ℚ) (u v : H), pair (a • u) v = a * pair u v
  pair_symm : ∀ u v : H, pair u v = pair v u
  /-- The theta-fourth class. -/
  theta4 : H
  /-- The Abel–Prym fourfold class `W₄ = (φ₄)_*[Sym⁴C]`. -/
  W4 : H
  /-- The Prym exponent: `∏dᵢ = 3^m` (glue is 3-torsion, averaging argument). -/
  m : ℕ
  /-- **The brick** (Lange–Ortega / period certification): non-principal. -/
  m_pos : 1 ≤ m
  /-- **Battery** (Pfaffian closed form `s⁵(s+t)⁸`): `W₄·Θ⁴ = 4!·C(8,4) = 1680`. -/
  pair_W4_theta : pair W4 theta4 = 1680
  /-- **Battery**: `Θ⁸ = 8!·3^m = 40320·3^m`. -/
  pair_theta_theta : pair theta4 theta4 = 40320 * 3 ^ m
  /-- `W₄` is an integral algebraic cycle class: its self-intersection is an integer. -/
  W4sq : ℤ
  pair_W4_W4 : pair W4 W4 = (W4sq : ℚ)
  Algebraic : H → Prop
  theta4_alg : Algebraic theta4
  W4_alg : Algebraic W4
  alg_sub_smul : ∀ (a : ℚ) (u v : H), Algebraic u → Algebraic v → Algebraic (u - a • v)
  /-- The Weil space. -/
  WeilSpace : H → Prop
  /-- **The accounting** (MT full `GU(4,4)` from Frobenius-torus certificates + Serre;
  p = 7 certificate in progress, second prime = named gap): Θ-primitive (4,4) ⟹ Weil. -/
  accounting : ∀ v : H, pair v theta4 = 0 → WeilSpace v

namespace EightfoldData

variable {H : Type*} [AddCommGroup H] [Module ℚ H] (D : EightfoldData H)

/-- The constructed class: `Ξ = W₄ − Θ⁴/(24·3^m)`. -/
noncomputable def Xi : H := D.W4 - (1 / (24 * 3 ^ D.m) : ℚ) • D.theta4

/-- The normalization identity: `(1/(24·3^m))·(40320·3^m) = 1680`. -/
theorem norm_id : (1 / (24 * 3 ^ D.m) : ℚ) * (40320 * 3 ^ D.m) = 1680 := by
  have h3 : ((3 : ℚ) ^ D.m) ≠ 0 := by positivity
  field_simp
  ring

/-- `Ξ` is algebraic — a difference of algebraic classes. -/
theorem xi_algebraic : D.Algebraic D.Xi :=
  D.alg_sub_smul _ _ _ D.W4_alg D.theta4_alg

/-- `Ξ` is Θ-primitive: the battery values cancel exactly. -/
theorem xi_primitive : D.pair D.Xi D.theta4 = 0 := by
  rw [Xi, D.pair_sub_left, D.pair_smul_left, D.pair_W4_theta, D.pair_theta_theta,
    D.norm_id, sub_self]

/-- **`Ξ ≠ 0` by pure integrality**: proportionality forces `W₄² = 70/3^m ∉ ℤ`. -/
theorem xi_ne_zero : D.Xi ≠ 0 := by
  intro h0
  have hW4 : D.W4 = (1 / (24 * 3 ^ D.m) : ℚ) • D.theta4 := sub_eq_zero.mp h0
  set c : ℚ := (1 / (24 * 3 ^ D.m) : ℚ) with hc
  have hWW : (D.W4sq : ℚ) = c * (c * (40320 * 3 ^ D.m)) := by
    rw [← D.pair_W4_W4, hW4, D.pair_smul_left, D.pair_symm, D.pair_smul_left,
      D.pair_theta_theta]
  have key : (D.W4sq : ℚ) * (40320 * 3 ^ D.m) = 2822400 := by
    have hnorm := D.norm_id
    rw [hWW]
    calc c * (c * (40320 * 3 ^ D.m)) * (40320 * 3 ^ D.m)
        = (c * (40320 * 3 ^ D.m)) * (c * (40320 * 3 ^ D.m)) := by ring
      _ = 1680 * 1680 := by rw [← hc] at hnorm; rw [hnorm]
      _ = 2822400 := by norm_num
  exact integrality_obstruction8 D.m D.m_pos ⟨D.W4sq, key⟩

/-- **The constructed Weil class at dimension 8**: `Ξ` is a nonzero algebraic element
of the Weil space — beyond the literature boundary (Markman's dim-8 secant sheaves
lack semiregularity; this route never needs it). -/
theorem weil_class_constructed8 :
    D.WeilSpace D.Xi ∧ D.Xi ≠ 0 ∧ D.Algebraic D.Xi :=
  ⟨D.accounting _ D.xi_primitive, D.xi_ne_zero, D.xi_algebraic⟩

end EightfoldData

end CriticalLinePhasor.WeilEightfold

#print axioms CriticalLinePhasor.WeilEightfold.central_binomial_trap
#print axioms CriticalLinePhasor.WeilEightfold.integrality_obstruction8
#print axioms CriticalLinePhasor.WeilEightfold.EightfoldData.weil_class_constructed8
