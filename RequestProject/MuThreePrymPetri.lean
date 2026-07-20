import Mathlib

/-!
# The μ₃-Prym–Petri arithmetic core (depth-one stratum)

Companion to `tmp/mu3_petri_proofs.md` (2026-07-19 restructuring) and
`tmp/mu3_prym_petri.tex`.  This file proves, unconditionally, the arithmetic
skeleton of the theorem "for C Lemma-C-general and any nonzero 3-torsion ε,
every L ∈ Nm⁻¹(ω_C) with h⁰(L) = 1 has injective reduced Prym–Petri map":

* Lemma B's collision arithmetic (fiber triples, max-descent, excess,
  the ⌈3k/2⌉ canonical-multiplicity bound);
* the zone-emptiness contradiction (Z1) and virtual-dimension bound (Z2);
* the dimension-comparison kill against Farkas' de Jonquières bound
  (arXiv:2210.07843, Thm 1.1), its specialization to genus ≤ 5 and to the
  pipeline case g = 4, and the HONESTY MARKER that g = 6, e = 4 is a
  boundary case the comparison does NOT kill.

Scope: does not assume or prove RH/GRH.  The function-theoretic content
(Lemma A's descent equivalence; Farkas' dimension theorem) enters only
through hypotheses of the typed statements; this file proves the arithmetic
that combines them, nothing more.
-/

namespace MuThreePrymPetri

/-- Fiber multiplicities (a, b, c) of a section divisor over one base point
of an étale triple cover, normalized so `a` is the maximum: the max-descent
multiplicity is `a`, the collision excess is `b + c`. -/
structure FiberTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  hb : b ≤ a
  hc : c ≤ a

namespace FiberTriple

/-- The collision excess k = b + c at this point. -/
def excess (t : FiberTriple) : ℕ := t.b + t.c

/-- Lemma B, pointwise: on three sheets, k ≤ 2a. -/
theorem excess_le_two_descent (t : FiberTriple) : t.excess ≤ 2 * t.a := by
  have := t.hb; have := t.hc; unfold excess; omega

/-- Lemma B, ceiling form: ⌈k/2⌉ ≤ a (Nat: ⌈k/2⌉ = (k+1)/2). -/
theorem ceil_half_excess_le_descent (t : FiberTriple) :
    (t.excess + 1) / 2 ≤ t.a := by
  have := t.hb; have := t.hc; unfold excess; omega

/-- Lemma B, canonical-multiplicity form: the multiplicity a + b + c of the
canonical divisor π₋W at this point is at least k + ⌈k/2⌉ = ⌈3k/2⌉. -/
theorem canonical_ge_three_half (t : FiberTriple) :
    t.excess + (t.excess + 1) / 2 ≤ t.a + t.b + t.c := by
  have := t.hb; have := t.hc; unfold excess; omega

end FiberTriple

/-- List-level Z1 kernel: for a list of positive naturals,
Σk ≤ Σ⌈k/2⌉ + Σ(k−1), because pointwise ⌈k/2⌉ + (k−1) ≥ k when k ≥ 1. -/
theorem sum_le_ceilHalf_add_pred (l : List ℕ) (h : ∀ k ∈ l, 1 ≤ k) :
    l.sum ≤ (l.map fun k => (k + 1) / 2).sum + (l.map fun k => k - 1).sum := by
  induction l with
  | nil => simp
  | cons k ks ih =>
    have hk : 1 ≤ k := h k List.mem_cons_self
    have hks : ∀ x ∈ ks, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := ih hks
    simp only [List.map_cons, List.sum_cons]
    omega

/-- List-level: the length is at most Σ⌈k/2⌉ (each term ≥ 1). -/
theorem length_le_ceilHalf_sum (l : List ℕ) (h : ∀ k ∈ l, 1 ≤ k) :
    l.length ≤ (l.map fun k => (k + 1) / 2).sum := by
  induction l with
  | nil => simp
  | cons k ks ih =>
    have hk : 1 ≤ k := h k List.mem_cons_self
    have hks : ∀ x ∈ ks, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := ih hks
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- A collision profile: the positive excess multiplicities k_i at the r
distinct collision points of the moving excess divisor E = Σ k_i x_i. -/
structure Profile where
  ks : List ℕ
  pos : ∀ k ∈ ks, 1 ≤ k

namespace Profile

/-- deg E. -/
def e (P : Profile) : ℕ := P.ks.sum

/-- Number of distinct collision points. -/
def r (P : Profile) : ℕ := P.ks.length

/-- c = Σ⌈k_i/2⌉, the half-thickening degree increment. -/
def c (P : Profile) : ℕ := (P.ks.map fun k => (k + 1) / 2).sum

/-- δ = Σ(k_i − 1), the coincidence count of the profile. -/
def delta (P : Profile) : ℕ := (P.ks.map fun k => k - 1).sum

/-- Z1 master inequality: e ≤ c + δ. -/
theorem e_le_c_add_delta (P : Profile) : P.e ≤ P.c + P.delta :=
  sum_le_ceilHalf_add_pred P.ks P.pos

/-- r ≤ c. -/
theorem r_le_c (P : Profile) : P.r ≤ P.c :=
  length_le_ceilHalf_sum P.ks P.pos

/-- **Z1 (zone emptiness).**  In the automatic-speciality zone the two
constraints  c ≤ g − 1 − e  (zone) and  δ ≤ 2e − g − 1  (existence of a
profile-δ member, Farkas-on-pencils) are jointly contradictory:
they force e ≤ c + δ ≤ e − 2. -/
theorem zone_empty (P : Profile) (g : ℤ)
    (hzone : (P.c : ℤ) ≤ g - 1 - P.e)
    (hexist : (P.delta : ℤ) ≤ 2 * P.e - g - 1) : False := by
  have h := P.e_le_c_add_delta
  have h' : (P.e : ℤ) ≤ (P.c : ℤ) + (P.delta : ℤ) := by exact_mod_cast h
  linarith

/-- **Z2 (virtual dimension).**  Outside the zone the bad locus has virtual
dimension r − c − 2 ≤ −2: expected-empty with margin 2. -/
theorem virtual_dim_le_neg_two (P : Profile) : (P.r : ℤ) - P.c - 2 ≤ -2 := by
  have h : (P.r : ℤ) ≤ (P.c : ℤ) := by exact_mod_cast P.r_le_c
  linarith

end Profile

/-- **The dimension-comparison kill** (δ = 0 case of Lemma C).  If a bad
pencil exists, the canonical de Jonquières locus with profile (2^e) contains
a family of dimension 2e − g − 1, while by Farkas (arXiv:2210.07843,
Thm 1.1; hypotheses source-verified 2026-07-19) every component has
dimension g − e − 1.  Containment forces 3e ≤ 2g. -/
theorem dimension_comparison {g e : ℤ}
    (hcontain : 2 * e - g - 1 ≤ g - e - 1) : 3 * e ≤ 2 * g := by linarith

/-- For g ≤ 5 the moving range e ≥ (g+2)/2 forces 3e > 2g: the comparison
kills the entire δ = 0 case. -/
theorem moving_range_beats_window {g e : ℤ} (hg : g ≤ 5)
    (he : g + 2 ≤ 2 * e) : 2 * g < 3 * e := by linarith

/-- g = 4, the sixfold pipeline case: every moving degree e ≥ 3 has 3e > 8.
Combined with `dimension_comparison`, no bad pencil exists at genus 4. -/
theorem g4_kill {e : ℤ} (he : 3 ≤ e) : 2 * 4 < 3 * e := by linarith

/-- HONESTY MARKER: at g = 6, e = 4 (minimal moving degree, ρ = 0) the
comparison does NOT kill — 3e = 12 = 2g exactly.  This boundary point
belongs to the open window; recorded as a theorem so the gap cannot be
silently papered over. -/
theorem g6_boundary_not_killed : ¬ (2 * 6 < 3 * (4 : ℤ)) := by norm_num

/-- The assembled δ = 0 exclusion at genus 4, as pure arithmetic: a bad
pencil datum (moving range + Farkas containment) is contradictory. -/
theorem delta0_excluded_g4 {e : ℤ} (he : 3 ≤ e)
    (hcontain : 2 * e - 4 - 1 ≤ 4 - e - 1) : False := by linarith

end MuThreePrymPetri
