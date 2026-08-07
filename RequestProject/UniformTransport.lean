import RequestProject.SeedStandardRung

/-!
# Uniform transport of arbitrary representation data: rung 7 finished

The transport half of rung 7, completed as one uniform package.  A representation datum
of the seed is a finite list of symmetric-power constituents, `ρ = ⊕ᵢ Sym^{rᵢ}` — for the
level-one seed this is the general finite algebraic representation, since determinant
twists are trivial at det-one normalization.  The channel type and weight system are
built by recursion, so every constituent step is *definitionally* a direct sum and the
transport-closure calculus applies with no reindexing:

* `repIndex` / `repWeight` — the channel type (one `Fin (rᵢ+1)` block per constituent)
  and the disjoint-union clock system;
* `repBank_eq` — **the uniform bank law**: the transported bank is the Dirichlet product
  of the constituent `Sym^r` banks, by one induction over the closure engine;
* `repWeight_bound` / `repWeight_inv_bound` / `repSatakePair` — the datum as a polynomial
  Satake pair, bounds inherited from the constituent pairs with one exponent
  `E·(Σᵢ rᵢ)`;
* `repBound` / `repBank_LSeriesSummable` — **uniform summability**: absolute convergence
  beyond one explicit polynomial threshold, for every datum, with no temperedness input;
* `prodBank_summable` / `LSeries_repBank` — **the uniform L-factorization**:
  `L(ρ, s) = ∏ᵢ L(Sym^{rᵢ}, s)` on the common half-plane;
* `repBank_append` — **composition is automatic**: transport of a direct sum is the
  product of the transports — rung 8's law at the level of arbitrary data;
* `uniform_transport` — rung 7 in one quantified conclusion: bank, summability,
  factorization, and composition, simultaneously, for every `ρ`, with no
  per-representation argument.

Scope, stated exactly: the datum class is finite direct sums of symmetric powers of the
GL(2) seed — the finite algebraic representations of its dual group at level one; the
reflection layer at every rank is the carrier's (`prop:localid` and the carrier
involution, per the program register), with per-rank chart registration the corroboration
currency of the companion notes.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.UniformTransport

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.BaseChangeInduction CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.SymrBank CriticalLinePhasor.SymCubeQuartic
open CriticalLinePhasor.CarrierTheta

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}



/-- The channel type of a finite representation datum: one `Sym^{r}` block per entry. -/
def repIndex : List ℕ → Type
  | [] => Empty
  | r :: ρ => Fin (r + 1) ⊕ repIndex ρ

instance repIndex.fintype : ∀ ρ : List ℕ, Fintype (repIndex ρ)
  | [] => (inferInstance : Fintype Empty)
  | _ :: ρ => letI := repIndex.fintype ρ; (inferInstance : Fintype (_ ⊕ _))

instance repIndex.isEmpty_nil : IsEmpty (repIndex []) :=
  (inferInstance : IsEmpty Empty)

/-- The weight system of the datum: the disjoint union of the constituent clocks. -/
noncomputable def repWeight (H : HeckeEigenData f) :
    ∀ ρ : List ℕ, Nat.Primes → repIndex ρ → ℂ
  | [], _, x => x.elim
  | r :: ρ, p, x =>
      Sum.elim (fun j : Fin (r + 1) => symClockWeight r (H.satake p.2) (j : ℕ))
        (repWeight H ρ p) x

/-- **The uniform bank law**: the bank of the datum is the Dirichlet product of the
constituent `Sym^r` banks — one induction over the closure engine. -/
theorem repBank_eq (H : HeckeEigenData f) :
    ∀ ρ : List ℕ,
      coefficientArithmetic (radialGlobalSatakeCoeff (repWeight H ρ))
        = (ρ.map (fun r => symrBank H r)).prod
  | [] => by
      ext m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [coefficientArithmetic]
      · show (if m = 0 then 0 else radialGlobalSatakeCoeff (repWeight H []) (m - 1)) = _
        rw [if_neg hm.ne']
        rw [radialGlobalSatakeCoeff_eq_prod_dite]
        have hempty : ∀ p ∈ (m - 1 + 1).primeFactors,
            (if hp : p.Prime then
              radialLocalEulerCoeff (repWeight H [] ⟨p, hp⟩)
                ((m - 1 + 1).factorization p) else 1)
            = if (m - 1 + 1).factorization p = 0 then 1 else 0 := by
          intro p hp
          rw [dif_pos (Nat.prime_of_mem_primeFactors hp)]
          have hz : repWeight H [] ⟨p, Nat.prime_of_mem_primeFactors hp⟩
              = (fun x : repIndex [] => (0 : ℂ)) := by
            funext x
            exact x.elim
          rw [hz]
          exact radialLocalEulerCoeff_isEmpty _
        rcases eq_or_ne m 1 with rfl | hm1
        · simp [List.map_nil, List.prod_nil]
        · have hne : m - 1 + 1 ≠ 1 := by omega
          obtain ⟨p, hpmem⟩ := Nat.exists_prime_and_dvd hne
          have hpf : p ∈ (m - 1 + 1).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpmem.1, hpmem.2, by omega⟩
          rw [Finset.prod_congr rfl hempty]
          rw [Finset.prod_eq_zero hpf (by
            rw [if_neg]
            have := Nat.Prime.factorization_pos_of_dvd hpmem.1 (by omega) hpmem.2
            omega)]
          show (0 : ℂ) = ((1 : ArithmeticFunction ℂ)) m
          rw [ArithmeticFunction.one_apply, if_neg hm1]
  | r :: ρ => by
      show coefficientArithmetic (radialGlobalSatakeCoeff
        (fun p => Sum.elim (fun j : Fin (r + 1) =>
          symClockWeight r (H.satake p.2) (j : ℕ)) (repWeight H ρ p))) = _
      rw [bankArithmetic_sumElim, bankArithmetic_symClock H r, repBank_eq H ρ]
      rw [List.map_cons, List.prod_cons]



/-- The primal bound over the whole datum, by induction over the constituents. -/
theorem repWeight_bound (H : HeckeEigenData f) :
    ∀ ρ : List ℕ, ∀ (p : Nat.Primes) (x : repIndex ρ),
      ‖repWeight H ρ p x‖ ≤
        (p.1 : ℝ) ^ ((satake_single_bound H).choose * ρ.sum)
  | [], _, x => x.elim
  | r :: ρ, p, x => by
      have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
      rcases x with j | y
      · calc ‖repWeight H (r :: ρ) p (Sum.inl j)‖
            = ‖symClockWeight r (H.satake p.2) (j : ℕ)‖ := rfl
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * r) :=
              symClock_norm_bound H _ (satake_single_bound H).choose_spec r p j
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * (r :: ρ).sum) := by
              refine pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left _ ?_)
              simp [List.sum_cons]
      · calc ‖repWeight H (r :: ρ) p (Sum.inr y)‖
            = ‖repWeight H ρ p y‖ := rfl
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * ρ.sum) :=
              repWeight_bound H ρ p y
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * (r :: ρ).sum) := by
              refine pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left _ ?_)
              simp [List.sum_cons]

/-- The dual (inverse) bound over the whole datum. -/
theorem repWeight_inv_bound (H : HeckeEigenData f) :
    ∀ ρ : List ℕ, ∀ (p : Nat.Primes) (x : repIndex ρ),
      ‖(repWeight H ρ p x)⁻¹‖ ≤
        (p.1 : ℝ) ^ ((satake_single_bound H).choose * ρ.sum)
  | [], _, x => x.elim
  | r :: ρ, p, x => by
      have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
      rcases x with j | y
      · calc ‖(repWeight H (r :: ρ) p (Sum.inl j))⁻¹‖
            = ‖(symClockWeight r (H.satake p.2) (j : ℕ))⁻¹‖ := rfl
          _ = ‖(symrSatakePair H r).dual p j‖ := rfl
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * r) :=
              (symrSatakePair H r).dual_bound p j
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * (r :: ρ).sum) := by
              refine pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left _ ?_)
              simp [List.sum_cons]
      · calc ‖(repWeight H (r :: ρ) p (Sum.inr y))⁻¹‖
            = ‖(repWeight H ρ p y)⁻¹‖ := rfl
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * ρ.sum) :=
              repWeight_inv_bound H ρ p y
          _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * (r :: ρ).sum) := by
              refine pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left _ ?_)
              simp [List.sum_cons]

/-- Non-vanishing of every channel. -/
theorem repWeight_ne_zero (H : HeckeEigenData f) :
    ∀ ρ : List ℕ, ∀ (p : Nat.Primes) (x : repIndex ρ), repWeight H ρ p x ≠ 0
  | [], _, x => x.elim
  | r :: ρ, p, x => by
      rcases x with j | y
      · exact zpow_ne_zero _ (H.satake_ne_zero p.2)
      · exact repWeight_ne_zero H ρ p y

/-- **The uniform Satake pair of an arbitrary representation datum.** -/
noncomputable def repSatakePair (H : HeckeEigenData f) (ρ : List ℕ) :
    PolynomialSatakeDualPair (repIndex ρ) where
  primal := repWeight H ρ
  dual := fun p x => (repWeight H ρ p x)⁻¹
  primalExponent := (satake_single_bound H).choose * ρ.sum
  dualExponent := (satake_single_bound H).choose * ρ.sum
  primal_ne_zero := repWeight_ne_zero H ρ
  dual_eq_inv := fun _ _ => rfl
  primal_bound := repWeight_bound H ρ
  dual_bound := repWeight_inv_bound H ρ

/-- The summability threshold of the datum. -/
noncomputable def repBound (H : HeckeEigenData f) (ρ : List ℕ) : ℕ :=
  Fintype.card (repIndex ρ) + (satake_single_bound H).choose * ρ.sum

/-- **Uniform summability**: the bank of every datum converges absolutely beyond its
polynomial threshold — no temperedness input, uniformly over all representations. -/
theorem repBank_LSeriesSummable (H : HeckeEigenData f) (ρ : List ℕ) {s : ℂ}
    (hs : ((repBound H ρ : ℕ) : ℝ) + 1 < s.re) :
    LSeriesSummable (⇑((ρ.map (fun r => symrBank H r)).prod)) s := by
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨1, fun m hm => ?_⟩
  have hb := cpsPolynomialPrimalArithmetic_norm_le (repSatakePair H ρ) m
  have hid : (coefficientArithmetic (cpsPolynomialPrimalCoeff (repSatakePair H ρ))) m
      = ((ρ.map (fun r => symrBank H r)).prod) m :=
    congrArg (fun A : ArithmeticFunction ℂ => A m) (repBank_eq H ρ)
  rw [← hid]
  calc ‖(coefficientArithmetic (cpsPolynomialPrimalCoeff (repSatakePair H ρ))) m‖
      ≤ (1 : ℝ) * (m : ℝ) ^ ((Fintype.card (repIndex ρ)
          + (repSatakePair H ρ).primalExponent : ℕ)) := hb
    _ ≤ 1 * (m : ℝ) ^ ((((repBound H ρ : ℕ) : ℝ) + 1) - 1) := by
        rw [one_mul, one_mul, add_sub_cancel_right, Real.rpow_natCast]
        exact le_of_eq rfl

/-- The product bank is summable on the common half-plane. -/
theorem prodBank_summable (H : HeckeEigenData f) :
    ∀ ρ : List ℕ, ∀ {s : ℂ},
      (∀ r ∈ ρ, ((symrBound H r : ℕ) : ℝ) + 1 < s.re) →
      LSeriesSummable (⇑((ρ.map (fun r => symrBank H r)).prod)) s
  | [], s, _ => by
      rw [show (⇑((List.map (fun r => symrBank H r) []).prod) : ℕ → ℂ)
        = ↗(1 : ArithmeticFunction ℂ) from rfl, ArithmeticFunction.one_eq_delta]
      unfold LSeriesSummable
      refine summable_of_ne_finset_zero (s := {1}) ?_
      intro n hn
      rw [LSeries.term_delta]
      simp only [Finset.mem_singleton] at hn
      rw [if_neg hn]
  | r :: ρ, s, hall => by
      rw [List.map_cons, List.prod_cons]
      exact ArithmeticFunction.LSeriesSummable_mul
        (symrBank_LSeriesSummable H r (hall r List.mem_cons_self))
        (prodBank_summable H ρ (fun r' hr' => hall r' (List.mem_cons_of_mem r hr')))

/-- **The uniform L-factorization**: on the common half-plane, the L-series of the datum
is the product of the constituent `Sym^r` L-series. -/
theorem LSeries_repBank (H : HeckeEigenData f) :
    ∀ ρ : List ℕ, ∀ {s : ℂ},
      (∀ r ∈ ρ, ((symrBound H r : ℕ) : ℝ) + 1 < s.re) →
      LSeries (⇑((ρ.map (fun r => symrBank H r)).prod)) s
        = (ρ.map (fun r => LSeries (⇑(symrBank H r)) s)).prod
  | [], s, _ => by
      simp only [List.map_nil, List.prod_nil]
      rw [show (⇑(1 : ArithmeticFunction ℂ) : ℕ → ℂ)
        = ↗(1 : ArithmeticFunction ℂ) from rfl, ArithmeticFunction.one_eq_delta,
        LSeries_delta]
      rfl
  | r :: ρ, s, hall => by
      have hρ : ∀ r' ∈ ρ, ((symrBound H r' : ℕ) : ℝ) + 1 < s.re := by
        intro r' hr'
        exact hall r' (List.mem_cons_of_mem r hr')
      rw [List.map_cons, List.prod_cons,
        ArithmeticFunction.LSeries_mul'
          (symrBank_LSeriesSummable H r (hall r List.mem_cons_self))
          (prodBank_summable H ρ hρ),
        LSeries_repBank H ρ hρ, List.map_cons, List.prod_cons]



/-- **Composition is automatic**: transporting the direct sum of two representation data
is the Dirichlet product of the two transports — rung 8's closure law, at the level of
arbitrary representation data. -/
theorem repBank_append (H : HeckeEigenData f) (ρ₁ ρ₂ : List ℕ) :
    ((ρ₁ ++ ρ₂).map (fun r => symrBank H r)).prod
      = (ρ₁.map (fun r => symrBank H r)).prod * (ρ₂.map (fun r => symrBank H r)).prod := by
  rw [List.map_append, List.prod_append]

/-- **Rung 7, one theorem — the uniform transport.**  For every representation datum
`ρ = ⊕ᵢ Sym^{rᵢ}` of the seed, simultaneously: the transported bank is the Dirichlet
product of the constituent banks (with the weight system the disjoint union of the
constituent clocks), it is absolutely convergent beyond one explicit polynomial threshold
with no temperedness input, its L-series factors as the product of the constituent
L-series on the common half-plane, and transport of a direct sum is the product of the
transports.  Uniform in `ρ`: no per-representation argument occurs. -/
theorem uniform_transport (H : HeckeEigenData f) (ρ : List ℕ) :
    (coefficientArithmetic (radialGlobalSatakeCoeff (repWeight H ρ))
        = (ρ.map (fun r => symrBank H r)).prod) ∧
    (∀ {s : ℂ}, ((repBound H ρ : ℕ) : ℝ) + 1 < s.re →
      LSeriesSummable (⇑((ρ.map (fun r => symrBank H r)).prod)) s) ∧
    (∀ {s : ℂ}, (∀ r ∈ ρ, ((symrBound H r : ℕ) : ℝ) + 1 < s.re) →
      LSeries (⇑((ρ.map (fun r => symrBank H r)).prod)) s
        = (ρ.map (fun r => LSeries (⇑(symrBank H r)) s)).prod) ∧
    (∀ ρ₂ : List ℕ, ((ρ ++ ρ₂).map (fun r => symrBank H r)).prod
        = (ρ.map (fun r => symrBank H r)).prod * (ρ₂.map (fun r => symrBank H r)).prod) :=
  ⟨repBank_eq H ρ,
   fun hs => repBank_LSeriesSummable H ρ hs,
   fun hall => LSeries_repBank H ρ hall,
   fun ρ₂ => repBank_append H ρ ρ₂⟩

end CriticalLinePhasor.UniformTransport

#print axioms CriticalLinePhasor.UniformTransport.repBank_eq
#print axioms CriticalLinePhasor.UniformTransport.repWeight_bound
#print axioms CriticalLinePhasor.UniformTransport.repSatakePair
#print axioms CriticalLinePhasor.UniformTransport.repBank_LSeriesSummable
#print axioms CriticalLinePhasor.UniformTransport.prodBank_summable
#print axioms CriticalLinePhasor.UniformTransport.LSeries_repBank
#print axioms CriticalLinePhasor.UniformTransport.repBank_append
#print axioms CriticalLinePhasor.UniformTransport.uniform_transport
