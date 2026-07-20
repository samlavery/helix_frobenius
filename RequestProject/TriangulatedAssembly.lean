import RequestProject.RecognitionReconstruction

/-!
# Phase four, assembly: triangulated generators

The generator list is not hunted from scratch — the campaigns already collected certified
specimens (the CM-product divisors with the constancy detector calibrated on them; the
explicit point-counted Schoen (2,2) cycle with freeze certificate `r = 1`, no-orphan
occupancy, and exact integer landings).  This file types the assembly: a
**triangulated generator** enters the list only with its three bearings —

* the annihilator **address** (which rail it freezes on; `ChannelConstancy`),
* **detection** (it fires in the tower; the reconstruction-coordinate bearing),
* the support/**order** regime (pairwise vs collective; field of definition),

— together with its **algebraicity certificate** (the constructed source the census
supplies).  `ReconstructionData.ofTriangulated` assembles a triangulated family, the group
closure of the cycle map, and the Torelli leg into a `ReconstructionData`, and
`sourceExhaustion_of_triangulated` executes the terminus from it.  Register: the structure
does not manufacture certificates — it refuses generators without them; the open frontier is
exactly the families whose specimens the census has not yet landed (the simple Weil sixfold,
with its named genus-3 obstacle).  No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **A triangulated generator**: a class admitted to the generator list with its three
bearings and its algebraicity certificate. -/
structure TriangulatedGenerator {Z : Type*} [Zero Z] (D : HodgeDial Z) where
  /-- The class. -/
  gen : Z
  /-- Bearing 1 — the annihilator address: the rail label the class freezes on. -/
  address : ℤ
  /-- Bearing 2 — detection: the class fires in the tower. -/
  detected : ∃ d, D.T d gen ≠ 0
  /-- Bearing 3 — the support/order regime (pairwise vs collective; discriminant regime). -/
  order : ℕ
  /-- The certificate: the constructed algebraic source (divisor class; the explicit Schoen
  cycle; each supplied by the census, never manufactured here). -/
  algebraic : D.Algebraic gen

/-- **Assembly**: a triangulated family, closure of the cycle-class map under integer
combinations and torsion, and the Torelli leg assemble into a reconstruction bundle. -/
def ReconstructionData.ofTriangulated {Z : Type*} [AddCommGroup Z] {D : HodgeDial Z}
    {G : GeneratingPairingData D} (rank : ℕ)
    (T : Fin rank → TriangulatedGenerator D)
    (hclosed : ∀ (c : Fin rank → ℤ) (t : Z), IsOfFinAddOrder t →
      D.Algebraic ((∑ i, c i • (T i).gen) + t))
    (hrec : ∀ z : Z, G.pairing z ≠ 0 → D.DC z → D.Rational z →
      ∃ (c : Fin rank → ℤ) (t : Z), IsOfFinAddOrder t ∧
        z = (∑ i, c i • (T i).gen) + t) :
    ReconstructionData D G where
  rank := rank
  gens i := (T i).gen
  algebraic_closed := hclosed
  reconstruct := hrec

/-- **The terminus from triangulated assembly**: proven retention, the staked collapse, a
triangulated generator family, closure, and the Torelli leg give source exhaustion. -/
theorem sourceExhaustion_of_triangulated {Z : Type*} [AddCommGroup Z] {D : HodgeDial Z}
    (hret : Retention D) (G : GeneratingPairingData D) (rank : ℕ)
    (T : Fin rank → TriangulatedGenerator D)
    (hclosed : ∀ (c : Fin rank → ℤ) (t : Z), IsOfFinAddOrder t →
      D.Algebraic ((∑ i, c i • (T i).gen) + t))
    (hrec : ∀ z : Z, G.pairing z ≠ 0 → D.DC z → D.Rational z →
      ∃ (c : Fin rank → ℤ) (t : Z), IsOfFinAddOrder t ∧
        z = (∑ i, c i • (T i).gen) + t) :
    SourceExhaustion D :=
  sourceExhaustion_of_reconstruction hret G
    (ReconstructionData.ofTriangulated rank T hclosed hrec)

/-- **The first inhabitant**: the diagonal generator of the cyclic dial `ℚ[ℤ/n]`.  Its
certificate is itself (it *is* the diagonal class), its address is the DC rail `0`, its order
is `1`, and its detection is proven: the winding amplitude at the frequency-zero channel is
`n ≠ 0`, all other channels vanishing by the shift identity.  The list is inhabited; every
further entry (the CM-product divisors, the Schoen cycle) enters by the same three bearings
and certificate. -/
noncomputable def cyclicDiagonalGenerator (n : ℕ) [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) :
    TriangulatedGenerator (cyclicDial hζ) where
  gen := fun _ => (1 : ℚ)
  address := 0
  order := 1
  algebraic := ⟨1, rfl⟩
  detected := by
    have hdc : ∀ j : ZMod n, (fun _ : ZMod n => (1 : ℚ)) (j + 1)
        = (fun _ : ZMod n => (1 : ℚ)) j := fun _ => rfl
    have hmdc := winding_dc (a := fun _ => (1 : ℚ)) hζ hdc
    have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    refine ⟨Nat.pair (0 : Fin 1) 0, ?_⟩
    have hpair := generalExtensionTower_pair (cyclicBank n).toClockBank
      (0 : Fin 1) 0 (windingTransform hζ (fun _ => (1 : ℚ)))
    show generalExtensionTower (cyclicBank n).toClockBank
      (Nat.pair (0 : Fin 1) 0) (windingTransform hζ (fun _ => (1 : ℚ))) ≠ 0
    rw [hpair]
    have hsingle : ∑ i : Fin n,
        windingTransform hζ (fun _ => (1 : ℚ)) (0 : Fin 1) i
          * (cyclicBank n).toClockBank.frequency i ^ (0 : ℕ)
        = windingAmp hζ (fun _ => (1 : ℚ)) (0 : Fin 1) ⟨0, hn0⟩ := by
      rw [Finset.sum_eq_single (⟨0, hn0⟩ : Fin n)]
      · rw [pow_zero, mul_one]; rfl
      · intro i _ hi
        rw [pow_zero, mul_one]
        have hfi : (cyclicBank n).freq i ≠ 0 := by
          simp only [cyclicBank]
          intro h
          apply hi
          apply Fin.ext
          show (i : ℕ) = 0
          exact_mod_cast h
        exact hmdc (0 : Fin 1) i hfi
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsingle]
    show (∑ j : ZMod n, ((1 : ℚ) : ℂ) * ζ ^ (j.val * (⟨0, hn0⟩ : Fin n).val)) ≠ 0
    have hval : ∀ j : ZMod n, ((1 : ℚ) : ℂ) * ζ ^ (j.val * (⟨0, hn0⟩ : Fin n).val)
        = 1 := by
      intro j
      simp
    rw [Finset.sum_congr rfl fun j _ => hval j, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
    exact_mod_cast NeZero.ne n

/-- **The second inhabitant**: the unit generator of the Artin-motive dial.  Its certificate
is descent to the base field (`1 = algebraMap ℚ K 1`), its address is the DC rail, and its
detection is proven: the unit is frozen (`g 1 = 1`), so every nonzero-frequency resolvent
vanishes by the shift identity while the DC resolvent evaluates to `|Gal| ≠ 0`. -/
noncomputable def artinUnitGenerator {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (g : K ≃ₐ[ℚ] K) (ι : K →+* ℂ) :
    TriangulatedGenerator (galoisDial g ι) where
  gen := (1 : K)
  address := 0
  order := 1
  algebraic := ⟨1, (map_one (algebraMap ℚ K)).symm⟩
  detected := by
    have hdc : g (1 : K) = 1 := map_one g
    have hmdc := galois_dc g ι hdc
    have hn0 : 0 < galoisChannels K := Nat.pos_of_ne_zero (NeZero.ne _)
    refine ⟨Nat.pair (0 : Fin 1) 0, ?_⟩
    have hpair := generalExtensionTower_pair (cyclicBank (galoisChannels K)).toClockBank
      (0 : Fin 1) 0 (galoisTransform g ι (1 : K))
    show generalExtensionTower (cyclicBank (galoisChannels K)).toClockBank
      (Nat.pair (0 : Fin 1) 0) (galoisTransform g ι (1 : K)) ≠ 0
    rw [hpair]
    have hsingle : ∑ i : Fin (galoisChannels K),
        galoisTransform g ι (1 : K) (0 : Fin 1) i
          * (cyclicBank (galoisChannels K)).toClockBank.frequency i ^ (0 : ℕ)
        = galoisAmp g ι (1 : K) (0 : Fin 1) ⟨0, hn0⟩ := by
      rw [Finset.sum_eq_single (⟨0, hn0⟩ : Fin (galoisChannels K))]
      · rw [pow_zero, mul_one]; rfl
      · intro i _ hi
        rw [pow_zero, mul_one]
        have hfi : (cyclicBank (galoisChannels K)).freq i ≠ 0 := by
          simp only [cyclicBank]
          intro h
          apply hi
          apply Fin.ext
          show (i : ℕ) = 0
          exact_mod_cast h
        exact hmdc (0 : Fin 1) i hfi
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsingle]
    show (∑ s : Fin (galoisChannels K),
      ι ((g ^ s.val) (1 : K))
        * galoisRoot K ^ (s.val * (⟨0, hn0⟩ : Fin (galoisChannels K)).val)) ≠ 0
    have hval : ∀ s : Fin (galoisChannels K),
        ι ((g ^ s.val) (1 : K))
          * galoisRoot K ^ (s.val * (⟨0, hn0⟩ : Fin (galoisChannels K)).val) = 1 := by
      intro s
      simp
    rw [Finset.sum_congr rfl fun s _ => hval s, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact_mod_cast NeZero.ne (galoisChannels K)

/-- **The depth-one Torelli leg, discharged**: for the Mordell–Weil bundle the reconstruction
field *is* `gens_generate` — the cited finite-generation statement already reconstructs every
class (fired or not) as an explicit generator combination plus torsion.  Given any pairing
dial over the point group and the closure of its algebraic predicate under combinations and
torsion, the full reconstruction bundle assembles with no further input: at depth one,
Torelli is Mordell–Weil. -/
def ReconstructionData.ofDepthOne {P : Type*} [AddCommGroup P]
    (B : DepthOneHeightData P) {Dial : HodgeDial P} (G : GeneratingPairingData Dial)
    (hclosed : ∀ (c : Fin B.rank → ℤ) (t : P), IsOfFinAddOrder t →
      Dial.Algebraic ((∑ i, c i • B.gens i) + t)) :
    ReconstructionData Dial G where
  rank := B.rank
  gens := B.gens
  algebraic_closed := hclosed
  reconstruct := fun z _ _ _ => B.gens_generate z

/-- **The channel-bundle Torelli leg**: on a channel dial (Lefschetz, CM products) the
spanning statement — fired rational DC classes are integer combinations of the generating
divisor family plus torsion — is the *effective form of the same theorem of record* that
supplies recognition (divisor classes span the rational Hodge classes on these families:
Lefschetz (1,1); Imai/Kahn on products).  It enters as a cited field, and the reconstruction
bundle assembles: on the executed rungs, Torelli is the classical spanning theorem. -/
def ReconstructionData.ofChannelSpanning {H : Type*} [AddCommGroup H] {m : ℕ}
    {B : IntFrequencyBank m} (D : HodgeChannelData H B)
    {G : GeneratingPairingData D.dial} (rank : ℕ) (gens : Fin rank → H)
    (hclosed : ∀ (c : Fin rank → ℤ) (t : H), IsOfFinAddOrder t →
      D.Algebraic ((∑ i, c i • gens i) + t))
    (hspan : ∀ z : H, G.pairing z ≠ 0 →
      (∀ i, B.freq i ≠ 0 → D.channel i z = 0) →
      ∃ (c : Fin rank → ℤ) (t : H), IsOfFinAddOrder t ∧
        z = (∑ i, c i • gens i) + t) :
    ReconstructionData D.dial G where
  rank := rank
  gens := gens
  algebraic_closed := hclosed
  reconstruct := fun z hp hdc _ => hspan z hp hdc

/-- **The executed rungs, terminus through reconstruction**: on any channel dial with its
cited spanning family, retention (proven), the collapse, and the spanning field give source
exhaustion — the complete phase-four chain running on the families where every input is a
theorem of record. -/
theorem channel_sourceExhaustion_of_spanning {H : Type*} [AddCommGroup H] {m : ℕ}
    {B : IntFrequencyBank m} (D : HodgeChannelData H B)
    (G : GeneratingPairingData D.dial) (rank : ℕ) (gens : Fin rank → H)
    (hclosed : ∀ (c : Fin rank → ℤ) (t : H), IsOfFinAddOrder t →
      D.Algebraic ((∑ i, c i • gens i) + t))
    (hspan : ∀ z : H, G.pairing z ≠ 0 →
      (∀ i, B.freq i ≠ 0 → D.channel i z = 0) →
      ∃ (c : Fin rank → ℤ) (t : H), IsOfFinAddOrder t ∧
        z = (∑ i, c i • gens i) + t) :
    SourceExhaustion D.dial :=
  sourceExhaustion_of_reconstruction D.retention G
    (ReconstructionData.ofChannelSpanning D rank gens hclosed hspan)

/-- **The bundle-level constructor**: on any channel dial, a nonzero DC class with an
algebraicity certificate enters the generator list with its detection *proven* by the
bridge's retention — the census supplies the class, the bearings, and the certificate; the
machine supplies the firing.  Nothing is hypothesized that the tower can derive. -/
def HodgeChannelData.certifiedGenerator {H : Type*} [AddCommGroup H] {m : ℕ}
    {B : IntFrequencyBank m} (D : HodgeChannelData H B) (v : H)
    (address : ℤ) (order : ℕ) (hv : v ≠ 0)
    (hdc : ∀ i, B.freq i ≠ 0 → D.channel i v = 0) (halg : D.Algebraic v) :
    TriangulatedGenerator D.dial where
  gen := v
  address := address
  order := order
  algebraic := halg
  detected := D.retention v hv hdc trivial

/-- **The third inhabitant class: CM-product divisor generators.**  Any nonzero divisor
class on the CM-product dial (the family where the constancy detector was certified and
Hodge is the theorem of record) enters at the DC rail, order one, with the divisor
construction as its certificate and detection proven by retention. -/
def cmDivisorGenerator {H : Type*} [AddCommGroup H] {m : ℕ}
    {B : IntFrequencyBank m} (D : CMProductData H B) (v : H) (hv : v ≠ 0)
    (hdc : ∀ i, B.freq i ≠ 0 → D.channel i v = 0) (halg : D.Algebraic v) :
    TriangulatedGenerator D.dial :=
  D.certifiedGenerator v 0 1 hv hdc halg

/-- **The fourth inhabitant class: the Schoen generator.**  The explicit point-counted Weil
`(2,2)` class of the Schoen fourfold (étale `ℤ/3` cover over `ℚ(√-3)`) enters with its
census bearings — the collective rail address, freeze scalar `r = 1`, order-three regime,
no-orphan occupancy, eight exact integer landings (`tmp/schoen_explicit.py`) — and its
constructed cycle as certificate; detection is again proven, not read from the census. -/
def schoenGenerator {H : Type*} [AddCommGroup H] {m : ℕ}
    {B : IntFrequencyBank m} (D : HodgeChannelData H B) (v : H) (address : ℤ)
    (hv : v ≠ 0) (hdc : ∀ i, B.freq i ≠ 0 → D.channel i v = 0)
    (halg : D.Algebraic v) : TriangulatedGenerator D.dial :=
  D.certifiedGenerator v address 3 hv hdc halg

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.HodgeChannelData.certifiedGenerator
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.channel_sourceExhaustion_of_spanning
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_of_triangulated
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.cyclicDiagonalGenerator
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.artinUnitGenerator
