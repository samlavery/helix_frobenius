import RequestProject.EisensteinWheelBank
import RequestProject.ThreeDNativeLaneCoupling

/-!
# Tracing (A, B, N₀) into the native paired structure (ledger 1146)

Forward from the enriched pencil (`EnrichedPencil.enrichedPencil`, ledger 1145) along the geometric
construction. The native paired object before J is the two-lane pencil (GeometricPhasorClosure §9;
ThreeDNativeLaneCoupling): reference lane `Q₊(n) = 1` (carrier presence at every site) and native
fiber lane `Q₋(n) = cell(n)⁻¹ · readout(w, s, n)`, coupled by the π/3 cell; its coupling is the
signed sum `Σ w(n) n^{−s}` (`nativeCoupling_eq_sum`). The J-level object
(`ThreeDAntihelixPairing`) comes after it.

The destructive test (same `B`, same `A² + N₀²`, different `(A, N₀)`):
* the enriched row Gram identifies them (`enrichedPencil_rowGram_radial`, `gram_identifies_3_4_and_5_0`);
* the enriched pencil distinguishes them while the focal readout agrees (`pencil_distinguishes_3_4_and_5_0`);
* the native fiber lane is the PLANE readout of the 3D phasor (`nativeFiberLane_eq_plane`): at a
  neutral site its entry is `0` while the 3D phasor there has positive mass, and the reference
  lane records the site only as presence `1` (`nativeFiberLane_neutral`); the lane is site-resolved
  and determines the routing (`nativeFiberLane_determines_routing`);
* the native metric's blocks are the site count and the plane energy
  (`nativeMetric_reference_block`, `nativeMetric_fiber_block`): no neutral mass enters.
-/

open Complex Matrix
open scoped Matrix BigOperators

namespace CriticalLinePhasor.PairedTrace

open CriticalLinePhasor CriticalLinePhasor.EisensteinWheelBank CriticalLinePhasor.EnrichedPencil

/-! ## The enriched pencil and its Gram under the test -/

/-- The enriched row Gram, entry by entry: `(A, N₀)` enter only through `A² + N₀²`. -/
theorem enrichedPencil_rowGram_eq (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) :
    enrichedPencil A B N₀ μ lam * (enrichedPencil A B N₀ μ lam)ᴴ =
      !![((A : ℂ) ^ 2 + (N₀ : ℂ) ^ 2) + B * star B,
          star μ * ((A : ℂ) ^ 2 + (N₀ : ℂ) ^ 2) + star lam * (B * star B);
        μ * ((A : ℂ) ^ 2 + (N₀ : ℂ) ^ 2) + lam * (B * star B),
          μ * star μ * ((A : ℂ) ^ 2 + (N₀ : ℂ) ^ 2) + lam * star lam * (B * star B)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [enrichedPencil, Matrix.mul_apply, Fin.sum_univ_three, map_mul,
      Complex.conj_ofReal] <;> ring

/-- **The Gram collapses to the radial norm:** equal `A² + N₀²` give equal row Grams. -/
theorem enrichedPencil_rowGram_radial (A₁ N₁ A₂ N₂ : ℝ) (B μ lam : ℂ)
    (h : A₁ ^ 2 + N₁ ^ 2 = A₂ ^ 2 + N₂ ^ 2) :
    enrichedPencil A₁ B N₁ μ lam * (enrichedPencil A₁ B N₁ μ lam)ᴴ =
      enrichedPencil A₂ B N₂ μ lam * (enrichedPencil A₂ B N₂ μ lam)ᴴ := by
  have hC : (A₁ : ℂ) ^ 2 + (N₁ : ℂ) ^ 2 = (A₂ : ℂ) ^ 2 + (N₂ : ℂ) ^ 2 := by exact_mod_cast h
  rw [enrichedPencil_rowGram_eq, enrichedPencil_rowGram_eq, hC]

/-- **Destructive test, Gram:** `(A, N₀) = (3, 4)` and `(5, 0)` have the same row Gram. -/
theorem gram_identifies_3_4_and_5_0 (B μ lam : ℂ) :
    enrichedPencil 3 B 4 μ lam * (enrichedPencil 3 B 4 μ lam)ᴴ =
      enrichedPencil 5 B 0 μ lam * (enrichedPencil 5 B 0 μ lam)ᴴ :=
  enrichedPencil_rowGram_radial 3 4 5 0 B μ lam (by norm_num)

/-- **Destructive test, pencil:** the enriched pencil distinguishes `(3, 4)` from `(5, 0)`, and the
focal readout agrees for both (rank drop exactly when `B = 0`). -/
theorem pencil_distinguishes_3_4_and_5_0 (B μ lam : ℂ) (hlam : lam ≠ μ) :
    enrichedPencil 3 B 4 μ lam ≠ enrichedPencil 5 B 0 μ lam ∧
      ((enrichedPencil 3 B 4 μ lam * (enrichedPencil 3 B 4 μ lam)ᴴ).det = 0 ↔ B = 0) ∧
      ((enrichedPencil 5 B 0 μ lam * (enrichedPencil 5 B 0 μ lam)ᴴ).det = 0 ↔ B = 0) := by
  refine ⟨fun h => ?_, enrichedPencil_rankDrop_iff 3 B 4 μ lam hlam (by norm_num),
    enrichedPencil_rankDrop_iff 5 B 0 μ lam hlam (by norm_num)⟩
  have h00 := congrFun (congrFun h 0) 0
  simp [enrichedPencil] at h00

/-! ## The native paired structure -/

/-- The native fiber lane is the despun PLANE readout of the 3D phasor. -/
theorem nativeFiberLane_eq_plane (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (i : Fin N) :
    Pencil3D.nativeFiberLane w s N i 0 =
      (Geometric.cell (i.val + 1))⁻¹ * Phasor3D.plane (Phasor3D.phasor3D w s.re s.im (i.val + 1)) :=
  rfl

/-- **At a neutrally routed site** the native fiber lane entry is `0`, while the 3D phasor there has
positive mass, and the reference lane records the site only as presence `1`. -/
theorem nativeFiberLane_neutral (r : Routing) (s : ℂ) (N : ℕ) (i : Fin N)
    (h : r.coeff (i.val + 1) = 0) :
    Pencil3D.nativeFiberLane r.coeff s N i 0 = 0 ∧
      0 < Phasor3D.massAxis (Phasor3D.phasor3D r.coeff s.re s.im (i.val + 1)) ∧
      Pencil3D.referenceLane N i 0 = 1 := by
  obtain ⟨-, -, hmass, -, hplane⟩ := routed_neutral r s.re s.im (i.val + 1) (Nat.succ_pos _) h
  refine ⟨?_, hmass, rfl⟩
  rw [nativeFiberLane_eq_plane, hplane, mul_zero]

/-- The native fiber lane is site-resolved: it determines the routing coefficient at every site. -/
theorem nativeFiberLane_determines_routing (w w' : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (h : Pencil3D.nativeFiberLane w s N = Pencil3D.nativeFiberLane w' s N) (i : Fin N) :
    w (i.val + 1) = w' (i.val + 1) := by
  have hi := congrFun (congrFun h i) 0
  rw [nativeFiberLane_eq_plane, nativeFiberLane_eq_plane] at hi
  have hc : (Geometric.cell (i.val + 1))⁻¹ ≠ 0 := inv_ne_zero (Pencil3D.cell_ne_zero _)
  have hp := mul_left_cancel₀ hc hi
  rw [plane_phasor3D_eq w s.re s.im (i.val + 1) (Nat.succ_pos _),
    plane_phasor3D_eq w' s.re s.im (i.val + 1) (Nat.succ_pos _)] at hp
  have hb : (((i.val + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i.val
  have hz : (((i.val + 1 : ℕ)) : ℂ) ^ (-((s.re : ℂ) + (s.im : ℂ) * Complex.I)) ≠ 0 := by
    intro h0
    exact hb ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  exact mul_right_cancel₀ hz hp

/-- The native metric's reference block is the site count: presence, unit weight, every site. -/
theorem nativeMetric_reference_block (N : ℕ) :
    ((Pencil3D.referenceLane N)ᴴ * Pencil3D.referenceLane N) 0 0 = (N : ℂ) := by
  simp [Pencil3D.referenceLane, Matrix.mul_apply]

/-- The native metric's fiber block is the plane energy `Σ ‖readout‖²`; the neutral mass is not an
entry. -/
theorem nativeMetric_fiber_block (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    ((Pencil3D.nativeFiberLane w s N)ᴴ * Pencil3D.nativeFiberLane w s N) 0 0 =
      ∑ i : Fin N, ((Complex.normSq (SpectralFiber.readout w s (i.val + 1)) : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Pencil3D.nativeFiberLane
  have hc : Complex.normSq (Geometric.cell (i.val + 1)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Geometric.cell_norm]
    norm_num
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_mul, Complex.normSq_inv,
    hc]
  simp

/-! ## Encode / decode: the lane is lossless on routed states (ledger 1147)

A routed 3D bank state at parameter `s` is the 3D phasor of a coefficient at each site. Encoding
takes the despun plane component; decoding recovers the coefficient with the fixed amplitude law
`n^{−s}` and rebuilds the full 3D phasor, mass axis included. The lane does not contain the mass;
on routed states it encodes enough to recover it. On arbitrary 3D states encoding is not injective. -/

/-- A routed 3D bank state on sites `1, …, N` at parameter `s`. -/
noncomputable def routed3DState (w : ℕ → ℂ) (s : ℂ) (N : ℕ) : Fin N → Phasor3D.Vec3 :=
  fun i => Phasor3D.phasor3D w s.re s.im (i.val + 1)

/-- Encode a 3D bank state as a lane: the despun plane component at each site. -/
noncomputable def encodeLane {N : ℕ} (X : Fin N → Phasor3D.Vec3) : Matrix (Fin N) (Fin 1) ℂ :=
  fun i _ => (Geometric.cell (i.val + 1))⁻¹ * Phasor3D.plane (X i)

/-- On routed states the encoding is the native fiber lane. -/
theorem encodeLane_routed (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    encodeLane (routed3DState w s N) = Pencil3D.nativeFiberLane w s N :=
  rfl

/-- Decode the coefficient at site `n` from a lane, with the amplitude law at `s`. -/
noncomputable def decodeCoeff {N : ℕ} (L : Matrix (Fin N) (Fin 1) ℂ) (s : ℂ) : ℕ → ℂ :=
  fun n => if h : 1 ≤ n ∧ n ≤ N then
    Geometric.cell n * L ⟨n - 1, by omega⟩ 0 * (n : ℂ) ^ ((s.re : ℂ) + (s.im : ℂ) * Complex.I)
  else 0

/-- Decode a lane at `s` into a routed 3D bank state. -/
noncomputable def decodeLane {N : ℕ} (L : Matrix (Fin N) (Fin 1) ℂ) (s : ℂ) :
    Fin N → Phasor3D.Vec3 :=
  routed3DState (decodeCoeff L s) s N

/-- The 3D phasor at a site depends on the coefficient only through its value there. -/
theorem phasor3D_congr_site (c c' : ℕ → ℂ) (σ y : ℝ) (n : ℕ) (h : c n = c' n) :
    Phasor3D.phasor3D c σ y n = Phasor3D.phasor3D c' σ y n := by
  unfold Phasor3D.phasor3D LFunctionPhasor.phasorTerm
  rw [h]

/-- **decode ∘ encode = id on routed states.** -/
theorem decode_encode (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    decodeLane (encodeLane (routed3DState w s N)) s = routed3DState w s N := by
  funext i
  apply phasor3D_congr_site
  have hn : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ N := ⟨by omega, by omega⟩
  unfold decodeCoeff
  simp only [hn.1, hn.2, and_self, ↓reduceDIte]
  have hidx : (⟨i.val + 1 - 1, by omega⟩ : Fin N) = i := Fin.ext (by simp)
  rw [hidx]
  show Geometric.cell (i.val + 1) * ((Geometric.cell (i.val + 1))⁻¹ *
      Phasor3D.plane (Phasor3D.phasor3D w s.re s.im (i.val + 1))) *
      (((i.val + 1 : ℕ)) : ℂ) ^ ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = w (i.val + 1)
  rw [plane_phasor3D_eq w s.re s.im (i.val + 1) (Nat.succ_pos _), Complex.cpow_neg]
  have hc : Geometric.cell (i.val + 1) ≠ 0 := Pencil3D.cell_ne_zero _
  have hb : (((i.val + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i.val
  have hz : (((i.val + 1 : ℕ)) : ℂ) ^ ((s.re : ℂ) + (s.im : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact hb ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  field_simp

/-- **Destructive test, lane:** two routed banks with the same lane are the same full 3D state —
every plane and every mass coordinate, neutral sites included. -/
theorem lane_lossless_on_routed (w w' : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (h : Pencil3D.nativeFiberLane w s N = Pencil3D.nativeFiberLane w' s N) :
    routed3DState w s N = routed3DState w' s N := by
  rw [← decode_encode w s N, ← decode_encode w' s N, encodeLane_routed, encodeLane_routed, h]

/-- On arbitrary 3D states the encoding is not injective: two states with the same plane and
different mass have the same lane. The losslessness above comes from the amplitude law. -/
theorem encodeLane_not_injective :
    ∃ X Y : Fin 1 → Phasor3D.Vec3, X ≠ Y ∧ encodeLane X = encodeLane Y := by
  refine ⟨fun _ => (0, 1), fun _ => (0, 2), fun h => ?_, ?_⟩
  · have := congrArg Prod.snd (congrFun h 0)
    norm_num at this
  · funext i j
    simp [encodeLane, Phasor3D.plane]

/-! ## The next morphism consumes aggregates: a destructive witness (ledger 1147)

The native two-lane pencil (`twoLaneHelixA`, `twoLaneB` on `referenceLane N` and
`nativeFiberLane w s N`, heights `i + 1`) reads the lane through site sums. Two routed banks with
different lanes and different neutral sites give the same pencil operators. -/

theorem readout_at_zero (w : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) : SpectralFiber.readout w 0 n = w n := by
  rw [SpectralFiber.readout_eq_phasorTerm]
  unfold LFunctionPhasor.phasorTerm LFunctionPhasor.mellinSpin
  simp [hn]

theorem lane_entry_normSq (w : ℕ → ℂ) (s : ℂ) (N : ℕ) (i : Fin N) :
    star (Pencil3D.nativeFiberLane w s N i 0) * Pencil3D.nativeFiberLane w s N i 0 =
      ((Complex.normSq (SpectralFiber.readout w s (i.val + 1)) : ℝ) : ℂ) := by
  unfold Pencil3D.nativeFiberLane
  have hc : Complex.normSq (Geometric.cell (i.val + 1)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Geometric.cell_norm]
    norm_num
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_mul, Complex.normSq_inv,
    hc]
  simp

theorem native_height_fiber_block (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (Geometric.heightA (Pencil3D.nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ))) 0 0 =
      ∑ i : Fin N, ((i.val + 1 : ℝ) : ℂ) *
        ((Complex.normSq (SpectralFiber.readout w s (i.val + 1)) : ℝ) : ℂ) := by
  unfold Geometric.heightA
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  show star (Pencil3D.nativeFiberLane w s N i 0) * (((i.val + 1 : ℝ)) : ℂ) *
      Pencil3D.nativeFiberLane w s N i 0 = _
  rw [mul_comm (star _) _, mul_assoc, lane_entry_normSq]

/-- Routing 1: coefficient 1 at sites 1 and 4, neutral at 2 and 3. -/
noncomputable def wA : ℕ → ℂ := fun n => if n = 1 ∨ n = 4 then 1 else 0

/-- Routing 2: coefficient 1 at sites 2 and 3, neutral at 1 and 4. -/
noncomputable def wB : ℕ → ℂ := fun n => if n = 2 ∨ n = 3 then 1 else 0

/-- **Destructive test, aggregate:** at `s = 0`, `N = 4`, the two routings have different lanes and
different neutral sites, yet the native pencil's metric, height and coupling blocks agree
(plane energy 2, height-weighted energy 5, coupling 2). -/
theorem aggregate_identifies_wA_wB :
    Pencil3D.nativeFiberLane wA 0 4 ≠ Pencil3D.nativeFiberLane wB 0 4 ∧
      ((Pencil3D.nativeFiberLane wA 0 4)ᴴ * Pencil3D.nativeFiberLane wA 0 4) 0 0 =
        ((Pencil3D.nativeFiberLane wB 0 4)ᴴ * Pencil3D.nativeFiberLane wB 0 4) 0 0 ∧
      (Geometric.heightA (Pencil3D.nativeFiberLane wA 0 4) (fun i => (i.val + 1 : ℝ))) 0 0 =
        (Geometric.heightA (Pencil3D.nativeFiberLane wB 0 4) (fun i => (i.val + 1 : ℝ))) 0 0 ∧
      Pencil3D.nativeCoupling wA 0 4 = Pencil3D.nativeCoupling wB 0 4 := by
  have hA : ∀ i : Fin 4, SpectralFiber.readout wA 0 (i.val + 1) = wA (i.val + 1) :=
    fun i => readout_at_zero wA _ (Nat.succ_ne_zero _)
  have hB : ∀ i : Fin 4, SpectralFiber.readout wB 0 (i.val + 1) = wB (i.val + 1) :=
    fun i => readout_at_zero wB _ (Nat.succ_ne_zero _)
  refine ⟨fun h => ?_, ?_, ?_, ?_⟩
  · have h0 := nativeFiberLane_determines_routing wA wB 0 4 h 0
    simp [wA, wB] at h0
  · rw [nativeMetric_fiber_block, nativeMetric_fiber_block]
    simp only [hA, hB, Fin.sum_univ_four]
    simp [wA, wB]
  · rw [native_height_fiber_block, native_height_fiber_block]
    simp only [hA, hB, Fin.sum_univ_four]
    simp [wA, wB]
    norm_num
  · rw [Pencil3D.nativeCoupling_eq_sum, Pencil3D.nativeCoupling_eq_sum]
    simp only [hA, hB, Fin.sum_univ_four]
    simp [wA, wB]

/-! ## Factorization through the aggregates (ledger 1148)

Every native object downstream of the lane (ThreeDNativePencilLimit, ThreeDNativeFrobenius,
ThreeDAntihelixPairing, ThreeDAntihelixZeroPair) is built from the two-lane operators
`twoLaneB` and `twoLaneHelixA` on the lane space `Fin 1 ⊕ Fin 1`. Those operators are determined by
the aggregates (`nativePencil_eq_of_aggregates`), so every such observable factors through them
(`nativePencilDet_factors` for the pencil determinant). On the character class mod `q` the metric
and height aggregates depend only on coefficient norms, which all characters mod `q` share; the
pencil therefore sees a character mod `q` only through its coupling, the partial L-sum
(`characters_mod_q_pencil_iff_coupling`, `walk_coupling_eq_partialSum`). -/

open Pencil3D Geometric in
/-- **Factorization:** the native two-lane operators are determined by the fiber metric block,
the height block and the coupling. -/
theorem nativePencil_eq_of_aggregates (w w' : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (hE : ((nativeFiberLane w s N)ᴴ * nativeFiberLane w s N) 0 0 =
      ((nativeFiberLane w' s N)ᴴ * nativeFiberLane w' s N) 0 0)
    (hEd : (heightA (nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ))) 0 0 =
      (heightA (nativeFiberLane w' s N) (fun i => (i.val + 1 : ℝ))) 0 0)
    (hC : nativeCoupling w s N = nativeCoupling w' s N) :
    twoLaneB (referenceLane N) (nativeFiberLane w s N) =
        twoLaneB (referenceLane N) (nativeFiberLane w' s N) ∧
      twoLaneHelixA (referenceLane N) (nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ)) =
        twoLaneHelixA (referenceLane N) (nativeFiberLane w' s N) (fun i => (i.val + 1 : ℝ)) := by
  have h1 : (nativeFiberLane w s N)ᴴ * nativeFiberLane w s N =
      (nativeFiberLane w' s N)ᴴ * nativeFiberLane w' s N := by
    ext i j
    fin_cases i
    fin_cases j
    exact hE
  have h2 : heightA (nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ)) =
      heightA (nativeFiberLane w' s N) (fun i => (i.val + 1 : ℝ)) := by
    ext i j
    fin_cases i
    fin_cases j
    exact hEd
  have h3 : laneCouplingC (referenceLane N) (nativeFiberLane w s N) =
      laneCouplingC (referenceLane N) (nativeFiberLane w' s N) := by
    ext i j
    fin_cases i
    fin_cases j
    exact hC
  refine ⟨?_, ?_⟩
  · rw [twoLaneB_eq_blockDiag, twoLaneB_eq_blockDiag, h1]
  · unfold twoLaneHelixA twoLaneA
    rw [h2, h3]

open Pencil3D Geometric in
/-- The pencil determinant factors through the aggregates, at every height. -/
theorem nativePencilDet_factors (w w' : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (hE : ((nativeFiberLane w s N)ᴴ * nativeFiberLane w s N) 0 0 =
      ((nativeFiberLane w' s N)ᴴ * nativeFiberLane w' s N) 0 0)
    (hEd : (heightA (nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ))) 0 0 =
      (heightA (nativeFiberLane w' s N) (fun i => (i.val + 1 : ℝ))) 0 0)
    (hC : nativeCoupling w s N = nativeCoupling w' s N) (Z : ℝ) :
    twoLanePencilDet (referenceLane N) (nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ)) Z =
      twoLanePencilDet (referenceLane N) (nativeFiberLane w' s N) (fun i => (i.val + 1 : ℝ)) Z := by
  obtain ⟨hB, hA⟩ := nativePencil_eq_of_aggregates w w' s N hE hEd hC
  unfold twoLanePencilDet
  rw [hA, hB]

/-- The metric and height aggregates depend on the coefficients only through their norms. -/
theorem aggregates_depend_on_norms (w w' : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (h : ∀ i : Fin N, ‖w (i.val + 1)‖ = ‖w' (i.val + 1)‖) :
    ((Pencil3D.nativeFiberLane w s N)ᴴ * Pencil3D.nativeFiberLane w s N) 0 0 =
        ((Pencil3D.nativeFiberLane w' s N)ᴴ * Pencil3D.nativeFiberLane w' s N) 0 0 ∧
      (Geometric.heightA (Pencil3D.nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ))) 0 0 =
        (Geometric.heightA (Pencil3D.nativeFiberLane w' s N) (fun i => (i.val + 1 : ℝ))) 0 0 := by
  have hr : ∀ i : Fin N, Complex.normSq (SpectralFiber.readout w s (i.val + 1)) =
      Complex.normSq (SpectralFiber.readout w' s (i.val + 1)) := by
    intro i
    show Complex.normSq (Phasor3D.plane (Phasor3D.phasor3D w s.re s.im (i.val + 1))) =
      Complex.normSq (Phasor3D.plane (Phasor3D.phasor3D w' s.re s.im (i.val + 1)))
    rw [plane_phasor3D_eq w s.re s.im (i.val + 1) (Nat.succ_pos _),
      plane_phasor3D_eq w' s.re s.im (i.val + 1) (Nat.succ_pos _), Complex.normSq_mul,
      Complex.normSq_mul, Complex.normSq_eq_norm_sq (w _), Complex.normSq_eq_norm_sq (w' _), h i]
  refine ⟨?_, ?_⟩
  · rw [nativeMetric_fiber_block, nativeMetric_fiber_block]
    exact Finset.sum_congr rfl fun i _ => by rw [hr i]
  · rw [native_height_fiber_block, native_height_fiber_block]
    exact Finset.sum_congr rfl fun i _ => by rw [hr i]

open Pencil3D Geometric in
/-- **With equal coefficient norms, the native pencils agree exactly when the couplings agree.** -/
theorem nativePencil_eq_iff_coupling (w w' : ℕ → ℂ) (s : ℂ) (N : ℕ)
    (h : ∀ i : Fin N, ‖w (i.val + 1)‖ = ‖w' (i.val + 1)‖) :
    (twoLaneB (referenceLane N) (nativeFiberLane w s N) =
        twoLaneB (referenceLane N) (nativeFiberLane w' s N) ∧
      twoLaneHelixA (referenceLane N) (nativeFiberLane w s N) (fun i => (i.val + 1 : ℝ)) =
        twoLaneHelixA (referenceLane N) (nativeFiberLane w' s N) (fun i => (i.val + 1 : ℝ))) ↔
      nativeCoupling w s N = nativeCoupling w' s N := by
  constructor
  · rintro ⟨-, hA⟩
    have := congrFun (congrFun hA (Sum.inl 0)) (Sum.inr 0)
    simp only [twoLaneHelixA, twoLaneA, Matrix.fromBlocks_apply₁₂] at this
    exact this
  · intro hC
    obtain ⟨hE, hEd⟩ := aggregates_depend_on_norms w w' s N h
    exact nativePencil_eq_of_aggregates w w' s N hE hEd hC

/-- All characters mod `q` route with the same coefficient norms: `1` on units, `0` off them. -/
theorem character_walk_norms_agree {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (order₁ : ℕ) (gens₁ strides₁ : List ℕ)
    (hχ₁ : List.Forall₂ (fun (g st : ℕ) => χ₁ ((g : ℕ) : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (st : ℂ) / (order₁ : ℂ))) gens₁ strides₁)
    (hgen₁ : ∀ u : (ZMod q)ˣ, ∃ ks ∈ stepTuples q gens₁.length,
      (((List.zipWith (fun g k => g ^ k) gens₁ ks).prod : ℕ) : ZMod q) = (u : ZMod q))
    (order₂ : ℕ) (gens₂ strides₂ : List ℕ)
    (hχ₂ : List.Forall₂ (fun (g st : ℕ) => χ₂ ((g : ℕ) : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (st : ℂ) / (order₂ : ℂ))) gens₂ strides₂)
    (hgen₂ : ∀ u : (ZMod q)ˣ, ∃ ks ∈ stepTuples q gens₂.length,
      (((List.zipWith (fun g k => g ^ k) gens₂ ks).prod : ℕ) : ZMod q) = (u : ZMod q))
    (n : ℕ) :
    ‖(Routing.walk q order₁ gens₁ strides₁).coeff n‖ =
      ‖(Routing.walk q order₂ gens₂ strides₂).coeff n‖ := by
  show ‖walkValueC q order₁ gens₁ strides₁ n‖ = ‖walkValueC q order₂ gens₂ strides₂ n‖
  rw [← character_eq_walk χ₁ order₁ gens₁ strides₁ hχ₁ hgen₁ n,
    ← character_eq_walk χ₂ order₂ gens₂ strides₂ hχ₂ hgen₂ n]
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨u, hu⟩ := hu
    rw [← hu, DirichletCharacter.unit_norm_eq_one, DirichletCharacter.unit_norm_eq_one]
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]

open Pencil3D Geometric in
/-- **On the character class mod `q`, the native pencil sees the character only through its
coupling:** two characters mod `q` have the same two-lane operators exactly when their couplings
agree. -/
theorem characters_mod_q_pencil_iff_coupling {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (order₁ : ℕ) (gens₁ strides₁ : List ℕ)
    (hχ₁ : List.Forall₂ (fun (g st : ℕ) => χ₁ ((g : ℕ) : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (st : ℂ) / (order₁ : ℂ))) gens₁ strides₁)
    (hgen₁ : ∀ u : (ZMod q)ˣ, ∃ ks ∈ stepTuples q gens₁.length,
      (((List.zipWith (fun g k => g ^ k) gens₁ ks).prod : ℕ) : ZMod q) = (u : ZMod q))
    (order₂ : ℕ) (gens₂ strides₂ : List ℕ)
    (hχ₂ : List.Forall₂ (fun (g st : ℕ) => χ₂ ((g : ℕ) : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (st : ℂ) / (order₂ : ℂ))) gens₂ strides₂)
    (hgen₂ : ∀ u : (ZMod q)ˣ, ∃ ks ∈ stepTuples q gens₂.length,
      (((List.zipWith (fun g k => g ^ k) gens₂ ks).prod : ℕ) : ZMod q) = (u : ZMod q))
    (s : ℂ) (N : ℕ) :
    (twoLaneB (referenceLane N) (nativeFiberLane (Routing.walk q order₁ gens₁ strides₁).coeff s N) =
        twoLaneB (referenceLane N) (nativeFiberLane (Routing.walk q order₂ gens₂ strides₂).coeff s N) ∧
      twoLaneHelixA (referenceLane N) (nativeFiberLane (Routing.walk q order₁ gens₁ strides₁).coeff s N)
          (fun i => (i.val + 1 : ℝ)) =
        twoLaneHelixA (referenceLane N)
          (nativeFiberLane (Routing.walk q order₂ gens₂ strides₂).coeff s N)
          (fun i => (i.val + 1 : ℝ))) ↔
      nativeCoupling (Routing.walk q order₁ gens₁ strides₁).coeff s N =
        nativeCoupling (Routing.walk q order₂ gens₂ strides₂).coeff s N :=
  nativePencil_eq_iff_coupling _ _ s N fun i =>
    character_walk_norms_agree χ₁ χ₂ order₁ gens₁ strides₁ hχ₁ hgen₁ order₂ gens₂ strides₂ hχ₂
      hgen₂ (i.val + 1)

/-- The coupling of a character walk is the partial L-sum `Σ_{n ≤ N} χ(n) n^{−s}`. -/
theorem walk_coupling_eq_partialSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (order : ℕ) (gens strides : List ℕ)
    (hχ : List.Forall₂ (fun (g st : ℕ) => χ ((g : ℕ) : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (st : ℂ) / (order : ℂ))) gens strides)
    (hgen : ∀ u : (ZMod q)ˣ, ∃ ks ∈ stepTuples q gens.length,
      (((List.zipWith (fun g k => g ^ k) gens ks).prod : ℕ) : ZMod q) = (u : ZMod q))
    (s : ℂ) (N : ℕ) :
    Pencil3D.nativeCoupling (Routing.walk q order gens strides).coeff s N =
      ∑ i : Fin N, DirichletPhasorCarrier.phasorTerm χ s (i.val + 1) := by
  rw [Pencil3D.nativeCoupling_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := plane_routed_walk_eq_phasorTerm χ order gens strides hχ hgen s.re s.im (i.val + 1)
    (Nat.succ_pos _)
  rw [Complex.re_add_im] at h
  exact h

end CriticalLinePhasor.PairedTrace

#print axioms CriticalLinePhasor.PairedTrace.enrichedPencil_rowGram_radial
#print axioms CriticalLinePhasor.PairedTrace.gram_identifies_3_4_and_5_0
#print axioms CriticalLinePhasor.PairedTrace.pencil_distinguishes_3_4_and_5_0
#print axioms CriticalLinePhasor.PairedTrace.nativeFiberLane_neutral
#print axioms CriticalLinePhasor.PairedTrace.nativeFiberLane_determines_routing
#print axioms CriticalLinePhasor.PairedTrace.nativeMetric_reference_block
#print axioms CriticalLinePhasor.PairedTrace.nativeMetric_fiber_block
#print axioms CriticalLinePhasor.PairedTrace.decode_encode
#print axioms CriticalLinePhasor.PairedTrace.lane_lossless_on_routed
#print axioms CriticalLinePhasor.PairedTrace.encodeLane_not_injective
#print axioms CriticalLinePhasor.PairedTrace.aggregate_identifies_wA_wB
