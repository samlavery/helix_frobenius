import RequestProject.EisensteinWheelBank
import RequestProject.FiberPencilWiring
import RequestProject.ThreeDPencilOperator
import RequestProject.GlobalHelixIntertwiner
import RequestProject.CarrierChannelReadout

/-!
# The fiber–detector chain, wired end to end (ledger 1153)

    scaled carrier → warp → grown fiber → focal cancellation ⇔ detector rank drop
      → limit → event height → projection → J → readout

The cancellation is an event of the fiber; the harmonic pencil `!![A, B; μA, λB]` detects it
(`phasor_explorer/model.py`, "GRAM PENCIL").

* **Carrier → warp → fiber** (`carrier_warp_fiber`): the warp on a carrier scaled by `Δ` is the factor
  `Δ^{−s}` on the grown fiber, and the grown fiber is the head-windowed plane readout of the routed 3D
  state. `lawFiber w Z s` is the grown fiber of a site law `w`; `lawFiber_routed`, `lawFiber_eta`
  (`= finiteFiber`), `lawFiber_walk` (a character walk is its character).
* **Finite stage** (`finite_cancel_iff_rankDrop`): at every head `Z > 1`, the grown fiber cancels
  exactly when the detector fed with its own channels drops rank. The unsigned channel is the grown
  unsigned mass `lawUnsigned`, positive (`lawUnsigned_pos`). On the two-ended state:
  `focalCancellation_iff_detector` (helix end ⇔ J-end ⇔ rank drop at the physical head).
  The unsigned channel scales the first column only (`harmonicPencil_factor`), so the normalized
  detector `harmonicPencil 1 B μ λ` detects the same event (`normalized_rankDrop_iff`).
* **Finite → limit.** `windowed_tendsto`: a head-windowed sum tends to the limit of its partial
  sums. Hence `lawFiber_char_tendsto` (→ `L(χ, s)`, `Re s > 0`) and `lawFiber_eta_tendsto`
  (→ `(1 − 2^{1−s})ζ(s)`). The normalized detector converges as an operator
  (`normalizedDetector_tendsto`); for a character its limit is `fullFiberMatrix χ s`
  (`detector_tendsto_fullFiberMatrix`). `lawFiber_tendsto_fiberResultant` joins FiberPencilWiring.
* **Limit stage** (`limit_chain_char`, `limit_chain_eta`): the grown fiber's limit cancels ⇔ the
  limit detector drops rank ⇔ (for χ) the 3D full-fiber Gram is singular.
* **Event → projection → J → readout** (`event_projection`): the event read at `s` sits at physical
  height `e^{Im s}`; the cone projection keeps that height and reconstructs the carrier point from it;
  the 1D readout of the height is `Im s`; J acts on the Cayley readout by conjugation.
* **The carrier-point chains** (promoted from tmp/att1080 and tmp/att1081): `all_fibers_chain`,
  `sam_chain`. Here the fiber is read at `carrierPointAtHeight Z`, whose real part is the carrier
  abscissa; its value is used only for `0 < Re s < 1` (`carrierAbscissa_pos`, `carrierAbscissa_lt_one`).
-/

open Complex Filter Topology Finset Matrix
open scoped BigOperators

noncomputable section

namespace CriticalLinePhasor.FiberDetectorChain

open CriticalLinePhasor
open CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.GrownFiber
open CriticalLinePhasor.GrownFiberEvolution
open CriticalLinePhasor.EisensteinWheelBank
open CriticalLinePhasor.HarmonicCell

/-! ## 1. Windowed sums and their limits -/

/-- The head-windowed sum at head `Z` of a site sequence (`c k` sits at site `k + 1`). -/
def windowed (c : ℕ → ℂ) (Z : ℝ) : ℂ :=
  ∑ k ∈ range ⌈Z⌉₊, ((headWindow Z k : ℝ) : ℂ) * c k

/-- The completed partial sums of the same sequence. -/
def partialSum (c : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ range n, c k

/-- **Abel summation on a windowed sum.** -/
theorem windowed_eq_avg {Z : ℝ} (hZ : 0 < Z) (c : ℕ → ℂ) :
    windowed c Z = ∑ i ∈ range (⌈Z⌉₊ - 1), ((weight Z i : ℝ) : ℂ) * partialSum c (i + 1) := by
  unfold windowed
  set M : ℕ := ⌈Z⌉₊ with hM
  set f : ℕ → ℂ := fun i => ((smoothEntry (((i + 1 : ℕ) : ℝ) / Z) : ℝ) : ℂ) with hf
  have hsum_eq : (∑ k ∈ range M, ((headWindow Z k : ℝ) : ℂ) * c k) = ∑ i ∈ range M, f i • c i :=
    Finset.sum_congr rfl fun i _ => by rw [hf, smul_eq_mul]; rfl
  rw [hsum_eq, Finset.sum_range_by_parts f c M]
  have hM1 : 1 ≤ M := Nat.ceil_pos.mpr hZ
  have hfM : f (M - 1) = 0 := by
    rw [hf]
    simp only
    rw [show ((M - 1 + 1 : ℕ) : ℝ) = (M : ℝ) by rw [Nat.sub_add_cancel hM1]]
    rw [smoothEntry_of_one_le, Complex.ofReal_zero]
    rw [le_div_iff₀ hZ, one_mul]
    exact Nat.le_ceil Z
  rw [hfM, zero_smul, zero_sub, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, smul_eq_mul]
  unfold weight partialSum
  simp only
  push_cast
  ring_nf

/-- **A head-windowed sum tends to the limit of its partial sums** as the head climbs. -/
theorem windowed_tendsto {c : ℕ → ℂ} {L : ℂ} (hP : Tendsto (partialSum c) atTop (𝓝 L)) :
    Tendsto (windowed c) atTop (𝓝 L) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖partialSum c n‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hP)
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set B : ℝ := C + ‖L‖ + 1 with hB
  have hBpos : 0 < B := by positivity
  have hPB : ∀ n, ‖partialSum c n - L‖ ≤ B := fun n =>
    (norm_sub_le _ _).trans (by linarith [hC n])
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / 4 with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hP ε' hε'pos
  set N₀ : ℕ := N₁ + 1 with hN₀
  have hPclose : ∀ n, N₀ ≤ n → ‖partialSum c n - L‖ < ε' := fun n hn => by
    have h := hN₁ n (by omega)
    rwa [dist_eq_norm] at h
  have hN1 : (1 : ℝ) ≤ N₀ := by rw [hN₀]; push_cast; linarith [(N₁.cast_nonneg : (0:ℝ) ≤ N₁)]
  refine ⟨max (2 * N₀ + 2) (max (8 * (N₀ : ℝ) ^ 2 * B / ε') (2 * (‖L‖ + 1) / ε')),
    fun Zn hn => ?_⟩
  have hZ1 : 2 * (N₀ : ℝ) + 2 ≤ Zn := (le_max_left _ _).trans hn
  have hZ2 : 8 * (N₀ : ℝ) ^ 2 * B / ε' ≤ Zn :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hZ3 : 2 * (‖L‖ + 1) / ε' ≤ Zn := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hZpos : 0 < Zn := by linarith
  have hZ2' : 2 ≤ Zn := by linarith
  have hZsq : Zn ≤ Zn ^ 2 := by nlinarith
  set M : ℕ := ⌈Zn⌉₊ with hM
  have hMZ : Zn ≤ M := Nat.le_ceil Zn
  have hMN : N₀ + 1 ≤ M - 1 := by
    have h1 : (2 * N₀ + 2 : ℝ) ≤ M := hZ1.trans hMZ
    have h2 : 2 * N₀ + 2 ≤ M := by exact_mod_cast h1
    omega
  have hM1 : 1 ≤ M := by omega
  have h01 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  have hMcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by rw [Nat.cast_sub hM1]; push_cast; ring
  have hw1 : ∑ i ∈ range (M - 1), weight Zn i = smoothEntry (1 / Zn) := by
    rw [Finset.range_eq_Ico, sum_weight_Ico Zn (Nat.zero_le _), h01, hMcast,
      smoothEntry_of_one_le (u := (M : ℝ) / Zn) (by rw [le_div_iff₀ hZpos, one_mul]; exact hMZ),
      sub_zero]
  have hsumC : (∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ)) = ((smoothEntry (1 / Zn) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum, hw1]
  rw [dist_eq_norm, windowed_eq_avg hZpos]
  have hdecomp : ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * partialSum c (i + 1) - L
      = (∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L))
        - ((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * L := by
    have hsplit : ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L)
        = ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * partialSum c (i + 1)
          - (∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ)) * L := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hsumC]
    push_cast
    ring
  rw [hdecomp]
  have hsplit2 : ∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L)
      = ∑ i ∈ Finset.Ico 0 N₀, ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L)
        + ∑ i ∈ Finset.Ico N₀ (M - 1), ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]
  have hbound1 : ‖∑ i ∈ Finset.Ico 0 N₀, ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L)‖
      ≤ (∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * B := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hZpos i)]
    exact mul_le_mul_of_nonneg_left (hPB _) (weight_nonneg hZpos i)
  have hbound2 : ‖∑ i ∈ Finset.Ico N₀ (M - 1), ((weight Zn i : ℝ) : ℂ) *
      (partialSum c (i + 1) - L)‖ ≤ (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε' := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hZpos i)]
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg hZpos i)
    exact (hPclose (i + 1) (by rw [Finset.mem_Ico] at hi; omega)).le
  have hsum1 : ∑ i ∈ Finset.Ico 0 N₀, weight Zn i ≤ 2 * (((N₀ : ℝ) + 1) / Zn) ^ 2 := by
    rw [sum_weight_Ico Zn (Nat.zero_le _), h01]
    have h1 := smoothEntry_le_one (u := 1 / Zn) (by positivity)
    have h2 := one_sub_smoothEntry_le (u := ((N₀ : ℝ) + 1) / Zn) (by positivity)
      (by rw [div_le_iff₀ hZpos]; linarith)
    linarith
  have hsum2 : ∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i ≤ 1 := by
    rw [sum_weight_Ico Zn (by omega)]
    have h1 := smoothEntry_le_one (u := ((N₀ : ℝ) + 1) / Zn) (by positivity)
    have h2 := smoothEntry_nonneg ((((M - 1 : ℕ) : ℝ) + 1) / Zn)
    linarith
  have hlast : ‖((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * L‖ ≤ 2 * (1 / Zn) ^ 2 * (‖L‖ + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := one_sub_smoothEntry_le (u := 1 / Zn) (by positivity)
      (by rw [div_le_iff₀ hZpos]; linarith)
    have h0 := smoothEntry_le_one (u := 1 / Zn) (by positivity)
    rw [abs_of_nonneg (by linarith)]
    exact mul_le_mul h1 (by linarith) (norm_nonneg _) (by positivity)
  have hpiece1 : (∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * B ≤ ε' := by
    have hN : ((N₀ : ℝ) + 1) ^ 2 ≤ 4 * (N₀ : ℝ) ^ 2 := by nlinarith
    have h1 : ((N₀ : ℝ) + 1) ^ 2 / Zn ^ 2 ≤ 4 * (N₀ : ℝ) ^ 2 / Zn := by
      rw [div_le_div_iff₀ (by positivity) hZpos]
      nlinarith [mul_nonneg (sq_nonneg (N₀ : ℝ)) (sub_nonneg.mpr hZsq)]
    calc (∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * B
        ≤ 2 * (((N₀ : ℝ) + 1) / Zn) ^ 2 * B := mul_le_mul_of_nonneg_right hsum1 hBpos.le
      _ = 2 * (((N₀ : ℝ) + 1) ^ 2 / Zn ^ 2 * B) := by rw [div_pow]; ring
      _ ≤ 2 * (4 * (N₀ : ℝ) ^ 2 / Zn * B) := by
          have := mul_le_mul_of_nonneg_right h1 hBpos.le
          linarith
      _ = 8 * (N₀ : ℝ) ^ 2 * B / Zn := by ring
      _ ≤ ε' := by
          rw [div_le_iff₀ hZpos]
          calc 8 * (N₀ : ℝ) ^ 2 * B = (8 * (N₀ : ℝ) ^ 2 * B / ε') * ε' := by field_simp
            _ ≤ Zn * ε' := mul_le_mul_of_nonneg_right hZ2 hε'pos.le
            _ = ε' * Zn := mul_comm _ _
  have hpiece2 : (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε' ≤ ε' := by
    calc (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε' ≤ 1 * ε' :=
          mul_le_mul_of_nonneg_right hsum2 hε'pos.le
      _ = ε' := one_mul _
  have hpiece3 : 2 * (1 / Zn) ^ 2 * (‖L‖ + 1) ≤ ε' := by
    calc 2 * (1 / Zn) ^ 2 * (‖L‖ + 1) = 2 * (‖L‖ + 1) / Zn ^ 2 := by ring
      _ ≤ 2 * (‖L‖ + 1) / Zn := div_le_div_of_nonneg_left (by positivity) hZpos hZsq
      _ ≤ ε' := by
          rw [div_le_iff₀ hZpos]
          calc 2 * (‖L‖ + 1) = (2 * (‖L‖ + 1) / ε') * ε' := by field_simp
            _ ≤ Zn * ε' := mul_le_mul_of_nonneg_right hZ3 hε'pos.le
            _ = ε' * Zn := mul_comm _ _
  calc ‖(∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L))
        - ((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * L‖
      ≤ ‖∑ i ∈ range (M - 1), ((weight Zn i : ℝ) : ℂ) * (partialSum c (i + 1) - L)‖
        + ‖((1 - smoothEntry (1 / Zn) : ℝ) : ℂ) * L‖ := norm_sub_le _ _
    _ ≤ ((∑ i ∈ Finset.Ico 0 N₀, weight Zn i) * B
          + (∑ i ∈ Finset.Ico N₀ (M - 1), weight Zn i) * ε')
        + 2 * (1 / Zn) ^ 2 * (‖L‖ + 1) := by
        apply add_le_add _ hlast
        rw [hsplit2]
        exact (norm_add_le _ _).trans (add_le_add hbound1 hbound2)
    _ ≤ ε' + ε' + ε' := by linarith [hpiece1, hpiece2, hpiece3]
    _ < ε := by rw [hε']; linarith

/-! ## 2. The grown fiber of a site law -/

/-- The grown fiber of a site law `w` at head `Z`: site `n = k + 1` carries `w(n)·n^{−s}` with the
head window. -/
def lawFiber (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) : ℂ :=
  windowed (fun k => w (k + 1) * ((k : ℂ) + 1) ^ (-s)) Z

theorem lawFiber_routed (r : Routing) (Z : ℝ) (s : ℂ) :
    routedGrownFiber r Z s = lawFiber r.coeff Z s :=
  rfl

/-- The η law is the carrier's grown fiber `finiteFiber`. -/
theorem lawFiber_eta (Z : ℝ) (s : ℂ) : finiteFiber Z s = lawFiber Routing.eta.coeff Z s := by
  rw [finiteFiber_eq_routed_eta, lawFiber_routed]

/-- A character walk's grown fiber is its character's grown fiber. -/
theorem lawFiber_walk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (order : ℕ)
    (gens strides : List ℕ)
    (hχ : List.Forall₂ (fun (g st : ℕ) => χ ((g : ℕ) : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (st : ℂ) / (order : ℂ))) gens strides)
    (hgen : ∀ u : (ZMod q)ˣ, ∃ ks ∈ stepTuples q gens.length,
      (((List.zipWith (fun g k => g ^ k) gens ks).prod : ℕ) : ZMod q) = (u : ZMod q))
    (Z : ℝ) (s : ℂ) :
    routedGrownFiber (.walk q order gens strides) Z s =
      lawFiber (fun n => χ (n : ZMod q)) Z s := by
  rw [routedGrownFiber_walk_eq χ order gens strides hχ hgen]
  unfold lawFiber windowed
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold DirichletPhasorCarrier.phasorTerm
  push_cast
  rfl

/-- **Carrier → warp → fiber.** On the carrier scaled by `Δ` the warp multiplies the grown fiber by
`Δ^{−s}`, and the grown fiber is the head-windowed plane readout of the routed 3D state. -/
theorem carrier_warp_fiber (r : Routing) {Δ : ℝ} (hΔ : 0 < Δ) (Z σ y : ℝ) :
    routedGaugedFiber r Δ Z ((σ : ℂ) + (y : ℂ) * Complex.I) =
        (Δ : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I)) *
          lawFiber r.coeff Z ((σ : ℂ) + (y : ℂ) * Complex.I) ∧
      lawFiber r.coeff Z ((σ : ℂ) + (y : ℂ) * Complex.I) =
        ∑ k ∈ Finset.range ⌈Z⌉₊, ((headWindow Z k : ℝ) : ℂ) *
          Phasor3D.plane (Phasor3D.phasor3D r.coeff σ y (k + 1)) :=
  ⟨routedGaugedFiber_eq r hΔ Z _, routedGrownFiber_eq_plane_sum r σ y Z⟩

/-! ## 3. Finite stage: the fiber cancels ⇔ the detector drops rank -/

/-- The grown unsigned channel `A = Σ window·‖w(n)‖·n^{−σ}`. -/
def lawUnsigned (w : ℕ → ℂ) (Z σ : ℝ) : ℝ :=
  ∑ k ∈ range ⌈Z⌉₊, headWindow Z k * ‖w (k + 1)‖ * ((k : ℝ) + 1) ^ (-σ)

theorem smoothEntry_pos {u : ℝ} (hu : u < 1) : 0 < smoothEntry u := by
  unfold smoothEntry
  simp only [hu, ↓reduceIte]
  positivity

/-- The grown unsigned channel is positive once the head is past the first site. -/
theorem lawUnsigned_pos (w : ℕ → ℂ) {Z : ℝ} (hZ : 1 < Z) (hw : ‖w 1‖ = 1) (σ : ℝ) :
    0 < lawUnsigned w Z σ := by
  unfold lawUnsigned
  have hmem : 0 ∈ range ⌈Z⌉₊ := Finset.mem_range.mpr (Nat.ceil_pos.mpr (by linarith))
  refine Finset.sum_pos' (fun k _ => ?_) ⟨0, hmem, ?_⟩
  · exact mul_nonneg (mul_nonneg (smoothEntry_nonneg _) (norm_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  · have h1 : 0 < headWindow Z 0 := by
      unfold headWindow
      apply smoothEntry_pos
      rw [div_lt_one (by linarith)]
      push_cast
      linarith
    simp only [zero_add, hw, mul_one, Nat.cast_zero, Real.one_rpow]
    exact h1

/-- The specified detector `!![A, B; μA, λB]` fed with the grown fiber's own channels. -/
def lawDetector (w : ℕ → ℂ) (Z : ℝ) (s μ lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  harmonicPencil ((lawUnsigned w Z s.re : ℝ) : ℂ) (lawFiber w Z s) μ lam

/-- **Finite stage: the grown fiber cancels at head `Z` exactly when the detector drops rank.** -/
theorem finite_cancel_iff_rankDrop (w : ℕ → ℂ) {Z : ℝ} (hZ : 1 < Z) (hw : ‖w 1‖ = 1)
    (s μ lam : ℂ) (hlam : lam ≠ μ) :
    lawFiber w Z s = 0 ↔ ((lawDetector w Z s μ lam)ᴴ * lawDetector w Z s μ lam).det = 0 :=
  (harmonicGram_rank_drop_iff_channel_zero _ _ μ lam
    (by exact_mod_cast (lawUnsigned_pos w hZ hw s.re).ne') hlam).symm

/-- The unsigned channel scales the detector's first column only. -/
theorem harmonicPencil_factor (A B μ lam : ℂ) :
    harmonicPencil A B μ lam = harmonicPencil 1 B μ lam * Matrix.diagonal ![A, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [harmonicPencil, Matrix.mul_diagonal]

/-- The normalized detector `harmonicPencil 1 B μ λ` detects the same event. -/
theorem normalized_rankDrop_iff {A : ℂ} (hA : A ≠ 0) (B μ lam : ℂ) (hlam : lam ≠ μ) :
    ((harmonicPencil A B μ lam)ᴴ * harmonicPencil A B μ lam).det = 0 ↔
      ((harmonicPencil 1 B μ lam)ᴴ * harmonicPencil 1 B μ lam).det = 0 := by
  rw [harmonicGram_rank_drop_iff_channel_zero _ _ μ lam hA hlam,
    harmonicGram_rank_drop_iff_channel_zero _ _ μ lam one_ne_zero hlam]

theorem one_lt_physicalHead {y : ℝ} (hy : 0 ≤ y) : 1 < physicalHead y := by
  have h := physicalHead_lower y
  have he : 1 ≤ Real.exp y := Real.one_le_exp hy
  nlinarith

/-- **The two-ended focal cancellation is the detector's rank drop at the physical head**, for every
unimodular routing (η included): helix end ⇔ J-end ⇔ rank drop. -/
theorem focalCancellation_iff_detector (r : Routing) (hunit : ∀ k, ‖r.coeff (k + 1)‖ = 1)
    (σ : ℝ) {y : ℝ} (hy : 0 ≤ y) (μ lam : ℂ) (hlam : lam ≠ μ) :
    (TwoEndedJState.FocalCancellation (routingData r hunit σ) y ↔
        TwoEndedJState.grownJEnd (routingData r hunit σ) (physicalHead y) y = 0) ∧
      (TwoEndedJState.FocalCancellation (routingData r hunit σ) y ↔
        ((lawDetector r.coeff (physicalHead y) ((σ : ℂ) + (y : ℂ) * Complex.I) μ lam)ᴴ *
          lawDetector r.coeff (physicalHead y) ((σ : ℂ) + (y : ℂ) * Complex.I) μ lam).det = 0) := by
  refine ⟨TwoEndedJState.focalCancellation_iff_jEnd _ _, ?_⟩
  rw [focalCancellation_routed r hunit σ y, lawFiber_routed]
  exact finite_cancel_iff_rankDrop r.coeff (one_lt_physicalHead hy) (hunit 0) _ μ lam hlam

/-! ## 4. Finite → limit -/

theorem partialSum_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re)
    (n : ℕ) :
    partialSum (fun k => χ ((k + 1 : ℕ) : ZMod q) * ((k : ℂ) + 1) ^ (-s)) n =
      ∑ m ∈ range (n + 1), SpectralFiber.readout (fun m => χ (m : ZMod q)) s m := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  rw [Finset.sum_range_succ', SpectralFiber.readout_term χ hs 0]
  simp only [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0), mul_zero, add_zero]
  unfold partialSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [SpectralFiber.readout_term χ hs (k + 1)]
  push_cast
  ring

/-- **The character grown fiber converges to `L(χ, s)`** as the head climbs, for `Re s > 0`. -/
theorem lawFiber_char_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun Z => lawFiber (fun n => χ (n : ZMod q)) Z s) atTop
      (𝓝 (DirichletCharacter.LFunction χ s)) := by
  apply windowed_tendsto
  have h := (SpectralFiber.spectralFiber_readout_tendsto_LFunction χ hχ hs).comp
    (tendsto_add_atTop_nat 1)
  refine h.congr fun n => ?_
  simp only [Function.comp_def]
  rw [partialSum_char χ hs n]

theorem partialSum_eta (s : ℂ) (n : ℕ) :
    partialSum (fun k => Routing.eta.coeff (k + 1) * ((k : ℂ) + 1) ^ (-s)) n = partialReadout n s := by
  unfold partialSum partialReadout
  exact Finset.sum_congr rfl fun k _ => by simp only [coeff_eta]

/-- **The η grown fiber converges to `(1 − 2^{1−s})·ζ(s)`**, for `Re s > 0`, `s ≠ 1`. -/
theorem lawFiber_eta_tendsto {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun Z => lawFiber Routing.eta.coeff Z s) atTop
      (𝓝 ((1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s)) := by
  rw [← BankNoTransient.etaTailLimit_eq_etaProduct hs hs1]
  apply windowed_tendsto
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have h := (hardPartial_tendstoLocallyUniformlyOn.tendsto_at
    (show s ∈ {s : ℂ | 0 < s.re} from hs)).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun n => ?_
  simp only [Function.comp_def]
  rw [partialSum_eta, partialReadout_eq_hardPartial n hs0]

/-- The grown fiber's limit is FiberPencilWiring's resultant. -/
theorem lawFiber_tendsto_fiberResultant {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun Z => lawFiber (fun n => χ (n : ZMod q)) Z s) atTop
      (𝓝 (FiberPencilWiring.fiberResultant (fun n => χ (n : ZMod q)) s)) := by
  rw [FiberPencilWiring.fiberResultant_eq_LFunction χ hχ hs]
  exact lawFiber_char_tendsto χ hχ hs

/-- **The normalized detector converges as an operator** whenever its signed channel converges. -/
theorem normalizedDetector_tendsto {f : ℝ → ℂ} {L : ℂ} (hf : Tendsto f atTop (𝓝 L)) (μ lam : ℂ) :
    Tendsto (fun Z => harmonicPencil 1 (f Z) μ lam) atTop (𝓝 (harmonicPencil 1 L μ lam)) := by
  have hc : Continuous fun B : ℂ => harmonicPencil 1 B μ lam :=
    continuous_matrix fun i j => by
      fin_cases i <;> fin_cases j <;> simp [harmonicPencil] <;> fun_prop
  exact (hc.tendsto L).comp hf

/-- **The completed full-fiber matrix is the operator limit of the normalized finite detector** fed
with the character's grown fiber. -/
theorem detector_tendsto_fullFiberMatrix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun Z => harmonicPencil 1 (lawFiber (fun n => χ (n : ZMod q)) Z s) 0 1) atTop
      (𝓝 (Pencil3D.fullFiberMatrix χ s)) :=
  normalizedDetector_tendsto (lawFiber_char_tendsto χ hχ hs) 0 1

/-! ## 5. Limit stage -/

/-- **The limit chain for a character**: the grown fiber's limit cancels ⇔ `L(χ, s) = 0` ⇔ the limit
detector drops rank ⇔ the 3D full-fiber Gram is singular. -/
theorem limit_chain_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (μ lam : ℂ) (hlam : lam ≠ μ) :
    (Tendsto (fun Z => lawFiber (fun n => χ (n : ZMod q)) Z s) atTop (𝓝 0) ↔
        DirichletCharacter.LFunction χ s = 0) ∧
      (DirichletCharacter.LFunction χ s = 0 ↔
        ((harmonicPencil 1 (DirichletCharacter.LFunction χ s) μ lam)ᴴ *
          harmonicPencil 1 (DirichletCharacter.LFunction χ s) μ lam).det = 0) ∧
      (DirichletCharacter.LFunction χ s = 0 ↔ (Pencil3D.fullFiberGram3D χ s).det = 0) := by
  have h := lawFiber_char_tendsto χ hχ hs
  refine ⟨⟨fun h0 => tendsto_nhds_unique h h0, fun hL => hL ▸ h⟩,
    (harmonicGram_rank_drop_iff_channel_zero _ _ μ lam one_ne_zero hlam).symm, ?_⟩
  rw [Pencil3D.fullFiberGram3D_det]
  constructor
  · intro hL
    rw [hL]
    simp
  · intro h0
    have h1 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h0
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact star_eq_zero.mp h2
    · exact h2

/-- **The limit chain for η** on the open strip: the grown fiber's limit cancels ⇔ `ζ(s) = 0` ⇔ the
limit detector drops rank. -/
theorem limit_chain_eta {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (μ lam : ℂ) (hlam : lam ≠ μ) :
    (Tendsto (fun Z => lawFiber Routing.eta.coeff Z s) atTop (𝓝 0) ↔ riemannZeta s = 0) ∧
      (riemannZeta s = 0 ↔
        ((harmonicPencil 1 ((1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) μ lam)ᴴ *
          harmonicPencil 1 ((1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) μ lam).det = 0) := by
  have hne : s ≠ 1 := by
    rintro rfl
    simp at hs1
  have hfac := CarrierChannelReadout.etaFactor_ne_zero hs1
  have h := lawFiber_eta_tendsto hs0 hne
  have hiff : (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s = 0 ↔ riemannZeta s = 0 :=
    ⟨fun h0 => (mul_eq_zero.mp h0).resolve_left hfac, fun hz => by rw [hz, mul_zero]⟩
  refine ⟨⟨fun h0 => hiff.mp (tendsto_nhds_unique h h0), fun hz => ?_⟩, ?_⟩
  · rwa [hiff.mpr hz] at h
  · rw [harmonicGram_rank_drop_iff_channel_zero _ _ μ lam one_ne_zero hlam, hiff]

/-! ## 6. Event → projection → J → readout -/

/-- **From the event to the readout.** The event read at `s` sits at physical height `e^{Im s}`.
The cone projection keeps that height and reconstructs the carrier point from it; the 1D readout of
the height is `Im s`; J acts on the Cayley readout of the carrier point by conjugation. -/
theorem event_projection (s : ℂ) :
    0 < TwoEndedJState.eventHeight s.im ∧
      ConeProjection.project (ConeProjection.coneFiber (TwoEndedJState.eventHeight s.im)) =
        TwoEndedJState.eventHeight s.im ∧
      ConeProjection.coneFiber
          (ConeProjection.project (ConeProjection.coneFiber (TwoEndedJState.eventHeight s.im))) =
        ConeProjection.coneFiber (TwoEndedJState.eventHeight s.im) ∧
      Readout.heightReadout (TwoEndedJState.eventHeight s.im) = s.im ∧
      GlobalHelix.circleReadout (GlobalHelix.globalHelixInvolution
          (ConeProjection.coneFiber (TwoEndedJState.eventHeight s.im))) =
        (starRingEnd ℂ) (GlobalHelix.circleReadout
          (ConeProjection.coneFiber (TwoEndedJState.eventHeight s.im))) :=
  ⟨Real.exp_pos _, ConeProjection.project_coneFiber _, ConeProjection.coneFiber_height_section _,
    TwoEndedJState.heightReadout_eventHeight _, GlobalHelix.circleReadout_globalHelixInvolution _⟩

/-! ## 7. The carrier-point chains (promoted from tmp/att1080, tmp/att1081) -/

/-- The carrier abscissa's value is used here only for `0 < Re s < 1`. -/
theorem carrierAbscissa_pos : 0 < ThreeDFocal.carrierAbscissa := by
  rw [ThreeDFocal.carrierAbscissa_eq_half]
  norm_num

theorem carrierAbscissa_lt_one : ThreeDFocal.carrierAbscissa < 1 := by
  rw [ThreeDFocal.carrierAbscissa_eq_half]
  norm_num

/-- **Every L-function fiber, at the carrier point of height `Z`** (att1081 promoted): the
normalized detector fed with the grown fiber converges to the limit detector, which drops rank
exactly at the house 3D focal event at height `Z`; the point is `carrierAbscissa + i log Z`.
Scope (cleanup, ledger 1237): the "3D focal event" here is the completed, observer-side predicate
`CompletedThreeDZeroAtHeight` (readout-defined through `Dcell`), not the rich physical `FocalEvent`. -/
theorem all_fibers_chain {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {Z : ℝ}
    (hZ : 0 < Z) (μ lam : ℂ) (hlam : lam ≠ μ) :
    Tendsto (fun Z' => harmonicPencil 1
        (lawFiber (fun n => χ (n : ZMod q)) Z' (ThreeDFocal.carrierPointAtHeight Z)) μ lam) atTop
        (𝓝 (harmonicPencil 1
          (DirichletCharacter.LFunction χ (ThreeDFocal.carrierPointAtHeight Z)) μ lam)) ∧
      (((harmonicPencil 1 (DirichletCharacter.LFunction χ (ThreeDFocal.carrierPointAtHeight Z))
            μ lam)ᴴ *
          harmonicPencil 1 (DirichletCharacter.LFunction χ (ThreeDFocal.carrierPointAtHeight Z))
            μ lam).det = 0 ↔ ThreeDFocal.CompletedThreeDZeroAtHeight χ Z) ∧
      ThreeDFocal.carrierPointAtHeight Z =
        (ThreeDFocal.carrierAbscissa : ℂ) + Complex.I * (Real.log Z : ℂ) := by
  have hre : 0 < (ThreeDFocal.carrierPointAtHeight Z).re := by
    rw [ThreeDFocal.carrierPointAtHeight_re]
    exact carrierAbscissa_pos
  refine ⟨normalizedDetector_tendsto (lawFiber_char_tendsto χ hχ hre) μ lam, ?_,
    ThreeDFocal.carrierPointAtHeight_eq Z⟩
  rw [harmonicGram_rank_drop_iff_channel_zero _ _ μ lam one_ne_zero hlam,
    ThreeDFocal.completedThreeDZeroAtHeight_iff_L_zero χ Z hZ]

/-- **η at the carrier point of height `Z`** (att1080 promoted): the normalized detector fed with the
carrier's grown fiber converges to the limit detector, which drops rank exactly when `ζ` vanishes at
the carrier point. -/
theorem sam_chain (Z : ℝ) (μ lam : ℂ) (hlam : lam ≠ μ) :
    Tendsto (fun Z' => harmonicPencil 1 (finiteFiber Z' (ThreeDFocal.carrierPointAtHeight Z)) μ lam)
        atTop (𝓝 (harmonicPencil 1 ((1 - (2 : ℂ) ^ ((1 : ℂ) - ThreeDFocal.carrierPointAtHeight Z)) *
          riemannZeta (ThreeDFocal.carrierPointAtHeight Z)) μ lam)) ∧
      (((harmonicPencil 1 ((1 - (2 : ℂ) ^ ((1 : ℂ) - ThreeDFocal.carrierPointAtHeight Z)) *
            riemannZeta (ThreeDFocal.carrierPointAtHeight Z)) μ lam)ᴴ *
          harmonicPencil 1 ((1 - (2 : ℂ) ^ ((1 : ℂ) - ThreeDFocal.carrierPointAtHeight Z)) *
            riemannZeta (ThreeDFocal.carrierPointAtHeight Z)) μ lam).det = 0 ↔
        riemannZeta (ThreeDFocal.carrierPointAtHeight Z) = 0) := by
  have hre0 : 0 < (ThreeDFocal.carrierPointAtHeight Z).re := by
    rw [ThreeDFocal.carrierPointAtHeight_re]
    exact carrierAbscissa_pos
  have hre1 : (ThreeDFocal.carrierPointAtHeight Z).re < 1 := by
    rw [ThreeDFocal.carrierPointAtHeight_re]
    exact carrierAbscissa_lt_one
  have hne : ThreeDFocal.carrierPointAtHeight Z ≠ 1 := by
    intro h
    rw [h] at hre1
    simp at hre1
  refine ⟨?_, (limit_chain_eta hre0 hre1 μ lam hlam).2.symm⟩
  have h := lawFiber_eta_tendsto hre0 hne
  refine normalizedDetector_tendsto (h.congr fun Z' => ?_) μ lam
  rw [lawFiber_eta]

end CriticalLinePhasor.FiberDetectorChain

#print axioms CriticalLinePhasor.FiberDetectorChain.windowed_tendsto
#print axioms CriticalLinePhasor.FiberDetectorChain.carrier_warp_fiber
#print axioms CriticalLinePhasor.FiberDetectorChain.finite_cancel_iff_rankDrop
#print axioms CriticalLinePhasor.FiberDetectorChain.focalCancellation_iff_detector
#print axioms CriticalLinePhasor.FiberDetectorChain.lawFiber_char_tendsto
#print axioms CriticalLinePhasor.FiberDetectorChain.lawFiber_eta_tendsto
#print axioms CriticalLinePhasor.FiberDetectorChain.detector_tendsto_fullFiberMatrix
#print axioms CriticalLinePhasor.FiberDetectorChain.limit_chain_char
#print axioms CriticalLinePhasor.FiberDetectorChain.limit_chain_eta
#print axioms CriticalLinePhasor.FiberDetectorChain.event_projection
#print axioms CriticalLinePhasor.FiberDetectorChain.all_fibers_chain
#print axioms CriticalLinePhasor.FiberDetectorChain.sam_chain
