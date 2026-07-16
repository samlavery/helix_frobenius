import RequestProject.SpectralFiberIsLFunction
import RequestProject.ClosedForm
import RequestProject.ZetaContourXiReceiverIdentification3D
import RequestProject.XiZeroLedgerResolvent3D

/-!
# Transfer of a genuine zeta zero to its native three-dimensional source

This file keeps the analytic and geometric parts of the transfer in separate fields and then
assembles them into one certificate.

* `PrincipalZeroAnalyticFiber3D` is available for every member of `ZD.NontrivialZeros`.  Its state
  is the literal eta-configured `Vec3` spectral fiber at the original complex point, and its
  rescaled spin-plane partial sums converge to zero.
* The same object carries the event-independent ambient helix state at ordinate `Im rho` and
  physical height `exp (Im rho)`, together with its nonzero eigenvector.
* `PrincipalZeroNativeCarrierEvent3D` registers that analytic focal closure on the typed carrier
  state at the same physical height.  Literal helix membership then proves zero radial drift;
  no analytic radial magnitude or scale limit is used in this registration.
* `PrincipalZeroNative3DSourceTransfer` adds the geometric projection: zero radial drift produces
  a conservative source mode, identifies its area-law coordinate with the original analytic
  point, and selects the already-defined completed focal/operator certificate.

The numerical half-unit does not occur in the analytic-fiber or native-carrier-event constructors.
It is generated only by the area-law theorem hidden behind `carrierAbscissa` when a carrier
readout or parameter-preserving projection is evaluated.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.Phasor3D
open CriticalLinePhasor.SpectralFiber
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.ResidueJump

/-- The literal three-dimensional analytic fiber and event-independent ambient carrier state
attached to a genuine nontrivial zeta zero. -/
structure PrincipalZeroAnalyticFiber3D (rho : ℂ) where
  analyticZero : rho ∈ ZD.NontrivialZeros
  state : ℕ → Vec3
  state_eq : state = spectralFiber etaW rho
  etaFactor : ℂ
  etaFactor_eq : etaFactor = 1 - (2 : ℂ) ^ (1 - rho)
  etaFactor_ne_zero : etaFactor ≠ 0
  readout_closes :
    Tendsto
      (fun N : ℕ => etaFactor⁻¹ * ∑ n ∈ Finset.range N, plane (state n))
      atTop (nhds 0)
  sourceHeight : ℝ
  sourceHeight_eq : sourceHeight = Real.exp rho.im
  sourceHeight_pos : 0 < sourceHeight
  ambientState : CarrierState3D 1 1
  ambientState_eq : ambientState = carrierState3D 1 1 rho.im
  ambient_physicalHeight : ambientState.physicalHeight = sourceHeight
  ambient_nonzero : Finsupp.single ambientState (1 : ℂ) ≠ 0
  ambient_eigenvector :
    carrierThreeDOperator 1 1 (Finsupp.single ambientState (1 : ℂ)) =
      (rho.im : ℂ) • Finsupp.single ambientState (1 : ℂ)

/-- Every genuine nontrivial zeta zero has a literal three-dimensional spectral fiber whose
readout closes to zero, and an independently defined ambient helix eigenstate at the same
logarithmic ordinate. -/
noncomputable def principalZeroAnalyticFiber3D {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) : PrincipalZeroAnalyticFiber3D rho := by
  have hrho_ne_one : rho ≠ 1 := by
    have hlt := hrho.2.1
    intro h
    rw [h] at hlt
    norm_num at hlt
  have hfactor : (1 : ℂ) - (2 : ℂ) ^ (1 - rho) ≠ 0 := by
    intro h
    have hpow : (2 : ℂ) ^ (1 - rho) = 1 := by
      linear_combination -h
    have hre := correction_factor_zero_re_eq_one rho hpow
    linarith [hrho.2.1]
  have hclose := etaSpectralFiber_readout_recovers_zeta hrho.1 hrho_ne_one hfactor
  have heigen := carrierThreeDOperator_eigenvector 1 1 (carrierState3D 1 1 rho.im)
  refine
    { analyticZero := hrho
      state := spectralFiber etaW rho
      state_eq := rfl
      etaFactor := 1 - (2 : ℂ) ^ (1 - rho)
      etaFactor_eq := rfl
      etaFactor_ne_zero := hfactor
      readout_closes := ?_
      sourceHeight := Real.exp rho.im
      sourceHeight_eq := rfl
      sourceHeight_pos := Real.exp_pos rho.im
      ambientState := carrierState3D 1 1 rho.im
      ambientState_eq := rfl
      ambient_physicalHeight := ?_
      ambient_nonzero := heigen.1
      ambient_eigenvector := heigen.2 }
  · simpa only [hrho.2.2, readout] using hclose
  · rw [CarrierState3D.physicalHeight_eq_exp one_ne_zero]
    rfl

/-- The physical focal-cancellation height and the analytic ordinate are exact inverse
coordinates: the stored height is `Z = exp (Im rho)`, hence its 1D ordinate is
`log Z = Im rho`. -/
@[simp] theorem PrincipalZeroAnalyticFiber3D.log_sourceHeight_eq_im {rho : ℂ}
    (fiber : PrincipalZeroAnalyticFiber3D rho) :
    Real.log fiber.sourceHeight = rho.im := by
  rw [fiber.sourceHeight_eq, Real.log_exp]

/-- Reading the analytic fiber's physical height on the carrier recovers precisely the carrier
point at the original analytic ordinate. -/
theorem PrincipalZeroAnalyticFiber3D.carrierPointAt_sourceHeight {rho : ℂ}
    (fiber : PrincipalZeroAnalyticFiber3D rho) :
    carrierPointAtHeight fiber.sourceHeight = carrierPoint rho.im := by
  rw [carrierPointAtHeight, fiber.log_sourceHeight_eq_im]

/-- The event-independent ambient carrier state uses the same logarithmic ordinate as the
physical focal-cancellation height. -/
theorem PrincipalZeroAnalyticFiber3D.ambient_ordinate_eq_log_sourceHeight {rho : ℂ}
    (fiber : PrincipalZeroAnalyticFiber3D rho) :
    fiber.ambientState.ordinate = Real.log fiber.sourceHeight := by
  rw [fiber.ambientState_eq, fiber.log_sourceHeight_eq_im]
  rfl

/-- Consequently the carrier readout of the physical focal height has the analytic zero's
imaginary coordinate. -/
@[simp] theorem PrincipalZeroAnalyticFiber3D.carrierPointAt_sourceHeight_im {rho : ℂ}
    (fiber : PrincipalZeroAnalyticFiber3D rho) :
    (carrierPointAtHeight fiber.sourceHeight).im = rho.im := by
  rw [carrierPointAtHeight_im, fiber.log_sourceHeight_eq_im]

/-! ## Geometry-first native carrier registration -/

/-- A genuine analytic focal cancellation registered on the independently defined native 3D
carrier.  The analytic fiber supplies closure; `carrierState` supplies literal membership in
`Geometry.gammaY`.  No radial magnitude, scale limit, carrier abscissa, or midpoint occurs in this
event type. -/
structure PrincipalZeroNativeCarrierEvent3D (rho : ℂ) where
  analyticFiber : PrincipalZeroAnalyticFiber3D rho
  carrierState : CarrierState3D 1 1
  carrierState_eq : carrierState = analyticFiber.ambientState
  focalCancellation :
    Tendsto
      (fun N : ℕ => analyticFiber.etaFactor⁻¹ *
        ∑ n ∈ Finset.range N, plane (analyticFiber.state n))
      atTop (nhds 0)

/-- Every genuine nontrivial zeta zero first produces a native carrier focal event at physical
height `exp (Im rho)`.  This registration uses only the analytic closure theorem and the already
typed ambient helix state; it does not compare radial magnitudes. -/
noncomputable def principalZero_focalCancellation_on_carrier {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) : PrincipalZeroNativeCarrierEvent3D rho := by
  let fiber := principalZeroAnalyticFiber3D hrho
  exact
    { analyticFiber := fiber
      carrierState := fiber.ambientState
      carrierState_eq := rfl
      focalCancellation := fiber.readout_closes }

/-- The registered focal state lies literally on the Archimedean helix, by the membership field
of `CarrierState3D`; this is not reconstructed from an asymptotic radius. -/
theorem PrincipalZeroNativeCarrierEvent3D.on_archimedeanHelix {rho : ℂ}
    (event : PrincipalZeroNativeCarrierEvent3D rho) :
    event.carrierState.point =
      Geometry.gammaY 1 1 event.carrierState.ordinate :=
  event.carrierState.point_eq_gammaY

/-- The carrier event and the analytic focal cancellation use the same physical height. -/
theorem PrincipalZeroNativeCarrierEvent3D.physicalHeight_eq_focalHeight {rho : ℂ}
    (event : PrincipalZeroNativeCarrierEvent3D rho) :
    event.carrierState.physicalHeight = event.analyticFiber.sourceHeight := by
  rw [event.carrierState_eq]
  exact event.analyticFiber.ambient_physicalHeight

/-- The event-independent ambient 3D carrier operator acts on the registered focal state with the
analytic ordinate as its real eigenvalue. -/
theorem PrincipalZeroNativeCarrierEvent3D.ambient_eigenvector {rho : ℂ}
    (event : PrincipalZeroNativeCarrierEvent3D rho) :
    carrierThreeDOperator 1 1 (Finsupp.single event.carrierState (1 : ℂ)) =
      (rho.im : ℂ) • Finsupp.single event.carrierState (1 : ℂ) := by
  rw [event.carrierState_eq]
  exact event.analyticFiber.ambient_eigenvector

/-- No radial drift is a direct theorem of the registered carrier point at the focal height.
Neither the analytic fiber magnitude nor the area-normalized magnitude limit is used. -/
theorem PrincipalZeroNativeCarrierEvent3D.noRadialDrift {rho : ℂ}
    (event : PrincipalZeroNativeCarrierEvent3D rho) (n : ℝ) (hn : 1 < n) :
    n ^ ((carrierPointAtHeight event.analyticFiber.sourceHeight).re - carrierAbscissa) = 1 :=
  carrierPointAtHeight_noRadialDrift event.analyticFiber.sourceHeight n hn

/-- The area law is now consumed only after carrier registration: the real coordinate read from
the marked carrier height is scale-balanced because it is the selected carrier abscissa. -/
theorem PrincipalZeroNativeCarrierEvent3D.carrierReadout_scaleBalanced {rho : ℂ}
    (event : PrincipalZeroNativeCarrierEvent3D rho) :
    CarrierScaleBalanced
      (carrierPointAtHeight event.analyticFiber.sourceHeight).re := by
  rw [carrierPointAtHeight_re]
  exact carrierAbscissa_scaleBalanced

/-- Same-height geometry-first assembly: analytic focal closure, literal helix membership,
physical-height agreement, ambient eigenvector, and no drift all hold before any
parameter-preserving carrier-to-chart identification. -/
theorem PrincipalZeroNativeCarrierEvent3D.focalCancellation_onCarrier_noRadialDrift
    {rho : ℂ} (event : PrincipalZeroNativeCarrierEvent3D rho)
    (n : ℝ) (hn : 1 < n) :
    Tendsto
        (fun N : ℕ => event.analyticFiber.etaFactor⁻¹ *
          ∑ k ∈ Finset.range N, plane (event.analyticFiber.state k))
        atTop (nhds 0) ∧
      event.carrierState.point =
        Geometry.gammaY 1 1 event.carrierState.ordinate ∧
      event.carrierState.physicalHeight = event.analyticFiber.sourceHeight ∧
      carrierThreeDOperator 1 1 (Finsupp.single event.carrierState (1 : ℂ)) =
        (rho.im : ℂ) • Finsupp.single event.carrierState (1 : ℂ) ∧
      n ^ ((carrierPointAtHeight event.analyticFiber.sourceHeight).re -
        carrierAbscissa) = 1 := by
  exact ⟨event.focalCancellation, event.on_archimedeanHelix,
    event.physicalHeight_eq_focalHeight, event.ambient_eigenvector,
    event.noRadialDrift n hn⟩

/-- At every positive site, the Euclidean magnitude of the literal eta-configured 3D zero fiber
is its radial power `n ^ (-Re rho)`.  This is extracted from the `Vec3` state itself: the eta
charge is `±1`, hence the mass coordinate vanishes and the spin-plane norm is exactly the radial
profile.  No carrier coordinate, focal certificate, or midpoint value enters the statement. -/
theorem PrincipalZeroAnalyticFiber3D.radialMagnitude {rho : ℂ}
    (fiber : PrincipalZeroAnalyticFiber3D rho) (n : ℕ) (hn : 0 < n) :
    mag3 (fiber.state n) = (n : ℝ) ^ (-rho.re) := by
  rw [fiber.state_eq, spectralFiber]
  have hcharge : etaW n = 1 ∨ etaW n = -1 := by
    unfold etaW
    rcases Nat.even_or_odd (n + 1) with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  have hmass := phasor3D_charged_massless etaW rho.re rho.im n hcharge
  have hnorm := phasor3D_charged_plane_norm etaW rho.re rho.im n hn hcharge
  unfold mag3
  change Real.sqrt (‖plane (phasor3D etaW rho.re rho.im n)‖ ^ 2 +
    massAxis (phasor3D etaW rho.re rho.im n) ^ 2) = _
  rw [hmass, hnorm, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- The canonical fiber attached to a carrier readout has the radial magnitude prescribed by
that readout.  This is the state-level calculation used below to distinguish "the fiber rides
the carrier" from the weaker assertion that the two objects merely have the same ordinate. -/
theorem etaSpectralFiber_radialMagnitude (s : ℂ) (n : ℕ) (hn : 0 < n) :
    mag3 (spectralFiber etaW s n) = (n : ℝ) ^ (-s.re) := by
  have hcharge : etaW n = 1 ∨ etaW n = -1 := by
    unfold etaW
    rcases Nat.even_or_odd (n + 1) with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  have hmass := phasor3D_charged_massless etaW s.re s.im n hcharge
  have hnorm := phasor3D_charged_plane_norm etaW s.re s.im n hn hcharge
  rw [spectralFiber]
  unfold mag3
  change Real.sqrt (‖plane (phasor3D etaW s.re s.im n)‖ ^ 2 +
    massAxis (phasor3D etaW s.re s.im n) ^ 2) = _
  rw [hmass, hnorm, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- **Fiber-to-carrier attachment.**  The literal analytic fiber rides its registered carrier
when it is the canonical spectral fiber evaluated at that carrier's own complex readout.  This
compares like objects (`ℕ → Vec3`) and contains no separately supplied real-coordinate equation. -/
def PrincipalZeroAnalyticFiber3D.RidesCarrier {rho : ℂ}
    (fiber : PrincipalZeroAnalyticFiber3D rho) : Prop :=
  fiber.state = spectralFiber etaW (carrierPointAtHeight fiber.sourceHeight)

/-- The state-level fiber-to-carrier attachment is exactly the parameter-preserving weld.  The
forward direction reads the radial exponent from one nontrivial carrier site; the ordinate was
already fixed by `log sourceHeight = Im rho`. -/
theorem PrincipalZeroAnalyticFiber3D.ridesCarrier_iff_carrierWeld
    {rho : ℂ} (fiber : PrincipalZeroAnalyticFiber3D rho) :
    fiber.RidesCarrier ↔ carrierPointAtHeight fiber.sourceHeight = rho := by
  constructor
  · intro hride
    have hstate : fiber.state 2 =
        spectralFiber etaW (carrierPointAtHeight fiber.sourceHeight) 2 :=
      congrFun hride 2
    have hmag := congrArg mag3 hstate
    rw [fiber.radialMagnitude 2 (by norm_num),
      etaSpectralFiber_radialMagnitude _ 2 (by norm_num), carrierPointAtHeight_re] at hmag
    have hexp : -rho.re = -carrierAbscissa :=
      (Real.strictMono_rpow_of_base_gt_one (b := (2 : ℝ)) (by norm_num)).injective hmag
    apply Complex.ext
    · simpa using (congrArg Neg.neg hexp).symm
    · exact fiber.carrierPointAt_sourceHeight_im
  · intro hweld
    unfold PrincipalZeroAnalyticFiber3D.RidesCarrier
    rw [fiber.state_eq, hweld]

/-- Completed reflection preserves the genuine nontrivial-zero set.  This is derived from the
entire xi functional equation, rather than supplied as a carrier certificate. -/
theorem one_sub_conj_mem_nontrivialZeros {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) :
    1 - (starRingEnd ℂ) rho ∈ ZD.NontrivialZeros := by
  apply (ZD.riemannXi_eq_zero_iff _).mp
  rw [riemannXi_one_sub_conj, (ZD.riemannXi_eq_zero_iff rho).mpr hrho, map_zero]

/-- A zero fiber and its completed-reflection fiber occupy the same positive physical height.
Completed reflection changes the radial exponent but preserves the analytic ordinate. -/
theorem reflected_principalZeroAnalyticFiber3D_sourceHeight_eq {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) :
    (principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).sourceHeight =
      (principalZeroAnalyticFiber3D hrho).sourceHeight := by
  rw [(principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).sourceHeight_eq,
    (principalZeroAnalyticFiber3D hrho).sourceHeight_eq]
  simp

/-- The event-independent ambient carrier state is literally the same for the two completed
reflections.  Thus the reflection pair cannot be represented by two different carrier heights;
all of its possible discrepancy is confined to the analytic fiber's radial scale. -/
theorem reflected_principalZeroAnalyticFiber3D_ambientState_eq {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) :
    (principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).ambientState =
      (principalZeroAnalyticFiber3D hrho).ambientState := by
  rw [(principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).ambientState_eq,
    (principalZeroAnalyticFiber3D hrho).ambientState_eq]
  congr 1
  simp

/-- The two literal eta-configured 3D fibers have the same normalized spin-plane direction at
every positive site.  Cross-multiplication by their positive Euclidean magnitudes avoids choosing
a normalization or inserting a midpoint: completed reflection changes only radial scale, not the
site's 3D spin direction. -/
theorem reflected_principalZeroAnalyticFiber3D_plane_cross_scaled {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) (n : ℕ) (hn : 0 < n) :
    ((mag3 ((principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).state n) : ℝ) : ℂ) *
        plane ((principalZeroAnalyticFiber3D hrho).state n) =
      ((mag3 ((principalZeroAnalyticFiber3D hrho).state n) : ℝ) : ℂ) *
        plane ((principalZeroAnalyticFiber3D
          (one_sub_conj_mem_nontrivialZeros hrho)).state n) := by
  rw [(principalZeroAnalyticFiber3D hrho).radialMagnitude n hn,
    (principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).radialMagnitude n hn]
  rw [(principalZeroAnalyticFiber3D hrho).state_eq,
    (principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).state_eq]
  simp [spectralFiber, LFunctionPhasor.phasorTerm, hn.ne',
    Complex.sub_re, Complex.sub_im]
  ring

/-- At any nontrivial site, equality of the two completed-reflection radial magnitudes is exactly
individual carrier scale balance.  This is the precise state-space fixed-point criterion: the
shared height and spin direction are already proved above, while equality of the reciprocal radial
scales selects the unique area-law exponent. -/
theorem reflected_radialMagnitude_eq_iff_carrierScaleBalanced {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) (n : ℕ) (hn : 1 < n) :
    mag3 ((principalZeroAnalyticFiber3D hrho).state n) =
        mag3 ((principalZeroAnalyticFiber3D
          (one_sub_conj_mem_nontrivialZeros hrho)).state n) ↔
      CarrierScaleBalanced rho.re := by
  rw [(principalZeroAnalyticFiber3D hrho).radialMagnitude n (by omega),
    (principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).radialMagnitude n (by omega)]
  constructor
  · intro h
    apply (carrierScaleBalanced_iff rho.re).2
    have hexp : -rho.re = -(1 - rho.re) :=
      (Real.strictMono_rpow_of_base_gt_one
        (b := (n : ℝ)) (by exact_mod_cast hn)).injective (by simpa using h)
    linarith
  · intro h
    have hre := (carrierScaleBalanced_iff rho.re).1 h
    congr 1
    simp [Complex.sub_re, hre]
    norm_num

/-- The literal 3D radial magnitudes of a zero fiber and its completed-reflection fiber have
determinant-one exponent: their product is exactly `n⁻¹`.  This is a state-space identity and
does not insert a midpoint into either individual fiber. -/
theorem paired_radialMagnitude_product {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) (n : ℕ) (hn : 0 < n) :
    mag3 ((principalZeroAnalyticFiber3D hrho).state n) *
        mag3 ((principalZeroAnalyticFiber3D
          (one_sub_conj_mem_nontrivialZeros hrho)).state n) =
      (n : ℝ) ^ (-1 : ℝ) := by
  rw [(principalZeroAnalyticFiber3D hrho).radialMagnitude n hn,
    (principalZeroAnalyticFiber3D
      (one_sub_conj_mem_nontrivialZeros hrho)).radialMagnitude n hn]
  rw [← Real.rpow_add (by positivity : 0 < (n : ℝ))]
  congr 1
  simp
  ring

/-- After multiplying each reflected analytic fiber by the arclength-derived carrier radius,
the product of the two normalized Euclidean magnitudes tends to one.  Thus the completed pair is
globally area-balanced before any claim that either individual strand is balanced. -/
theorem paired_areaNormalizedRadialMagnitude_tendsto_one {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) :
    Tendsto
      (fun n : ℕ =>
        (mag3 ((principalZeroAnalyticFiber3D hrho).state n) *
            Geometry.carrierRadius 1 3 n) *
          (mag3 ((principalZeroAnalyticFiber3D
            (one_sub_conj_mem_nontrivialZeros hrho)).state n) *
            Geometry.carrierRadius 1 3 n))
      atTop (nhds 1) := by
  have harea := Geometry.carrierRadius_sq_div_tendsto 1 3 (by norm_num)
  have hconstant : (3 : ℝ) * (Real.pi / 3) / Real.pi = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [hconstant] at harea
  apply harea.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  calc
    Geometry.carrierRadius 1 3 n ^ 2 / (n : ℝ) =
        (n : ℝ) ^ (-1 : ℝ) * Geometry.carrierRadius 1 3 n ^ 2 := by
          rw [Real.rpow_neg_one]
          field_simp
    _ =
        (mag3 ((principalZeroAnalyticFiber3D hrho).state n) *
          mag3 ((principalZeroAnalyticFiber3D
            (one_sub_conj_mem_nontrivialZeros hrho)).state n)) *
            Geometry.carrierRadius 1 3 n ^ 2 := by
          rw [paired_radialMagnitude_product hrho n hnpos]
    _ = _ := by ring

/-- Carrier scale balance is equivalently the positive finite limit of the *actual Euclidean
magnitude* of the literal 3D analytic fiber multiplied by the arclength-derived carrier radius.
Thus the remaining transport problem is stated entirely on the 3D state and the geometric area
law, rather than as a supplied real-coordinate equality. -/
theorem PrincipalZeroAnalyticFiber3D.carrierScaleBalanced_iff_radialMagnitude
    {rho : ℂ} (fiber : PrincipalZeroAnalyticFiber3D rho) :
    CarrierScaleBalanced rho.re ↔
      ∃ L : ℝ, 0 < L ∧
        Tendsto (fun n : ℕ => mag3 (fiber.state n) * Geometry.carrierRadius 1 3 n)
          atTop (nhds L) := by
  unfold CarrierScaleBalanced
  apply exists_congr
  intro L
  apply and_congr_right
  intro _hL
  apply tendsto_congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [fiber.radialMagnitude n (by omega)]

/-- The parameter-preserving carrier weld at the analytic fiber's own physical focal height is
exactly its area-law scale balance.  The imaginary coordinate is already forced by
`log sourceHeight = Im rho`; the real coordinate is supplied by the independently proved unique
scale-critical exponent. -/
theorem PrincipalZeroAnalyticFiber3D.carrierWeld_iff_scaleBalanced
    {rho : ℂ} (fiber : PrincipalZeroAnalyticFiber3D rho) :
    carrierPointAtHeight fiber.sourceHeight = rho ↔ CarrierScaleBalanced rho.re := by
  constructor
  · intro hweld
    apply (carrierScaleBalanced_iff rho.re).2
    have hre := congrArg Complex.re hweld
    rw [carrierPointAtHeight_re, carrierAbscissa_eq_half] at hre
    exact hre.symm
  · intro hbalanced
    apply Complex.ext
    · rw [carrierPointAtHeight_re, carrierAbscissa_eq_half]
      exact ((carrierScaleBalanced_iff rho.re).1 hbalanced).symm
    · exact fiber.carrierPointAt_sourceHeight_im

/-- The fiber-to-carrier attachment is therefore exactly the area-law scale-balance condition;
the numerical half-unit remains a theorem internal to the area law. -/
theorem PrincipalZeroAnalyticFiber3D.ridesCarrier_iff_scaleBalanced
    {rho : ℂ} (fiber : PrincipalZeroAnalyticFiber3D rho) :
    fiber.RidesCarrier ↔ CarrierScaleBalanced rho.re := by
  rw [fiber.ridesCarrier_iff_carrierWeld, fiber.carrierWeld_iff_scaleBalanced]

/-- Exact operator/state identification at one analytic zero: its no-drift projection residual
vanishes exactly when the literal eta-configured 3D fiber has a positive finite area-normalized
Euclidean magnitude limit. -/
theorem principalZeroProjectionResidual_eq_zero_iff_radialMagnitude
    (rho : CriticalLinePhasor.XiChannel.XiZeroIndex) :
    (CriticalLinePhasor.XiChannel.xiZeroLedgerOperator -
        CriticalLinePhasor.XiChannel.xiZeroLedgerNoDriftProjection)
        (Finsupp.single rho (1 : ℂ)) = 0 ↔
      ∃ L : ℝ, 0 < L ∧
        Tendsto
          (fun n : ℕ =>
            mag3 ((principalZeroAnalyticFiber3D rho.property).state n) *
              Geometry.carrierRadius 1 3 n)
          atTop (nhds L) :=
  (CriticalLinePhasor.XiChannel.xiZeroLedgerProjectionResidual_on_basis_eq_zero_iff_scaleBalanced
      rho).trans
    (principalZeroAnalyticFiber3D rho.property).carrierScaleBalanced_iff_radialMagnitude

/-- Operator form of the same weld: the analytic zero equals the carrier readout at its physical
focal height exactly when its individual zero-ledger mode is fixed by the canonical no-drift
projection.  Because this is basiswise, no cancellation involving another zero can establish the
weld. -/
theorem PrincipalZeroAnalyticFiber3D.carrierWeld_iff_projectionResidual_eq_zero
    {rho : ℂ} (fiber : PrincipalZeroAnalyticFiber3D rho) :
    carrierPointAtHeight fiber.sourceHeight = rho ↔
      (CriticalLinePhasor.XiChannel.xiZeroLedgerOperator -
          CriticalLinePhasor.XiChannel.xiZeroLedgerNoDriftProjection)
        (Finsupp.single
          (⟨rho, fiber.analyticZero⟩ : CriticalLinePhasor.XiChannel.XiZeroIndex) (1 : ℂ)) = 0 := by
  rw [fiber.carrierWeld_iff_scaleBalanced,
    CriticalLinePhasor.XiChannel.xiZeroLedgerProjectionResidual_on_basis_eq_zero_iff_scaleBalanced]

/-- The complete transfer object: the genuine analytic 3D fiber, its conservative native source,
and the completed focal/operator certificate all refer to the same complex zero. -/
structure PrincipalZeroNative3DSourceTransfer
    (chiOne : DirichletCharacter ℂ 1) (rho : ℂ) where
  analyticFiber : PrincipalZeroAnalyticFiber3D rho
  carrierEvent : PrincipalZeroNativeCarrierEvent3D rho
  carrierEvent_analyticFiber : carrierEvent.analyticFiber = analyticFiber
  source : HelixSource.SourceMode
  sourceCoordinate : rho = conservativeCarrierCoord source
  nativeCertificate : PrincipalContourNative3DCertificate chiOne rho

/-- The carrier weld is precisely what assembles the complete native certificate.  Both sides use
the same physical height `Z = exp (Im rho)`; the reverse implication obtains the real coordinate
from the area-law carrier readout and then invokes the existing certificate constructor without
replacing any of its component proofs. -/
theorem nonempty_principalContourNative3DCertificate_iff_carrierWeld
    (chiOne : DirichletCharacter ℂ 1) {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) :
    Nonempty (PrincipalContourNative3DCertificate chiOne rho) ↔
      carrierPointAtHeight (principalZeroAnalyticFiber3D hrho).sourceHeight = rho := by
  let fiber := principalZeroAnalyticFiber3D hrho
  constructor
  · rintro ⟨certificate⟩
    calc
      carrierPointAtHeight fiber.sourceHeight =
          carrierPointAtHeight certificate.event.1 := by
            congr 1
            rw [fiber.sourceHeight_eq, certificate.event_height]
      _ = rho := certificate.analyticPoint
  · intro hweld
    have hre := congrArg Complex.re hweld
    have hline : rho.re = 1 / 2 := by
      rw [carrierPointAtHeight_re, carrierAbscissa_eq_half] at hre
      exact hre.symm
    exact ⟨principalContourNative3DCertificate_of_nontrivialZero_on_line
      chiOne hrho hline⟩

/-- The literal analytic `Vec3` fiber in a native certificate is the very same fiber evaluated at
the certificate's marked physical helix height.  This is the parameter-preserving weld between
the L-function representation and the carrier event, not merely an equality of ordinates. -/
theorem PrincipalContourNative3DCertificate.analyticFiber_eq_carrierFiber
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (certificate : PrincipalContourNative3DCertificate chiOne rho) :
    spectralFiber etaW rho =
      spectralFiber etaW (carrierPointAtHeight certificate.event.1) := by
  rw [certificate.analyticPoint]

/-- A native 3D certificate has no radial drift because its analytic point is the readout of its
marked helix height.  The result is derived from carrier membership; no midpoint or no-drift
premise is supplied. -/
theorem PrincipalContourNative3DCertificate.noRadialDrift
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (certificate : PrincipalContourNative3DCertificate chiOne rho)
    (n : ℝ) (hn : 1 < n) :
    n ^ (rho.re - carrierAbscissa) = 1 := by
  rw [← certificate.analyticPoint]
  exact carrierPointAtHeight_noRadialDrift certificate.event.1 n hn

/-- Native 3D realization alone constructs the complete source transfer.  Conservation of the
source is recovered from the certificate's helix membership, so this constructor has no supplied
radial equation or real-coordinate equality. -/
noncomputable def principalZeroNative3DSourceTransfer_of_nativeCertificate
    (chiOne : DirichletCharacter ℂ 1) {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros)
    (certificate : PrincipalContourNative3DCertificate chiOne rho) :
    PrincipalZeroNative3DSourceTransfer chiOne rho := by
  let source := HelixSource.SourceMode.ofReal rho.im
  have hre : rho.re = carrierAbscissa := by
    have hnoDrift := certificate.noRadialDrift 2 (by norm_num)
    exact (noRadialDrift_iff_carrierAbscissa 2 rho.re (by norm_num)).1 hnoDrift
  have hsource : rho = conservativeCarrierCoord source := by
    apply Complex.ext
    · simpa [conservativeCarrierCoord, source] using hre
    · simp [conservativeCarrierCoord, source, HelixSource.SourceMode.ofReal]
  exact
    { analyticFiber := principalZeroAnalyticFiber3D hrho
      carrierEvent := principalZero_focalCancellation_on_carrier hrho
      carrierEvent_analyticFiber := rfl
      source := source
      sourceCoordinate := hsource
      nativeCertificate := certificate }

/-- The native event is marked at the literal analytic fiber's focal-cancellation height, not at
a separately reconstructed height.  Both stored coordinates are definitionally tied to
`exp (Im rho)`, and this theorem exposes their equality for downstream pencil rewrites. -/
theorem PrincipalZeroNative3DSourceTransfer.eventHeight_eq_focalCancellationHeight
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho) :
    transfer.nativeCertificate.event.1 = transfer.analyticFiber.sourceHeight := by
  rw [transfer.nativeCertificate.event_height, transfer.analyticFiber.sourceHeight_eq]

/-- The completed spatial harmonic pencil detects the rank drop at the exact height where the
literal 3D L-fiber focally cancels.  The proof rewrites by the preceding height identity; it does
not substitute a second carrier event or merely compare ordinates. -/
theorem PrincipalZeroNative3DSourceTransfer.harmonicRankDrop_at_focalCancellationHeight
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho)
    (mu lam : ℂ) (hlam : lam ≠ mu) :
    (completedHarmonicGram3DAtHeight chiOne transfer.analyticFiber.sourceHeight mu lam).det = 0 := by
  rw [← transfer.eventHeight_eq_focalCancellationHeight]
  exact transfer.nativeCertificate.harmonic_rankDrop mu lam hlam

/-- Same-height assembly for the literal fiber: its rescaled plane readout closes, the completed
3D harmonic pencil rank-drops at that stored focal-cancellation height, and the carrier readout at
that very height has no radial drift. -/
theorem PrincipalZeroNative3DSourceTransfer.focalCancellation_rankDrop_noRadialDrift_sameHeight
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho)
    (mu lam : ℂ) (hlam : lam ≠ mu) (n : ℝ) (hn : 1 < n) :
    Tendsto
        (fun N : ℕ => transfer.analyticFiber.etaFactor⁻¹ *
          ∑ k ∈ Finset.range N, plane (transfer.analyticFiber.state k))
        atTop (nhds 0) ∧
      (completedHarmonicGram3DAtHeight chiOne transfer.analyticFiber.sourceHeight mu lam).det = 0 ∧
      n ^ ((carrierPointAtHeight transfer.analyticFiber.sourceHeight).re - carrierAbscissa) = 1 := by
  exact ⟨transfer.analyticFiber.readout_closes,
    transfer.harmonicRankDrop_at_focalCancellationHeight mu lam hlam,
    carrierPointAtHeight_noRadialDrift transfer.analyticFiber.sourceHeight n hn⟩

/-- Zero radial drift transfers a genuine zeta zero into its conservative native source and its
complete physical-height 3D certificate.  The carrier coordinate is derived from the no-drift
equation; no midpoint equality is an input. -/
noncomputable def principalZeroNative3DSourceTransfer_of_noRadialDrift
    (chiOne : DirichletCharacter ℂ 1) {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) (n : ℝ) (hn : 1 < n)
    (hnoDrift : n ^ (rho.re - carrierAbscissa) = 1) :
    PrincipalZeroNative3DSourceTransfer chiOne rho := by
  have hre : rho.re = carrierAbscissa :=
    (noRadialDrift_iff_carrierAbscissa n rho.re hn).1 hnoDrift
  let source := HelixSource.SourceMode.ofReal rho.im
  have hsource : rho = conservativeCarrierCoord source := by
    apply Complex.ext
    · simpa [conservativeCarrierCoord, source] using hre
    · simp [conservativeCarrierCoord, source, HelixSource.SourceMode.ofReal]
  exact
    { analyticFiber := principalZeroAnalyticFiber3D hrho
      carrierEvent := principalZero_focalCancellation_on_carrier hrho
      carrierEvent_analyticFiber := rfl
      source := source
      sourceCoordinate := hsource
      nativeCertificate :=
        principalContourNative3DCertificate_of_conservativeSource chiOne hrho source hsource }

/-- A completed source transfer returns no radial drift at every base greater than one, directly
from conservation of the source mode. -/
theorem PrincipalZeroNative3DSourceTransfer.noRadialDrift
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho)
    (n : ℝ) (hn : 1 < n) :
    n ^ (rho.re - carrierAbscissa) = 1 := by
  exact transfer.nativeCertificate.noRadialDrift n hn

/-- A completed native source transfer makes the analytic fiber scale-balanced on the
area-law carrier.  The limiting exponent is not read from a supplied midpoint: the source
coordinate first identifies the zero with a conservative carrier mode, and the independently
proved area law then identifies that mode's real coordinate with the unique scale-balanced
abscissa. -/
theorem PrincipalZeroNative3DSourceTransfer.carrierScaleBalanced
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho) :
    CarrierScaleBalanced rho.re := by
  apply (carrierScaleBalanced_iff rho.re).2
  calc
    rho.re = (conservativeCarrierCoord transfer.source).re :=
      congrArg Complex.re transfer.sourceCoordinate
    _ = carrierAbscissa := conservativeCarrierCoord_re transfer.source
    _ = 1 / 2 := carrierAbscissa_eq_half

/-- A completed native source transfer proves the literal state-level attachment: the analytic
`Vec3` fiber is the canonical fiber evaluated at the readout of the carrier height on which it
rides. -/
theorem PrincipalZeroNative3DSourceTransfer.fiberRidesCarrier
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho) :
    transfer.analyticFiber.RidesCarrier :=
  (transfer.analyticFiber.ridesCarrier_iff_scaleBalanced).2
    transfer.carrierScaleBalanced

/-- The state-level attachment recovers the original analytic parameter.  Thus the same complex
parameter labels the L-function fiber and the carrier readout; equality is derived from the ride,
not inserted in the carrier-state constructor. -/
theorem PrincipalZeroNative3DSourceTransfer.carrierReadout_eq_analyticParameter
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho) :
    carrierPointAtHeight transfer.analyticFiber.sourceHeight = rho :=
  (transfer.analyticFiber.ridesCarrier_iff_carrierWeld).1 transfer.fiberRidesCarrier

/-- **Fiber rides carrier; carrier rides helix.**  This is the composed, typed 3D weld.  The first
equality attaches the literal analytic `Vec3` fiber to the carrier readout.  The second places the
carrier state on `Geometry.gammaY`.  The third proves that both maps use the same physical focal
height. -/
theorem PrincipalZeroNative3DSourceTransfer.fiberRidesCarrier_carrierRidesHelix
    {chiOne : DirichletCharacter ℂ 1} {rho : ℂ}
    (transfer : PrincipalZeroNative3DSourceTransfer chiOne rho) :
    transfer.analyticFiber.state =
        spectralFiber etaW (carrierPointAtHeight transfer.analyticFiber.sourceHeight) ∧
      transfer.carrierEvent.carrierState.point =
        Geometry.gammaY 1 1 transfer.carrierEvent.carrierState.ordinate ∧
      transfer.carrierEvent.carrierState.physicalHeight =
        transfer.analyticFiber.sourceHeight := by
  refine ⟨transfer.fiberRidesCarrier, transfer.carrierEvent.on_archimedeanHelix, ?_⟩
  rw [transfer.carrierEvent.physicalHeight_eq_focalHeight,
    transfer.carrierEvent_analyticFiber]

/-- For a fixed genuine zero, the native source transfer is exactly its geometric no-drift
projection. -/
theorem nonempty_principalZeroNative3DSourceTransfer_iff_noRadialDrift
    (chiOne : DirichletCharacter ℂ 1) {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) (n : ℝ) (hn : 1 < n) :
    Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho) ↔
      n ^ (rho.re - carrierAbscissa) = 1 := by
  constructor
  · rintro ⟨transfer⟩
    exact transfer.noRadialDrift n hn
  · intro hnoDrift
    exact ⟨principalZeroNative3DSourceTransfer_of_noRadialDrift
      chiOne hrho n hn hnoDrift⟩

/-- For a genuine analytic zero, existence of its completed native 3D source is exactly
scale balance of its literal analytic fiber against the arclength-derived carrier radius. -/
theorem nonempty_principalZeroNative3DSourceTransfer_iff_carrierScaleBalanced
    (chiOne : DirichletCharacter ℂ 1) {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) :
    Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho) ↔
      CarrierScaleBalanced rho.re := by
  rw [nonempty_principalZeroNative3DSourceTransfer_iff_noRadialDrift
      chiOne hrho 2 (by norm_num),
    noRadialDrift_iff_carrierAbscissa 2 rho.re (by norm_num),
    carrierScaleBalanced_iff,
    carrierAbscissa_eq_half]

/-- Per-zero state-space assembly theorem: a completed native 3D source transfer exists exactly
when the literal analytic `Vec3` fiber rides the event-independent carrier at its stored physical
focal height.  This removes the source and certificate structures from the interface while
retaining equality of complete fiber states rather than equality of bare ordinates. -/
theorem nonempty_principalZeroNative3DSourceTransfer_iff_fiberRidesCarrier
    (chiOne : DirichletCharacter ℂ 1) {rho : ℂ}
    (hrho : rho ∈ ZD.NontrivialZeros) :
    Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho) ↔
      (principalZeroAnalyticFiber3D hrho).RidesCarrier :=
  (nonempty_principalZeroNative3DSourceTransfer_iff_carrierScaleBalanced
      chiOne hrho).trans
    (principalZeroAnalyticFiber3D hrho).ridesCarrier_iff_scaleBalanced.symm

/-- At one good contour height, coordinate agreement is exactly scale balance of every literal
analytic 3D zero fiber enclosed by that contour.  This is the finite-window form of the global
source-transfer criterion. -/
theorem classicalSContour_eq_Smult_iff_everyAnalyticZeroFiberScaleBalanced
    (chiOne : DirichletCharacter ℂ 1) {T : ℝ} (hT : GoodHeight T) :
    classicalSContour hT = Smult T ↔
      ∀ rho ∈ stripZeroFinset T, CarrierScaleBalanced rho.re := by
  rw [classicalSContour_eq_Smult_iff_everyKernelNoRadialDrift
      chiOne hT (by norm_num : (1 : ℝ) < 2)]
  constructor
  · intro hall rho hrho
    apply (carrierScaleBalanced_iff rho.re).2
    calc
      rho.re = carrierAbscissa :=
        (noRadialDrift_iff_carrierAbscissa 2 rho.re (by norm_num)).1 (hall rho hrho)
      _ = 1 / 2 := carrierAbscissa_eq_half
  · intro hall rho hrho
    apply (noRadialDrift_iff_carrierAbscissa 2 rho.re (by norm_num)).2
    calc
      rho.re = 1 / 2 := (carrierScaleBalanced_iff rho.re).1 (hall rho hrho)
      _ = carrierAbscissa := carrierAbscissa_eq_half.symm

/-- The independent contour coordinate and native carrier coordinate agree throughout the
zero-free base interval.  Here the full strip census vanishes, so the exact nonnegative defect
ledger vanishes as well; no source-coverage premise is used. -/
theorem classicalSContour_eq_Smult_of_lt_two
    {T : ℝ} (hT : GoodHeight T) (hT2 : T < 2) :
    classicalSContour hT = Smult T := by
  apply (classicalSContour_eq_Smult_iff_offLine_eq_zero hT).2
  have hzero : stripZeroCountMult T = 0 :=
    stripZeroCountMult_eq_zero_of_lt_two hT2
  have hsplit := stripZeroCountMult_eq_line_add_offLine T
  omega

/-- Global contour/carrier identification is equivalent to transferring every upper analytic
zero, with its literal 3D eta fiber, into a conservative native source and complete 3D event. -/
theorem globalCoordinateIdentification_iff_upperNative3DSourceTransfer
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ rho ∈ ZD.NontrivialZeros, 0 < rho.im →
        Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho) := by
  rw [globalCoordinateIdentification_iff_upperNoRadialDrift chiOne 2 (by norm_num)]
  constructor
  · intro hall rho hrho hrhoIm
    exact ⟨principalZeroNative3DSourceTransfer_of_noRadialDrift
      chiOne hrho 2 (by norm_num) (hall rho hrho hrhoIm)⟩
  · intro hall rho hrho hrhoIm
    obtain ⟨transfer⟩ := hall rho hrho hrhoIm
    exact transfer.noRadialDrift 2 (by norm_num)

/-- The conjugation-complete form: global coordinate identification is equivalent to native
source transfer for every nontrivial zero, in both half-planes. -/
theorem globalCoordinateIdentification_iff_allNative3DSourceTransfer
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ rho ∈ ZD.NontrivialZeros,
        Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho) := by
  rw [globalCoordinateIdentification_iff_allNoRadialDrift chiOne 2 (by norm_num)]
  constructor
  · intro hall rho hrho
    exact ⟨principalZeroNative3DSourceTransfer_of_noRadialDrift
      chiOne hrho 2 (by norm_num) (hall rho hrho)⟩
  · intro hall rho hrho
    obtain ⟨transfer⟩ := hall rho hrho
    exact transfer.noRadialDrift 2 (by norm_num)

/-- Family-level source/state assembly with no contour coordinate in the statement: complete
native 3D source transfer for every analytic zero is exactly complete fiber-to-carrier attachment
for every canonical eta-configured zero fiber. -/
theorem allNative3DSourceTransfer_iff_allCanonicalZeroFibersRideCarrier
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ rho ∈ ZD.NontrivialZeros,
        Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho)) ↔
      ∀ (rho : ℂ) (hrho : rho ∈ ZD.NontrivialZeros),
        (principalZeroAnalyticFiber3D hrho).RidesCarrier := by
  constructor
  · intro hall rho hrho
    exact
      (nonempty_principalZeroNative3DSourceTransfer_iff_fiberRidesCarrier
        chiOne hrho).1 (hall rho hrho)
  · intro hall rho hrho
    exact
      (nonempty_principalZeroNative3DSourceTransfer_iff_fiberRidesCarrier
        chiOne hrho).2 (hall rho hrho)

/-- Global contour/carrier identification is exactly scale balance of the literal 3D analytic
fiber attached to every nontrivial zero.  This is the scale-limit form of the all-source transfer
criterion and contains no carrier-point equality in its statement. -/
theorem globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ rho ∈ ZD.NontrivialZeros, CarrierScaleBalanced rho.re := by
  rw [globalCoordinateIdentification_iff_allNative3DSourceTransfer chiOne]
  constructor
  · intro hall rho hrho
    obtain ⟨transfer⟩ := hall rho hrho
    exact transfer.carrierScaleBalanced
  · intro hall rho hrho
    exact
      (nonempty_principalZeroNative3DSourceTransfer_iff_carrierScaleBalanced
        chiOne hrho).2 (hall rho hrho)

/-- Fully typed two-map form of the global identification: every literal analytic zero fiber
rides the carrier at its own focal height, and every such carrier state already rides the
Archimedean helix by `CarrierState3D.point_eq_gammaY`.  Unlike an equality of bare ordinates, the
right side is equality of the complete `ℕ → Vec3` fiber states. -/
theorem globalCoordinateIdentification_iff_allCanonicalZeroFibersRideCarrier
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ (rho : ℂ) (hrho : rho ∈ ZD.NontrivialZeros),
        (principalZeroAnalyticFiber3D hrho).RidesCarrier := by
  rw [globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced chiOne]
  constructor
  · intro hall rho hrho
    exact ((principalZeroAnalyticFiber3D hrho).ridesCarrier_iff_scaleBalanced).2
      (hall rho hrho)
  · intro hall rho hrho
    exact ((principalZeroAnalyticFiber3D hrho).ridesCarrier_iff_scaleBalanced).1
      (hall rho hrho)

/-- A complete family of native 3D source transfers produces the state-level fiber-to-carrier
attachment for every canonical analytic zero.  This is a direct structure projection: no global
trace equality and no cancellation between modes is used. -/
theorem allCanonicalZeroFibersRideCarrier_of_allNative3DSourceTransfer
    (chiOne : DirichletCharacter ℂ 1)
    (hall : ∀ rho ∈ ZD.NontrivialZeros,
      Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho)) :
    ∀ (rho : ℂ) (hrho : rho ∈ ZD.NontrivialZeros),
      (principalZeroAnalyticFiber3D hrho).RidesCarrier := by
  intro rho hrho
  obtain ⟨transfer⟩ := hall rho hrho
  exact ((principalZeroAnalyticFiber3D hrho).ridesCarrier_iff_scaleBalanced).2
    transfer.carrierScaleBalanced

/-- Fully state-space form of global coordinate identification: the independently continued
coordinate agrees with the native coordinate exactly when every canonical eta-configured zero
fiber has a positive finite area-normalized Euclidean magnitude limit.  Neither side supplies a
carrier point or a real-coordinate value; the half-unit is recovered only through the area law
inside the preceding equivalences. -/
theorem globalCoordinateIdentification_iff_allCanonicalZeroFiberRadialMagnitudeBalanced
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ (rho : ℂ) (hrho : rho ∈ ZD.NontrivialZeros),
        ∃ L : ℝ, 0 < L ∧
          Tendsto
            (fun n : ℕ =>
              mag3 ((principalZeroAnalyticFiber3D hrho).state n) *
                Geometry.carrierRadius 1 3 n)
            atTop (nhds L) := by
  rw [globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced chiOne]
  constructor
  · intro hall rho hrho
    exact
      ((principalZeroAnalyticFiber3D hrho).carrierScaleBalanced_iff_radialMagnitude).1
        (hall rho hrho)
  · intro hall rho hrho
    exact
      ((principalZeroAnalyticFiber3D hrho).carrierScaleBalanced_iff_radialMagnitude).2
        (hall rho hrho)

/-- The independently continued contour coordinate agrees globally with the native carrier
coordinate exactly when the zero-ledger operator identified from the Hadamard resolvent trace is
symmetric.  This is the operator/state-space unification: the analytic partial fraction fixes the
operator's diagonal eigenparameters, while the 3D area law converts their spectral reality into
scale balance of every literal eta fiber.  No carrier-point equality is a premise. -/
theorem globalCoordinateIdentification_iff_xiZeroLedgerOperator_symmetric
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      (CriticalLinePhasor.XiChannel.xiZeroLedgerOperator).IsSymmetric := by
  rw [globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced chiOne]
  constructor
  · intro hall
    apply
      (CriticalLinePhasor.XiChannel.xiZeroLedgerOperator_isSymmetric_iff).2
    intro rho
    have hbalance := hall rho.val rho.property
    have hre := (carrierScaleBalanced_iff rho.val.re).1 hbalance
    rw [HelixLimit.poleParam_im, hre]
    ring
  · intro hsym rho hrho
    exact
      CriticalLinePhasor.XiChannel.xiZeroLedgerOperator_symmetric_imp_scaleBalanced
        hsym ⟨rho, hrho⟩

/-- Symmetry of the analytically identified zero-ledger operator propagates the zero-free base
identity across every event and yields the global contour/carrier coordinate identity. -/
theorem globalCoordinateIdentification_of_xiZeroLedgerOperator_symmetric
    (chiOne : DirichletCharacter ℂ 1)
    (hsym : (CriticalLinePhasor.XiChannel.xiZeroLedgerOperator).IsSymmetric) :
    ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T :=
  (globalCoordinateIdentification_iff_xiZeroLedgerOperator_symmetric chiOne).2 hsym

/-- Global coordinate identification is exactly extinction of the radial component in the
height/radial decomposition of the independently identified zero-ledger operator. -/
theorem globalCoordinateIdentification_iff_xiRadialDriftOperator_eq_zero
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      CriticalLinePhasor.XiChannel.xiRadialDriftOperator = 0 := by
  rw [globalCoordinateIdentification_iff_xiZeroLedgerOperator_symmetric chiOne,
    CriticalLinePhasor.XiChannel.xiZeroLedgerOperator_isSymmetric_iff_radialDrift_eq_zero]

/-- Equivalent realization statement: global coordinate identification holds precisely when
the analytic zero-resolvent operator is the pullback of the real ambient carrier-height
operator.  Because the comparison is operator equality on individual basis modes, distinct
events cannot cancel a nonzero radial discrepancy. -/
theorem globalCoordinateIdentification_iff_zeroLedger_eq_carrierHeight
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      CriticalLinePhasor.XiChannel.xiZeroLedgerOperator =
        CriticalLinePhasor.XiChannel.xiCarrierHeightOperator := by
  rw [globalCoordinateIdentification_iff_xiRadialDriftOperator_eq_zero chiOne,
    ← CriticalLinePhasor.XiChannel.xiZeroLedgerOperator_eq_carrierHeight_iff_radialDrift_eq_zero]

/-- Operator/state weld with no contour coordinate in its statement: every canonical analytic
zero fiber rides its carrier exactly when the analytic zero-ledger operator is the real ambient
carrier-height operator. -/
theorem allCanonicalZeroFibersRideCarrier_iff_zeroLedger_eq_carrierHeight
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (rho : ℂ) (hrho : rho ∈ ZD.NontrivialZeros),
        (principalZeroAnalyticFiber3D hrho).RidesCarrier) ↔
      CriticalLinePhasor.XiChannel.xiZeroLedgerOperator =
        CriticalLinePhasor.XiChannel.xiCarrierHeightOperator :=
  (globalCoordinateIdentification_iff_allCanonicalZeroFibersRideCarrier chiOne).symm.trans
    (globalCoordinateIdentification_iff_zeroLedger_eq_carrierHeight chiOne)

/-- Complete source/operator weld: native 3D realization of every analytic zero is exactly
equality of the independently identified zero-ledger operator and the event-independent real
carrier-height operator.  The intermediate state condition is equality of each complete fiber. -/
theorem allNative3DSourceTransfer_iff_zeroLedger_eq_carrierHeight
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ rho ∈ ZD.NontrivialZeros,
        Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho)) ↔
      CriticalLinePhasor.XiChannel.xiZeroLedgerOperator =
        CriticalLinePhasor.XiChannel.xiCarrierHeightOperator :=
  (allNative3DSourceTransfer_iff_allCanonicalZeroFibersRideCarrier chiOne).trans
    (allCanonicalZeroFibersRideCarrier_iff_zeroLedger_eq_carrierHeight chiOne)

/-- Complete native 3D realization of every analytic zero identifies the independently obtained
zero-resolvent operator with the real ambient carrier-height operator.  The proof is basiswise:
each transfer supplies scale balance for its own zero mode, so no trace sum or cancellation
between distinct events is used. -/
theorem xiZeroLedgerOperator_eq_carrierHeight_of_allNative3DSourceTransfer
    (chiOne : DirichletCharacter ℂ 1)
    (hall : ∀ rho ∈ ZD.NontrivialZeros,
      Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho)) :
    CriticalLinePhasor.XiChannel.xiZeroLedgerOperator =
      CriticalLinePhasor.XiChannel.xiCarrierHeightOperator := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro rho
  obtain ⟨transfer⟩ := hall rho.val rho.property
  have hre : rho.val.re = 1 / 2 :=
    (carrierScaleBalanced_iff rho.val.re).1 transfer.carrierScaleBalanced
  simp [CriticalLinePhasor.XiChannel.xiZeroLedgerOperator,
    CriticalLinePhasor.XiChannel.xiCarrierHeightOperator,
    CriticalLinePhasor.ThreeDFocal.complexDiagOp_apply,
    UnconditionalFrobenius.diagOp_apply, HelixLimit.poleParam, hre]

/-- The basiswise native-realization operator equality propagates the zero-free base identity
across every analytic event and closes the global contour/carrier coordinate identification. -/
theorem globalCoordinateIdentification_of_allNative3DSourceTransfer
    (chiOne : DirichletCharacter ℂ 1)
    (hall : ∀ rho ∈ ZD.NontrivialZeros,
      Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho)) :
    ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T := by
  apply (globalCoordinateIdentification_iff_zeroLedger_eq_carrierHeight chiOne).2
  exact xiZeroLedgerOperator_eq_carrierHeight_of_allNative3DSourceTransfer chiOne hall

/-- Projection form of the endpoint: global coordinate identification holds exactly when the
analytic zero-ledger operator is fixed by its canonical Hermitian/no-drift projection. -/
theorem globalCoordinateIdentification_iff_zeroLedger_fixedByNoDriftProjection
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      CriticalLinePhasor.XiChannel.xiZeroLedgerOperator =
        CriticalLinePhasor.XiChannel.xiZeroLedgerNoDriftProjection := by
  rw [globalCoordinateIdentification_iff_zeroLedger_eq_carrierHeight chiOne,
    CriticalLinePhasor.XiChannel.xiZeroLedgerOperator_eq_noDriftProjection_iff_carrierHeight]

/-- Residual form of the endpoint: the two global coordinates agree exactly when the analytic
zero-ledger has zero component complementary to the canonical no-drift projection. -/
theorem globalCoordinateIdentification_iff_zeroLedgerProjectionResidual_eq_zero
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      CriticalLinePhasor.XiChannel.xiZeroLedgerOperator -
          CriticalLinePhasor.XiChannel.xiZeroLedgerNoDriftProjection = 0 := by
  rw [globalCoordinateIdentification_iff_zeroLedger_fixedByNoDriftProjection chiOne,
    sub_eq_zero]

/-- Basiswise residual form: global identification is equivalent to zero no-drift residual on
every canonical analytic zero mode separately.  No trace sum can discharge this criterion. -/
theorem globalCoordinateIdentification_iff_eachZeroBasisProjectionResidual_eq_zero
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ ρ : CriticalLinePhasor.XiChannel.XiZeroIndex,
        (CriticalLinePhasor.XiChannel.xiZeroLedgerOperator -
            CriticalLinePhasor.XiChannel.xiZeroLedgerNoDriftProjection)
          (Finsupp.single ρ (1 : ℂ)) = 0 := by
  rw [globalCoordinateIdentification_iff_zeroLedgerProjectionResidual_eq_zero chiOne,
    CriticalLinePhasor.XiChannel.xiZeroLedgerResidual_eq_zero_iff_each_basis]

/-- Receiver form with no trace-level cancellation: at any fixed spectral sample `z`, global
contour/carrier identification is equivalent to equality of the analytic pole receiver and the
event-free 3D carrier basis receiver for every zero mode separately.  A single sample suffices
because scalar inversion is injective. -/
theorem globalCoordinateIdentification_iff_eachZeroPoleResolvent_eq_carrierBasisReadout
    (chiOne : DirichletCharacter ℂ 1) (z : ℂ) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ rho : CriticalLinePhasor.XiChannel.XiZeroIndex,
        Complex.I * (z - HelixLimit.poleParam rho.val)⁻¹ =
          Complex.I * CriticalLinePhasor.ThreeDFocal.carrierBasisResolventReadout
            (CriticalLinePhasor.ThreeDFocal.carrierState3D 1 1 rho.val.im) z := by
  rw [globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced chiOne]
  constructor
  · intro hall rho
    exact
      (CriticalLinePhasor.XiChannel.zeroPoleResolvent_eq_carrierBasisReadout_iff_scaleBalanced
        rho.val z).2
        (hall rho.val rho.property)
  · intro hall rho hrho
    exact
      (CriticalLinePhasor.XiChannel.zeroPoleResolvent_eq_carrierBasisReadout_iff_scaleBalanced
        rho z).1
        (hall ⟨rho, hrho⟩)

/-- Basis-resolved trace bridge.  The global contour coordinate agrees with the carrier
coordinate exactly when every multiplicity-weighted analytic zero-resolvent kernel agrees with
the corresponding kernel of the independently defined real carrier-height operator.  Keeping
`rho` free makes the statement immune to cancellation in the subsequent `tsum`. -/
theorem globalCoordinateIdentification_iff_basisResolvedCarrierResolventBridge
    (chiOne : DirichletCharacter ℂ 1) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ↔
      ∀ (z : ℂ) (rho : CriticalLinePhasor.XiChannel.XiZeroIndex),
        CriticalLinePhasor.XiChannel.xiZeroResolventKernel z rho =
          CriticalLinePhasor.XiChannel.xiCarrierHeightResolventKernel z rho := by
  rw [globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced chiOne]
  constructor
  · intro hall z rho
    exact
      (CriticalLinePhasor.XiChannel.xiZeroResolventKernel_eq_carrierHeightKernel_iff_scaleBalanced
        z rho).2
        (hall rho.val rho.property)
  · intro hbridge rho hrho
    exact
      (CriticalLinePhasor.XiChannel.xiZeroResolventKernel_eq_carrierHeightKernel_iff_scaleBalanced
        0 ⟨rho, hrho⟩).1
        (hbridge 0 ⟨rho, hrho⟩)

/-- Summed trace consequence of the basis-resolved global bridge.  The conclusion identifies the
independently continued completed channel with the event-independent real carrier-height
resolvent trace, with the Hadamard constant and counterterms unchanged. -/
theorem carrierHeightResolventTrace_of_globalCoordinateIdentification
    (chiOne : DirichletCharacter ℂ 1)
    (hglobal : ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) :
    ∃ C : ℂ, ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
      CriticalLinePhasor.XiChannel.xiChannel z =
        C + CriticalLinePhasor.XiChannel.xiCarrierHeightResolventTrace z := by
  have hall :=
    (globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced chiOne).1 hglobal
  apply CriticalLinePhasor.XiChannel.xiChannel_eq_constant_add_carrierHeightResolventTrace_of_all_scaleBalanced
  intro rho
  exact hall rho.val rho.property

/-- Complete assembly under the stated primary-3D/shadow-1D reading.  One native source transfer
for every analytic shadow simultaneously supplies the global contour coordinate identity, the
basis-resolved resolvent weld (before any summation), and the regularized carrier-height trace.
Thus the projection-dominance conditional is consumed once and no midpoint equality is added as
a separate premise. -/
theorem globalCoordinateIdentification_basisResolvedBridge_and_carrierTrace_of_allNative3DSourceTransfer
    (chiOne : DirichletCharacter ℂ 1)
    (hall : ∀ rho ∈ ZD.NontrivialZeros,
      Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho)) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ∧
      (∀ (z : ℂ) (rho : CriticalLinePhasor.XiChannel.XiZeroIndex),
        CriticalLinePhasor.XiChannel.xiZeroResolventKernel z rho =
          CriticalLinePhasor.XiChannel.xiCarrierHeightResolventKernel z rho) ∧
      ∃ C : ℂ, ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
        CriticalLinePhasor.XiChannel.xiChannel z =
          C + CriticalLinePhasor.XiChannel.xiCarrierHeightResolventTrace z := by
  have hglobal :=
    globalCoordinateIdentification_of_allNative3DSourceTransfer chiOne hall
  refine ⟨hglobal, ?_, ?_⟩
  · exact
      (globalCoordinateIdentification_iff_basisResolvedCarrierResolventBridge chiOne).1 hglobal
  · exact carrierHeightResolventTrace_of_globalCoordinateIdentification chiOne hglobal

/-- Basis-resolvent form of the same operator/state weld.  Equality is required separately on
every canonical zero basis mode, so a discrepancy on one fiber cannot be canceled by another. -/
theorem allCanonicalZeroFibersRideCarrier_iff_eachZeroPoleResolvent_eq_carrierBasisReadout
    (chiOne : DirichletCharacter ℂ 1) (z : ℂ) :
    (∀ (rho : ℂ) (hrho : rho ∈ ZD.NontrivialZeros),
        (principalZeroAnalyticFiber3D hrho).RidesCarrier) ↔
      ∀ rho : CriticalLinePhasor.XiChannel.XiZeroIndex,
        Complex.I * (z - HelixLimit.poleParam rho.val)⁻¹ =
          Complex.I * CriticalLinePhasor.ThreeDFocal.carrierBasisResolventReadout
            (CriticalLinePhasor.ThreeDFocal.carrierState3D 1 1 rho.val.im) z :=
  (globalCoordinateIdentification_iff_allCanonicalZeroFibersRideCarrier chiOne).symm.trans
    (globalCoordinateIdentification_iff_eachZeroPoleResolvent_eq_carrierBasisReadout chiOne z)

/-- A self-adjoint xi receiver transfers every upper analytic zero all the way from its literal
3D spectral fiber to its conservative native source and completed focal/operator event. -/
theorem upperNative3DSourceTransfer_of_selfAdjointXiReceiver
    (chiOne : DirichletCharacter ℂ 1)
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (hReg : ∀ z, z ∉ spectrum ℂ a →
      ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (nhdsWithin z {z}ᶜ) (nhds L)) :
    ∀ rho ∈ ZD.NontrivialZeros, 0 < rho.im →
      Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho) := by
  have hglobal :=
    (globalCoordinateIdentification_and_upperNative3D_of_selfAdjointXiReceiver
      chiOne ha hReg).1
  exact (globalCoordinateIdentification_iff_upperNative3DSourceTransfer chiOne).1 hglobal

/-- The same receiver transfers the complete two-sided nontrivial zero set into native 3D
sources, using the proved conjugation transport and real-axis exclusion. -/
theorem allNative3DSourceTransfer_of_selfAdjointXiReceiver
    (chiOne : DirichletCharacter ℂ 1)
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (hReg : ∀ z, z ∉ spectrum ℂ a →
      ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (nhdsWithin z {z}ᶜ) (nhds L)) :
    ∀ rho ∈ ZD.NontrivialZeros,
      Nonempty (PrincipalZeroNative3DSourceTransfer chiOne rho) := by
  have hglobal :=
    (globalCoordinateIdentification_and_upperNative3D_of_selfAdjointXiReceiver
      chiOne ha hReg).1
  exact (globalCoordinateIdentification_iff_allNative3DSourceTransfer chiOne).1 hglobal

/-- The self-adjoint xi receiver route lands directly in the literal state-level assertion that
every canonical analytic zero fiber rides its carrier, after which carrier-to-helix placement is
already the geometric field `CarrierState3D.point_eq_gammaY`. -/
theorem allCanonicalZeroFibersRideCarrier_of_selfAdjointXiReceiver
    (chiOne : DirichletCharacter ℂ 1)
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (hReg : ∀ z, z ∉ spectrum ℂ a →
      ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (nhdsWithin z {z}ᶜ) (nhds L)) :
    ∀ (rho : ℂ) (hrho : rho ∈ ZD.NontrivialZeros),
      (principalZeroAnalyticFiber3D hrho).RidesCarrier := by
  apply allCanonicalZeroFibersRideCarrier_of_allNative3DSourceTransfer chiOne
  exact allNative3DSourceTransfer_of_selfAdjointXiReceiver chiOne ha hReg

/-- The self-adjoint xi receiver therefore identifies the analytic zero-ledger operator with the
event-independent real carrier-height operator through the complete native 3D transfers. -/
theorem xiZeroLedgerOperator_eq_carrierHeight_of_selfAdjointXiReceiver
    (chiOne : DirichletCharacter ℂ 1)
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (hReg : ∀ z, z ∉ spectrum ℂ a →
      ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (nhdsWithin z {z}ᶜ) (nhds L)) :
    CriticalLinePhasor.XiChannel.xiZeroLedgerOperator =
      CriticalLinePhasor.XiChannel.xiCarrierHeightOperator := by
  apply xiZeroLedgerOperator_eq_carrierHeight_of_allNative3DSourceTransfer chiOne
  exact allNative3DSourceTransfer_of_selfAdjointXiReceiver chiOne ha hReg

/-- Receiver capstone: the same native 3D assembly returns both the global coordinate identity
and its basiswise zero-ledger/carrier-height operator realization. -/
theorem globalCoordinateIdentification_and_zeroLedger_eq_carrierHeight_of_selfAdjointXiReceiver
    (chiOne : DirichletCharacter ℂ 1)
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (hReg : ∀ z, z ∉ spectrum ℂ a →
      ∃ L, Tendsto CriticalLinePhasor.XiChannel.xiChannel (nhdsWithin z {z}ᶜ) (nhds L)) :
    (∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) ∧
      CriticalLinePhasor.XiChannel.xiZeroLedgerOperator =
        CriticalLinePhasor.XiChannel.xiCarrierHeightOperator := by
  have hall := allNative3DSourceTransfer_of_selfAdjointXiReceiver chiOne ha hReg
  have hop := xiZeroLedgerOperator_eq_carrierHeight_of_allNative3DSourceTransfer chiOne hall
  exact ⟨(globalCoordinateIdentification_iff_zeroLedger_eq_carrierHeight chiOne).2 hop, hop⟩

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.principalZeroAnalyticFiber3D
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.log_sourceHeight_eq_im
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.carrierPointAt_sourceHeight
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.ambient_ordinate_eq_log_sourceHeight
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.carrierPointAt_sourceHeight_im
#print axioms CriticalLinePhasor.ContourArgument.principalZero_focalCancellation_on_carrier
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNativeCarrierEvent3D.on_archimedeanHelix
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNativeCarrierEvent3D.physicalHeight_eq_focalHeight
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNativeCarrierEvent3D.ambient_eigenvector
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNativeCarrierEvent3D.noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNativeCarrierEvent3D.carrierReadout_scaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNativeCarrierEvent3D.focalCancellation_onCarrier_noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.radialMagnitude
#print axioms CriticalLinePhasor.ContourArgument.etaSpectralFiber_radialMagnitude
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.ridesCarrier_iff_carrierWeld
#print axioms CriticalLinePhasor.ContourArgument.one_sub_conj_mem_nontrivialZeros
#print axioms CriticalLinePhasor.ContourArgument.reflected_principalZeroAnalyticFiber3D_sourceHeight_eq
#print axioms CriticalLinePhasor.ContourArgument.reflected_principalZeroAnalyticFiber3D_ambientState_eq
#print axioms CriticalLinePhasor.ContourArgument.reflected_principalZeroAnalyticFiber3D_plane_cross_scaled
#print axioms CriticalLinePhasor.ContourArgument.reflected_radialMagnitude_eq_iff_carrierScaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.paired_radialMagnitude_product
#print axioms CriticalLinePhasor.ContourArgument.paired_areaNormalizedRadialMagnitude_tendsto_one
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.carrierScaleBalanced_iff_radialMagnitude
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.carrierWeld_iff_scaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.ridesCarrier_iff_scaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.principalZeroProjectionResidual_eq_zero_iff_radialMagnitude
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroAnalyticFiber3D.carrierWeld_iff_projectionResidual_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.nonempty_principalContourNative3DCertificate_iff_carrierWeld
#print axioms CriticalLinePhasor.ContourArgument.principalZeroNative3DSourceTransfer_of_noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.PrincipalContourNative3DCertificate.analyticFiber_eq_carrierFiber
#print axioms CriticalLinePhasor.ContourArgument.PrincipalContourNative3DCertificate.noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.principalZeroNative3DSourceTransfer_of_nativeCertificate
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.eventHeight_eq_focalCancellationHeight
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.harmonicRankDrop_at_focalCancellationHeight
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.focalCancellation_rankDrop_noRadialDrift_sameHeight
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.carrierScaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.fiberRidesCarrier
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.carrierReadout_eq_analyticParameter
#print axioms CriticalLinePhasor.ContourArgument.PrincipalZeroNative3DSourceTransfer.fiberRidesCarrier_carrierRidesHelix
#print axioms CriticalLinePhasor.ContourArgument.nonempty_principalZeroNative3DSourceTransfer_iff_noRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.nonempty_principalZeroNative3DSourceTransfer_iff_carrierScaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.nonempty_principalZeroNative3DSourceTransfer_iff_fiberRidesCarrier
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_iff_everyAnalyticZeroFiberScaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_of_lt_two
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_upperNative3DSourceTransfer
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_allNative3DSourceTransfer
#print axioms CriticalLinePhasor.ContourArgument.allNative3DSourceTransfer_iff_allCanonicalZeroFibersRideCarrier
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_allAnalyticZeroFibersScaleBalanced
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_allCanonicalZeroFibersRideCarrier
#print axioms CriticalLinePhasor.ContourArgument.allCanonicalZeroFibersRideCarrier_of_allNative3DSourceTransfer
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_allCanonicalZeroFiberRadialMagnitudeBalanced
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_xiZeroLedgerOperator_symmetric
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_of_xiZeroLedgerOperator_symmetric
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_xiRadialDriftOperator_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_zeroLedger_eq_carrierHeight
#print axioms CriticalLinePhasor.ContourArgument.allCanonicalZeroFibersRideCarrier_iff_zeroLedger_eq_carrierHeight
#print axioms CriticalLinePhasor.ContourArgument.allNative3DSourceTransfer_iff_zeroLedger_eq_carrierHeight
#print axioms CriticalLinePhasor.ContourArgument.allCanonicalZeroFibersRideCarrier_iff_eachZeroPoleResolvent_eq_carrierBasisReadout
#print axioms CriticalLinePhasor.ContourArgument.xiZeroLedgerOperator_eq_carrierHeight_of_allNative3DSourceTransfer
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_of_allNative3DSourceTransfer
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_zeroLedger_fixedByNoDriftProjection
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_zeroLedgerProjectionResidual_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_eachZeroBasisProjectionResidual_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_eachZeroPoleResolvent_eq_carrierBasisReadout
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_iff_basisResolvedCarrierResolventBridge
#print axioms CriticalLinePhasor.ContourArgument.carrierHeightResolventTrace_of_globalCoordinateIdentification
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_basisResolvedBridge_and_carrierTrace_of_allNative3DSourceTransfer
#print axioms CriticalLinePhasor.ContourArgument.upperNative3DSourceTransfer_of_selfAdjointXiReceiver
#print axioms CriticalLinePhasor.ContourArgument.allNative3DSourceTransfer_of_selfAdjointXiReceiver
#print axioms CriticalLinePhasor.ContourArgument.allCanonicalZeroFibersRideCarrier_of_selfAdjointXiReceiver
#print axioms CriticalLinePhasor.ContourArgument.xiZeroLedgerOperator_eq_carrierHeight_of_selfAdjointXiReceiver
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_and_zeroLedger_eq_carrierHeight_of_selfAdjointXiReceiver
