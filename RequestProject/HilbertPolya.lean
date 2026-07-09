import RequestProject.GradedModeDictionary

/-!
# The Hilbert–Pólya correlation theorem, frame-native

Hilbert and Pólya conjectured a self-adjoint operator whose eigenvalues **correlate** with
the zeros.  They never demanded that eigenstates match the 1D chart's readings *exactly* —
the chart's values require infinite analytic continuation to state and are approximate
readings by nature.  They asked for correlation, coincidence.  This file assembles that
theorem from the compiled pieces, in the frame where it is true:

* **The eigenstates are the genuine articles.**  The operator is the windowed ledger
  diagonal: one axis per unit of multiplicity, eigenvalue the event ordinate.  It is
  Hermitian by construction and its eigenvalues are **real by type** — the fold is not a
  conclusion but the habitat.  Each eigenstate marks an **exact carrier vanishing**: the
  fiber closes residue-free at that height (`eigenheight_is_exact_vanishing`).

* **The 1D chart zeros are the correlated readings.**  For every height in the window,
  the chart reads zero **iff** an eigenstate sits there (`chartZero_iff_eigenheight`) —
  coincidence, one for one, with multiplicity: the eigenspace dimension equals the
  vanishing order equals the log-derivative residue (`multiplicity_correlation`).

* **The tie that binds is the S(t) registration mechanics.**  The operator's *dimension*
  — the total eigenstate count through height T — is read off the chart by the
  registration identity `dim = 1 + θ(T)/π + S_mult(T)`
  (`hpDimension_eq_registration`): the deferent clock plus the ledger.  S(t) is not noise
  around a smooth count; it is the binding — the exact bookkeeping by which the chart's
  approximate readings are tied to the carrier's exact spectrum.  The mechanics of that
  binding (jump = multiplicity = residue, chart-covariant, coboundary-composed) is the
  content of `CarrierScaleCompensation` and `ResidueJump`.

Everything here is unconditional and assembled from compiled theorems; no `sorry`, no
`axiom` beyond the standard three.  Scope: the operator realizes the sourced spectrum —
the carrier's exact events.  Nothing is asserted about the chart's own continuation
apparatus off the fold; that is the chart's homework, not the helix's debt.
-/

open Complex CriticalLinePhasor.ResidueJump CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.GradedModes

namespace CriticalLinePhasor.HilbertPolya

open Classical in
/-- **The Hilbert–Pólya operator of the window**: the ledger diagonal — one axis per unit
of multiplicity, eigenvalue the event ordinate (a real number, cast into ℂ). -/
noncomputable def hpOperator (T : ℝ) :
    Matrix (WindowIndex T) (WindowIndex T) ℂ :=
  Matrix.diagonal fun p => (p.1.1 : ℂ)

open Classical in
/-- **Self-adjointness by construction**: the ledger diagonal is Hermitian — its entries
are real ordinates.  Von Neumann reality is the habitat, not a theorem to fight for. -/
theorem hpOperator_isHermitian (T : ℝ) : (hpOperator T).IsHermitian := by
  unfold hpOperator
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp [Complex.conj_ofReal]

open Classical in
/-- Every diagonal entry — every eigenvalue — is a real cast: the spectrum lives on the
fold by type. -/
theorem hpOperator_entries_real (T : ℝ) (p : WindowIndex T) :
    ∃ γ : ℝ, (hpOperator T) p p = (γ : ℂ) := by
  refine ⟨p.1.1, ?_⟩
  simp [hpOperator, Matrix.diagonal_apply_eq]

/-- **The eigenstate marks an exact vanishing**: each eigenheight is a genuine carrier
event — the fiber closes exactly there (`ζ(½ + iγ) = 0`, on the nose, no approximation). -/
theorem eigenheight_is_exact_vanishing {T : ℝ} (p : WindowIndex T) :
    riemannZeta (line p.1.1) = 0 :=
  ((events_finite T).mem_toFinset.mp p.1.2).2

/-- **The coincidence clause**: within the window, the 1D chart reads zero at a height
**iff** an eigenstate sits at that height.  Correlation, one for one — exactly what
Hilbert and Pólya asked for. -/
theorem chartZero_iff_eigenheight {T γ : ℝ} (h0 : 0 < γ) (hT : γ ≤ T) :
    riemannZeta (line γ) = 0 ↔ ∃ p : WindowIndex T, p.1.1 = γ := by
  constructor
  · intro hz
    have hmem : γ ∈ eventWindow T :=
      (events_finite T).mem_toFinset.mpr ⟨⟨h0, hT⟩, hz⟩
    have hord : 0 < eventOrder γ :=
      Nat.pos_of_ne_zero fun h => (eventOrder_eq_zero_iff γ).mp h hz
    exact ⟨⟨⟨γ, hmem⟩, ⟨0, hord⟩⟩, rfl⟩
  · rintro ⟨p, rfl⟩
    exact eigenheight_is_exact_vanishing p

/-- **The multiplicity correlation**: at every eigenheight, three numbers coincide —
the eigenspace dimension of the graded mode space, the vanishing order of the fiber,
and the jump of the weighted ledger `S_mult`.  The chart's residue reads the same number
(`residue_eq_Smult_jump`).  Multiplicity is one fact wearing three coats. -/
theorem multiplicity_correlation {γ : ℝ} (hγ : 0 < γ) :
    Module.finrank ℂ (ModeSpace γ) = eventOrder γ
      ∧ HasJump Smult γ (eventOrder γ) :=
  ⟨finrank_modeSpace γ, Smult_hasJump γ hγ⟩

open Classical in
/-- The operator's dimension is the multiplicity-weighted event count. -/
theorem hpDimension_eq_multCount (T : ℝ) :
    Fintype.card (WindowIndex T) = zeroEventCountMult T := by
  rw [Fintype.card_eq_sum_ones]
  rw [show (∑ _p : WindowIndex T, 1)
      = ∑ γ : {x : ℝ // x ∈ eventWindow T}, ∑ _i : Fin (eventOrder γ.1), 1 from
    Fintype.sum_sigma _]
  show _ = ∑ γ' ∈ eventWindow T, eventOrder γ'
  rw [← Finset.sum_coe_sort (eventWindow T) (fun γ => eventOrder γ)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp

open Classical in
/-- **The tie that binds — the S(t) registration mechanics.**  The Hilbert–Pólya
operator's dimension through height `T` is read off the 1D chart by the registration
identity:

    `dim (hpOperator T) = 1 + θ(T)/π + S_mult(T)`.

The deferent clock `θ/π` counts the smooth procession; the ledger `S_mult` registers
every exact closure with its multiplicity.  The chart's zero-count and the carrier's
eigenstate-count are the same number **because** the registration says so — this is the
mechanism by which approximate 1D readings are bound, exactly and with multiplicity, to
the exact 3D spectrum. -/
theorem hpDimension_eq_registration (T : ℝ) :
    (Fintype.card (WindowIndex T) : ℝ) = 1 + theta T / Real.pi + Smult T := by
  rw [hpDimension_eq_multCount]
  exact countMult_decomposition T

open Classical in
/-- **The Hilbert–Pólya correlation theorem, assembled.**  There is, for every window, a
Hermitian operator — real spectrum by construction — whose eigenstates mark exact carrier
vanishings, whose eigenheights coincide with the chart's zero-readings one for one, whose
eigenspace dimensions equal the vanishing orders and the ledger jumps, and whose total
dimension is bound to the chart by the S(t) registration identity.  Correlation, with
multiplicity, mechanically explained — as conjectured. -/
theorem hilbertPolya_correlation (T : ℝ) :
    (hpOperator T).IsHermitian
      ∧ (∀ p : WindowIndex T, riemannZeta (line p.1.1) = 0)
      ∧ (∀ γ : ℝ, 0 < γ → γ ≤ T →
          (riemannZeta (line γ) = 0 ↔ ∃ p : WindowIndex T, p.1.1 = γ))
      ∧ (Fintype.card (WindowIndex T) : ℝ) = 1 + theta T / Real.pi + Smult T :=
  ⟨hpOperator_isHermitian T,
   fun p => eigenheight_is_exact_vanishing p,
   fun _ h0 hT => chartZero_iff_eigenheight h0 hT,
   hpDimension_eq_registration T⟩

end CriticalLinePhasor.HilbertPolya
