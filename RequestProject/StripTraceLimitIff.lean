import RequestProject.StripTraceCapture

/-!
# Draft D's hypothesis is inhabited exactly when GRH(χ) holds (ledger 606)

`grh_of_stripTraceLimit` (parallel session) is the direction *hypothesis ⟹ GRH χ*: a locally uniform
limit of finite real-spectrum traces on `stripOffReal` is holomorphic there, so the normalized
L-trace minus the strip-holomorphic correction `E` is holomorphic, and a zero off the line would be a
pole inside the chart.

This file supplies the converse with an explicit inhabitant, hence the iff
**`stripTraceLimit_iff_GRH`**:

  `(∃ tower (d, c) and E holomorphic on stripOffReal with
      normalizedSpectrumTrace (d n) (c n) → normalizedLTrace χ − E locally uniformly on stripOffReal)
    ↔ GRH χ`.

The inhabitant under GRH: the EMPTY tower and `E := normalizedLTrace χ`. Under GRH every chart point
of `stripOffReal` maps to `s = ½ + iz` with `0 < Re s < 1`, `s ≠ 1`, and `L(χ, s) ≠ 0` (a zero there
would be a nontrivial zero off the line), so the L-trace is itself holomorphic on the chart, and the
zero tower converges to `L-trace − E = 0`.

What this shows about D, stated as content and not as a verdict. The hypothesis is inhabited
exactly when GRH χ holds; that is an equivalence, which is what every sufficient condition for GRH
is, and it says nothing about attackability (rule 10). What it does say is where D's construction
lives: the freedom in `E` must be spent. With `E := 0` the hypothesis asks for finite real spectra
whose traces converge to the L-trace on the chart; under GRH the tower of the zeros' own
`poleParam`s does this by the Hadamard expansion, and the constructive target is a tower built from
the fiber that converges to the same trace — the HP object in the trace register. With the
registry's stations as spectra the correction carries a pole at each off-line zero (605), which
locates the residual law as the thing to prove in that reading. Both readings are attacks on D, not
reasons to stop.
-/

open Complex Filter Topology Set
open DirichletCharacter

namespace CriticalLinePhasor.CaptureInterfaceAudit

variable {N : ℕ} [NeZero N]

/-- The chart `½ + iz` sends the strip chart into the open critical strip, away from `1`. -/
theorem chart_mem_strip {z : ℂ} (hz : z ∈ stripOffReal) :
    0 < (1 / 2 + I * z).re ∧ (1 / 2 + I * z).re < 1 ∧ (1 / 2 + I * z) ≠ 1 := by
  obtain ⟨_, hz2⟩ := hz
  have h1 : -(1 / 2 : ℝ) < z.im := hz2.1
  have h2 : z.im < 1 / 2 := hz2.2
  refine ⟨?_, ?_, ?_⟩
  · simp [Complex.add_re, Complex.mul_re]; linarith
  · simp [Complex.add_re, Complex.mul_re]; linarith
  · intro h
    have := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at this
    linarith

/-- Under GRH χ the L-function does not vanish on the image of the strip chart. -/
theorem LFunction_ne_zero_of_GRH {χ : DirichletCharacter ℂ N} (hχ : GRHSpectral.GRH χ)
    {z : ℂ} (hz : z ∈ stripOffReal) : LFunction χ (1 / 2 + I * z) ≠ 0 := by
  intro h0
  obtain ⟨hre0, hre1, _⟩ := chart_mem_strip hz
  have hmem : (1 / 2 + I * z) ∈ GRHSpectral.NontrivialZeros χ := ⟨hre0, hre1, h0⟩
  have hre := hχ _ hmem
  have hz1 : z.im ≠ 0 := hz.1
  simp [Complex.add_re, Complex.mul_re] at hre
  exact hz1 (by linarith)

/-- Under GRH χ the normalized L-trace is holomorphic on the strip chart. -/
theorem normalizedLTrace_differentiableOn_of_GRH {χ : DirichletCharacter ℂ N}
    (hχ : GRHSpectral.GRH χ) : DifferentiableOn ℂ (normalizedLTrace χ) stripOffReal := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨_, _, hne1⟩ := chart_mem_strip hz
  have hL0 := LFunction_ne_zero_of_GRH hχ hz
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hdiffOn : DifferentiableOn ℂ (LFunction χ) {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have han : AnalyticAt ℂ (LFunction χ) (1 / 2 + I * z) :=
    hdiffOn.analyticAt (hopen.mem_nhds hne1)
  have hchart : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + I * w) z := by fun_prop
  have hlog : DifferentiableAt ℂ (logDeriv (LFunction χ)) (1 / 2 + I * z) := by
    have h1 : DifferentiableAt ℂ (deriv (LFunction χ)) (1 / 2 + I * z) := han.deriv.differentiableAt
    have h2 : DifferentiableAt ℂ (LFunction χ) (1 / 2 + I * z) := han.differentiableAt
    have h3 : DifferentiableAt ℂ (fun s => deriv (LFunction χ) s / LFunction χ s) (1 / 2 + I * z) :=
      h2 |> fun _ => h1.div h2 hL0
    have heq : logDeriv (LFunction χ) = fun s => deriv (LFunction χ) s / LFunction χ s :=
      funext (fun s => logDeriv_apply _ _)
    rw [heq]
    exact h3
  have hcomp : DifferentiableAt ℂ (fun w : ℂ => I * logDeriv (LFunction χ) (1 / 2 + I * w)) z :=
    (hlog.comp z hchart).const_mul I
  unfold normalizedLTrace
  exact hcomp

/-- The empty tower has zero trace. -/
theorem normalizedSpectrumTrace_empty (z : ℂ) :
    normalizedSpectrumTrace (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j) z = 0 := by
  simp [normalizedSpectrumTrace]

/-- **Draft D's hypothesis ⟺ GRH χ.** -/
theorem stripTraceLimit_iff_GRH (χ : DirichletCharacter ℂ N) :
    (∃ (ι : ℕ → Type) (_ : ∀ n, Fintype (ι n)) (d : ∀ n, ι n → ℝ) (c : ∀ n, ι n → ℂ) (E : ℂ → ℂ),
        DifferentiableOn ℂ E stripOffReal ∧
        TendstoLocallyUniformlyOn (fun n => normalizedSpectrumTrace (d n) (c n))
          (fun z => normalizedLTrace χ z - E z) atTop stripOffReal)
      ↔ GRHSpectral.GRH χ := by
  constructor
  · rintro ⟨ι, hι, d, c, E, hE, hlim⟩
    exact @grh_of_stripTraceLimit N _ χ ι hι d c E hE hlim
  · intro hχ
    refine ⟨fun _ => Fin 0, fun _ => inferInstance, fun _ => Fin.elim0, fun _ => Fin.elim0,
      normalizedLTrace χ, normalizedLTrace_differentiableOn_of_GRH hχ, ?_⟩
    have h0 : (fun n : ℕ => normalizedSpectrumTrace (fun j : Fin 0 => Fin.elim0 j)
        (fun j : Fin 0 => Fin.elim0 j)) = fun _ => fun _ => (0 : ℂ) := by
      funext n z
      exact normalizedSpectrumTrace_empty z
    rw [h0]
    have htarget : (fun z => normalizedLTrace χ z - normalizedLTrace χ z) = fun _ => (0 : ℂ) := by
      funext z; simp
    rw [htarget]
    intro u hu x _
    exact ⟨stripOffReal, self_mem_nhdsWithin,
      Eventually.of_forall (fun n y _ => refl_mem_uniformity hu)⟩

/-- The same for every character at once: GRHComplete ⟺ every character has a strip-trace tower. -/
theorem stripTraceLimit_forall_iff_GRHComplete :
    (∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      ∃ (ι : ℕ → Type) (_ : ∀ n, Fintype (ι n)) (d : ∀ n, ι n → ℝ) (c : ∀ n, ι n → ℂ) (E : ℂ → ℂ),
        DifferentiableOn ℂ E stripOffReal ∧
        TendstoLocallyUniformlyOn (fun n => normalizedSpectrumTrace (d n) (c n))
          (fun z => normalizedLTrace χ z - E z) atTop stripOffReal)
      ↔ GRHSpectral.GRHComplete := by
  constructor
  · intro h M _ χ
    exact (stripTraceLimit_iff_GRH χ).1 (h M χ)
  · intro h M _ χ
    exact (stripTraceLimit_iff_GRH χ).2 (h M χ)

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.normalizedLTrace_differentiableOn_of_GRH
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.stripTraceLimit_iff_GRH
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.stripTraceLimit_forall_iff_GRHComplete
