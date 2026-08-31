import RequestProject.SeatingDetector

/-!
# Chain packing: disjoint flip windows assemble into one alternating chain

The greedy extraction: processing flip windows left to right, each window
appends at least one consecutive flip to the chain — both window edges when
the junction itself flips, the far edge alone otherwise (the window's own
flip forces the alternation either way).  Hence `m` separated windows yield a
strictly monotone chain with at least `m` consecutive sign changes: the exact
hypothesis shape of `rh_of_flip_visibility`.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- One chain step: increase with a readout sign change. -/
def FlipStep (x y : ℝ) : Prop := x < y ∧ XiLine x * XiLine y < 0

private theorem getLast_app (l : List ℝ) (a : ℝ) (h : l ++ [a] ≠ []) :
    (l ++ [a]).getLast h = a :=
  List.getLast_concat

private theorem getLast_app2 (l : List ℝ) (a b : ℝ) (h : l ++ [a, b] ≠ []) :
    (l ++ [a, b]).getLast h = b := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have h2 : t ++ [a, b] ≠ [] := by simp
    calc ((x :: t) ++ [a, b]).getLast h
        = (t ++ [a, b]).getLast h2 := List.getLast_cons h2
      _ = b := ih h2

/-- **The greedy extraction.**  Separated flip windows assemble into a single
`FlipStep`-chain with at least one more point than there are windows, all
points inside the windows' hull, ending at the last right edge with a nonzero
readout. -/
theorem exists_flip_chain_of_windows {δ : ℝ} (hδ : 0 < δ) :
    ∀ zs : List ℝ, zs.Chain' (fun x y => x + δ < y - δ) →
    (∀ z ∈ zs, XiLine (z - δ) * XiLine (z + δ) < 0) →
    ∀ hne : zs ≠ [],
    ∃ l : List ℝ, ∃ hl : l ≠ [],
      l.Chain' FlipStep ∧ zs.length + 1 ≤ l.length ∧
      (∀ x ∈ l, zs.head hne - δ ≤ x ∧ x ≤ zs.getLast hne + δ) ∧
      l.getLast hl = zs.getLast hne + δ ∧
      XiLine (l.getLast hl) ≠ 0 := by
  intro zs
  induction zs using List.reverseRecOn with
  | nil =>
    intro _ _ hne
    exact absurd rfl hne
  | append_singleton zs z ih =>
    intro hsep hflip hne0
    have hzflip : XiLine (z - δ) * XiLine (z + δ) < 0 :=
      hflip z (List.mem_append_right _ (List.mem_singleton_self z))
    have hQne : XiLine (z + δ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hzflip
      exact absurd hzflip (lt_irrefl 0)
    have hPne : XiLine (z - δ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hzflip
      exact absurd hzflip (lt_irrefl 0)
    have hlast_all : (zs ++ [z]).getLast hne0 = z := getLast_app zs z hne0
    rcases eq_or_ne zs [] with hnil | hzs
    · -- single window
      subst hnil
      have hhead_all : (([] : List ℝ) ++ [z]).head hne0 = z := rfl
      refine ⟨[z - δ, z + δ], by simp, ?_, by simp, ?_, ?_, ?_⟩
      · exact List.isChain_cons_cons.mpr
          ⟨⟨by linarith, hzflip⟩, List.isChain_singleton _⟩
      · intro x hx
        rw [hhead_all, hlast_all]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl
        · constructor <;> linarith
        · constructor <;> linarith
      · rw [hlast_all]
        rfl
      · have : ([z - δ, z + δ] : List ℝ).getLast (by simp) = z + δ := rfl
        rw [this]
        exact hQne
    · -- extend the chain of zs
      have happ := List.isChain_append.mp hsep
      have hsep' : zs.Chain' (fun x y => x + δ < y - δ) := happ.1
      have hflip' : ∀ w ∈ zs, XiLine (w - δ) * XiLine (w + δ) < 0 :=
        fun w hw => hflip w (List.mem_append_left _ hw)
      obtain ⟨l, hl, hchain, hlen, hrange, hlast, hLne⟩ := ih hsep' hflip' hzs
      have hhead_all : (zs ++ [z]).head hne0 = zs.head hzs := by
        cases zs with
        | nil => exact absurd rfl hzs
        | cons a t => rfl
      have hjun : zs.getLast hzs + δ < z - δ :=
        happ.2.2 (zs.getLast hzs) (List.getLast?_eq_getLast_of_ne_nil hzs) z rfl
      have hLlt : l.getLast hl < z - δ := by
        rw [hlast]
        exact hjun
      have hLlo : zs.head hzs - δ ≤ l.getLast hl :=
        (hrange (l.getLast hl) (List.getLast_mem hl)).1
      rcases lt_trichotomy
        (XiLine (l.getLast hl) * XiLine (z - δ)) 0 with hLP | hLP | hLP
      · -- junction flips: append both edges
        refine ⟨l ++ [z - δ, z + δ], by simp, ?_, ?_, ?_, ?_, ?_⟩
        · refine List.isChain_append.mpr ⟨hchain, List.isChain_cons_cons.mpr
            ⟨⟨by linarith, hzflip⟩, List.isChain_singleton _⟩, ?_⟩
          intro x hx y hy
          rw [List.getLast?_eq_getLast_of_ne_nil hl, Option.mem_def,
            Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hx
          subst hy
          exact ⟨hLlt, hLP⟩
        · simp only [List.length_append, List.length_cons,
            List.length_singleton, List.length_nil]
          omega
        · intro x hx
          rw [hhead_all, hlast_all]
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · have := hrange x hx
            exact ⟨this.1, by linarith [this.2, hjun]⟩
          · simp only [List.mem_cons, List.mem_singleton,
              List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact ⟨by linarith, by linarith⟩
            · exact ⟨by linarith, by linarith⟩
        · rw [hlast_all, getLast_app2]
        · rw [getLast_app2]
          exact hQne
      · exact absurd hLP (mul_ne_zero hLne hPne)
      · -- same sign at junction: append the far edge alone
        have hLQ : XiLine (l.getLast hl) * XiLine (z + δ) < 0 := by
          have hP2 : 0 < XiLine (z - δ) * XiLine (z - δ) := by
            rcases lt_or_gt_of_ne hPne with h | h
            · exact mul_pos_of_neg_of_neg h h
            · exact mul_pos h h
          nlinarith [hzflip, hLP]
        refine ⟨l ++ [z + δ], by simp, ?_, ?_, ?_, ?_, ?_⟩
        · refine List.isChain_append.mpr ⟨hchain, List.isChain_singleton _, ?_⟩
          intro x hx y hy
          rw [List.getLast?_eq_getLast_of_ne_nil hl, Option.mem_def,
            Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hx
          subst hy
          exact ⟨by linarith, hLQ⟩
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro x hx
          rw [hhead_all, hlast_all]
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · have := hrange x hx
            exact ⟨this.1, by linarith [this.2, hjun]⟩
          · simp only [List.mem_singleton] at hx
            subst hx
            exact ⟨by linarith, by linarith⟩
        · rw [hlast_all, getLast_app]
        · rw [getLast_app]
          exact hQne

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.exists_flip_chain_of_windows
