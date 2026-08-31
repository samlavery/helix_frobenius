import RequestProject.SeatingChain
import RequestProject.SeatingTransversal

/-!
# Uniform window radius for a sorted list of simple on-line ordinates

For finitely many simple on-line zeros there is one radius `δ` — below every
zero's own flip radius, below half of every gap, inside the left margin, and
at most 1 — making all windows flip, all windows disjoint, and the hull sit
right of `T₁`.  Stated in the downward-closed form `∀ δ < δ*` so the
inductive minima compose.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

theorem exists_uniform_delta (T₁ : ℝ) :
    ∀ gs : List ℝ, gs.Chain' (· < ·) →
    (∀ g ∈ gs, T₁ < g ∧ g ≠ 0 ∧ linePt g ∈ ZD.NontrivialZeros ∧
      Zeta23.zeroMult (linePt g) = 1) →
    ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < δstar →
      gs.Chain' (fun x y => x + δ < y - δ) ∧
      (∀ g ∈ gs, XiLine (g - δ) * XiLine (g + δ) < 0) ∧
      (∀ g ∈ gs, T₁ ≤ g - δ) := by
  intro gs
  induction gs with
  | nil =>
    intro _ _
    exact ⟨1, one_pos, le_refl 1, fun δ _ _ =>
      ⟨List.isChain_nil, fun g hg => absurd hg (List.not_mem_nil),
        fun g hg => absurd hg (List.not_mem_nil)⟩⟩
  | cons g rest ih =>
    intro hchain hmem
    obtain ⟨hT₁g, hgne, hgmem, hgmult⟩ := hmem g List.mem_cons_self
    obtain ⟨εg, hεg, hflipg⟩ := simple_zero_flips hgne hgmem hgmult
    have hchain' : rest.Chain' (· < ·) := hchain.tail
    have hmem' : ∀ x ∈ rest, T₁ < x ∧ x ≠ 0 ∧ linePt x ∈ ZD.NontrivialZeros ∧
        Zeta23.zeroMult (linePt x) = 1 :=
      fun x hx => hmem x (List.mem_cons_of_mem g hx)
    obtain ⟨δ₁, hδ₁, hδ₁1, hprop⟩ := ih hchain' hmem'
    -- the head gap (1 if rest is empty)
    rcases hr : rest with _ | ⟨g', rest'⟩
    · -- single element
      refine ⟨min εg (min (g - T₁) 1), by
        have : (0:ℝ) < g - T₁ := by linarith
        positivity, ?_, ?_⟩
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
      · intro δ hδ0 hδ
        have hδε : δ < εg := lt_of_lt_of_le hδ (min_le_left _ _)
        have hδm : δ < g - T₁ :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_left _ _))
        refine ⟨List.isChain_singleton _, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact hflipg δ hδ0 hδε
        · intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          linarith
    · -- head gap to g'
      subst hr
      have hgg' : g < g' := (List.isChain_cons_cons.mp hchain).1
      refine ⟨min (min δ₁ εg) (min ((g' - g)/2) (min (g - T₁) 1)), by
        have h1 : (0:ℝ) < g' - g := by linarith
        have h2 : (0:ℝ) < g - T₁ := by linarith
        positivity, ?_, ?_⟩
      · exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _))
      · intro δ hδ0 hδ
        have hδδ₁ : δ < δ₁ :=
          lt_of_lt_of_le hδ (le_trans (min_le_left _ _) (min_le_left _ _))
        have hδε : δ < εg :=
          lt_of_lt_of_le hδ (le_trans (min_le_left _ _) (min_le_right _ _))
        have hδgap : δ < (g' - g)/2 :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_left _ _))
        have hδm : δ < g - T₁ :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _)))
        obtain ⟨hsep', hflip', hmarg'⟩ := hprop δ hδ0 hδδ₁
        refine ⟨?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨by linarith, hsep'⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hflipg δ hδ0 hδε
          · exact hflip' x hx
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · linarith
          · exact hmarg' x hx

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.exists_uniform_delta

/-! ## The ½-flips capstone: half the census flips, in chain form, per box -/

namespace CriticalLinePhasor.SeatingLedger

open Complex

/-- **Half the census flips** — per dyadic box, eventually: a strictly
monotone chain of consecutive sign changes of the bank readout, at least
`(1/2 − ε)` times the strip census long.  The flip-visibility hypothesis of
`rh_of_flip_visibility`, compiled at density ½. -/
theorem half_flips_per_box :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∃ (n : ℕ) (a : Fin (n+1) → ℝ),
      (1/2 - ε) * ((stripBox T (2*T)).ncard : ℝ) ≤ (n : ℝ) ∧
      StrictMono a ∧ T ≤ a 0 ∧ a (Fin.last n) ≤ 2*T + 1 ∧
      ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0 := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := seating_simple_floor ε hε
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : (1:ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hfloor := hT₀ T (le_trans (le_max_left _ _) hT)
  -- the simple on-line ordinates, sorted
  set S := simpleOnLineBox T (2*T) with hS
  have hfin : S.Finite :=
    (stripBox_finite T (2*T)).subset (fun x hx => hx.1.1)
  set ords : Finset ℝ := hfin.toFinset.image Complex.im with hords
  set gs : List ℝ := ords.sort (· ≤ ·) with hgs
  -- membership facts
  have hmemS : ∀ g ∈ gs, ∃ ρ ∈ S, ρ.im = g := by
    intro g hg
    rw [hgs, Finset.mem_sort] at hg
    rw [hords, Finset.mem_image] at hg
    obtain ⟨ρ, hρ, him⟩ := hg
    exact ⟨ρ, hfin.mem_toFinset.mp hρ, him⟩
  have hfacts : ∀ g ∈ gs, T < g ∧ g ≠ 0 ∧ linePt g ∈ ZD.NontrivialZeros ∧
      Zeta23.zeroMult (linePt g) = 1 := by
    intro g hg
    obtain ⟨ρ, hρS, him⟩ := hmemS g hg
    obtain ⟨⟨⟨hNT, hIoc⟩, hre⟩, hmult⟩ := hρS
    have hρeq : linePt g = ρ := by
      apply Complex.ext
      · rw [linePt_re, hre]
      · rw [linePt_im, him]
    have hTg : T < g := by rw [← him]; exact hIoc.1
    refine ⟨hTg, by linarith, ?_, ?_⟩
    · rw [hρeq]; exact hNT
    · rw [hρeq]; exact hmult
  have hub : ∀ g ∈ gs, g ≤ 2*T := by
    intro g hg
    obtain ⟨ρ, hρS, him⟩ := hmemS g hg
    rw [← him]
    exact hρS.1.1.2.2
  -- sorted-nodup gives the strict chain
  have hsorted : gs.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnodup : gs.Nodup := Finset.sort_nodup _ _
  have hpair : gs.Pairwise (· < ·) :=
    (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hchainlt : gs.Chain' (· < ·) := List.isChain_iff_pairwise.mpr hpair
  -- the census count
  have hcount : gs.length = S.ncard := by
    rw [hgs, Finset.length_sort, hords]
    rw [Finset.card_image_of_injOn, ← Set.ncard_eq_toFinset_card _ hfin]
    intro x hx y hy hxy
    have hx' := (hfin.mem_toFinset.mp hx).1.2
    have hy' := (hfin.mem_toFinset.mp hy).1.2
    apply Complex.ext
    · rw [hx', hy']
    · exact hxy
  rcases eq_or_ne gs [] with hnil | hne
  · -- empty: census ≤ 0, trivial chain
    have hzero : S.ncard = 0 := by rw [← hcount, hnil]; rfl
    refine ⟨0, fun _ => T, ?_, ?_, le_refl T, by linarith, fun i => i.elim0⟩
    · calc (1/2 - ε) * ((stripBox T (2*T)).ncard : ℝ)
          ≤ ((simpleOnLineBox T (2*T)).ncard : ℝ) := hfloor
        _ = ((0:ℕ) : ℝ) := by rw [← hS, hzero]
        _ = ((0:ℕ) : ℝ) := rfl
    · intro i j hij
      have : i = j := by omega
      rw [this] at hij
      exact absurd hij (lt_irrefl j)
  · -- nonempty: pack the windows
    obtain ⟨δs, hδs, hδs1, hδprop⟩ := exists_uniform_delta T gs hchainlt hfacts
    obtain ⟨hsep, hflips, hmarg⟩ := hδprop (δs/2) (by linarith) (by linarith)
    obtain ⟨l, hl, hchain, hlen, hhull, hlast, _⟩ :=
      exists_flip_chain_of_windows (by linarith : (0:ℝ) < δs/2)
        gs hsep hflips hne
    -- the Fin chain
    have hlpos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
    set n : ℕ := l.length - 1 with hn
    have hlen1 : l.length = n + 1 := by omega
    set a : Fin (n+1) → ℝ := fun i => l.get (Fin.cast hlen1.symm i) with ha
    have hltchain : l.Chain' (· < ·) := hchain.imp (fun _ _ h => h.1)
    have hltpair : l.Pairwise (· < ·) := List.isChain_iff_pairwise.mp hltchain
    have hmono : StrictMono a := by
      intro i j hij
      exact List.pairwise_iff_get.mp hltpair _ _ (by simpa using hij)
    have hmemhull : ∀ i : Fin (n+1), T ≤ a i ∧ a i ≤ 2*T + 1 := by
      intro i
      have hmem : a i ∈ l := List.get_mem _ _
      have h1 := (hhull _ hmem).1
      have h2 := (hhull _ hmem).2
      have hheadgs : T ≤ gs.head hne - δs/2 :=
        hmarg (gs.head hne) (List.head_mem hne)
      have hlastgs : gs.getLast hne ≤ 2*T := hub _ (List.getLast_mem hne)
      constructor
      · linarith
      · linarith
    have hflipfin : ∀ i : Fin n,
        XiLine (a i.castSucc) * XiLine (a i.succ) < 0 := by
      intro i
      have h := List.isChain_iff_getElem.mp hchain i.val (by
        rw [hlen1]
        omega)
      exact h.2
    refine ⟨n, a, ?_, hmono, (hmemhull 0).1, (hmemhull _).2, hflipfin⟩
    -- the count: (1/2−ε)·census ≤ S.ncard = gs.length ≤ l.length − 1 = n
    have hcast : (S.ncard : ℝ) ≤ (n : ℝ) := by
      have : S.ncard ≤ n := by
        rw [← hcount]
        omega
      exact_mod_cast this
    calc (1/2 - ε) * ((stripBox T (2*T)).ncard : ℝ)
        ≤ ((simpleOnLineBox T (2*T)).ncard : ℝ) := hfloor
      _ = (S.ncard : ℝ) := by rw [hS]
      _ ≤ (n : ℝ) := hcast

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.half_flips_per_box
