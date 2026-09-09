import RequestProject.XiKernelTheta

/-!
# T1a, step 4: the kernel `K(u) = e^{u/2}(Ψ″(u) + Ψ′(u))` is even (ledger 669)

Differentiating the reflection `Ψ(u) = e^{−u}Ψ(−u) + (e^{−u} − 1)/2` twice on the axis (the derivatives
exist as restrictions of the holomorphic `PsiC`, `XiKernelTheta.lean`) gives

* `Ψ′(u) = −e^{−u}Ψ(−u) − e^{−u}Ψ′(−u) − e^{−u}/2`,
* `Ψ″(u) = e^{−u}Ψ(−u) + 2e^{−u}Ψ′(−u) + e^{−u}Ψ″(−u) + e^{−u}/2`,

so `Ψ″(u) + Ψ′(u) = e^{−u}(Ψ″(−u) + Ψ′(−u))` and `K(−u) = K(u)`.
-/

open Complex

namespace CriticalLinePhasor.XiKernel

/-- `Ψ′` and `Ψ″` on the axis, as restrictions of the holomorphic derivatives. -/
noncomputable def Psi1 (u : ℝ) : ℂ := deriv PsiC u
noncomputable def Psi2 (u : ℝ) : ℂ := deriv (deriv PsiC) u

theorem hasDerivAt_Psi0 (u : ℝ) : HasDerivAt (fun y : ℝ => PsiC y) (Psi1 u) u :=
  hasDerivAt_PsiC_ofReal u

theorem hasDerivAt_Psi1 (u : ℝ) : HasDerivAt Psi1 (Psi2 u) u :=
  hasDerivAt_deriv_PsiC_ofReal u

theorem neg_ofReal_mem_strip (u : ℝ) : (-(u : ℂ)) ∈ strip := by
  rw [← Complex.ofReal_neg]; exact ofReal_mem_strip (-u)

/-- `y ↦ Ψ(−y)` has derivative `−Ψ′(−u)`. -/
theorem hasDerivAt_PsiC_neg (u : ℝ) :
    HasDerivAt (fun y : ℝ => PsiC (-(y : ℂ))) (-(Psi1 (-u))) u := by
  have hd : HasDerivAt PsiC (deriv PsiC (-(u : ℂ))) (-(u : ℂ)) :=
    (differentiableOn_PsiC.differentiableAt (strip_isOpen.mem_nhds (neg_ofReal_mem_strip u))).hasDerivAt
  have hc : HasDerivAt (fun w : ℂ => PsiC (-w)) (deriv PsiC (-(u : ℂ)) * (-1)) (u : ℂ) :=
    hd.comp (u : ℂ) (hasDerivAt_neg (u : ℂ))
  refine hc.comp_ofReal.congr_deriv ?_
  rw [Psi1, Complex.ofReal_neg]; ring

/-- `y ↦ Ψ′(−y)` has derivative `−Ψ″(−u)`. -/
theorem hasDerivAt_Psi1_neg (u : ℝ) :
    HasDerivAt (fun y : ℝ => Psi1 (-y)) (-(Psi2 (-u))) u := by
  have hd : HasDerivAt (deriv PsiC) (deriv (deriv PsiC) (-(u : ℂ))) (-(u : ℂ)) :=
    (differentiableOn_deriv_PsiC.differentiableAt
      (strip_isOpen.mem_nhds (neg_ofReal_mem_strip u))).hasDerivAt
  have hc : HasDerivAt (fun w : ℂ => deriv PsiC (-w)) (deriv (deriv PsiC) (-(u : ℂ)) * (-1)) (u : ℂ) :=
    hd.comp (u : ℂ) (hasDerivAt_neg (u : ℂ))
  have hfun : (fun y : ℝ => Psi1 (-y)) = fun y : ℝ => deriv PsiC (-(y : ℂ)) := by
    funext y; rw [Psi1, Complex.ofReal_neg]
  rw [hfun]
  refine hc.comp_ofReal.congr_deriv ?_
  rw [Psi2, Complex.ofReal_neg]; ring

/-- `y ↦ e^{−y}` has derivative `−e^{−u}`. -/
theorem hasDerivAt_cexp_neg (u : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(y : ℂ))) (-Complex.exp (-(u : ℂ))) u := by
  have hc : HasDerivAt (fun w : ℂ => Complex.exp (-w)) (Complex.exp (-(u : ℂ)) * (-1)) (u : ℂ) :=
    (hasDerivAt_neg (u : ℂ)).cexp
  exact hc.comp_ofReal.congr_deriv (by ring)

/-- `Ψ(u) = e^{−u}Ψ(−u) + (e^{−u} − 1)/2` in `ℂ`. -/
theorem PsiC_reflect (u : ℝ) :
    PsiC u = Complex.exp (-(u : ℂ)) * PsiC (-(u : ℂ)) + (Complex.exp (-(u : ℂ)) - 1) / 2 := by
  rw [← Complex.ofReal_neg, PsiC_ofReal, PsiC_ofReal, Psi_reflect u]
  push_cast
  ring

/-- **First reflection:** `Ψ′(u) = −e^{−u}Ψ(−u) − e^{−u}Ψ′(−u) − e^{−u}/2`. -/
theorem Psi1_reflect (u : ℝ) :
    Psi1 u = -Complex.exp (-(u : ℂ)) * PsiC (-(u : ℂ)) - Complex.exp (-(u : ℂ)) * Psi1 (-u)
      - Complex.exp (-(u : ℂ)) / 2 := by
  have hL : HasDerivAt (fun y : ℝ => PsiC y) (Psi1 u) u := hasDerivAt_Psi0 u
  have hR := ((hasDerivAt_cexp_neg u).mul (hasDerivAt_PsiC_neg u)).add
    (((hasDerivAt_cexp_neg u).sub_const 1).div_const 2)
  have hfun : (fun y : ℝ => PsiC y) = fun y : ℝ => Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ))
      + (Complex.exp (-(y : ℂ)) - 1) / 2 := by
    funext y; exact PsiC_reflect y
  rw [hfun] at hL
  have := hL.unique hR
  rw [this]; ring

/-- **Second reflection:** `Ψ″(u) = e^{−u}Ψ(−u) + 2e^{−u}Ψ′(−u) + e^{−u}Ψ″(−u) + e^{−u}/2`. -/
theorem Psi2_reflect (u : ℝ) :
    Psi2 u = Complex.exp (-(u : ℂ)) * PsiC (-(u : ℂ)) + 2 * Complex.exp (-(u : ℂ)) * Psi1 (-u)
      + Complex.exp (-(u : ℂ)) * Psi2 (-u) + Complex.exp (-(u : ℂ)) / 2 := by
  have hL : HasDerivAt Psi1 (Psi2 u) u := hasDerivAt_Psi1 u
  have hR := ((((hasDerivAt_cexp_neg u).neg).mul (hasDerivAt_PsiC_neg u)).sub
    ((hasDerivAt_cexp_neg u).mul (hasDerivAt_Psi1_neg u))).sub
    ((hasDerivAt_cexp_neg u).div_const 2)
  have hfun : Psi1 = fun y : ℝ => -Complex.exp (-(y : ℂ)) * PsiC (-(y : ℂ))
      - Complex.exp (-(y : ℂ)) * Psi1 (-y) - Complex.exp (-(y : ℂ)) / 2 := by
    funext y; exact Psi1_reflect y
  rw [hfun] at hL
  have := hL.unique hR
  simp only [Pi.neg_apply] at this
  rw [this]; ring

/-- **The kernel** `K(u) = e^{u/2}(Ψ″(u) + Ψ′(u))`. -/
noncomputable def Kker (u : ℝ) : ℂ := Complex.exp ((u : ℂ) / 2) * (Psi2 u + Psi1 u)

/-- `Ψ″(u) + Ψ′(u) = e^{−u}(Ψ″(−u) + Ψ′(−u))`. -/
theorem Psi2_add_Psi1_reflect (u : ℝ) :
    Psi2 u + Psi1 u = Complex.exp (-(u : ℂ)) * (Psi2 (-u) + Psi1 (-u)) := by
  rw [Psi2_reflect u, Psi1_reflect u]; ring

/-- **Step 4: `K` is even.** -/
theorem Kker_even (u : ℝ) : Kker (-u) = Kker u := by
  unfold Kker
  rw [Psi2_add_Psi1_reflect u]
  push_cast
  rw [show Complex.exp ((u : ℂ) / 2) * (Complex.exp (-(u : ℂ)) * (Psi2 (-u) + Psi1 (-u)))
      = (Complex.exp ((u : ℂ) / 2) * Complex.exp (-(u : ℂ))) * (Psi2 (-u) + Psi1 (-u)) by ring,
    ← Complex.exp_add]
  congr 2
  ring

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.Psi1_reflect
#print axioms CriticalLinePhasor.XiKernel.Kker_even
