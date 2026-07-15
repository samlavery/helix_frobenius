import RequestProject.TransferContinuation

/-!
# Abel transfer through an inverse-warp kernel

This is the kernel-level form of summation by parts required by an inverse-warp readout.  Unlike
`TransferContinuation.transfer_analytic`, the theorem below permits an `n`-dependent kernel.  Its two
analytic inputs are exactly the Abel difference series and the boundary term.
-/

namespace InverseWarpKernelTransfer

open Complex Finset Filter Topology

/-- Summation by parts for an arbitrary complex kernel. -/
theorem kernel_transfer_tendsto
    (b K : ℕ → ℂ)
    (hDiff : Summable (fun i : ℕ =>
      (K (i + 1) - K i) * (∑ k ∈ range (i + 1), b k)))
    (hBoundary : Tendsto (fun n : ℕ =>
      K (n - 1) * (∑ k ∈ range n, b k)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, b n * K n) atTop
      (nhds (0 - ∑' i : ℕ,
        (K (i + 1) - K i) * (∑ k ∈ range (i + 1), b k))) := by
  let A : ℕ → ℂ := fun n => ∑ k ∈ range n, b k
  let d : ℕ → ℂ := fun i => (K (i + 1) - K i) * A (i + 1)
  have hParts : ∀ n : ℕ,
      (∑ i ∈ range n, b i * K i) =
        K (n - 1) * A n - ∑ i ∈ range (n - 1), d i := by
    intro n
    have h := Finset.sum_range_by_parts K b n
    simp only [smul_eq_mul] at h
    rw [show (∑ i ∈ range n, b i * K i) = ∑ i ∈ range n, K i * b i by
      apply sum_congr rfl
      intro i _
      exact mul_comm _ _, h]
  have hd : Summable d := by
    simpa [d, A] using hDiff
  have hT : Tendsto (fun m : ℕ => ∑ i ∈ range m, d i) atTop (nhds (∑' i, d i)) :=
    hd.hasSum.tendsto_sum_nat
  have hTshift : Tendsto (fun n : ℕ => ∑ i ∈ range (n - 1), d i)
      atTop (nhds (∑' i, d i)) :=
    hT.comp (Filter.tendsto_sub_atTop_nat 1)
  have hfinal := hBoundary.sub hTshift
  simpa [A, d] using hfinal.congr (fun n => (hParts n).symm)

/-- A nonvanishing coefficient warp is removed exactly at every finite stage once its full inverse
kernel satisfies the Abel difference and boundary conditions. -/
theorem inverseWarp_transfer_tendsto
    (a ω : ℕ → ℂ) (s : ℂ) (hω : ∀ n, ω n ≠ 0)
    (hDiff : Summable (fun i : ℕ =>
      ((ω (i + 1))⁻¹ * (((i + 2 : ℕ) : ℂ) ^ (-s)) -
          (ω i)⁻¹ * (((i + 1 : ℕ) : ℂ) ^ (-s))) *
        (∑ k ∈ range (i + 1), a k * ω k)))
    (hBoundary : Tendsto (fun n : ℕ =>
      (ω (n - 1))⁻¹ * (((n : ℕ) : ℂ) ^ (-s)) *
        (∑ k ∈ range n, a k * ω k)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ range N, a n * (((n + 1 : ℕ) : ℂ) ^ (-s))) atTop
      (nhds (0 - ∑' i : ℕ,
        (((ω (i + 1))⁻¹ * (((i + 2 : ℕ) : ℂ) ^ (-s)) -
            (ω i)⁻¹ * (((i + 1 : ℕ) : ℂ) ^ (-s))) *
          (∑ k ∈ range (i + 1), a k * ω k)))) := by
  have hBoundary' : Tendsto (fun n : ℕ =>
      (ω (n - 1))⁻¹ * ((((n - 1) + 1 : ℕ) : ℂ) ^ (-s)) *
        (∑ k ∈ range n, a k * ω k)) atTop (nhds 0) := by
    apply hBoundary.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.sub_add_cancel hn]
  have h := kernel_transfer_tendsto
    (fun n => a n * ω n)
    (fun n => (ω n)⁻¹ * (((n + 1 : ℕ) : ℂ) ^ (-s))) hDiff hBoundary'
  convert h using 1
  ext N
  apply sum_congr rfl
  intro n _
  field_simp [hω n]

end InverseWarpKernelTransfer

#print axioms InverseWarpKernelTransfer.kernel_transfer_tendsto
#print axioms InverseWarpKernelTransfer.inverseWarp_transfer_tendsto
