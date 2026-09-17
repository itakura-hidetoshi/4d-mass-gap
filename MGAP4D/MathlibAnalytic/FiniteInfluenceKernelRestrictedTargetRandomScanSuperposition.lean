import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScan
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One influence-kernel target update distributes exactly over a finite
superposition of variation profiles. -/
theorem finiteInfluenceKernelUpdatedVariation_finset_sum
    {ι κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (indices : Finset κ)
    (family : κ → ι → ℝ)
    (updateTarget source : ι) :
    finiteInfluenceKernelUpdatedVariation
        K (fun e => ∑ k ∈ indices, family k e) updateTarget source =
      ∑ k ∈ indices,
        finiteInfluenceKernelUpdatedVariation
          K (family k) updateTarget source := by
  by_cases hEq : source = updateTarget
  · simp [finiteInfluenceKernelUpdatedVariation, hEq]
  · simp only [finiteInfluenceKernelUpdatedVariation, hEq, if_false]
    rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- One restricted-target random-scan update distributes exactly over a finite
superposition of variation profiles. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_finset_sum
    {ι τ κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    [DecidableEq κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (indices : Finset κ)
    (family : κ → ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K target (fun e => ∑ k ∈ indices, family k e) source =
      ∑ k ∈ indices,
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
          K target (family k) source := by
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
  simp_rw [finiteInfluenceKernelUpdatedVariation_finset_sum]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Restricted-target random-scan iteration distributes exactly over every
finite superposition of variation profiles.  This is a purely linear carrier
identity; it adds no positivity, contraction, or probabilistic assumption. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_finset_sum
    {ι τ κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    [DecidableEq κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (indices : Finset κ)
    (family : κ → ι → ℝ)
    (n : ℕ)
    (source : ι) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target (fun e => ∑ k ∈ indices, family k e) n source =
      ∑ k ∈ indices,
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target (family k) n source := by
  induction n generalizing source with
  | zero => rfl
  | succ n ih =>
      simp only [finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ]
      calc
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
            K target
            (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K target (fun e => ∑ k ∈ indices, family k e) n)
            source =
          finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
            K target
            (fun e => ∑ k ∈ indices,
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                K target (family k) n e)
            source := by
          apply congrArg
            (fun profile : ι → ℝ =>
              finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
                K target profile source)
          funext e
          exact ih e
        _ = ∑ k ∈ indices,
            finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
              K target
              (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                K target (family k) n)
              source :=
          finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_finset_sum
            K target indices
            (fun k =>
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                K target (family k) n)
            source

end

end MathlibAnalytic
end MGAP4D
