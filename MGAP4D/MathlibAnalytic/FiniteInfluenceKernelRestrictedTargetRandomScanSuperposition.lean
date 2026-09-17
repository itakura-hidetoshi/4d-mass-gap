import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScan
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

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
  rfl

end

end MathlibAnalytic
end MGAP4D
