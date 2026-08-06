import MGAP4D.MathlibAnalytic.FiniteRealProbabilityKernelCouplingIteration
import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalRandomScanHammingContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Iterate the canonical same-weight random-scan overlap coupling from an
arbitrary exact initial coupling.  This remains an auxiliary heat-bath
coupling construction and does not identify its rate with the geometric
one-slab transfer gap. -/
noncomputable def finitePositiveWeightRandomScanOverlapCouplingIterateData
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    {leftLaw rightLaw : FiniteRealProbabilityData (ι → G)}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (n : ℕ) :
    FiniteRealCouplingData
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n leftLaw)
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n rightLaw) :=
  finiteRealProbabilityKernelCouplingIterateData
    (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
    (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
    (finitePositiveWeightRandomScanOverlapCouplingData weight hweight hCard)
    initial n

/-- The iterated canonical random-scan overlap coupling contracts expected
Hamming cost by the exact power of the one-step random-scan rate.  The rate
is the heat-bath coupling rate, not the geometric one-slab transfer rate. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanOverlapCouplingIterate_expectedHamming_le_pow_mul
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    {leftLaw rightLaw : FiniteRealProbabilityData (ι → G)}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (n : ℕ) :
    (finitePositiveWeightRandomScanOverlapCouplingIterateData
        weight hweight hCard initial n).expectedCost
      finiteProductHammingDistanceReal ≤
      finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        initial.expectedCost finiteProductHammingDistanceReal := by
  simpa only [finitePositiveWeightRandomScanOverlapCouplingIterateData] using
    finiteRealProbabilityKernelCouplingIterateData_expectedCost_le_pow_mul
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      (finitePositiveWeightRandomScanOverlapCouplingData weight hweight hCard)
      initial
      finiteProductHammingDistanceReal
      (finitePositiveWeightBidirectionalRandomScanHammingRate B)
      (finitePositiveWeightBidirectionalRandomScanHammingRate_nonneg B hCard)
      (fun left right =>
        B.randomScanOverlapCoupling_expectedHamming_le_rate_mul
          hweight hCard left right)
      n

end
end MathlibAnalytic
end MGAP4D
