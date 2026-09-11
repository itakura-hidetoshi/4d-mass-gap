import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelObservableResponseMatrix
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The target-summed column of the unit observable-response matrix is bounded
by the existing finite bidirectional response coefficient.  This is the
coordinate-resolved form needed for a direct parallel variation estimate. -/
theorem finiteInfluenceKernelObservableResponseEntry_columnSum_le
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ target : ι,
        finiteInfluenceKernelRowSum K target ≤ rowCoefficient)
    (envelopeMagnitude : ℝ)
    (hEnvelopeMagnitude : 0 ≤ envelopeMagnitude)
    (iterations : ℕ)
    (source : ι) :
    (∑ target : ι,
      finiteInfluenceKernelObservableResponseEntry
        K
        (finiteInfluenceKernelSingletonVariation
          envelopeMagnitude target)
        iterations source) ≤
      finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
        ι iterations rowCoefficient envelopeMagnitude 1 := by
  have hSingletonNonneg :
      ∀ e : ι,
        0 ≤ finiteInfluenceKernelSingletonVariation 1 source e := by
    intro e
    unfold finiteInfluenceKernelSingletonVariation
    split <;> norm_num
  have hPartial :=
    finiteInfluenceKernelPartialSource_singletonEnvelope_sum_target_le
      K hCard rowCoefficient hRowNonneg hRowSum
      envelopeMagnitude hEnvelopeMagnitude
      (finiteInfluenceKernelSingletonVariation 1 source)
      hSingletonNonneg iterations
  rw [finiteInfluenceKernelSingletonVariation_total 1 source] at hPartial
  have hTerminal :=
    finiteInfluenceKernelSingletonVariation_iterate_total_sum_target_le
      K hCard rowCoefficient hRowNonneg hRowSum
      1 (by norm_num) source iterations
  have hTerminalScaled :
      2 *
          (∑ target : ι,
            finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                K (finiteInfluenceKernelSingletonVariation 1 source)
                iterations)) ≤
        2 * (Fintype.card ι : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              ι rowCoefficient ^ iterations * 1) := by
    calc
      2 *
          (∑ target : ι,
            finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                K (finiteInfluenceKernelSingletonVariation 1 source)
                iterations)) ≤
        2 *
          ((Fintype.card ι : ℝ) *
            (finiteInfluenceKernelReciprocalRandomScanRate
                ι rowCoefficient ^ iterations * 1)) :=
        mul_le_mul_of_nonneg_left hTerminal (by norm_num)
      _ = 2 * (Fintype.card ι : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              ι rowCoefficient ^ iterations * 1) := by ring
  unfold finiteInfluenceKernelObservableResponseEntry
    finiteInfluenceKernelObservableResponse
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply (add_le_add hPartial hTerminalScaled).trans_eq
  unfold finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
  ring

end

end MathlibAnalytic
end MGAP4D
