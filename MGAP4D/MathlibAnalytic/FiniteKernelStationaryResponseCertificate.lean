import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- State-space-independent stationary-response interface over a finite
coordinate set.  The local state space and the construction of the
expectation discrepancy are intentionally absent: downstream kernel algebra
only needs a common source bound, declared variation profiles, and the
finite-step kernel residual inequality.

This certificate can therefore be supplied either by the existing finite
positive-weight theory or, separately, by a continuous-state comparison once
such a construction is proved. -/
structure FiniteKernelStationaryResponseFamilyCertificate
    {ι κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : κ → ι → ℝ) where
  discrepancy : κ → ℝ
  sourceBound : ι → ℝ
  sourceBound_nonneg : ∀ e : ι, 0 ≤ sourceBound e
  variation_nonneg : ∀ k : κ, ∀ e : ι, 0 ≤ variation k e
  discrepancy_le_kernelResidual :
    ∀ (k : κ)
      (sourceEnvelope : ι → ℝ),
      (∀ e : ι, 0 ≤ sourceEnvelope e) →
      (∀ e : ι, sourceBound e ≤ sourceEnvelope e) →
      ∀ n : ℕ,
        discrepancy k ≤
          finiteInfluenceKernelPartialSource
              K sourceEnvelope (variation k) n +
            2 * finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                K (variation k) n)

/-- Every genuine finite positive-weight stationary non-strict comparison
maps canonically to the state-space-independent kernel-response interface once
its right influence is dominated by a chosen nonnegative kernel.

No converse is asserted: the certificate deliberately forgets the finite
state space, weights, stationarity witnesses, and concrete update operators. -/
noncomputable def
    FinitePositiveWeightStationaryNonstrictComparisonData.toKernelStationaryResponseFamilyCertificate
    {ι κ G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight : (ι → G) → ℝ}
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (f : κ → ((ι → G) → ℝ))
    (P : ∀ k : κ, FiniteProductVariationBound (f k))
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        C.rightInfluence K.influence) :
    FiniteKernelStationaryResponseFamilyCertificate
      K (fun k => (P k).variation) := by
  classical
  refine
    { discrepancy := fun k => C.expectationDiscrepancy (f k)
      sourceBound := C.sourceBound
      sourceBound_nonneg := C.sourceBound_nonneg
      variation_nonneg := fun k => (P k).variation_nonneg
      discrepancy_le_kernelResidual := ?_ }
  intro k sourceEnvelope hEnvelopeNonneg hEnvelope n
  have hPartial :=
    C.partialStationarySource_le_kernel
      (P k) K hDomination sourceEnvelope
      hEnvelopeNonneg hEnvelope n
  have hTerminal :
      finiteProductVariationTotal
          (C.rightRandomScanIterateVariationBound (P k) n).variation ≤
        finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            K (P k).variation n) := by
    unfold finiteProductVariationTotal
    apply Finset.sum_le_sum
    intro e _he
    rw [C.rightRandomScanIterateVariation_eq (P k) n]
    exact
      finitePositiveWeightNonstrictRandomScanVariationIterate_le_kernel
        C.rightInfluence K hDomination
        (P k).variation (P k).variation_nonneg n e
  have hFinite :=
    C.expectationDiscrepancy_le_partialSource_add_two_mul_terminalVariation
      (P k) n
  exact hFinite.trans
    (add_le_add hPartial
      (mul_le_mul_of_nonneg_left hTerminal (by norm_num)))

@[simp] theorem
    FinitePositiveWeightStationaryNonstrictComparisonData.toKernelStationaryResponseFamilyCertificate_discrepancy
    {ι κ G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight : (ι → G) → ℝ}
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (f : κ → ((ι → G) → ℝ))
    (P : ∀ k : κ, FiniteProductVariationBound (f k))
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        C.rightInfluence K.influence)
    (k : κ) :
    (C.toKernelStationaryResponseFamilyCertificate
      f P K hDomination).discrepancy k =
      C.expectationDiscrepancy (f k) := by
  rfl

@[simp] theorem
    FinitePositiveWeightStationaryNonstrictComparisonData.toKernelStationaryResponseFamilyCertificate_sourceBound
    {ι κ G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight : (ι → G) → ℝ}
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (f : κ → ((ι → G) → ℝ))
    (P : ∀ k : κ, FiniteProductVariationBound (f k))
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        C.rightInfluence K.influence)
    (e : ι) :
    (C.toKernelStationaryResponseFamilyCertificate
      f P K hDomination).sourceBound e = C.sourceBound e := by
  rfl

end

end MathlibAnalytic
end MGAP4D
