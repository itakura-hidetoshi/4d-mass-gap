import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanOverlapCouplingIteration
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingKantorovichWeakDuality
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingHammingCardinality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The normalized global Gibbs law associated with a strictly positive finite
product weight, packaged as finite real probability data. -/
noncomputable def finitePositiveWeightGlobalProbabilityData
    {ι G : Type} [DecidableEq ι] [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A) :
    FiniteRealProbabilityData (ι → G) :=
  { probability := finitePositiveWeightGlobalProbability weight
    probability_nonneg :=
      finitePositiveWeightGlobalProbability_nonneg weight hweight
    probability_sum_eq_one :=
      finitePositiveWeightGlobalProbability_sum_eq_one weight hweight }

/-- One exact random-scan pushforward leaves the normalized global Gibbs law
pointwise unchanged. -/
theorem finitePositiveWeightGlobalProbabilityData_randomScan_pushforward_probability
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (output : ι → G) :
    (finiteRealProbabilityKernelPushforwardData
      (finitePositiveWeightGlobalProbabilityData weight hweight)
      (finitePositiveWeightRandomScanProbabilityData
        weight hweight hCard)).probability output =
      (finitePositiveWeightGlobalProbabilityData
        weight hweight).probability output := by
  simpa [finiteRealProbabilityKernelPushforwardData,
    finiteRealProbabilityMixtureData,
    finitePositiveWeightGlobalProbabilityData,
    finitePositiveWeightRandomScanProbabilityData] using
      finitePositiveWeightGlobalProbability_randomScan_stationary
        weight hweight hCard output

/-- Every finite iterate of the exact random-scan kernel leaves the normalized
Gibbs law pointwise unchanged. -/
theorem finitePositiveWeightGlobalProbabilityData_randomScan_iterate_probability
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (n : ℕ)
    (output : ι → G) :
    (finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      n
      (finitePositiveWeightGlobalProbabilityData weight hweight)).probability
        output =
      (finitePositiveWeightGlobalProbabilityData
        weight hweight).probability output := by
  induction n generalizing output with
  | zero =>
      rfl
  | succ n ih =>
      change
        (finiteRealProbabilityKernelPushforwardData
          (finiteRealProbabilityKernelIterateData
            (finitePositiveWeightRandomScanProbabilityData
              weight hweight hCard)
            n
            (finitePositiveWeightGlobalProbabilityData weight hweight))
          (finitePositiveWeightRandomScanProbabilityData
            weight hweight hCard)).probability output = _
      unfold finiteRealProbabilityKernelPushforwardData
        finiteRealProbabilityMixtureData
      calc
        (∑ input : ι → G,
          (finiteRealProbabilityKernelIterateData
            (finitePositiveWeightRandomScanProbabilityData
              weight hweight hCard)
            n
            (finitePositiveWeightGlobalProbabilityData
              weight hweight)).probability input *
          (finitePositiveWeightRandomScanProbabilityData
            weight hweight hCard input).probability output) =
            ∑ input : ι → G,
              (finitePositiveWeightGlobalProbabilityData
                weight hweight).probability input *
              (finitePositiveWeightRandomScanProbabilityData
                weight hweight hCard input).probability output := by
          apply Finset.sum_congr rfl
          intro input _hinput
          rw [ih input]
        _ = (finitePositiveWeightGlobalProbabilityData
              weight hweight).probability output :=
          finitePositiveWeightGlobalProbabilityData_randomScan_pushforward_probability
            weight hweight hCard output

/-- Expectations under every random-scan iterate of the Gibbs law equal the
normalized global Gibbs expectation. -/
theorem finitePositiveWeightGlobalProbabilityData_randomScan_iterate_expectation_eq_globalExpectation
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (n : ℕ)
    (f : (ι → G) → ℝ) :
    (finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      n
      (finitePositiveWeightGlobalProbabilityData weight hweight)).expectation f =
      finitePositiveWeightGlobalExpectation weight f := by
  calc
    (finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      n
      (finitePositiveWeightGlobalProbabilityData weight hweight)).expectation f =
        (finitePositiveWeightGlobalProbabilityData
          weight hweight).expectation f := by
      exact FiniteRealProbabilityData.expectation_eq_of_probability_eq
        _ _
        (finitePositiveWeightGlobalProbabilityData_randomScan_iterate_probability
          weight hweight hCard n)
        f
    _ = finitePositiveWeightGlobalExpectation weight f := by
      rfl

/-- Iterate the canonical same-weight random-scan overlap coupling from an
arbitrary finite initial law to the stationary normalized Gibbs law. -/
noncomputable def finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → G))
    (n : ℕ) :
    FiniteRealCouplingData
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw)
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n (finitePositiveWeightGlobalProbabilityData weight hweight)) :=
  finitePositiveWeightRandomScanOverlapCouplingIterateData
    weight hweight hCard
    (initialLaw.overlapCouplingData
      (finitePositiveWeightGlobalProbabilityData weight hweight))
    n

/-- Quantitative expected-Hamming convergence from an arbitrary finite initial
law to the stationary Gibbs orbit, retaining the exact initial overlap-coupling
cost. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_initial
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → G))
    (n : ℕ) :
    (finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
      weight hweight hCard initialLaw n).expectedCost
        finiteProductHammingDistanceReal ≤
      finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        (initialLaw.overlapCouplingData
          (finitePositiveWeightGlobalProbabilityData
            weight hweight)).expectedCost
          finiteProductHammingDistanceReal := by
  simpa only [
    finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData] using
      B.randomScanOverlapCouplingIterate_expectedHamming_le_pow_mul
        hweight hCard
        (initialLaw.overlapCouplingData
          (finitePositiveWeightGlobalProbabilityData weight hweight))
        n

/-- Uniform cardinality form of finite random-scan expected-Hamming mixing. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_card
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → G))
    (n : ℕ) :
    (finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
      weight hweight hCard initialLaw n).expectedCost
        finiteProductHammingDistanceReal ≤
      finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        (Fintype.card ι : ℝ) := by
  calc
    (finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
      weight hweight hCard initialLaw n).expectedCost
        finiteProductHammingDistanceReal ≤
      finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        (initialLaw.overlapCouplingData
          (finitePositiveWeightGlobalProbabilityData
            weight hweight)).expectedCost
          finiteProductHammingDistanceReal :=
      B.randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_initial
        hweight hCard initialLaw n
    _ ≤ finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        (Fintype.card ι : ℝ) :=
      mul_le_mul_of_nonneg_left
        ((initialLaw.overlapCouplingData
          (finitePositiveWeightGlobalProbabilityData
            weight hweight)).expectedFiniteProductHamming_le_card)
        (pow_nonneg
          (finitePositiveWeightBidirectionalRandomScanHammingRate_nonneg
            B hCard)
          n)

/-- Every real Hamming `1`-Lipschitz observable converges from an arbitrary
finite initial law to its stationary Gibbs expectation at the explicit
random-scan heat-bath rate. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanIterate_expectation_sub_global_abs_le_pow_mul_card
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → G))
    (n : ℕ)
    (f : (ι → G) → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    |(finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw).expectation f -
      finitePositiveWeightGlobalExpectation weight f| ≤
      finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        (Fintype.card ι : ℝ) := by
  let C := finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
    weight hweight hCard initialLaw n
  have hDual := C.expectation_difference_abs_le_expectedCost
    finiteProductHammingDistanceReal f hLipschitz
  rw [finitePositiveWeightGlobalProbabilityData_randomScan_iterate_expectation_eq_globalExpectation
    weight hweight hCard n f] at hDual
  exact hDual.trans
    (B.randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_card
      hweight hCard initialLaw n)

end
end MathlibAnalytic
end MGAP4D
