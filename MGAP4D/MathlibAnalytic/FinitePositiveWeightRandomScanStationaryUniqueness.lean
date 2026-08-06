import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanStationaryMixing
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

namespace FiniteRealProbabilityData

/-- Pointwise stationarity of a finite law for a finite probability kernel. -/
def IsStationaryForKernel
    {G : Type} [Fintype G]
    (law : FiniteRealProbabilityData G)
    (kernel : G → FiniteRealProbabilityData G) : Prop :=
  ∀ output : G,
    (finiteRealProbabilityKernelPushforwardData law kernel).probability output =
      law.probability output

/-- A pointwise stationary finite law is unchanged by every finite kernel
iterate. -/
theorem kernelIterate_probability_eq_of_isStationaryForKernel
    {G : Type} [Fintype G]
    (law : FiniteRealProbabilityData G)
    (kernel : G → FiniteRealProbabilityData G)
    (hStationary : law.IsStationaryForKernel kernel)
    (n : ℕ)
    (output : G) :
    (finiteRealProbabilityKernelIterateData kernel n law).probability output =
      law.probability output := by
  induction n generalizing output with
  | zero =>
      rfl
  | succ n ih =>
      change
        (finiteRealProbabilityKernelPushforwardData
          (finiteRealProbabilityKernelIterateData kernel n law)
          kernel).probability output = _
      unfold finiteRealProbabilityKernelPushforwardData
        finiteRealProbabilityMixtureData
      calc
        (∑ input : G,
          (finiteRealProbabilityKernelIterateData
            kernel n law).probability input *
            (kernel input).probability output) =
          ∑ input : G,
            law.probability input * (kernel input).probability output := by
              apply Finset.sum_congr rfl
              intro input _hinput
              rw [ih input]
        _ = law.probability output := hStationary output

/-- Expectations under every finite kernel iterate of a pointwise stationary
law equal the original expectation. -/
theorem kernelIterate_expectation_eq_of_isStationaryForKernel
    {G : Type} [Fintype G]
    (law : FiniteRealProbabilityData G)
    (kernel : G → FiniteRealProbabilityData G)
    (hStationary : law.IsStationaryForKernel kernel)
    (n : ℕ)
    (f : G → ℝ) :
    (finiteRealProbabilityKernelIterateData kernel n law).expectation f =
      law.expectation f := by
  exact FiniteRealProbabilityData.expectation_eq_of_probability_eq
    _ _
    (law.kernelIterate_probability_eq_of_isStationaryForKernel
      kernel hStationary n)
    f

end FiniteRealProbabilityData

/-- The singleton indicator of any finite product configuration is Hamming
`1`-Lipschitz. -/
theorem finiteProductSingletonIndicator_hammingOneLipschitz
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (target : ι → G) :
    FiniteProductHammingOneLipschitz
      (fun A : ι → G => if A = target then 1 else 0) := by
  intro A B
  by_cases hAB : A = B
  · subst B
    simp
  · have hExists : ∃ source : ι, A source ≠ B source := by
      by_contra hNo
      apply hAB
      funext source
      by_contra hNe
      exact hNo ⟨source, hNe⟩
    obtain ⟨source, hSource⟩ := hExists
    have hMem :
        source ∈ finiteProductDisagreementFinset A B := by
      simp [finiteProductDisagreementFinset, hSource]
    have hOneLeCard :
        1 ≤ (finiteProductDisagreementFinset A B).card :=
      Finset.one_le_card.mpr ⟨source, hMem⟩
    have hOneLeHamming :
        (1 : ℝ) ≤ finiteProductHammingDistanceReal A B := by
      unfold finiteProductHammingDistanceReal
      exact_mod_cast hOneLeCard
    have hIndicatorLeOne :
        |(if A = target then (1 : ℝ) else 0) -
          (if B = target then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    exact hIndicatorLeOne.trans hOneLeHamming

/-- Under a strict bidirectional random-scan contraction, every pointwise
stationary finite law has the same expectation as the normalized Gibbs law on
all real Hamming `1`-Lipschitz observables.  This is an auxiliary heat-bath
uniqueness theorem and does not identify its rate with a geometric one-slab
transfer gap. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScan_stationary_expectation_eq_globalExpectation
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (law : FiniteRealProbabilityData (ι → G))
    (hStationary :
      law.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          weight hweight hCard))
    (f : (ι → G) → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    law.expectation f = finitePositiveWeightGlobalExpectation weight f := by
  let rate := finitePositiveWeightBidirectionalRandomScanHammingRate B
  let discrepancy :=
    |law.expectation f - finitePositiveWeightGlobalExpectation weight f|
  have hRateNonneg : 0 ≤ rate := by
    exact finitePositiveWeightBidirectionalRandomScanHammingRate_nonneg B hCard
  have hRateLtOne : rate < 1 := by
    exact finitePositiveWeightBidirectionalRandomScanHammingRate_lt_one B hCard
  have hBound (n : ℕ) :
      discrepancy ≤ rate ^ n * (Fintype.card ι : ℝ) := by
    have hMix :=
      B.randomScanIterate_expectation_sub_global_abs_le_pow_mul_card
        hweight hCard law n f hLipschitz
    rw [law.kernelIterate_expectation_eq_of_isStationaryForKernel
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      hStationary n f] at hMix
    exact hMix
  have hEnvelope :
      Tendsto
        (fun n : ℕ => rate ^ n * (Fintype.card ι : ℝ))
        atTop (nhds 0) := by
    have hPow : Tendsto (fun n : ℕ => rate ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hRateNonneg hRateLtOne
    simpa using hPow.mul_const (Fintype.card ι : ℝ)
  have hDiscrepancyNonpos : discrepancy ≤ 0 := by
    by_contra hNot
    have hDiscrepancyPos : 0 < discrepancy := lt_of_not_ge hNot
    have hEventually :
        ∀ᶠ n in atTop,
          rate ^ n * (Fintype.card ι : ℝ) < discrepancy :=
      (tendsto_order.1 hEnvelope).2 discrepancy hDiscrepancyPos
    obtain ⟨n, hn⟩ := hEventually.exists
    exact (not_lt_of_ge (hBound n)) hn
  have hDiscrepancyZero : discrepancy = 0 :=
    le_antisymm hDiscrepancyNonpos (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hDiscrepancyZero)

/-- Every pointwise stationary finite law for the strict random-scan kernel is
pointwise equal to the normalized Gibbs law. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScan_stationary_probability_eq_globalProbability
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (law : FiniteRealProbabilityData (ι → G))
    (hStationary :
      law.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          weight hweight hCard))
    (configuration : ι → G) :
    law.probability configuration =
      finitePositiveWeightGlobalProbability weight configuration := by
  have hExpectation :=
    B.randomScan_stationary_expectation_eq_globalExpectation
      hweight hCard law hStationary
      (fun A : ι → G => if A = configuration then 1 else 0)
      (finiteProductSingletonIndicator_hammingOneLipschitz configuration)
  simpa [FiniteRealProbabilityData.expectation,
    finitePositiveWeightGlobalExpectation] using hExpectation

/-- The normalized Gibbs law is the unique finite real probability data
structure stationary for the strict random-scan heat-bath kernel. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScan_stationary_law_eq_globalProbabilityData
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (law : FiniteRealProbabilityData (ι → G))
    (hStationary :
      law.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          weight hweight hCard)) :
    law = finitePositiveWeightGlobalProbabilityData weight hweight := by
  have hProbability :
      ∀ configuration : ι → G,
        law.probability configuration =
          (finitePositiveWeightGlobalProbabilityData
            weight hweight).probability configuration := by
    intro configuration
    exact B.randomScan_stationary_probability_eq_globalProbability
      hweight hCard law hStationary configuration
  cases law with
  | mk probability probability_nonneg probability_sum_eq_one =>
      have hFunction :
          probability = finitePositiveWeightGlobalProbability weight :=
        funext hProbability
      subst probability
      rfl

end
end MathlibAnalytic
end MGAP4D
