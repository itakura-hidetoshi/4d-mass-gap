import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanIteration
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The total concrete plaquette link-variation indicator is exactly the number
of distinct physical links in the periodic plaquette boundary.  This statement
allows boundary-link identifications at small side lengths. -/
theorem periodicHypercubicPlaquetteObservableLinkVariation_sum_eq_card
    (n : ℕ) [NeZero n]
    (p : PeriodicHypercubicPlaquette n) :
    (∑ source : PeriodicHypercubicEdge n,
      periodicHypercubicPlaquetteObservableLinkVariation n p source) =
      ((periodicHypercubicPlaquetteEdges n p).card : ℝ) := by
  classical
  have hSupport :
      (∑ source ∈ periodicHypercubicPlaquetteEdges n p,
          periodicHypercubicPlaquetteObservableLinkVariation n p source) =
        ∑ source : PeriodicHypercubicEdge n,
          periodicHypercubicPlaquetteObservableLinkVariation n p source := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro source _hUniv hNotMem
    simp [periodicHypercubicPlaquetteObservableLinkVariation_eq, hNotMem]
  rw [← hSupport]
  simp [periodicHypercubicPlaquetteObservableLinkVariation_eq]

/-- A periodic plaquette has at most four distinct physical boundary links, so
its total unit-width variation is at most four without any side-length or
boundary-edge distinctness assumption. -/
theorem periodicHypercubicPlaquetteObservableLinkVariation_sum_le_four
    (n : ℕ) [NeZero n]
    (p : PeriodicHypercubicPlaquette n) :
    (∑ source : PeriodicHypercubicEdge n,
      periodicHypercubicPlaquetteObservableLinkVariation n p source) ≤ 4 := by
  rw [periodicHypercubicPlaquetteObservableLinkVariation_sum_eq_card]
  exact_mod_cast periodicHypercubicPlaquetteEdges_card_le_four n p

/-- The explicit centered profile of a selected periodic `Z₂` plaquette has
initial total variation at most four. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_sum_le_four
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    (∑ source : PeriodicHypercubicEdge n,
      (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
        n beta hBeta p).variation source) ≤ 4 := by
  simpa only [
    z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_variation] using
    periodicHypercubicPlaquetteObservableLinkVariation_sum_le_four n p

/-- The selected periodic `Z₂` plaquette observable therefore has a concrete
finite-volume geometric random-scan variation bound after `k` updates. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteRandomScanVariationIterate_sum_le_four_mul_pow
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (k : ℕ) :
    (∑ source : PeriodicHypercubicEdge n,
      (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
        n beta hBeta p).randomScanConditionalAverageVariationIterate
          D k source) ≤
      4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n) :=
    Fintype.card_pos_iff.mpr ⟨((fun _ => 0), 0)⟩
  have hIter :=
    (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
      n beta hBeta p)
      |>.randomScanConditionalAverageVariationIterate_sum_le_pow D hEdge k
  have hInitial :
      (∑ source : PeriodicHypercubicEdge n,
        (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
          n beta hBeta p).variation source) ≤ 4 :=
    z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_sum_le_four
      n beta hBeta p
  have hPowNonneg :
      0 ≤ (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k :=
    pow_nonneg
      (finiteOrientedConditionalAverageRandomScanContractionFactor_nonneg
        D hEdge) k
  calc
    (∑ source : PeriodicHypercubicEdge n,
      (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
        n beta hBeta p).randomScanConditionalAverageVariationIterate
          D k source) ≤
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
          ∑ source : PeriodicHypercubicEdge n,
            (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
              n beta hBeta p).variation source := hIter
    _ ≤ (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k * 4 :=
      mul_le_mul_of_nonneg_left hInitial hPowNonneg
    _ = 4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
      ring

end

end MathlibAnalytic
end MGAP4D
