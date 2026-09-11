import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalAverageRandomScanVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Uniform random-scan conditional average of a real observable over all
physical target links. -/
def FiniteOrientedLatticeWilsonSystem.randomScanConditionalAverage
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) : ℝ :=
  (Fintype.card L.Edge : ℝ)⁻¹ *
    ∑ target : L.Edge,
      L.singleLinkConditionalAverage f A target

/-- The uniformly averaged one-link Dobrushin updates bound the physical-link
oscillation of the random-scan conditional-average observable. -/
theorem finite_oriented_randomScanConditionalAverage_difference_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (f : L.Configuration → ℝ)
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    |L.randomScanConditionalAverage f A -
        L.randomScanConditionalAverage f B| ≤
      finiteOrientedConditionalAverageRandomScanVariation
        D P.variation source := by
  classical
  have hInv : 0 ≤ (Fintype.card L.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hInner :
      |(∑ target : L.Edge,
          L.singleLinkConditionalAverage f A target) -
        ∑ target : L.Edge,
          L.singleLinkConditionalAverage f B target| ≤
        ∑ target : L.Edge,
          finiteOrientedConditionalAverageUpdatedVariation
            D P.variation target source := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ target : L.Edge,
          (L.singleLinkConditionalAverage f A target -
            L.singleLinkConditionalAverage f B target)| ≤
        ∑ target : L.Edge,
          |L.singleLinkConditionalAverage f A target -
            L.singleLinkConditionalAverage f B target| :=
        finite_abs_sum_le_sum_abs Finset.univ _
      _ ≤ ∑ target : L.Edge,
          finiteOrientedConditionalAverageUpdatedVariation
            D P.variation target source := by
        apply Finset.sum_le_sum
        intro target _htarget
        exact
          (P.conditionalAverageVariationBound D target).variation_bound
            source A B hAgree
  unfold FiniteOrientedLatticeWilsonSystem.randomScanConditionalAverage
    finiteOrientedConditionalAverageRandomScanVariation
  rw [← mul_sub, abs_mul, abs_of_nonneg hInv]
  exact mul_le_mul_of_nonneg_left hInner hInv

/-- Package the random-scan conditional average as a proof-relevant link
variation bound. -/
noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationBound
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    FiniteOrientedLatticeWilsonLinkVariationBound L
      (L.randomScanConditionalAverage f) :=
  { variation := finiteOrientedConditionalAverageRandomScanVariation
      D P.variation
    variation_nonneg :=
      finiteOrientedConditionalAverageRandomScanVariation_nonneg
        D P.variation P.variation_nonneg
    variation_bound := by
      intro source A B hAgree
      exact finite_oriented_randomScanConditionalAverage_difference_abs_le
        L D f P source A B hAgree }

/-- The total variation mass of the concrete random-scan observable contracts
by the same explicit `1 - (1-c)/N` factor. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariation_sum_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    (∑ source : L.Edge,
      (P.randomScanConditionalAverageVariationBound D).variation source) ≤
      finiteOrientedConditionalAverageRandomScanContractionFactor D *
        ∑ source : L.Edge, P.variation source := by
  exact finiteOrientedConditionalAverageRandomScanVariation_sum_le
    D hEdge P.variation P.variation_nonneg

/-- The periodic `Z₂` plaquette centered profile therefore produces an explicit
link-variation certificate for its random-scan conditional average. -/
noncomputable def z2PeriodicHypercubicOrientedPlaquetteRandomScanVariationBound
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)) :
    FiniteOrientedLatticeWilsonLinkVariationBound
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.randomScanConditionalAverage
          ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            |>.plaquetteObservable p)) :=
  (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
    n beta hBeta p).randomScanConditionalAverageVariationBound D

end

end MathlibAnalytic
end MGAP4D
