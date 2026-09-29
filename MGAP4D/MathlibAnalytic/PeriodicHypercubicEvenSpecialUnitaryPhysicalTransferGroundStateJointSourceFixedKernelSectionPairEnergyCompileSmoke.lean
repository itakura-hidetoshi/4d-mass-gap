import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedKernelSectionPairEnergy

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open GroundStateSourceFixedPairEnergy

#check oldFirstMean_diagonal_eq_targetMean
#check secondMean_diagonal_eq_targetMean
#check fullDifferenceL2_diagonal_coeFn
#check fullDifferenceL2_norm_sq_eq_pairEnergy
#check responseL2_norm_sq_eq_pairEnergy_of_sourceInvariant
#check pairEnergy_sqrt_le_canonicalPinFree_mul_rms

-- At current values, the auxiliary distinguished-source choice does not change
-- the actual pair energy. The two L2 types need not be definitionally equal.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (d₁ d₂ source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C d₁ source target (C d₁) (C source)
        F hF bound hbound C 0‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C d₂ source target (C d₂) (C source)
        F hF bound hbound C 0‖ ^ 2 := by
  exact (fullDifferenceL2_norm_sq_eq_pairEnergy
    H N hN beta hbeta C d₁ source target F hF bound hbound).trans
    (fullDifferenceL2_norm_sq_eq_pairEnergy
      H N hN beta hbeta C d₂ source target F hF bound hbound).symm

end MGAP4D.MathlibAnalytic
