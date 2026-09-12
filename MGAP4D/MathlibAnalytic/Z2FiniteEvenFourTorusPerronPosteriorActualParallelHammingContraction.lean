import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualParallelCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- The coefficient of the actual bidirectional matrix is exactly the common
row/column barrier selected by the high-temperature continuation family. -/
@[simp] theorem toBidirectionalDobrushinData_coefficient
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (C.toBidirectionalDobrushinData
      β hβ hβCutoff H environment).coefficient =
      (C.continuationFamily β hβ hβCutoff).barrier := by
  rfl

/-- The actual contraction factor is nonnegative. -/
theorem parallelHammingContractionFactor_nonneg
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff) :
    0 ≤ (2 : ℝ)⁻¹ *
      (C.continuationFamily β hβ hβCutoff).barrier := by
  have h :=
    (C.toBidirectionalDobrushinData
      β hβ hβCutoff 0 (fun _ => 1)).halfCoefficient_nonneg
  simpa using h

/-- The actual contraction factor is strictly below one. -/
theorem parallelHammingContractionFactor_lt_one
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff) :
    (2 : ℝ)⁻¹ *
      (C.continuationFamily β hβ hβCutoff).barrier < 1 := by
  have h :=
    (C.toBidirectionalDobrushinData
      β hβ hβCutoff 0 (fun _ => 1)).halfCoefficient_lt_one
  simpa using h

/-- Arbitrary hidden input slices are contracted in expected coordinate
Hamming disagreement by one half of the common actual row/column barrier.
This is the finite path-coupling extension of the single-link estimate. -/
theorem parallelTotalCoordinateDisagreement_le_halfBarrier_mul_hamming
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        leftHidden rightHidden ≤
      ((2 : ℝ)⁻¹ *
        (C.continuationFamily β hβ hβCutoff).barrier) *
          finiteProductHammingDistanceReal leftHidden rightHidden := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have hContraction :=
    B.parallelTotalCoordinateDisagreement_le_halfCoefficient_mul_hamming
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      leftHidden rightHidden
  simpa [B] using hContraction

/-- The same arbitrary-slice contraction stated directly for the canonical
all-volume continuation package. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualParallelTotalCoordinateDisagreement_le
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
            β hβ hβCutoff H environment)
        leftHidden rightHidden ≤
      ((2 : ℝ)⁻¹ *
        ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).continuationFamily
            β hβ hβCutoff).barrier) *
          finiteProductHammingDistanceReal leftHidden rightHidden := by
  exact
    parallelTotalCoordinateDisagreement_le_halfBarrier_mul_hamming
      (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
        energyIdentity energyNontrivial hEnergy)
      β hβ hβCutoff H environment leftHidden rightHidden

end Z2PerronPosteriorActualHighTemperatureContinuationData

end

end MathlibAnalytic
end MGAP4D
