import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparisonGeometricResidual
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedBoundaryStationaryComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The remaining actual input for stationary boundary comparison: a strict
Dobrushin matrix for the encoded augmented Gibbs weight at the replaced upper
boundary.  Its existence is not asserted by this structure. -/
structure Z2AugmentedBoundaryStationaryDobrushinData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) where
  rightDobrushin :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryWeight
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g))

namespace Z2AugmentedBoundaryStationaryDobrushinData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 ≤ β}
  {hEnergy : energyIdentity ≤ energyNontrivial}
  {source : FiniteEvenFourTorusSpatialLink H}
  {g : Z2Gauge}
  {B : FiniteEvenFourTorusZ2SliceConfiguration H}

/-- Convert the actual right-boundary Dobrushin input and the proved local
three-coordinate boundary source into the generic stationary comparison
package. -/
noncomputable def toGeneric
    (D : Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B) :
    FinitePositiveWeightStationaryRandomScanComparisonData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryWeight
        H β energyIdentity energyNontrivial hβ hEnergy B)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryWeight
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g)) :=
  { leftWeight_pos := fun X =>
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy B X
    rightWeight_pos := fun X =>
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g) X
    coordinateCard_pos :=
      finiteEvenFourTorusZ2AugmentedCoordinate_card_pos H
    sourceBound :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
        H β energyIdentity energyNontrivial source
    conditionalCrossL1_le_sourceBound := fun X target =>
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_sourceBound
        H β energyIdentity energyNontrivial hβ hEnergy source g B X target
    rightDobrushin := D.rightDobrushin }

/-- The generic source functional is exactly the proved actual
three-coordinate boundary error. -/
theorem toGeneric_sourceError_eq_threeCoordinateError
    (D : Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B)
    (variation : FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ) :
    D.toGeneric.sourceError variation =
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryThreeCoordinateError
        H β energyIdentity energyNontrivial source variation := by
  unfold toGeneric
    FinitePositiveWeightStationaryRandomScanComparisonData.sourceError
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryThreeCoordinateError
  rw [
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_pairing_eq
      H β energyIdentity energyNontrivial source variation]

/-- Accumulated actual three-coordinate source through the first `n` exact
right-boundary Gibbs random-scan variation profiles. -/
noncomputable def partialThreeCoordinateSource
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (D : Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B) :
    ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      partialThreeCoordinateSource P D n +
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryThreeCoordinateError
          H β energyIdentity energyNontrivial source
          (FinitePositiveWeightStationaryRandomScanComparisonData.rightRandomScanIterateVariationBound
            P D.toGeneric n).variation

@[simp] theorem partialThreeCoordinateSource_zero
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (D : Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B) :
    partialThreeCoordinateSource P D 0 = 0 :=
  rfl

@[simp] theorem partialThreeCoordinateSource_succ
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (D : Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B)
    (n : ℕ) :
    partialThreeCoordinateSource P D (n + 1) =
      partialThreeCoordinateSource P D n +
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryThreeCoordinateError
          H β energyIdentity energyNontrivial source
          (FinitePositiveWeightStationaryRandomScanComparisonData.rightRandomScanIterateVariationBound
            P D.toGeneric n).variation :=
  rfl

/-- The actual recursive three-coordinate source is the generic partial
stationary source after source-functional specialization. -/
theorem partialThreeCoordinateSource_eq_partialStationarySource
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (D : Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B)
    (n : ℕ) :
    partialThreeCoordinateSource P D n =
      FinitePositiveWeightStationaryRandomScanComparisonData.partialStationarySource
        P D.toGeneric n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [partialThreeCoordinateSource_succ,
        FinitePositiveWeightStationaryRandomScanComparisonData.partialStationarySource_succ,
        ih, D.toGeneric_sourceError_eq_threeCoordinateError]

/-- Actual stationary upper-boundary comparison with exact accumulated
three-coordinate source and a geometric right-boundary Dobrushin residual.
The auxiliary random-scan operator is not identified with the geometric
one-slab Doob transition. -/
theorem boundaryExpectation_difference_abs_le_partialSource_add_geometricResidual
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (D : Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B)
    (n : ℕ) :
    |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
          H β energyIdentity energyNontrivial hβ hEnergy B f -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g) f| ≤
      partialThreeCoordinateSource P D n +
        2 * finitePositiveWeightDobrushinRandomScanRate D.rightDobrushin ^ n *
          finiteProductVariationTotal P.variation := by
  have hGeneric :=
    FinitePositiveWeightStationaryRandomScanComparisonData.expectationDiscrepancy_le_partialSource_add_geometricResidual
      P D.toGeneric n
  rw [partialThreeCoordinateSource_eq_partialStationarySource P D n]
  simpa [FinitePositiveWeightStationaryRandomScanComparisonData.expectationDiscrepancy,
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation,
    toGeneric] using hGeneric

end Z2AugmentedBoundaryStationaryDobrushinData

end

end MathlibAnalytic
end MGAP4D
