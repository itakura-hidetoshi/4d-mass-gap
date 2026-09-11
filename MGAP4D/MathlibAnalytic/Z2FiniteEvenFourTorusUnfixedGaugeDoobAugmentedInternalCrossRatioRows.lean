import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedBoundaryStationaryGeometricResidual
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedInternalFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Augmented configurations differing only at a temporal coordinate have the
same decoded lower slice. -/
theorem finiteEvenFourTorusZ2AugmentedLowerSlice_eq_of_agreeOff_temporal
    (H : ℕ)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (source : FiniteEvenFourTorusSpatialVertex H)
    (hAgree : FiniteProductAgreeOff X Y (Sum.inl source)) :
    finiteEvenFourTorusZ2AugmentedLowerSlice H X =
      finiteEvenFourTorusZ2AugmentedLowerSlice H Y := by
  funext link
  exact hAgree (Sum.inr link) (by simp)

/-- Agreement away from one encoded lower coordinate descends to agreement
away from the corresponding lower-slice link. -/
theorem finiteEvenFourTorusZ2AugmentedLowerSlice_agreeOff_of_agreeOff_lower
    (H : ℕ)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff X Y (Sum.inr source)) :
    FiniteProductAgreeOff
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Y)
      source := by
  intro link hLink
  exact hAgree (Sum.inr link) (by simpa using hLink)

/-- If the environment perturbation is temporal, the lower Perron factor has
exact cross ratio one at every lower-link target. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronLowerCrossRatio_one_of_agreeOff_temporal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source : FiniteEvenFourTorusSpatialVertex H)
    (hAgree : FiniteProductAgreeOff X Y (Sum.inl source)) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H X)
      (finiteEvenFourTorusZ2AugmentedLowerSlice H Y)
      target 1 := by
  have hSlice :=
    finiteEvenFourTorusZ2AugmentedLowerSlice_eq_of_agreeOff_temporal
      H X Y source hAgree
  rw [hSlice]
  intro u v
  simp

/-- Rowwise cross-ratio inputs for the actual encoded augmented weight.
Temporal targets and the local part of lower targets are kept separate from
the lower Perron contribution. -/
structure Z2AugmentedInternalCrossRatioRowsData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) where
  temporalLocalRadius :
    FiniteEvenFourTorusSpatialVertex H →
      FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ
  temporalLocalRadius_nonneg :
    ∀ target source, 0 ≤ temporalLocalRadius target source
  temporalLocalCrossRatio :
    ∀ (target : FiniteEvenFourTorusSpatialVertex H)
      (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
      (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H),
      Sum.inl target ≠ source →
      FiniteProductAgreeOff X Y source →
        FinitePositiveWeightSingleSiteCrossRatioBound
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
            H β energyIdentity energyNontrivial B)
          X Y (Sum.inl target)
          (Real.exp (temporalLocalRadius target source))
  lowerLocalRadius :
    FiniteEvenFourTorusSpatialLink H →
      FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ
  lowerLocalRadius_nonneg :
    ∀ target source, 0 ≤ lowerLocalRadius target source
  lowerLocalCrossRatio :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
      (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H),
      Sum.inr target ≠ source →
      FiniteProductAgreeOff X Y source →
        FinitePositiveWeightSingleSiteCrossRatioBound
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedLocalFactor
            H β energyIdentity energyNontrivial B)
          X Y (Sum.inr target)
          (Real.exp (lowerLocalRadius target source))
  lowerPerronRadius :
    FiniteEvenFourTorusSpatialLink H →
      FiniteEvenFourTorusSpatialLink H → ℝ
  lowerPerronRadius_nonneg :
    ∀ target source, 0 ≤ lowerPerronRadius target source
  lowerPerronCrossRatio :
    ∀ (target source : FiniteEvenFourTorusSpatialLink H)
      (A C : FiniteEvenFourTorusZ2SliceConfiguration H),
      target ≠ source →
      FiniteProductAgreeOff A C source →
        FinitePositiveWeightSingleSiteCrossRatioBound
          (fun Z : FiniteEvenFourTorusZ2SliceConfiguration H =>
            finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
              H β energyIdentity energyNontrivial hβ hEnergy Z)
          A C target (Real.exp (lowerPerronRadius target source))

namespace Z2AugmentedInternalCrossRatioRowsData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 ≤ β}
  {hEnergy : energyIdentity ≤ energyNontrivial}
  {B : FiniteEvenFourTorusZ2SliceConfiguration H}

/-- The assembled actual augmented cross-ratio radius.  The Perron radius is
zero on temporal-source lower rows and is added only on lower/lower rows. -/
def assembledRadius
    (D : Z2AugmentedInternalCrossRatioRowsData
      H β energyIdentity energyNontrivial hβ hEnergy B)
    (target source : FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ :=
  match target, source with
  | Sum.inl targetVertex, sourceCoordinate =>
      D.temporalLocalRadius targetVertex sourceCoordinate
  | Sum.inr targetLink, Sum.inl sourceVertex =>
      D.lowerLocalRadius targetLink (Sum.inl sourceVertex)
  | Sum.inr targetLink, Sum.inr sourceLink =>
      D.lowerLocalRadius targetLink (Sum.inr sourceLink) +
        D.lowerPerronRadius targetLink sourceLink

/-- Every assembled radius is nonnegative. -/
theorem assembledRadius_nonneg
    (D : Z2AugmentedInternalCrossRatioRowsData
      H β energyIdentity energyNontrivial hβ hEnergy B)
    (target source : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤ D.assembledRadius target source := by
  cases target with
  | inl targetVertex =>
      exact D.temporalLocalRadius_nonneg targetVertex source
  | inr targetLink =>
      cases source with
      | inl sourceVertex =>
          exact D.lowerLocalRadius_nonneg targetLink (Sum.inl sourceVertex)
      | inr sourceLink =>
          exact add_nonneg
            (D.lowerLocalRadius_nonneg targetLink (Sum.inr sourceLink))
            (D.lowerPerronRadius_nonneg targetLink sourceLink)

/-- The assembled row radius controls the full encoded augmented weight at
every off-diagonal target/source pair. -/
theorem assembledCrossRatioBound
    (D : Z2AugmentedInternalCrossRatioRowsData
      H β energyIdentity energyNontrivial hβ hEnergy B)
    (target source : FiniteEvenFourTorusZ2AugmentedCoordinate H)
    (X Y : FiniteEvenFourTorusZ2AugmentedConfiguration H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff X Y source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B)
      X Y target (Real.exp (D.assembledRadius target source)) := by
  cases target with
  | inl targetVertex =>
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_temporalCrossRatio_of_local
          H β energyIdentity energyNontrivial hβ hEnergy B X Y
          targetVertex
          (Real.exp (D.temporalLocalRadius targetVertex source))
          (le_of_lt (Real.exp_pos _))
          (D.temporalLocalCrossRatio
            targetVertex source X Y hNe hAgree)
  | inr targetLink =>
      cases source with
      | inl sourceVertex =>
          have hLocal :=
            D.lowerLocalCrossRatio targetLink (Sum.inl sourceVertex)
              X Y hNe hAgree
          have hPerron :=
            finiteEvenFourTorusZ2UnfixedGaugePerronLowerCrossRatio_one_of_agreeOff_temporal
              H β energyIdentity energyNontrivial hβ hEnergy
              X Y targetLink sourceVertex hAgree
          simpa [assembledRadius] using
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_lowerCrossRatio_of_local_mul_perron
              H β energyIdentity energyNontrivial hβ hEnergy B X Y
              targetLink
              (Real.exp
                (D.lowerLocalRadius targetLink (Sum.inl sourceVertex)))
              1 (le_of_lt (Real.exp_pos _)) (by norm_num)
              hLocal hPerron)
      | inr sourceLink =>
          have hLinkNe : targetLink ≠ sourceLink := by
            intro hEq
            subst sourceLink
            exact hNe rfl
          have hLowerAgree :=
            finiteEvenFourTorusZ2AugmentedLowerSlice_agreeOff_of_agreeOff_lower
              H X Y sourceLink hAgree
          have hLocal :=
            D.lowerLocalCrossRatio targetLink (Sum.inr sourceLink)
              X Y hNe hAgree
          have hPerron :=
            D.lowerPerronCrossRatio targetLink sourceLink
              (finiteEvenFourTorusZ2AugmentedLowerSlice H X)
              (finiteEvenFourTorusZ2AugmentedLowerSlice H Y)
              hLinkNe hLowerAgree
          simpa [assembledRadius, Real.exp_add] using
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_lowerCrossRatio_of_local_mul_perron
              H β energyIdentity energyNontrivial hβ hEnergy B X Y
              targetLink
              (Real.exp
                (D.lowerLocalRadius targetLink (Sum.inr sourceLink)))
              (Real.exp (D.lowerPerronRadius targetLink sourceLink))
              (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
              hLocal hPerron)

end Z2AugmentedInternalCrossRatioRowsData

/-- A strict row-sum certificate added to the separated actual row data. -/
structure Z2AugmentedInternalStrictCrossRatioData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) where
  rows : Z2AugmentedInternalCrossRatioRowsData
    H β energyIdentity energyNontrivial hβ hEnergy B
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  rowSum_le_coefficient :
    ∀ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
      (∑ source : FiniteEvenFourTorusZ2AugmentedCoordinate H,
        if target = source then 0 else
          2 * ((Real.exp (rows.assembledRadius target source) - 1) /
            (Real.exp (rows.assembledRadius target source) + 1))) ≤
        coefficient
  coefficient_lt_one : coefficient < 1

namespace Z2AugmentedInternalStrictCrossRatioData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 ≤ β}
  {hEnergy : energyIdentity ≤ energyNontrivial}
  {B : FiniteEvenFourTorusZ2SliceConfiguration H}

/-- Assemble the separated actual rows into generic strict cross-ratio
Dobrushin data. -/
noncomputable def toCrossRatioDobrushinData
    (D : Z2AugmentedInternalStrictCrossRatioData
      H β energyIdentity energyNontrivial hβ hEnergy B) :
    FinitePositiveWeightCrossRatioDobrushinData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B) :=
  { radius := D.rows.assembledRadius
    radius_nonneg := D.rows.assembledRadius_nonneg
    crossRatioBound := D.rows.assembledCrossRatioBound
    coefficient := D.coefficient
    coefficient_nonneg := D.coefficient_nonneg
    rowSum_le_coefficient := D.rowSum_le_coefficient
    coefficient_lt_one := D.coefficient_lt_one }

/-- The actual strict row package constructs the full `L¹` Dobrushin matrix. -/
noncomputable def toDobrushinL1MatrixData
    (D : Z2AugmentedInternalStrictCrossRatioData
      H β energyIdentity energyNontrivial hβ hEnergy B) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy B) :=
  D.toCrossRatioDobrushinData.toDobrushinL1MatrixData
    (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
      H β energyIdentity energyNontrivial hβ hEnergy B)

/-- A strict row package for the replaced boundary supplies exactly the
right-boundary Dobrushin field required by stationary comparison. -/
noncomputable def toBoundaryStationaryDobrushinData
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (D : Z2AugmentedInternalStrictCrossRatioData
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteZ2GaugeReplaceCoordinate B source g)) :
    Z2AugmentedBoundaryStationaryDobrushinData
      H β energyIdentity energyNontrivial hβ hEnergy source g B :=
  { rightDobrushin := D.toDobrushinL1MatrixData }

end Z2AugmentedInternalStrictCrossRatioData

end

end MathlibAnalytic
end MGAP4D
