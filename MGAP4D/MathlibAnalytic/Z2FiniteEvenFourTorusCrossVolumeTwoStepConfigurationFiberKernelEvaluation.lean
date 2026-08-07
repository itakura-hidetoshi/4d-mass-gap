import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelEvaluation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact direct two-step embedding scale is constant along every finest
residual-gauge orbit. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H (g • A) =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul]

/-- The direct two-step fine kernel weight is invariant in its finest summed
configuration variable. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  intro g B
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_smul]

/-- The coarsest comparison weight in the direct two-step criterion is coarse
residual-gauge invariant. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  intro g b
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant]

/-- Finest kernel weight pushed once to the intermediate doubled volume. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepIntermediateConfigurationFiberKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (B₁ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) : ℝ :=
  finiteFiberPushforwardCoefficient
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A) B₁

/-- The intermediate fibre coefficient is invariant under the intermediate
residual gauge group. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepIntermediateConfigurationFiberKernelCoefficient_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepIntermediateConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepIntermediateConfigurationFiberKernelCoefficient
  apply finiteFiberPushforwardCoefficient_invariant_of_equivariant_surjective
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
      (finiteEvenFourTorusDoubleRefinement H))
  · exact finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom_surjective
      (finiteEvenFourTorusDoubleRefinement H)
  · intro g B
    exact finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul
      (finiteEvenFourTorusDoubleRefinement H) g B
  · exact finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight_invariant
      H β energyIdentity energyNontrivial hβ hEnergy A

/-- Successive finest-to-intermediate-to-coarsest configuration fibre
coefficient.  Package H proves that this is also the direct finest-to-coarsest
fibre pushforward. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteFiberPushforwardCoefficient
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepIntermediateConfigurationFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy A) b

/-- The final two-step configuration fibre coefficient is coarse residual-gauge
invariant. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
  apply finiteFiberPushforwardCoefficient_invariant_of_equivariant_surjective
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
  · exact finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom_surjective H
  · intro g B
    exact finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul H g B
  · exact
      finiteEvenFourTorusZ2GaugeInvariantTwoStepIntermediateConfigurationFiberKernelCoefficient_invariant
        H β energyIdentity energyNontrivial hβ hEnergy A

/-- Successive two-stage configuration pushforward is exactly the direct
finest-to-coarsest pushforward from Package H. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_direct
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      finiteFiberPushforwardCoefficient
        (fun B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)) =>
          finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B))
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A) b := by
  exact finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelPushforward_cocycle
    H β energyIdentity energyNontrivial hβ hEnergy A b

/-- The Package-H direct two-step orbit-fibre coefficient is exactly the orbit
aggregation of the successive configurationwise fibre coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A) q := by
  exact
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_successivePushforwardAggregate
      H β energyIdentity energyNontrivial hβ hEnergy A q

/-- Direct two-step raw transfer compatibility is equivalent to an equality at
every individual coarsest configuration. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A b =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A b := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients]
  constructor
  · intro h A
    apply
      (finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)).1
    intro q
    rw [← finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
    exact h A q
  · intro h A q
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
    unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
    exact
      (finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)).2
        (h A) q

/-- Audit-visible direct two-step Package-I bundle. -/
structure Z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  fineConfigurationFiberKernelCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ
  fineConfigurationFiberKernelCoefficient_eq :
    fineConfigurationFiberKernelCoefficient =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
  fibreInvariant : ∀ A,
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (fineConfigurationFiberKernelCoefficient A)
  directPushforwardFormula : ∀ A b,
    fineConfigurationFiberKernelCoefficient A b =
      finiteFiberPushforwardCoefficient
        (fun B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)) =>
          finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B))
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A) b
  rawResidualCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ A b,
        fineConfigurationFiberKernelCoefficient A b =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A b

/-- Construct the direct two-step Package-I receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  fineConfigurationFiberKernelCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  fineConfigurationFiberKernelCoefficient_eq := rfl
  fibreInvariant :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_invariant
      H β energyIdentity energyNontrivial hβ hEnergy
  directPushforwardFormula :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_direct
      H β energyIdentity energyNontrivial hβ hEnergy
  rawResidualCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
