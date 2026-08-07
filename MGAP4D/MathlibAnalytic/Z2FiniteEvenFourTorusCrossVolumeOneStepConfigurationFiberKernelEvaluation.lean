import MGAP4D.MathlibAnalytic.FiniteGroupEquivariantFiberPushforwardOrbitEvaluation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationSurjectivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact normalized one-step embedding scale is constant along every fine
residual-gauge orbit. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H (g • A) =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A := by
  unfold finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale
  unfold finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration
    finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration
  rw [finiteGroupOrbitClass_smul]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
  rw [finiteGroupOrbitClass_smul]

/-- At a fixed fine evaluation configuration, the exact fine kernel weight from
Package H is invariant in its summed fine configuration variable. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  intro g B
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul]

/-- The coarse comparison kernel weight is invariant in the coarse
configuration variable. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  intro g b
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant]

/-- Fine raw-kernel weight pushed to one individual coarse configuration. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteFiberPushforwardCoefficient
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A) b

/-- The pushed fine kernel coefficient is itself coarse-gauge invariant. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
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
  · exact finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight_invariant
      H β energyIdentity energyNontrivial hβ hEnergy A

/-- The Package-H fine orbit-fibre coefficient is exactly the orbit aggregation
of the configurationwise fibre-pushed fine kernel coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A) q := by
  exact
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_aggregate_pushforward
      H β energyIdentity energyNontrivial hβ hEnergy A q

/-- One-step raw transfer compatibility is now a configuration-by-configuration
fibre equation: the fine kernel summed over the actual coarse-map fibre equals
the scaled coarse kernel at every coarse configuration. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A b =
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A b := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients]
  constructor
  · intro h A
    apply
      (finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)).1
    intro q
    rw [← finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
    exact h A q
  · intro h A q
    rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
    unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
    exact
      (finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)).2
        (h A) q

/-- Audit-visible one-step Package-I bundle. -/
structure Z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  fineConfigurationFiberKernelCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ
  fineConfigurationFiberKernelCoefficient_eq :
    fineConfigurationFiberKernelCoefficient =
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
  fibreInvariant : ∀ A,
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (fineConfigurationFiberKernelCoefficient A)
  rawResidualCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ A b,
        fineConfigurationFiberKernelCoefficient A b =
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A b

/-- Construct the one-step Package-I receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  fineConfigurationFiberKernelCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  fineConfigurationFiberKernelCoefficient_eq := rfl
  fibreInvariant :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_invariant
      H β energyIdentity energyNontrivial hβ hEnergy
  rawResidualCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
