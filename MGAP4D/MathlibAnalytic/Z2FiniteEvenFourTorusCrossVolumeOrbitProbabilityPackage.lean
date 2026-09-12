import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeProbabilityCocycle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Audit-visible Package B receipt for actual finite `Z₂` cross-volume orbit
probability coarse graining.  It records the exact configuration probability
map, descended orbit probability map, probability pushforward, contravariant
`L²` isometry, and the two-step refinement cocycle without adding any
operator-intertwining assumption. -/
structure Z2FiniteEvenFourTorusCrossVolumeOrbitProbabilityPackage
    (H : ℕ) where
  configurationProbabilityMap :
    FiniteStrictProbabilityMap
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteUniformProbabilityL2Data
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)))
      (finiteUniformProbabilityL2Data
        (FiniteEvenFourTorusZ2SliceConfiguration H))
  configurationProbabilityMap_eq :
    configurationProbabilityMap =
      finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap H
  orbitProbabilityMap :
    FiniteStrictProbabilityMap
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
        (finiteEvenFourTorusDoubleRefinement H))
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H)
  orbitProbabilityMap_eq :
    orbitProbabilityMap =
      finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H
  orbitWeightPushforward :
    ∀ q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H,
      finiteProbabilityPushforwardWeight
          (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
            (finiteEvenFourTorusDoubleRefinement H))
          (finiteEvenFourTorusZ2GaugeOrbitCoarseMap H)
          q =
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight q
  l2Pullback :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H)
  l2Pullback_eq :
    l2Pullback =
      finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
  twoStepOrbitProbabilityMap :
    FiniteStrictProbabilityMap
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H)
  twoStepOrbitProbabilityMap_eq :
    twoStepOrbitProbabilityMap =
      finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H
  twoStepL2Pullback :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  twoStepL2Pullback_eq :
    twoStepL2Pullback =
      finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H
  l2Cocycle :
    ∀ y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H,
      finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry
          (finiteEvenFourTorusDoubleRefinement H)
          (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H y) =
        finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H y

/-- Construct the complete actual cross-volume orbit-probability Package B
receipt from the geometric and generic probability layers already proved. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOrbitProbabilityPackage
    (H : ℕ) :
    Z2FiniteEvenFourTorusCrossVolumeOrbitProbabilityPackage H where
  configurationProbabilityMap :=
    finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap H
  configurationProbabilityMap_eq := rfl
  orbitProbabilityMap :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H
  orbitProbabilityMap_eq := rfl
  orbitWeightPushforward :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap_weight_pushforward H
  l2Pullback :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
  l2Pullback_eq := rfl
  twoStepOrbitProbabilityMap :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H
  twoStepOrbitProbabilityMap_eq := rfl
  twoStepL2Pullback :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H
  twoStepL2Pullback_eq := rfl
  l2Cocycle :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry_twoStep_cocycle H

end

end MathlibAnalytic
end MGAP4D
