import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOrbitProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two successive canonical doubled-torus configuration coarse grainings,
bundled as one exact finite probability map. -/
noncomputable def finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseProbabilityMap
    (H : ℕ) :
    FiniteStrictProbabilityMap
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteUniformProbabilityL2Data
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))))
      (finiteUniformProbabilityL2Data
        (FiniteEvenFourTorusZ2SliceConfiguration H)) :=
  (finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap
      (finiteEvenFourTorusDoubleRefinement H)).comp
    (finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap H)

@[simp] theorem finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseProbabilityMap_toFun
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseProbabilityMap H).toFun A =
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) A) :=
  rfl

/-- Two successive actual residual-gauge orbit coarse grainings form one exact
probability map from the twice-refined orbit law to the original orbit law. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap
    (H : ℕ) :
    FiniteStrictProbabilityMap
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H) :=
  (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
      (finiteEvenFourTorusDoubleRefinement H)).comp
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)

@[simp] theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap_toFun
    (H : ℕ)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H).toFun q =
      finiteEvenFourTorusZ2GaugeOrbitCoarseMap H
        (finiteEvenFourTorusZ2GaugeOrbitCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) q) :=
  rfl

/-- Exact pushforward receipt for the two-step actual orbit coarse graining. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap_weight_pushforward
    (H : ℕ)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteProbabilityPushforwardWeight
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (fun r =>
          finiteEvenFourTorusZ2GaugeOrbitCoarseMap H
            (finiteEvenFourTorusZ2GaugeOrbitCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) r))
        q =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight q :=
  (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H).weight_pushforward q

/-- The canonical `L²` pullback along the two-step actual orbit probability
coarse graining. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H).l2PullbackLinearIsometry

/-- Contravariant cocycle law for actual cross-volume orbit `L²` pullback:
pulling back from `H` to its double refinement and then once more to the next
double refinement is exactly pullback along the composed two-step probability
map. -/
theorem finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry_twoStep_cocycle
    (H : ℕ)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry
        (finiteEvenFourTorusDoubleRefinement H)
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H y) =
      finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H y := by
  change
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
        (finiteEvenFourTorusDoubleRefinement H)).l2PullbackLinearMap
        ((finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H).l2PullbackLinearMap y) =
      ((finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
          (finiteEvenFourTorusDoubleRefinement H)).comp
        (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)).l2PullbackLinearMap y
  exact
    FiniteStrictProbabilityMap.l2PullbackLinearMap_comp
      (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
        (finiteEvenFourTorusDoubleRefinement H))
      (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
      y

end

end MathlibAnalytic
end MGAP4D
