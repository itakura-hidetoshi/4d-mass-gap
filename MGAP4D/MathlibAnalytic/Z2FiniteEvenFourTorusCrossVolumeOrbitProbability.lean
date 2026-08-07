import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityCommutingSquareDescent
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationSurjectivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The actual doubled-torus configuration coarse homomorphism, equipped with
uniform probability on both finite configuration groups, is an exact finite
probability map.  Exact pushforward is obtained from the explicit geometric
surjectivity proved for the actual `Z₂` coarse graining. -/
noncomputable def finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap
    (H : ℕ) :
    FiniteStrictProbabilityMap
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteUniformProbabilityL2Data
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)))
      (finiteUniformProbabilityL2Data
        (FiniteEvenFourTorusZ2SliceConfiguration H)) :=
  finiteSurjectiveGroupHomUniformProbabilityMap
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H)

@[simp] theorem finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap_toFun
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap H).toFun A =
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A :=
  rfl

/-- The actual fine-to-coarse residual-gauge orbit map preserves the literal
pushforward probability exactly.  The proof descends the already established
uniform configuration pushforward through the commuting square of quotient
class maps, so no orbit stabilizer or orbit-fibre cardinality is counted. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
    (H : ℕ) :
    FiniteStrictProbabilityMap
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
        (finiteEvenFourTorusDoubleRefinement H))
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H) :=
  FiniteStrictProbabilityMap.descendCommutingSquare
    (finiteGroupOrbitClassProbabilityMap
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H)))
    (finiteEvenFourTorusZ2SliceConfigurationCoarseProbabilityMap H)
    (finiteGroupOrbitClassProbabilityMap
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H))
    (finiteEvenFourTorusZ2GaugeOrbitCoarseMap H)
    (by
      intro A
      change
        finiteEvenFourTorusZ2GaugeOrbitCoarseMap H
            (finiteGroupOrbitClass
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
                (finiteEvenFourTorusDoubleRefinement H))
              (FiniteEvenFourTorusZ2SliceConfiguration
                (finiteEvenFourTorusDoubleRefinement H)) A) =
          finiteGroupOrbitClass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)
      exact finiteEvenFourTorusZ2GaugeOrbitCoarseMap_class H A)

@[simp] theorem finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap_toFun
    (H : ℕ)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H).toFun q =
      finiteEvenFourTorusZ2GaugeOrbitCoarseMap H q :=
  rfl

/-- Audit-visible exact pushforward identity for actual cross-volume residual
`Z₂` gauge-orbit probability. -/
theorem finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap_weight_pushforward
    (H : ℕ)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteProbabilityPushforwardWeight
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
          (finiteEvenFourTorusDoubleRefinement H))
        (finiteEvenFourTorusZ2GaugeOrbitCoarseMap H)
        q =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight q :=
  (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H).weight_pushforward q

/-- Contravariant `L²` pullback induced by the actual geometric fine-to-coarse
orbit probability map.  Its direction is coarse-orbit `L²` to fine-orbit `L²`,
as required for pullback. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) :=
  (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H).l2PullbackLinearIsometry

/-- Square-root-density formula for the actual cross-volume orbit `L²`
pullback.  This exposes both the geometric coarse map and the exact source and
target orbit probabilities in one theorem. -/
@[simp] theorem finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry_apply
    (H : ℕ)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H y q =
      Real.sqrt
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
            (finiteEvenFourTorusDoubleRefinement H)).weight q) *
        (y (finiteEvenFourTorusZ2GaugeOrbitCoarseMap H q) /
          Real.sqrt
            ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight
              (finiteEvenFourTorusZ2GaugeOrbitCoarseMap H q))) :=
  rfl

end

end MathlibAnalytic
end MGAP4D
