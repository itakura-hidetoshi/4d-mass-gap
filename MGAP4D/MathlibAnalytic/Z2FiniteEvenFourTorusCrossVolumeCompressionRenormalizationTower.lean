import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2CompressionTower
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOperatorCompression
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeProbabilityCocycle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Covariant conditional expectation along the actual two-step orbit
probability coarse graining. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2ConditionalExpectationLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  FiniteStrictProbabilityMap.l2ConditionalExpectationLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)

/-- Tower law for the actual Z2 conditional expectations: conditioning from
the twice-refined orbit law to the intermediate orbit law and then to the
original orbit law equals direct two-step conditioning. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2ConditionalExpectation_tower
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap H
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap
          (finiteEvenFourTorusDoubleRefinement H) x) =
      finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2ConditionalExpectationLinearMap H x :=
  FiniteStrictProbabilityMap.l2ConditionalExpectationLinearMap_comp
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    x

/-- The direct two-step conditional expectation is a left inverse of the
contravariant two-step pullback. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2ConditionalExpectation_leftInverse
    (H : ℕ)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2ConditionalExpectationLinearMap H
        (FiniteStrictProbabilityMap.l2PullbackLinearMap
          (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H) y) = y :=
  FiniteStrictProbabilityMap.l2ConditionalExpectation_l2Pullback
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H) y

/-- Orthogonal projection of the twice-refined orbit carrier onto observables
measurable at the original coarse scale. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProjectionLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  FiniteStrictProbabilityMap.l2CoarseProjectionLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)

/-- The actual two-step coarse projection is the projection tower dictated by
the intermediate orbit probability space. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProjection_tower
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProjectionLinearMap H x =
      FiniteStrictProbabilityMap.l2PullbackLinearMap
        (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
          (finiteEvenFourTorusDoubleRefinement H))
        (finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap H
          (finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap
            (finiteEvenFourTorusDoubleRefinement H) x)) :=
  FiniteStrictProbabilityMap.l2CoarseProjection_comp_apply
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    x

/-- The actual two-step coarse projection is symmetric. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProjection_isSymmetric
    (H : ℕ) :
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProjectionLinearMap H).IsSymmetric :=
  FiniteStrictProbabilityMap.l2CoarseProjection_isSymmetric
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)

/-- Direct two-step renormalized ground-lifted defect, obtained by compressing
the actual defect on the twice-refined volume directly to volume `H`. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Sequential two-stage renormalization: first compress from the twice-refined
volume to the intermediate volume, then compress once more to volume `H`. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitSequentialTwoStepRenormalizedGroundLiftedDefect
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Renormalization cocycle: direct two-step compression equals sequential
one-step compression exactly. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect_eq_sequential
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2GaugeOrbitSequentialTwoStepRenormalizedGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy := by
  change
    FiniteStrictProbabilityMap.compressContinuousLinearOperator
        ((finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
            (finiteEvenFourTorusDoubleRefinement H)).comp
          (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H))
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy) =
      FiniteStrictProbabilityMap.compressContinuousLinearOperator
        (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
        (FiniteStrictProbabilityMap.compressContinuousLinearOperator
          (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
            (finiteEvenFourTorusDoubleRefinement H))
          (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy))
  exact
    FiniteStrictProbabilityMap.compressContinuousLinearOperator_comp
      (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap
        (finiteEvenFourTorusDoubleRefinement H))
      (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy)

/-- The two-step renormalized defect is symmetric. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator_isSymmetric
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_isSymmetric
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact finite coercivity `1/2` is invariant under the full two-stage
renormalization tower. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect_half_coercive
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤
      inner ℝ
        (finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le y) y :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator_quadratic_lower_bound
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (1 / 2 : ℝ)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    y

/-- Two-step compression discrepancy relative to the independently constructed
actual defect at the original coarse volume. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCompressionDifference
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy -
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Strong two-step intertwining obstruction.  Its vanishing is not assumed;
it exactly records whether the twice-refined actual defect intertwines with the
actual coarse defect through the two-step geometric pullback. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact criterion for vanishing of the strong two-step intertwining
obstruction. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H,
        finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy
            (FiniteStrictProbabilityMap.l2PullbackLinearMap
              (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H) y) =
          FiniteStrictProbabilityMap.l2PullbackLinearMap
            (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
            (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
              H β energyIdentity energyNontrivial hβ hEnergy y) :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap_eq_zero_iff
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Vanishing of the strong two-step obstruction forces the actual coarse
defect to coincide with the direct, hence also sequential, two-step
renormalized defect. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_zero_implies_compression_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hzero :
      finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator_eq_of_intertwining
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)
    ((finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff
      H β energyIdentity energyNontrivial hβ hEnergy).mp hzero)

/-- Audit-visible Package D: actual conditional-expectation tower, projection
tower, renormalization cocycle, exact two-step coercivity and non-assumed
strong intertwining obstruction. -/
structure Z2FiniteEvenFourTorusCrossVolumeCompressionRenormalizationTowerPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) where
  twoStepConditionalExpectation :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  conditionalTower : ∀ x,
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap H
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap
          (finiteEvenFourTorusDoubleRefinement H) x) =
      twoStepConditionalExpectation x
  twoStepProjection :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  projectionSymmetric : twoStepProjection.IsSymmetric
  directRenormalizedDefect :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  sequentialRenormalizedDefect :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  renormalizationCocycle :
    directRenormalizedDefect = sequentialRenormalizedDefect
  directSymmetric : directRenormalizedDefect.toLinearMap.IsSymmetric
  directHalfCoercive : ∀ y,
    (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤ inner ℝ (directRenormalizedDefect y) y
  twoStepCompressionDifference :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  twoStepIntertwiningObstruction :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  obstructionCriterion :
    twoStepIntertwiningObstruction = 0 ↔
      ∀ y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H,
        finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ.le hEnergy.le
            (FiniteStrictProbabilityMap.l2PullbackLinearMap
              (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H) y) =
          FiniteStrictProbabilityMap.l2PullbackLinearMap
            (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
            (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
              H β energyIdentity energyNontrivial hβ.le hEnergy.le y)

/-- Construct the complete actual two-stage renormalization tower package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeCompressionRenormalizationTowerPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    Z2FiniteEvenFourTorusCrossVolumeCompressionRenormalizationTowerPackage
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H where
  twoStepConditionalExpectation :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2ConditionalExpectationLinearMap H
  conditionalTower :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2ConditionalExpectation_tower H
  twoStepProjection :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProjectionLinearMap H
  projectionSymmetric :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProjection_isSymmetric H
  directRenormalizedDefect :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  sequentialRenormalizedDefect :=
    finiteEvenFourTorusZ2GaugeOrbitSequentialTwoStepRenormalizedGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  renormalizationCocycle :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect_eq_sequential
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  directSymmetric :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect_isSymmetric
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  directHalfCoercive :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  twoStepCompressionDifference :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCompressionDifference
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  twoStepIntertwiningObstruction :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  obstructionCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff
      H β energyIdentity energyNontrivial hβ.le hEnergy.le

end

end MathlibAnalytic
end MGAP4D
