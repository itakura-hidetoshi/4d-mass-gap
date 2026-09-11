import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2ConditionalExpectationCompression
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOrbitProbability
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaugeOrbitProbabilityL2Realization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Covariant Hilbert map attached to the actual fine-to-coarse residual-gauge
orbit probability map.  It is the probability-weighted conditional
expectation from fine orbit `L²` to coarse orbit `L²`. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  FiniteStrictProbabilityMap.l2ConditionalExpectationLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)

/-- The actual conditional expectation is an exact left inverse of the
contravariant coarse-orbit pullback. -/
theorem finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectation_leftInverse
    (H : ℕ)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap H
        (FiniteStrictProbabilityMap.l2PullbackLinearMap
          (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) y) = y :=
  FiniteStrictProbabilityMap.l2ConditionalExpectation_l2Pullback
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) y

/-- Hilbert-adjoint pairing for the actual cross-volume Z2 orbit map. -/
theorem finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectation_adjoint
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
      (finiteEvenFourTorusDoubleRefinement H))
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    inner ℝ
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap H x)
        y =
      inner ℝ x
        (FiniteStrictProbabilityMap.l2PullbackLinearMap
          (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) y) :=
  FiniteStrictProbabilityMap.l2ConditionalExpectation_adjoint_pairing
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) x y

/-- Orthogonal projection of the fine orbit-probability carrier onto vectors
measurable with respect to the actual coarse orbit map. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) :=
  FiniteStrictProbabilityMap.l2CoarseProjectionLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)

/-- The actual cross-volume coarse-measurable projection is idempotent. -/
theorem finiteEvenFourTorusZ2GaugeOrbitCoarseProjection_idempotent
    (H : ℕ)
    (x : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap H
        (finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap H x) =
      finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap H x :=
  FiniteStrictProbabilityMap.l2CoarseProjection_idempotent
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) x

/-- The actual coarse-measurable projection is symmetric. -/
theorem finiteEvenFourTorusZ2GaugeOrbitCoarseProjection_isSymmetric
    (H : ℕ) :
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap H).IsSymmetric :=
  FiniteStrictProbabilityMap.l2CoarseProjection_isSymmetric
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)

/-- The mathematically canonical renormalized coarse defect: pull a coarse
orbit vector to the fine volume, evolve by the actual fine ground-lifted defect,
and condition back to the coarse orbit probability space.  No equality with
the independently constructed coarse defect is assumed. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)

/-- The renormalized coarse defect is symmetric because the actual fine defect
is symmetric and conditional expectation is the Hilbert adjoint of pullback. -/
theorem finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator_isSymmetric
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_isSymmetric
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact finite coercivity `1/2` survives the actual cross-volume compression.
This statement requires no cross-volume intertwining hypothesis. -/
theorem finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect_half_coercive
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
        (finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le y) y :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator_quadratic_lower_bound
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (1 / 2 : ℝ)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff
      (finiteEvenFourTorusDoubleRefinement H))
    y

/-- Compression-level discrepancy between the renormalized fine defect and the
independently constructed actual coarse defect.  Its vanishing is weaker than
full intertwining and is therefore recorded separately. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDifference
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy -
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Strong intertwining obstruction comparing the fine actual defect with the
independently constructed coarse actual defect.  It lives from coarse orbit
`L²` to fine orbit `L²`; no claim that it vanishes is made. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The actual obstruction vanishes exactly when the fine and coarse defects
strongly intertwine through the geometrically induced `L²` pullback. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H,
        finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy
            (FiniteStrictProbabilityMap.l2PullbackLinearMap
              (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) y) =
          FiniteStrictProbabilityMap.l2PullbackLinearMap
            (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
            (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
              H β energyIdentity energyNontrivial hβ hEnergy y) :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap_eq_zero_iff
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- If the strong geometric intertwining obstruction vanishes, the actual
coarse defect is exactly the conditional-expectation compression of the actual
fine defect. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_zero_implies_compression_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hzero :
      finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0) :
    finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy :=
  FiniteStrictProbabilityMap.compressContinuousLinearOperator_eq_of_intertwining
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)
    ((finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff
      H β energyIdentity energyNontrivial hβ hEnergy).mp hzero)

/-- Audit-visible complete Package C: actual cross-volume conditional
expectation, orthogonal projection, renormalized defect, exact coercivity and
explicit non-assumed intertwining obstruction. -/
structure Z2FiniteEvenFourTorusCrossVolumeOperatorCompressionPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) where
  conditionalExpectation :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  conditionalExpectation_eq :
    conditionalExpectation =
      finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap H
  leftInverse : ∀ y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H,
    conditionalExpectation
        (FiniteStrictProbabilityMap.l2PullbackLinearMap
          (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) y) = y
  projection :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H)
  projection_eq :
    projection = finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap H
  projectionIdempotent : ∀ x, projection (projection x) = projection x
  projectionSymmetric : projection.IsSymmetric
  renormalizedDefect :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  renormalizedDefect_eq :
    renormalizedDefect =
      finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
  renormalizedSymmetric : renormalizedDefect.toLinearMap.IsSymmetric
  renormalizedHalfCoercive : ∀ y,
    (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤ inner ℝ (renormalizedDefect y) y
  actualCoarseDefect :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  actualCoarseDefect_eq :
    actualCoarseDefect =
      finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
  compressionDifference :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  compressionDifference_eq :
    compressionDifference =
      finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDifference
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
  intertwiningObstruction :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H)
  intertwiningObstruction_eq :
    intertwiningObstruction =
      finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
  obstructionCriterion :
    intertwiningObstruction = 0 ↔
      ∀ y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H,
        finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ.le hEnergy.le
            (FiniteStrictProbabilityMap.l2PullbackLinearMap
              (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H) y) =
          FiniteStrictProbabilityMap.l2PullbackLinearMap
            (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
            (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
              H β energyIdentity energyNontrivial hβ.le hEnergy.le y)
  obstructionZeroImpliesCompressionEq :
    intertwiningObstruction = 0 →
      finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le =
        finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le

/-- Construct the complete actual cross-volume operator-compression package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOperatorCompressionPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    Z2FiniteEvenFourTorusCrossVolumeOperatorCompressionPackage
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H where
  conditionalExpectation :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectationLinearMap H
  conditionalExpectation_eq := rfl
  leftInverse :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseL2ConditionalExpectation_leftInverse H
  projection := finiteEvenFourTorusZ2GaugeOrbitCoarseProjectionLinearMap H
  projection_eq := rfl
  projectionIdempotent :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseProjection_idempotent H
  projectionSymmetric :=
    finiteEvenFourTorusZ2GaugeOrbitCoarseProjection_isSymmetric H
  renormalizedDefect :=
    finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  renormalizedDefect_eq := rfl
  renormalizedSymmetric :=
    finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect_isSymmetric
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  renormalizedHalfCoercive :=
    finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect_half_coercive
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  actualCoarseDefect :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  actualCoarseDefect_eq := rfl
  compressionDifference :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDifference
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  compressionDifference_eq := rfl
  intertwiningObstruction :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  intertwiningObstruction_eq := rfl
  obstructionCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  obstructionZeroImpliesCompressionEq :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_zero_implies_compression_eq
      H β energyIdentity energyNontrivial hβ.le hEnergy.le

end

end MathlibAnalytic
end MGAP4D
