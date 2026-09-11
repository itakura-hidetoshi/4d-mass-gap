import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2IntertwiningObstructionDecomposition
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeCompressionRenormalizationTower
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- One-step compression discrepancy for the actual finite `Z₂` ground-lifted
defect. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDiscrepancyLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  FiniteStrictProbabilityMap.compressionDiscrepancyLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- One-step fine-operator leakage out of the pulled-back coarse orbit subspace. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCoarseSubspaceLeakageLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H) :=
  FiniteStrictProbabilityMap.coarseSubspaceLeakageLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact decomposition of the previously defined actual one-step strong
intertwining obstruction. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy =
      (FiniteStrictProbabilityMap.l2PullbackLinearMap
          (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)).comp
          (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDiscrepancyLinearMap
            H β energyIdentity energyNontrivial hβ hEnergy) +
        finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCoarseSubspaceLeakageLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy :=
  FiniteStrictProbabilityMap.intertwiningResidual_decomposition
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The one-step compression-discrepancy and leakage components are exactly
orthogonal. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedObstruction_components_orthogonal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    inner ℝ
        (FiniteStrictProbabilityMap.l2PullbackLinearMap
          (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
          (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDiscrepancyLinearMap
            H β energyIdentity energyNontrivial hβ hEnergy y))
        (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCoarseSubspaceLeakageLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy y) = 0 :=
  FiniteStrictProbabilityMap.pullback_compressionDiscrepancy_inner_coarseSubspaceLeakage_eq_zero
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)
    y

/-- Pythagorean norm-square decomposition of the actual one-step strong
intertwining obstruction. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_norm_sq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    ‖finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 =
      ‖finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDiscrepancyLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 +
      ‖finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCoarseSubspaceLeakageLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 :=
  FiniteStrictProbabilityMap.norm_sq_intertwiningResidual_eq_discrepancy_add_leakage
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)
    y

/-- Exact one-step criterion: strong intertwining holds iff both compression
agreement and fine-operator leakage vanish. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_components
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDiscrepancyLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 ∧
        finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCoarseSubspaceLeakageLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap_eq_zero_iff_discrepancy_and_leakage
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Actual one-step coarse-subspace invariance obligation for the fine defect. -/
def finiteEvenFourTorusZ2GaugeOrbitGroundLiftedPullbackCoarseSubspaceInvariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  FiniteStrictProbabilityMap.PullbackCoarseSubspaceInvariant
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Conceptual one-step criterion: strong intertwining is exactly compression
equality together with invariance of the pulled-back coarse orbit subspace. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_compression_and_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeOrbitRenormalizedGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy ∧
      finiteEvenFourTorusZ2GaugeOrbitGroundLiftedPullbackCoarseSubspaceInvariant
        H β energyIdentity energyNontrivial hβ hEnergy :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap_eq_zero_iff_compression_and_invariant
    (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Two-step compression discrepancy relative to the independently constructed
actual defect at volume `H`. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCompressionDiscrepancyLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  FiniteStrictProbabilityMap.compressionDiscrepancyLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Two-step leakage of twice-refined source evolution out of the original
coarse pulled-back orbit subspace. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCoarseSubspaceLeakageLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  FiniteStrictProbabilityMap.coarseSubspaceLeakageLinearMap
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact two-step decomposition of the strong intertwining obstruction. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy =
      (FiniteStrictProbabilityMap.l2PullbackLinearMap
          (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)).comp
          (finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCompressionDiscrepancyLinearMap
            H β energyIdentity energyNontrivial hβ hEnergy) +
        finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCoarseSubspaceLeakageLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy :=
  FiniteStrictProbabilityMap.intertwiningResidual_decomposition
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact two-step Pythagorean norm-square decomposition. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_norm_sq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (y : FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H) :
    ‖finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 =
      ‖finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCompressionDiscrepancyLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 +
      ‖finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCoarseSubspaceLeakageLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 :=
  FiniteStrictProbabilityMap.norm_sq_intertwiningResidual_eq_discrepancy_add_leakage
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)
    y

/-- Exact two-step component criterion for strong intertwining. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_components
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCompressionDiscrepancyLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 ∧
        finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCoarseSubspaceLeakageLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap_eq_zero_iff_discrepancy_and_leakage
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Actual two-step coarse-subspace invariance obligation. -/
def finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedPullbackCoarseSubspaceInvariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  FiniteStrictProbabilityMap.PullbackCoarseSubspaceInvariant
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Conceptual two-step criterion: direct two-step compression must equal the
actual target defect and the twice-refined source evolution must preserve the
original pulled-back coarse subspace. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_compression_and_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeOrbitTwoStepRenormalizedGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy ∧
      finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedPullbackCoarseSubspaceInvariant
        H β energyIdentity energyNontrivial hβ hEnergy :=
  FiniteStrictProbabilityMap.intertwiningResidualLinearMap_eq_zero_iff_compression_and_invariant
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Audit-visible Package E: exact orthogonal decomposition of one-step and
two-step strong intertwining obstructions into compression discrepancy and
coarse-subspace leakage. -/
structure Z2FiniteEvenFourTorusCrossVolumeIntertwiningObstructionDecompositionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepDiscrepancy :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  oneStepLeakage :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement H)
  oneStepDecomposition :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy =
      (FiniteStrictProbabilityMap.l2PullbackLinearMap
        (finiteEvenFourTorusZ2GaugeOrbitCoarseProbabilityMap H)).comp
          oneStepDiscrepancy + oneStepLeakage
  oneStepPythagorean : ∀ y,
    ‖finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 =
      ‖oneStepDiscrepancy y‖ ^ 2 + ‖oneStepLeakage y‖ ^ 2
  oneStepCriterion :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      oneStepDiscrepancy = 0 ∧ oneStepLeakage = 0
  twoStepDiscrepancy :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  twoStepLeakage :
    FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  twoStepDecomposition :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy =
      (FiniteStrictProbabilityMap.l2PullbackLinearMap
        (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseProbabilityMap H)).comp
          twoStepDiscrepancy + twoStepLeakage
  twoStepPythagorean : ∀ y,
    ‖finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy y‖ ^ 2 =
      ‖twoStepDiscrepancy y‖ ^ 2 + ‖twoStepLeakage y‖ ^ 2
  twoStepCriterion :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      twoStepDiscrepancy = 0 ∧ twoStepLeakage = 0

/-- Construct the complete actual obstruction-decomposition package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeIntertwiningObstructionDecompositionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeIntertwiningObstructionDecompositionPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStepDiscrepancy :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCompressionDiscrepancyLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepLeakage :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedCoarseSubspaceLeakageLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepDecomposition :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepPythagorean :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_norm_sq
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_components
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepDiscrepancy :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCompressionDiscrepancyLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepLeakage :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedCoarseSubspaceLeakageLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepDecomposition :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepPythagorean :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_norm_sq
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_components
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
