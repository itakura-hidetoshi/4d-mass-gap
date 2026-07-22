import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonUniqueMinimumNormL2
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Generic kernel-range reconstruction from a projector-valued kernel
classification. -/
theorem continuousLinearMap_ker_eq_range_of_apply_eq_zero_iff_eq_projection
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (A Q : E →L[𝕜] E)
    (hAQ : ∀ x : E, A (Q x) = 0)
    (hKernel : ∀ x : E, A x = 0 ↔ x = Q x) :
    A.toLinearMap.ker = Q.toLinearMap.range := by
  ext x
  constructor
  · intro hx
    change A x = 0 at hx
    refine ⟨x, ?_⟩
    exact ((hKernel x).1 hx).symm
  · rintro ⟨y, rfl⟩
    change A (Q y) = 0
    exact hAQ y

/-- The cardinality-zero Gibbs-vacuum projector is idempotent as a continuous
linear endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_isIdempotentElem :
    IsIdempotentElem
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0) := by
  show
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0
  apply ContinuousLinearMap.ext
  intro f
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f) =
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f)
    _ =
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_fluctuationCardinalityProjectorL2_zero]
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum
        f).symm

/-- The kernel of the cardinality-zero projector is exactly the actual
Gibbs-vacuum orthogonal submodule. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_ker_eq_vacuumOrthogonalSubmoduleL2 :
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0).toLinearMap.ker =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
  ext f
  constructor
  · intro hf
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f = 0 at hf
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        f).2
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_iff_inner_vacuum_eq_zero
        f).1 hf
  · intro hf
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f = 0
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_iff_inner_vacuum_eq_zero
        f).2
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        f).1 hf

/-- The ambient beta-zero Poisson kernel is exactly the range of the
cardinality-zero Gibbs-vacuum projector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_ker_eq_range_fluctuationCardinalityProjectorL2_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.ker =
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0).toLinearMap.range := by
  apply continuousLinearMap_ker_eq_range_of_apply_eq_zero_iff_eq_projection
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0)
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_fluctuationCardinalityProjectorL2_zero_eq_zero
        f
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_zero_iff_eq_vacuumProjector
        f

/-- The vacuum-projector range and the Gibbs-vacuum orthogonal submodule are
topological complements. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_zero_isTopCompl_vacuumOrthogonalSubmoduleL2 :
    Submodule.IsTopCompl
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0).toLinearMap.range
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
  have hTop :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_isIdempotentElem.isTopCompl
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_ker_eq_vacuumOrthogonalSubmoduleL2]
    at hTop
  exact hTop

/-- The beta-zero Poisson kernel and the Gibbs-vacuum orthogonal submodule are
topological complements. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_ker_isTopCompl_vacuumOrthogonalSubmoduleL2 :
    Submodule.IsTopCompl
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.ker
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_ker_eq_range_fluctuationCardinalityProjectorL2_zero]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_zero_isTopCompl_vacuumOrthogonalSubmoduleL2

/-- Short name for the actual finite-volume beta-zero Poisson kernel. -/
abbrev periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 :
    Submodule ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.ker

/-- The exact vacuum projector, codomain-restricted to the Poisson kernel. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 :=
  (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
    0).codRestrict
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2
    (fun f => by
      change
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f) = 0
      exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_fluctuationCardinalityProjectorL2_zero_eq_zero
          f)

/-- Pointwise form of the vacuum projection into the Poisson kernel. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
        f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f := by
  rfl

/-- Recombine a Poisson-kernel vector and a vacuum-orthogonal vector in the
ambient Gibbs `L²` space. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2 :
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) ≃L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  Submodule.prodEquivOfIsTopCompl
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_ker_isTopCompl_vacuumOrthogonalSubmoduleL2

/-- The ambient Gibbs space decomposes continuously into its exact Poisson
kernel and Gibbs-vacuum orthogonal sectors. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure ≃L[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2.symm

/-- Recombination is ordinary addition in ambient Gibbs `L²`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2_apply
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2
        x =
      (x.1 : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
        (x.2 : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- The decomposition map returns the exact cardinality-zero vacuum component
and the exact centered component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        f =
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
          f,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f) := by
  apply
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2.injective
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f) = f :=
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2.apply_symm_apply
        f
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f +
        (f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) := by
      abel
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
            f,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
            f) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelProdVacuumOrthogonalContinuousLinearEquivL2_apply,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply]

/-- The quotient by the exact Poisson kernel is continuously linearly equivalent
to the Gibbs-vacuum orthogonal subspace. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelQuotientContinuousLinearEquivVacuumOrthogonalL2 :
    ((Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) ⧸
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) ≃L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  Submodule.quotientEquivOfIsTopCompl
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_ker_isTopCompl_vacuumOrthogonalSubmoduleL2

/-- The inverse quotient equivalence inserts the centered representative and
takes its Poisson-kernel class. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelQuotientContinuousLinearEquivVacuumOrthogonalL2_symm_apply
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelQuotientContinuousLinearEquivVacuumOrthogonalL2.symm
        f =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2.mkQ
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- The first-isomorphism form of the beta-zero Poisson operator: quotient by
the vacuum kernel and then apply the internal Poisson automorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelQuotientPoissonContinuousLinearEquivL2 :
    ((Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) ⧸
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) ≃L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelQuotientContinuousLinearEquivVacuumOrthogonalL2.trans
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonContinuousLinearEquivL2

/-- The Poisson operator in kernel-centered coordinates is zero on the kernel
factor and the exact internal Poisson automorphism on `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2 :
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) →L[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :=
  (0 : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2).prodMap
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2

/-- Pointwise block-diagonal action. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        x =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          x.2) := by
  rfl

/-- Conjugating the ambient Poisson operator by the exact decomposition produces
the block-diagonal operator `0 ⊕ (I-P)|Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_randomScanPoissonOperatorL2_eq_blockDiagonal
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply]
  apply Prod.ext
  · apply Subtype.ext
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f) = 0
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_of_inner_vacuum_eq_zero
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero
          f)
  · apply Subtype.ext
    have hVacuumZero :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              f) = 0 :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_of_inner_vacuum_eq_zero
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero
          f)
    calc
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f) : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f := by
        rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply,
          hVacuumZero, sub_zero]
      _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) :=
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_centering_eq_self
          f).symm
      _ =
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
              f) : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
            f)).symm

/-- Structured receipt for the exact beta-zero Poisson kernel decomposition. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelTopologicalDecompositionL2Receipt :
    Prop where
  vacuum_projector_idempotent :
    IsIdempotentElem
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0)
  vacuum_projector_ker_eq :
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0).toLinearMap.ker =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
  poisson_ker_eq :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.ker =
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0).toLinearMap.range
  topological_complement :
    Submodule.IsTopCompl
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
  exact_decomposition :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f =
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
            f,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
            f)
  block_diagonal :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
            f)

/-- The exact Poisson-kernel topological-decomposition receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelTopologicalDecompositionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelTopologicalDecompositionL2Receipt := by
  refine
    { vacuum_projector_idempotent :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_isIdempotentElem
      vacuum_projector_ker_eq :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_ker_eq_vacuumOrthogonalSubmoduleL2
      poisson_ker_eq :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_ker_eq_range_fluctuationCardinalityProjectorL2_zero
      topological_complement :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_ker_isTopCompl_vacuumOrthogonalSubmoduleL2
      exact_decomposition :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply
      block_diagonal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_randomScanPoissonOperatorL2_eq_blockDiagonal }

end

end MathlibAnalytic
end MGAP4D
