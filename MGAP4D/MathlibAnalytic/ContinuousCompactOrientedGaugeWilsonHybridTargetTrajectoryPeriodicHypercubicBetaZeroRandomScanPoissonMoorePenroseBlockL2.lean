import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonNormalEquationL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- In kernel-centered coordinates, the ambient generalized inverse is zero on
its exact Poisson-kernel factor and the centered Green inverse on `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2 :
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) →L[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :=
  (0 : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2).prodMap
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2

/-- Pointwise action of the generalized-inverse block. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        x =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          x.2) := by
  rfl

/-- The coordinate form of ambient orthogonal centering is zero on the exact
Poisson kernel and the identity on `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2 :
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) →L[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :=
  (0 : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2).prodMap
    (ContinuousLinearMap.id ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)

/-- Pointwise action of the coordinate-centering block. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelCenteringBlockL2_apply
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
        x = (0, x.2) := by
  rfl

/-- The exact Poisson-kernel coordinate of every generalized-inverse output is
zero because the output lies in `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply_generalizedInverse_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) = 0 := by
  apply Subtype.ext
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) = 0
  apply
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_of_inner_vacuum_eq_zero
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f)

/-- Centering a generalized-inverse output recovers its canonical `Ω⊥`
representative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_generalizedInverse_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f := by
  let g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f⟩
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        (g : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
        rfl
    _ = g :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_subtype_eq_self
        g
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f := by
      apply Subtype.ext
      exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply
          f

/-- The exact continuous kernel-centered decomposition conjugates the ambient
Moore--Penrose generalized inverse to `0 ⊕ A⊥⁻¹`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_generalizedInverse_eq_blockDiagonal
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply]
  apply Prod.ext
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply_generalizedInverse_eq_zero
        f
  · rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_generalizedInverse_eq_canonical,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply]

/-- Applying the Poisson block after the generalized-inverse block returns the
coordinate-centering block. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply_generalizedInverseBlock_eq_centeringBlock
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
          x) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
        x := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
          x) =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
            x).2)) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
          x)
    _ =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            x.2)) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply]
    _ = (0, x.2) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
        x :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelCenteringBlockL2_apply
        x).symm

/-- Applying the generalized-inverse block after the Poisson block returns the
same coordinate-centering block. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply_poissonBlock_eq_centeringBlock
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
          x) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
        x := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
          x) =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
            x).2)) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
          x)
    _ =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            x.2)) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply]
    _ = (0, x.2) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self]
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
        x :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelCenteringBlockL2_apply
        x).symm

/-- Operator-level form of `(0 ⊕ A⊥) (0 ⊕ A⊥⁻¹) = 0 ⊕ I`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_comp_generalizedInverseBlock_eq_centeringBlock :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply_generalizedInverseBlock_eq_centeringBlock
      x

/-- Operator-level form of `(0 ⊕ A⊥⁻¹) (0 ⊕ A⊥) = 0 ⊕ I`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_comp_poissonBlock_eq_centeringBlock :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply_poissonBlock_eq_centeringBlock
      x

/-- The Poisson block is unchanged after coordinate centering. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply_centeringBlock_eq_self
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        x := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x) =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
            x).2)) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x)
    _ =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          x.2) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelCenteringBlockL2_apply]
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        x :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply
        x).symm

/-- The generalized-inverse block is unchanged after coordinate centering. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply_centeringBlock_eq_self
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        x := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x) =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
            x).2)) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x)
    _ =
      (0,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          x.2) := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelCenteringBlockL2_apply]
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        x :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply
        x).symm

/-- Algebraic first Penrose equation in exact kernel-centered coordinates. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_comp_generalizedInverseBlock_comp_poissonBlock_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2.comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2.comp
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
            x)) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x) :=
      congrArg
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply_poissonBlock_eq_centeringBlock
          x)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
        x :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply_centeringBlock_eq_self
        x

/-- Algebraic second Penrose equation in exact kernel-centered coordinates. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_comp_poissonBlock_comp_generalizedInverseBlock_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2.comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2.comp
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
            x)) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          x) :=
      congrArg
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_apply_generalizedInverseBlock_eq_centeringBlock
          x)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        x :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply_centeringBlock_eq_self
        x

/-- Ambient orthogonal centering is conjugated to the exact coordinate-centering
block `0 ⊕ I`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_centeringEndL2_eq_centeringBlock
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f) := by
  have hCenter :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f) := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector]
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)) :=
      congrArg
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        hCenter
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_generalizedInverse_eq_blockDiagonal
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
            f)) :=
      congrArg
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_randomScanPoissonOperatorL2_eq_blockDiagonal
          f)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_apply_poissonBlock_eq_centeringBlock
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f)

/-- Structured receipt for the simultaneous algebraic block form of the actual
beta-zero Poisson operator, its Moore--Penrose generalized inverse, and ambient
centering. No inner-product statement is transported through the continuous
linear equivalence, which is not asserted here to be an isometry. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenroseBlockL2Receipt :
    Prop where
  generalized_inverse_block_diagonal :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
            f)
  poisson_times_generalized_inverse :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
  generalized_inverse_times_poisson :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
  first_penrose :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2.comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2.comp
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2
  second_penrose :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2.comp
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelBlockDiagonalL2.comp
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelGeneralizedInverseBlockDiagonalL2
  centering_block_diagonal :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelCenteringBlockL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
            f)

/-- The simultaneous algebraic Poisson/Moore--Penrose block receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenroseBlockL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonMoorePenroseBlockL2Receipt := by
  refine
    { generalized_inverse_block_diagonal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_generalizedInverse_eq_blockDiagonal
      poisson_times_generalized_inverse :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_comp_generalizedInverseBlock_eq_centeringBlock
      generalized_inverse_times_poisson :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_comp_poissonBlock_eq_centeringBlock
      first_penrose :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelBlockDiagonalL2_comp_generalizedInverseBlock_comp_poissonBlock_eq_self
      second_penrose :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelGeneralizedInverseBlockDiagonalL2_comp_poissonBlock_comp_generalizedInverseBlock_eq_self
      centering_block_diagonal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_centeringEndL2_eq_centeringBlock }

end

end MathlibAnalytic
end MGAP4D
