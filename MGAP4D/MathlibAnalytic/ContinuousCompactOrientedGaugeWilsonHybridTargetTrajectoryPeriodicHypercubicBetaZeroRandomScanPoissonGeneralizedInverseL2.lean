import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonFredholmAlternativeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Generic projected-inverse identity: if an ambient operator restricts to an
internal operator and an internal map is its right inverse, then composing the
internal inverse with any map into the submodule solves the corresponding
projected ambient equation. -/
theorem continuousLinearMap_apply_internalRightInverse_eq_projection
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (A : E →L[𝕜] E)
    (S : Submodule 𝕜 E)
    (Ainternal B : S →L[𝕜] S)
    (C : E →L[𝕜] S)
    (hAinternal_apply : ∀ x : S, ((Ainternal x : S) : E) = A (x : E))
    (hRightInverse : Function.RightInverse B Ainternal)
    (x : E) :
    A ((B (C x) : S) : E) = (C x : E) := by
  calc
    A ((B (C x) : S) : E) = (Ainternal (B (C x)) : E) :=
      (hAinternal_apply (B (C x))).symm
    _ = (C x : E) := by
      exact congrArg (fun z : S => (z : E)) (hRightInverse (C x))

/-- The canonical beta-zero Poisson solution map first removes the Gibbs-vacuum
component and then applies the exact inverse on `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2.comp
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2

/-- The ambient generalized inverse is the canonical `Ω⊥` solution followed by
the isometric subtype inclusion. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2.subtypeL.comp
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2

/-- Pointwise form of the canonical `Ω⊥` solution map. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f) := by
  rfl

/-- Pointwise form of the ambient generalized inverse. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- Applying the ambient Poisson operator after the generalized inverse returns
the exact Gibbs-vacuum orthogonal projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centering
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  have hGeneric :=
    continuousLinearMap_apply_internalRightInverse_eq_projection
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreen_rightInverse_poissonVacuumOrthogonalEndL2
      f
  have hGeneralized :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply
      f
  have hCanonical :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply
      f
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) :=
      congrArg
        (fun z : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            z)
        hGeneralized
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
              f) :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) := by
      have hCoe := congrArg
        (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
          (z : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        hCanonical
      exact congrArg
        (fun z : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            z)
        hCoe
    _ =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
      hGeneric

/-- Explicit ambient form of `(I - P) G† = C`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centering
        f
    _ =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply
        f

/-- Centering fixes the ambient Poisson image, viewed internally in `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_randomScanPoissonOperatorL2_eq_subtype
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f) =
      ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_mem_vacuumOrthogonalSubmoduleL2
          f⟩ := by
  apply Subtype.ext
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero,
    zero_smul, sub_zero]

/-- The ambient Poisson operator is unchanged by first removing the vacuum
component of its input. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_centering_eq_self
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
            f :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply,
    map_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_fluctuationCardinalityProjectorL2_zero_eq_zero,
    sub_zero]

/-- The canonical solution map applied to a Poisson image returns the centered
input. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply_poisson_eq_centering
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        f := by
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        f
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_randomScanPoissonOperatorL2_eq_subtype]
  have hInternal :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
            f) =
        ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_mem_vacuumOrthogonalSubmoduleL2
            f⟩ := by
    apply Subtype.ext
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_centering_eq_self
        f
  rw [← hInternal]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        f)

/-- Applying the generalized inverse after the ambient Poisson operator also
returns the exact Gibbs-vacuum orthogonal projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_centering
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f) =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  have hSubtype :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply_poisson_eq_centering
      f
  have hCoe := congrArg
    (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
      (z : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
    hSubtype
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply] using hCoe

/-- Explicit ambient form of `G† (I - P) = C`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f) =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f) =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_centering
        f
    _ =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply
        f

/-- First generalized-inverse identity: `(I - P) G† (I - P) = I - P`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_apply_poisson_eq_self
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)) =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f) :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centering
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 f := by
      have hSubtype :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_randomScanPoissonOperatorL2_eq_subtype
          f
      exact congrArg
        (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
          (z : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        hSubtype

/-- The generalized inverse always produces a vacuum-orthogonal vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
  change
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
      f).property

/-- Second generalized-inverse identity: `G† (I - P) G† = G†`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_apply_generalizedInverse_eq_self
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    hOrthogonal, zero_smul, sub_zero]

/-- The generalized inverse solves the Poisson equation exactly for every
vacuum-orthogonal datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_self_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    hOrthogonal, zero_smul, sub_zero]

/-- The generalized inverse has operator norm at most `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_le_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2‖ ≤
      324 := by
  apply
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.opNorm_le_bound
      (by norm_num)
  intro f
  have hCentering :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f‖ ≤
        ‖f‖ := by
    change
      ‖((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
        ‖f‖
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_fluctuationCardinalityProjectorL2_zero_apply_le_norm
        f
  change
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f)‖ ≤
      324 * ‖f‖
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f)‖ ≤
      324 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f‖ :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_le_324_mul_norm
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f)
    _ ≤ 324 * ‖f‖ := by
      exact mul_le_mul_of_nonneg_left hCentering (by norm_num)

/-- A cardinality-one vector attains the norm `324` for the ambient generalized
inverse. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_ge_324 :
    (324 : ℝ) ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenOperatorL2_apply_eq_324_smul
    with ⟨f, hfNe, hfOrthogonal, hGreen⟩
  let fOrthogonal :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨f,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        f).2 hfOrthogonal⟩
  have hCentering :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f =
        fOrthogonal := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_subtype_eq_self
        fOrthogonal
  have hVacuumZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f = 0 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      hfOrthogonal, zero_smul]
  have hCenteredGreen :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          fOrthogonal =
        (324 : ℝ) • fOrthogonal := by
    apply Subtype.ext
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply]
    change
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
              f) =
        (324 : ℝ) • f
    rw [hGreen, map_smul, hVacuumZero, smul_zero, sub_zero]
  have hAction :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f =
        (324 : ℝ) • f := by
    change
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
            f) :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      (324 : ℝ) • f
    rw [hCentering]
    have hCoe := congrArg
      (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (z : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hCenteredGreen
    simpa [fOrthogonal] using hCoe
  have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
  have hFundamental :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2.le_opNorm
      f
  have hActionNorm :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ =
        324 * ‖f‖ := by
    rw [hAction, norm_smul]
    norm_num
  rw [hActionNorm] at hFundamental
  nlinarith [
    ContinuousLinearMap.opNorm_nonneg
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2]

/-- The exact operator norm of the ambient generalized inverse is `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_eq_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2‖ =
      324 := by
  exact le_antisymm
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_le_324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_ge_324

/-- Among all ambient solutions of the same Poisson equation, the generalized
inverse gives a minimum-norm solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_randomScanPoissonOperatorL2_apply_eq
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f‖ ≤
      ‖u‖ := by
  have hCentered :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector
      u
  rw [hPoisson] at hCentered
  rw [hCentered]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_fluctuationCardinalityProjectorL2_zero_apply_le_norm
      u

/-- Compact receipt for the finite-volume beta-zero Poisson generalized inverse. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2Receipt :
    Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f) ∧
    (∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f) =
        f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) ∧
    (∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              f)) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f) ∧
    (∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) ∧
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2‖ =
      324 ∧
    (∀ f u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f →
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f‖ ≤
          ‖u‖)

/-- The finite-volume beta-zero Poisson generalized-inverse receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2Receipt := by
  constructor
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector
        f
  constructor
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector
        f
  constructor
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_apply_poisson_eq_self
        f
  constructor
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_apply_generalizedInverse_eq_self
        f
  constructor
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_eq_324
  · intro f u hPoisson
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_randomScanPoissonOperatorL2_apply_eq
        f u hPoisson

end

end MathlibAnalytic
end MGAP4D
