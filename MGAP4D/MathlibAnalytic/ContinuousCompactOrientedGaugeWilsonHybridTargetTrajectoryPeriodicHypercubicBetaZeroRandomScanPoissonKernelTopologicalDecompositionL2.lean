import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonUniqueMinimumNormL2
import Mathlib.LinearAlgebra.Isomorphisms
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

/-- The exact vacuum projection fixes every Poisson-kernel vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply_subtype_eq_self
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      f := by
  apply Subtype.ext
  have hKernel := f.property
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 at hKernel
  exact
    ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_zero_iff_eq_vacuumProjector
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1 hKernel).symm

/-- The exact vacuum projection annihilates every vacuum-orthogonal vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply_vacuumOrthogonal_eq_zero
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
  apply Subtype.ext
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0
  apply
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_of_inner_vacuum_eq_zero
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1 f.property

/-- Centering annihilates every Poisson-kernel vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_poissonKernel_eq_zero
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
  apply Subtype.ext
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply]
  have hFix :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply_subtype_eq_self
      f
  have hFixCoe := congrArg
    (fun x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 =>
      (x : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
    hFix
  exact sub_eq_zero.mpr hFixCoe.symm

/-- Split an ambient Gibbs vector into its exact Poisson-kernel and
vacuum-orthogonal components. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelDecompositionL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2.prod
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2

/-- Pointwise form of the exact kernel-centered decomposition. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelDecompositionL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelDecompositionL2
        f =
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
          f,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f) := by
  rfl

/-- Recombine a Poisson-kernel vector and a vacuum-orthogonal vector by ambient
addition. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelRecombinationL2 :
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2.subtypeL.comp
      (ContinuousLinearMap.fst ℝ
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) +
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2.subtypeL.comp
      (ContinuousLinearMap.snd ℝ
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)

/-- Pointwise form of recombination. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombinationL2_apply
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelRecombinationL2
        x =
      (x.1 : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
        (x.2 : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- Recombining the exact decomposition returns the ambient vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombinationL2_apply_decomposition_eq_self
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelRecombinationL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelDecompositionL2
          f) = f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelDecompositionL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombinationL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply]
  abel

/-- Decomposing a recombined kernel/centered pair returns the pair. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelDecompositionL2_apply_recombination_eq_self
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelDecompositionL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelRecombinationL2
          x) = x := by
  rcases x with ⟨k, o⟩
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombinationL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelDecompositionL2_apply]
  have hkSubtype :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply_subtype_eq_self
      k
  have hk :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (k : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        (k : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
    calc
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (k : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
            (k : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
        rfl
      _ =
        (k : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
        congrArg
          (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 =>
            (z : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
          hkSubtype
  have hoSubtype :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorToRandomScanPoissonKernelL2_apply_vacuumOrthogonal_eq_zero
      o
  have ho :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (o : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    calc
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (o : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
            (o : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
        rfl
      _ = ((0 : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
        congrArg
          (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 =>
            (z : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
          hoSubtype
      _ = 0 := rfl
  have hProjectorAdd :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          ((k : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
            (o : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) =
        (k : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
    rw [map_add, hk, ho, add_zero]
  apply Prod.ext
  · apply Subtype.ext
    exact hProjectorAdd
  · apply Subtype.ext
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply,
      hProjectorAdd]
    abel

/-- The decomposition and recombination maps are mutual inverses. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombination_leftInverse_decomposition :
    Function.LeftInverse
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelRecombinationL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelDecompositionL2 := by
  intro f
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombinationL2_apply_decomposition_eq_self
      f

/-- The decomposition and recombination maps are mutual inverses in the other
direction. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombination_rightInverse_decomposition :
    Function.RightInverse
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelRecombinationL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelDecompositionL2 := by
  intro x
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelDecompositionL2_apply_recombination_eq_self
      x

/-- The ambient Gibbs space is continuously linearly equivalent to its exact
Poisson kernel times the Gibbs-vacuum orthogonal sector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure ≃L[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :=
  ContinuousLinearEquiv.equivOfInverse
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelDecompositionL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelRecombinationL2
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombination_leftInverse_decomposition
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelRecombination_rightInverse_decomposition

/-- The continuous decomposition equivalence has the exact coordinates
`(E₀ f, f - E₀ f)`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
        f =
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
          f,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
          f) := by
  rfl

/-- The inverse continuous equivalence recombines by ordinary addition. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_symm_apply
    (x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2 ×
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2.symm
        x =
      (x.1 : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) +
        (x.2 : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- The first-isomorphism theorem for the actual beta-zero Poisson operator:
quotient by the exact vacuum kernel and identify the range with `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelQuotientPoissonLinearEquivL2 :
    ((Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) ⧸
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelL2) ≃ₗ[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_range_eq_vacuumOrthogonalSubmoduleL2)

/-- The quotient first-isomorphism sends the class of `f` to its exact Poisson
image in `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelQuotientPoissonLinearEquivL2_apply_mk
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelQuotientPoissonLinearEquivL2
        (Submodule.Quotient.mk f) :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 f := by
  rfl

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

/-- Conjugating the ambient Poisson operator by the exact continuous
decomposition produces the block-diagonal operator `0 ⊕ (I-P)|Ω⊥`. -/
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
  exact_decomposition :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroGibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2
          f =
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumProjectorToRandomScanPoissonKernelL2
            f,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringToVacuumOrthogonalL2
            f)
  quotient_first_isomorphism :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonKernelQuotientPoissonLinearEquivL2
          (Submodule.Quotient.mk f) :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 f
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
      exact_decomposition :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply
      quotient_first_isomorphism :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonKernelQuotientPoissonLinearEquivL2_apply_mk
      block_diagonal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsL2ContinuousLinearEquivRandomScanPoissonKernelProdVacuumOrthogonalL2_apply_randomScanPoissonOperatorL2_eq_blockDiagonal }

end

end MathlibAnalytic
end MGAP4D
