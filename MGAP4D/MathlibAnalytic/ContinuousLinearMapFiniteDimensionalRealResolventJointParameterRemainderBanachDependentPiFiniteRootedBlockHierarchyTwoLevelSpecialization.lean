import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyPathCutToleranceOrderCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {V ι τ β : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype τ] [Fintype β]
variable [DecidableEq β]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- A finite maximum of a two-valued family classified by a surjective Boolean
level map is exactly the maximum of the coarse and fine values. -/
theorem continuousLinearMapJointRemainderFiniteMaximum_twoLevelClassifier_eq_max
    (level : τ → Bool) (hlevel : Function.Surjective level)
    (f : τ → ℕ) (coarse fine : ℕ)
    (hCoarse : ∀ t, level t = false → f t = coarse)
    (hFine : ∀ t, level t = true → f t = fine) :
    continuousLinearMapJointRemainderFiniteMaximum f = max coarse fine := by
  let g : Bool → ℕ := fun b => if b then fine else coarse
  have hf : f = fun t => g (level t) := by
    funext t
    cases h : level t with
    | false => simpa [g, h] using hCoarse t h
    | true => simpa [g, h] using hFine t h
  rw [hf,
    continuousLinearMapJointRemainderFiniteMaximum_comp_surjective_eq
      level hlevel g,
    continuousLinearMapJointRemainderFiniteMaximum_bool_eq_max]
  rfl

/-- Any finite rooted hierarchy whose node data take exactly two homogeneous
levels specializes to the preceding coarse/fine block-hierarchy master. The
node type need not be `Bool`; only a surjective Boolean level classifier is
required. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_twoLevel_eq_blockHierarchyMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (level : τ → Bool) (hlevel : Function.Surjective level)
    (fineOf coarseOf : ι → β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine epsilonCoarse : β → ℝ)
    (epsilonNodeBundle : τ → ℝ) (epsilonNodeBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hBlockOf : ∀ t, H.blockOf t = if level t then fineOf else coarseOf)
    (hBundle : ∀ t, epsilonNodeBundle t = epsilonBundle)
    (hBlock : ∀ t,
      epsilonNodeBlock t = if level t then epsilonFine else epsilonCoarse) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonNodeBundle epsilonNodeBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  let coarseMaster :=
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
      epsilonCoordinate epsilonTrace
  let fineMaster :=
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ fineOf q M epsilonCarrier epsilonBundle epsilonFine
      epsilonCoordinate epsilonTrace
  unfold continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
  have hmax :=
    continuousLinearMapJointRemainderFiniteMaximum_twoLevelClassifier_eq_max
      level hlevel
      (fun t =>
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (H.blockOf t) q M epsilonCarrier (epsilonNodeBundle t)
          (epsilonNodeBlock t) epsilonCoordinate epsilonTrace)
      coarseMaster fineMaster
      (fun t ht => by
        have hOf := hBlockOf t
        have hTol := hBlock t
        simp [ht] at hOf hTol
        simp [coarseMaster, hOf, hBundle t, hTol])
      (fun t ht => by
        have hOf := hBlockOf t
        have hTol := hBlock t
        simp [ht] at hOf hTol
        simp [fineMaster, hOf, hBundle t, hTol])
  rw [hmax]
  rfl

end MathlibAnalytic
end MGAP4D
