import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyPathCutCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyToleranceOrderCore
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

/-- The master obtained by replacing every hierarchy node by the ancestor
selected by a finite level cut. Repetitions are harmless because the master is
a finite maximum. -/
noncomputable def continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (C : H.LevelCut)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteMaximum (fun t =>
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ (H.blockOf (C.node t)) q M epsilonCarrier
      (epsilonBundle (C.node t)) (epsilonBlock (C.node t))
      epsilonCoordinate epsilonTrace)

/-- Selecting ancestors cannot create a master larger than the full hierarchy
master evaluated on all nodes. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder_le_full
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (C : H.LevelCut)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder
        φ H C q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact
    continuousLinearMapJointRemainderFiniteMaximum_selectedNodes_le_full
      (node := C.node)
      (f := fun t =>
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
          (epsilonBlock t) epsilonCoordinate epsilonTrace)

/-- The identity level cut recovers the original hierarchy master exactly. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder_identity
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder
        φ H (.identity H) q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  rfl

/-- If every descendant tolerance inherits or relaxes the tolerance of its cut
ancestor, the full hierarchy master collapses exactly to the cut master. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_eq_levelCutMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (C : H.LevelCut)
    {q M epsilonCarrier epsilonTrace : ℝ}
    {epsilonBundle : τ → ℝ} {epsilonBlock : τ → β → ℝ}
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hCarrier : 0 < epsilonCarrier)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace)
    (hBundleRelax : ∀ t, epsilonBundle (C.node t) ≤ epsilonBundle t)
    (hBlockRelax : ∀ t b,
      epsilonBlock (C.node t) (C.blockMap t b) ≤ epsilonBlock t b) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder
        φ H C q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  apply le_antisymm
  · apply continuousLinearMapJointRemainderFiniteMaximum_mono
    intro t
    have hrelax :
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
            (epsilonBlock t) epsilonCoordinate epsilonTrace ≤
          continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf t) q M epsilonCarrier (epsilonBundle (C.node t))
            (epsilonBlock t) epsilonCoordinate epsilonTrace := by
      exact
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_antitone
          φ (H.blockOf t) hq0 hq1 hM
          hCarrier hCarrier (hBundle (C.node t)) (hBundle t)
          (hBlock t) (hBlock t) hCoordinate hCoordinate
          hTrace hTrace le_rfl (hBundleRelax t)
          (fun _ => le_rfl) (fun _ => le_rfl) le_rfl
    exact hrelax.trans
      (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_fine_le_coarse
        (W := W) φ (H.blockOf t) (H.blockOf (C.node t))
        (C.blockMap t) (C.refines t) epsilonCoordinate
        hq0 hq1 hM (hBlock t) (hBlock (C.node t)) (hBlockRelax t))
  · exact
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder_le_full
        φ H C q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace

/-- The root cut is a finite maximum of one repeated root master, hence equals
that root master exactly. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder_root
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyLevelCutToleranceMasterSafeOrder
        φ H (.root H) q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ (H.blockOf H.root) q M epsilonCarrier (epsilonBundle H.root)
        (epsilonBlock H.root) epsilonCoordinate epsilonTrace := by
  apply le_antisymm
  · apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff _ _).2
    intro t
    simp
  · simpa using
      (continuousLinearMapJointRemainder_le_finiteMaximum
        (fun t =>
          continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf ((.root H).node t)) q M epsilonCarrier
            (epsilonBundle ((.root H).node t))
            (epsilonBlock ((.root H).node t))
            epsilonCoordinate epsilonTrace) H.root)

/-- A finite maximum is invariant under a surjective reindexing. -/
theorem continuousLinearMapJointRemainderFiniteMaximum_comp_surjective_eq
    {δ : Type*} [Fintype δ]
    (node : τ → δ) (hnode : Function.Surjective node)
    (f : δ → ℕ) :
    continuousLinearMapJointRemainderFiniteMaximum (fun t => f (node t)) =
      continuousLinearMapJointRemainderFiniteMaximum f := by
  apply le_antisymm
  · exact continuousLinearMapJointRemainderFiniteMaximum_selectedNodes_le_full node f
  · apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff f _).2
    intro d
    rcases hnode d with ⟨t, rfl⟩
    exact
      continuousLinearMapJointRemainder_le_finiteMaximum
        (fun s => f (node s)) t

end MathlibAnalytic
end MGAP4D
