import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- Composed block-parent maps split exactly at every intermediate point of a
rooted path. The first `n` steps are followed by the remaining `m` steps. -/
theorem ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.blockMapAlong_add
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (m n : ℕ) (t : τ) :
    H.blockMapAlong (m + n) t =
      H.blockMapAlong m ((H.parent^[n]) t) ∘ H.blockMapAlong n t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [H.blockMapAlong_succ, Function.iterate_succ_apply]
      rw [ih (t := H.parent t)]
      simp only [Function.comp_assoc]

/-- Parent iteration itself splits at every intermediate point. -/
theorem ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.parent_iterate_add
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (m n : ℕ) (t : τ) :
    (H.parent^[m + n]) t = (H.parent^[m]) ((H.parent^[n]) t) := by
  exact Function.iterate_add_apply H.parent m n t

/-- A finite level cut chooses, for every hierarchy node, a canonical ancestor
on its path to the root. The cut never passes beyond the recorded root depth. -/
structure ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.LevelCut
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β) where
  steps : τ → ℕ
  steps_le_depth : ∀ t, steps t ≤ H.depth t

namespace ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.LevelCut

variable {ι τ β : Type*}
variable {H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β}

/-- The ancestor node selected by a level cut. -/
def node (C : H.LevelCut) (t : τ) : τ :=
  (H.parent^[C.steps t]) t

/-- The block-label transport from a node to its selected cut ancestor. -/
def blockMap (C : H.LevelCut) (t : τ) : β → β :=
  H.blockMapAlong (C.steps t) t

/-- Every node partition refines its selected cut partition. -/
theorem refines (C : H.LevelCut) (t : τ) :
    ContinuousLinearMapJointDependentPiBlockRefines
      (H.blockOf t) (H.blockOf (C.node t)) (C.blockMap t) := by
  exact H.refines_iterate (C.steps t) t

/-- The identity cut leaves every node unchanged. -/
def identity (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β) :
    H.LevelCut where
  steps := fun _ => 0
  steps_le_depth := fun _ => Nat.zero_le _

@[simp] theorem identity_node
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) :
    (identity H).node t = t := by
  rfl

@[simp] theorem identity_blockMap
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) :
    (identity H).blockMap t = id := by
  rfl

/-- The root cut sends every node to the distinguished root along its canonical
depth path. -/
def root (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β) :
    H.LevelCut where
  steps := H.depth
  steps_le_depth := fun _ => le_rfl

@[simp] theorem root_node
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) :
    (root H).node t = H.root := by
  exact H.reaches_root t

@[simp] theorem root_steps
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) :
    (root H).steps t = H.depth t := by
  rfl

end ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.LevelCut

variable {V ι τ β : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [Fintype ι] [Fintype τ] [Fintype β]
variable [DecidableEq β]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Zero-step ancestor restriction is exactly the identity map. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap_zero
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) (b : β) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
        (W := W) H 0 t b =
      ContinuousLinearMap.id ℝ
        (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
          (H.blockOf t) b, W i.1) := by
  ext x i
  rfl

/-- One-step ancestor restriction is the original fine-to-parent block
restriction from the two-level hierarchy calculus. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap_one
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) (b : β) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
        (W := W) H 1 t b =
      continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
        (W := W) (H.blockOf t) (H.blockOf (H.parent t))
        (H.blockParent t) (H.refines t) b := by
  ext x i
  rfl

/-- Exact pointwise action of a restriction path split into `n` initial steps
and `m` subsequent steps. This is the composition law before normalization of
the propositionally equal direct-path domain. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap_split_apply
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (m n : ℕ) (t : τ) (b : β)
    (x : ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        (H.blockOf ((H.parent^[m]) ((H.parent^[n]) t)))
        (H.blockMapAlong m ((H.parent^[n]) t)
          (H.blockMapAlong n t b)), W i.1)
    (i : continuousLinearMapJointRemainderDependentPiBlockFiber
      (H.blockOf t) b) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
        (W := W) H n t b
        (continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
          (W := W) H m ((H.parent^[n]) t) (H.blockMapAlong n t b) x) i =
      x ⟨i.1, by
        have h₁ := H.refines_iterate n t i.1
        have h₂ := H.refines_iterate m ((H.parent^[n]) t) i.1
        simpa [h₁, i.2] using h₂⟩ := by
  rfl

/-- Norm domination factors through every intermediate ancestor. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiFiniteRootedDescendantObservable_path_chain
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (m n : ℕ) (t : τ) (b : β) :
    ‖continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf t) b‖ ≤
      ‖continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b)‖ ∧
    ‖continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b)‖ ≤
      ‖continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf ((H.parent^[m + n]) t))
          (H.blockMapAlong (m + n) t b)‖ := by
  constructor
  · exact
      continuousLinearMapJointRemainder_norm_dependentPiFiniteRootedDescendantObservable_le_ancestorObservable
        (W := W) φ H n t b
  · have h :=
      continuousLinearMapJointRemainder_norm_dependentPiFiniteRootedDescendantObservable_le_ancestorObservable
        (W := W) φ H m ((H.parent^[n]) t) (H.blockMapAlong n t b)
    rw [H.parent_iterate_add m n t, H.blockMapAlong_add m n t]
    simpa only [Function.comp_apply] using h

/-- Response-safe-order domination factors through every intermediate ancestor
at one common positive tolerance. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_finiteRooted_path_chain
    [FiniteDimensional ℝ V]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (m n : ℕ) (t : τ) (b : β)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf t) b) q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b))
        q M epsilon ∧
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b))
        q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf ((H.parent^[m + n]) t))
          (H.blockMapAlong (m + n) t b)) q M epsilon := by
  constructor
  · exact
      continuousLinearMapJointRemainderResponseSafeOrder_finiteRootedDescendant_le_ancestor
        (W := W) φ H n t b hq0 hq1 hM hepsilon
  · have h :=
      continuousLinearMapJointRemainderResponseSafeOrder_finiteRootedDescendant_le_ancestor
        (W := W) φ H m ((H.parent^[n]) t) (H.blockMapAlong n t b)
        hq0 hq1 hM hepsilon
    rw [H.parent_iterate_add m n t, H.blockMapAlong_add m n t]
    simpa only [Function.comp_apply] using h

end MathlibAnalytic
end MGAP4D
