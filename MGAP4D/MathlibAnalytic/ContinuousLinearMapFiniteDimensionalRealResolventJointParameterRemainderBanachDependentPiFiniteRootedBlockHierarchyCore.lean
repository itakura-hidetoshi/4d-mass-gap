import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- A node is an ancestor of another node when it is reached by finitely many
applications of the parent map. -/
def ContinuousLinearMapJointFiniteRootedAncestor
    {τ : Type*} (parent : τ → τ) (descendant ancestor : τ) : Prop :=
  ∃ n : ℕ, (parent^[n]) descendant = ancestor

/-- Every node is its own ancestor. -/
theorem continuousLinearMapJointFiniteRootedAncestor_refl
    {τ : Type*} (parent : τ → τ) (t : τ) :
    ContinuousLinearMapJointFiniteRootedAncestor parent t t := by
  exact ⟨0, rfl⟩

/-- Ancestorhood is transitive. -/
theorem continuousLinearMapJointFiniteRootedAncestor_trans
    {τ : Type*} {parent : τ → τ} {d a r : τ}
    (hda : ContinuousLinearMapJointFiniteRootedAncestor parent d a)
    (har : ContinuousLinearMapJointFiniteRootedAncestor parent a r) :
    ContinuousLinearMapJointFiniteRootedAncestor parent d r := by
  rcases hda with ⟨n, hn⟩
  rcases har with ⟨m, hm⟩
  refine ⟨n + m, ?_⟩
  rw [Function.iterate_add_apply, hn, hm]

/-- A finite rooted hierarchy of finite coordinate partitions. Every hierarchy
node carries a block assignment. The explicit `blockParent` map transports a
block label to the parent partition, and `refines` records exact compatibility.
The depth witness makes every node reach the distinguished root in finitely
many parent steps. -/
structure ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy
    (ι τ β : Type*) where
  root : τ
  parent : τ → τ
  blockOf : τ → ι → β
  blockParent : τ → β → β
  depth : τ → ℕ
  parent_root : parent root = root
  blockParent_root : blockParent root = id
  depth_root : depth root = 0
  parent_depth_lt : ∀ t, t ≠ root → depth (parent t) < depth t
  reaches_root : ∀ t, (parent^[depth t]) t = root
  refines : ∀ t, ContinuousLinearMapJointDependentPiBlockRefines
    (blockOf t) (blockOf (parent t)) (blockParent t)

/-- Composition of block-parent maps along `n` parent steps. -/
def ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.blockMapAlong
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β) :
    ℕ → τ → β → β
  | 0, _ => id
  | n + 1, t => H.blockMapAlong n (H.parent t) ∘ H.blockParent t

@[simp] theorem ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.blockMapAlong_zero
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) : H.blockMapAlong 0 t = id := by
  rfl

@[simp] theorem ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.blockMapAlong_succ
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) :
    H.blockMapAlong (n + 1) t =
      H.blockMapAlong n (H.parent t) ∘ H.blockParent t := by
  rfl

/-- The composed block map exactly realizes refinement from a node to every
finite ancestor reached by iterating `parent`. -/
theorem ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.refines_iterate
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) :
    ContinuousLinearMapJointDependentPiBlockRefines
      (H.blockOf t) (H.blockOf ((H.parent^[n]) t))
      (H.blockMapAlong n t) := by
  induction n generalizing t with
  | zero =>
      simpa using
        (continuousLinearMapJointDependentPiBlockRefines_refl (H.blockOf t))
  | succ n ih =>
      have hstep := H.refines t
      have htail := ih (H.parent t)
      simpa [Nat.succ_eq_add_one, Function.iterate_succ_apply] using
        (continuousLinearMapJointDependentPiBlockRefines_trans hstep htail)

/-- Every hierarchy node refines the root through its canonical depth path. -/
theorem ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy.refines_root
    {ι τ β : Type*}
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) :
    ContinuousLinearMapJointDependentPiBlockRefines
      (H.blockOf t) (H.blockOf H.root)
      (H.blockMapAlong (H.depth t) t) := by
  simpa [H.reaches_root t] using H.refines_iterate (H.depth t) t

variable {V ι τ β : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [Fintype ι] [Fintype τ] [Fintype β]
variable [DecidableEq β]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Restrict an ancestor block product to a descendant block along an arbitrary
finite parent path. -/
noncomputable def continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) (b : β) :
    (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b), W i.1) →L[ℝ]
      (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        (H.blockOf t) b, W i.1) :=
  continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
    (W := W) (H.blockOf t) (H.blockOf ((H.parent^[n]) t))
    (H.blockMapAlong n t) (H.refines_iterate n t) b

@[simp] theorem continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap_apply
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) (b : β)
    (x : ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b), W i.1)
    (i : continuousLinearMapJointRemainderDependentPiBlockFiber
      (H.blockOf t) b) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
      (W := W) H n t b x i =
      x ⟨i.1, by simpa [i.2] using (H.refines_iterate n t i.1)⟩ := by
  rfl

/-- Every ancestor-to-descendant restriction map is contractive. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiFiniteRootedAncestorRestrictionMap_le_one
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) (b : β) :
    ‖(continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
      (W := W) H n t b)‖ ≤ 1 := by
  exact
    continuousLinearMapJointRemainder_norm_dependentPiFineBlockRestrictionMap_le_one
      (W := W) (H.blockOf t) (H.blockOf ((H.parent^[n]) t))
      (H.blockMapAlong n t) (H.refines_iterate n t) b

/-- A descendant observable is recovered exactly by postcomposing its ancestor
observable with the canonical restriction contraction. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap_comp_ancestorObservable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) (b : β) :
    (continuousLinearMapJointRemainderDependentPiFiniteRootedAncestorRestrictionMap
      (W := W) H n t b).comp
      (continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b)) =
      continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf t) b := by
  exact
    continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap_comp_coarseBlockObservable
      (W := W) φ (H.blockOf t) (H.blockOf ((H.parent^[n]) t))
      (H.blockMapAlong n t) (H.refines_iterate n t) b

/-- Descendant block observables have no larger norm than arbitrary ancestor
block observables on the same rooted path. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiFiniteRootedDescendantObservable_le_ancestorObservable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) (b : β) :
    ‖continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf t) b‖ ≤
      ‖continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b)‖ := by
  exact
    continuousLinearMapJointRemainder_norm_dependentPiFineBlockObservable_le_coarseBlockObservable
      (W := W) φ (H.blockOf t) (H.blockOf ((H.parent^[n]) t))
      (H.blockMapAlong n t) (H.refines_iterate n t) b

/-- At a common tolerance, every descendant safe order is bounded by the safe
order of the corresponding arbitrary ancestor block. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_finiteRootedDescendant_le_ancestor
    [FiniteDimensional ℝ V]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) (b : β)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf t) b) q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b))
        q M epsilon := by
  exact continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_coarseBlock
    (W := W) φ (H.blockOf t) (H.blockOf ((H.parent^[n]) t))
    (H.blockMapAlong n t) (H.refines_iterate n t) b
    hq0 hq1 hM hepsilon

/-- Descendant safe orders remain controlled when their tolerance is inherited
from, or relaxed relative to, the ancestor tolerance. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_finiteRootedDescendant_le_ancestor_of_tolerance
    [FiniteDimensional ℝ V]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (n : ℕ) (t : τ) (b : β)
    {q M : ℝ} {epsilonDescendant epsilonAncestor : β → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hDescendant : ∀ c, 0 < epsilonDescendant c)
    (hAncestor : ∀ c, 0 < epsilonAncestor c)
    (hRelax : ∀ c,
      epsilonAncestor (H.blockMapAlong n t c) ≤ epsilonDescendant c) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf t) b) q M (epsilonDescendant b) ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf ((H.parent^[n]) t)) (H.blockMapAlong n t b))
        q M (epsilonAncestor (H.blockMapAlong n t b)) := by
  exact
    continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_coarseBlock_of_parentTolerance_le
      (W := W) φ (H.blockOf t) (H.blockOf ((H.parent^[n]) t))
      (H.blockMapAlong n t) (H.refines_iterate n t) b
      hq0 hq1 hM hDescendant hAncestor hRelax

end MathlibAnalytic
end MGAP4D
