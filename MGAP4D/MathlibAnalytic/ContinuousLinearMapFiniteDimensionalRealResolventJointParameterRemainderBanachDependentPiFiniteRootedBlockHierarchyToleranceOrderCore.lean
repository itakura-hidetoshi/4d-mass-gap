import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyToleranceOrderCore
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

/-- One finite maximum controls carrier, every hierarchy-node bundle, every
node block, every original coordinate, and trace. -/
noncomputable def continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteMaximum (fun t =>
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
      (epsilonBlock t) epsilonCoordinate epsilonTrace)

/-- Exact threshold characterization of the finite rooted hierarchy master. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_le_iff
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace ≤ N ↔
      continuousLinearMapJointRemainderCarrierSharpOrder
          q M epsilonCarrier ≤ N ∧
      (∀ t, continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
            φ (H.blockOf t)) q M (epsilonBundle t) ≤ N) ∧
      (∀ t b, continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockObservable
            φ (H.blockOf t) b) q M (epsilonBlock t b) ≤ N) ∧
      (∀ i, continuousLinearMapJointRemainderResponseSafeOrder
          (φ i) q M (epsilonCoordinate i) ≤ N) ∧
      continuousLinearMapJointRemainderTraceSafeOrder
          V q M epsilonTrace ≤ N := by
  unfold continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
  rw [continuousLinearMapJointRemainderFiniteMaximum_le_iff]
  constructor
  · intro h
    have hr :=
      (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff
        φ (H.blockOf H.root) q M epsilonCarrier (epsilonBundle H.root)
        (epsilonBlock H.root) epsilonCoordinate epsilonTrace N).1 (h H.root)
    refine ⟨hr.1, ?_, ?_, hr.2.2.2.1, hr.2.2.2.2⟩
    · intro t
      exact
        ((continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff
          φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
          (epsilonBlock t) epsilonCoordinate epsilonTrace N).1 (h t)).2.1
    · intro t b
      exact
        ((continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff
          φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
          (epsilonBlock t) epsilonCoordinate epsilonTrace N).1 (h t)).2.2.1 b
  · rintro ⟨hCarrier, hBundle, hBlock, hCoordinate, hTrace⟩ t
    exact
      (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff
        φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
        (epsilonBlock t) epsilonCoordinate epsilonTrace N).2
        ⟨hCarrier, hBundle t, hBlock t, hCoordinate, hTrace⟩

/-- Carrier order lies below the rooted hierarchy master. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilonCarrier ≤
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact
    (continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockToleranceMaster
      φ (H.blockOf H.root) q M epsilonCarrier (epsilonBundle H.root)
      (epsilonBlock H.root) epsilonCoordinate epsilonTrace).trans
      (continuousLinearMapJointRemainder_le_finiteMaximum
        (fun t => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
          (epsilonBlock t) epsilonCoordinate epsilonTrace) H.root)

/-- Every node-bundle response order lies below the rooted hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_nodeBundle_le_finiteRootedHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ (H.blockOf t)) q M (epsilonBundle t) ≤
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact
    (continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
      φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
      (epsilonBlock t) epsilonCoordinate epsilonTrace).trans
      (continuousLinearMapJointRemainder_le_finiteMaximum
        (fun s => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (H.blockOf s) q M epsilonCarrier (epsilonBundle s)
          (epsilonBlock s) epsilonCoordinate epsilonTrace) t)

/-- Every node-block response order lies below the rooted hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_nodeBlock_le_finiteRootedHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (t : τ) (b : β) (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ (H.blockOf t) b) q M (epsilonBlock t b) ≤
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact
    (continuousLinearMapJointRemainderResponseSafeOrder_block_le_toleranceMaster
      φ (H.blockOf t) b q M epsilonCarrier (epsilonBundle t)
      (epsilonBlock t) epsilonCoordinate epsilonTrace).trans
      (continuousLinearMapJointRemainder_le_finiteMaximum
        (fun s => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (H.blockOf s) q M epsilonCarrier (epsilonBundle s)
          (epsilonBlock s) epsilonCoordinate epsilonTrace) t)

/-- Every coordinate response order lies below the rooted hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (i : ι) (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M (epsilonCoordinate i) ≤
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact
    (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
      φ (H.blockOf H.root) i q M epsilonCarrier (epsilonBundle H.root)
      (epsilonBlock H.root) epsilonCoordinate epsilonTrace).trans
      (continuousLinearMapJointRemainder_le_finiteMaximum
        (fun t => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
          (epsilonBlock t) epsilonCoordinate epsilonTrace) H.root)

/-- Trace order lies below the rooted hierarchy master. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiFiniteRootedBlockHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (q M epsilonCarrier : ℝ)
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact
    (continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockToleranceMaster
      φ (H.blockOf H.root) q M epsilonCarrier (epsilonBundle H.root)
      (epsilonBlock H.root) epsilonCoordinate epsilonTrace).trans
      (continuousLinearMapJointRemainder_le_finiteMaximum
        (fun t => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
          (epsilonBlock t) epsilonCoordinate epsilonTrace) H.root)

/-- Pointwise relaxation of every carrier, node-bundle, node-block, coordinate,
and trace tolerance cannot increase the rooted hierarchy master. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_antitone
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    {q M epsilonCarrier₁ epsilonCarrier₂ epsilonTrace₁ epsilonTrace₂ : ℝ}
    {epsilonBundle₁ epsilonBundle₂ : τ → ℝ}
    {epsilonBlock₁ epsilonBlock₂ : τ → β → ℝ}
    {epsilonCoordinate₁ epsilonCoordinate₂ : ι → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hCarrier₁ : 0 < epsilonCarrier₁) (hCarrier₂ : 0 < epsilonCarrier₂)
    (hBundle₁ : ∀ t, 0 < epsilonBundle₁ t)
    (hBundle₂ : ∀ t, 0 < epsilonBundle₂ t)
    (hBlock₁ : ∀ t b, 0 < epsilonBlock₁ t b)
    (hBlock₂ : ∀ t b, 0 < epsilonBlock₂ t b)
    (hCoordinate₁ : ∀ i, 0 < epsilonCoordinate₁ i)
    (hCoordinate₂ : ∀ i, 0 < epsilonCoordinate₂ i)
    (hTrace₁ : 0 < epsilonTrace₁) (hTrace₂ : 0 < epsilonTrace₂)
    (hCarrier : epsilonCarrier₁ ≤ epsilonCarrier₂)
    (hBundle : ∀ t, epsilonBundle₁ t ≤ epsilonBundle₂ t)
    (hBlock : ∀ t b, epsilonBlock₁ t b ≤ epsilonBlock₂ t b)
    (hCoordinate : ∀ i, epsilonCoordinate₁ i ≤ epsilonCoordinate₂ i)
    (hTrace : epsilonTrace₁ ≤ epsilonTrace₂) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier₂ epsilonBundle₂ epsilonBlock₂
        epsilonCoordinate₂ epsilonTrace₂ ≤
      continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier₁ epsilonBundle₁ epsilonBlock₁
        epsilonCoordinate₁ epsilonTrace₁ := by
  apply continuousLinearMapJointRemainderFiniteMaximum_mono
  intro t
  exact
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_antitone
      φ (H.blockOf t) hq0 hq1 hM
      hCarrier₁ hCarrier₂ (hBundle₁ t) (hBundle₂ t)
      (hBlock₁ t) (hBlock₂ t) hCoordinate₁ hCoordinate₂
      hTrace₁ hTrace₂ hCarrier (hBundle t) (hBlock t) hCoordinate hTrace

/-- The master of any finite selected node family is bounded by the full rooted
hierarchy master. This is the subtree-restriction monotonicity law. -/
theorem continuousLinearMapJointRemainderFiniteMaximum_selectedNodes_le_full
    {δ : Type*} [Fintype δ]
    (node : δ → τ)
    (f : τ → ℕ) :
    continuousLinearMapJointRemainderFiniteMaximum (fun d => f (node d)) ≤
      continuousLinearMapJointRemainderFiniteMaximum f := by
  apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff _ _).2
  intro d
  exact continuousLinearMapJointRemainder_le_finiteMaximum f (node d)

/-- Under inherited root tolerances, every descendant node master is dominated
by the root master, so the whole hierarchy collapses exactly to the root. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_eq_rootMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    {q M epsilonCarrier epsilonTrace : ℝ}
    {epsilonBundle : τ → ℝ} {epsilonBlock : τ → β → ℝ}
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hCarrier : 0 < epsilonCarrier)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace)
    (hBundleRelax : ∀ t, epsilonBundle H.root ≤ epsilonBundle t)
    (hBlockRelax : ∀ t b,
      epsilonBlock H.root (H.blockMapAlong (H.depth t) t b) ≤
        epsilonBlock t b) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ (H.blockOf H.root) q M epsilonCarrier (epsilonBundle H.root)
        (epsilonBlock H.root) epsilonCoordinate epsilonTrace := by
  apply le_antisymm
  · apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff _ _).2
    intro t
    have hrelax :
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
            (epsilonBlock t) epsilonCoordinate epsilonTrace ≤
          continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf t) q M epsilonCarrier (epsilonBundle H.root)
            (epsilonBlock t) epsilonCoordinate epsilonTrace := by
      exact
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_antitone
          φ (H.blockOf t) hq0 hq1 hM
          hCarrier hCarrier (hBundle H.root) (hBundle t)
          (hBlock t) (hBlock t) hCoordinate hCoordinate
          hTrace hTrace le_rfl (hBundleRelax t)
          (fun _ => le_rfl) (fun _ => le_rfl) le_rfl
    exact hrelax.trans
      (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_fine_le_coarse
        (W := W) φ (H.blockOf t) (H.blockOf H.root)
        (H.blockMapAlong (H.depth t) t) (H.refines_root t)
        epsilonCoordinate hq0 hq1 hM (hBlock t) (hBlock H.root)
        (hBlockRelax t))
  · exact continuousLinearMapJointRemainder_le_finiteMaximum
      (fun t => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
        (epsilonBlock t) epsilonCoordinate epsilonTrace) H.root

/-- A rooted hierarchy whose root bundle is the common product bundle and whose
node/block tolerances are all non-stricter collapses to the previous dependent
Pi-product tolerance master. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_eq_productMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    {q M epsilonCarrier epsilonProduct epsilonTrace : ℝ}
    (epsilonBundle : τ → ℝ) (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hCarrier : 0 < epsilonCarrier)
    (hProduct : 0 < epsilonProduct)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace)
    (hRootBundle : epsilonBundle H.root = epsilonProduct)
    (hBundleRelax : ∀ t, epsilonProduct ≤ epsilonBundle t)
    (hBlockRelax : ∀ t b, epsilonProduct ≤ epsilonBlock t b) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  apply le_antisymm
  · apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff _ _).2
    intro t
    have hrelax :
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
            (epsilonBlock t) epsilonCoordinate epsilonTrace ≤
          continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf t) q M epsilonCarrier epsilonProduct
            (epsilonBlock t) epsilonCoordinate epsilonTrace := by
      exact
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_antitone
          φ (H.blockOf t) hq0 hq1 hM
          hCarrier hCarrier hProduct (hBundle t)
          (hBlock t) (hBlock t) hCoordinate hCoordinate
          hTrace hTrace le_rfl (hBundleRelax t)
          (fun _ => le_rfl) (fun _ => le_rfl) le_rfl
    exact hrelax.trans
      (le_of_eq
        (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_eq_productMaster
          φ (H.blockOf t) (epsilonBlock t) epsilonCoordinate
          hq0 hq1 hM hProduct (hBlock t) (hBlockRelax t)))
  · have hEqRoot :
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
            φ (H.blockOf H.root) q M epsilonCarrier (epsilonBundle H.root)
            (epsilonBlock H.root) epsilonCoordinate epsilonTrace =
          continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
            φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
      rw [hRootBundle]
      exact
        continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_eq_productMaster
          φ (H.blockOf H.root) (epsilonBlock H.root) epsilonCoordinate
          hq0 hq1 hM hProduct (hBlock H.root) (hBlockRelax H.root)
    rw [← hEqRoot]
    exact continuousLinearMapJointRemainder_le_finiteMaximum
      (fun t => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ (H.blockOf t) q M epsilonCarrier (epsilonBundle t)
        (epsilonBlock t) epsilonCoordinate epsilonTrace) H.root

/-- A finite maximum over two hierarchy nodes is exactly an ordinary maximum. -/
theorem continuousLinearMapJointRemainderFiniteMaximum_bool_eq_max
    (f : Bool → ℕ) :
    continuousLinearMapJointRemainderFiniteMaximum f = max (f false) (f true) := by
  apply le_antisymm
  · apply (continuousLinearMapJointRemainderFiniteMaximum_le_iff f _).2
    intro b
    cases b <;> simp
  · exact max_le
      (continuousLinearMapJointRemainder_le_finiteMaximum f false)
      (continuousLinearMapJointRemainder_le_finiteMaximum f true)

/-- The homogeneous two-node specialization is exactly the merged coarse/fine
hierarchy master from the preceding package. -/
theorem continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_bool_eq_blockHierarchyMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (H : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι Bool β)
    (fineOf coarseOf : ι → β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine epsilonCoarse : β → ℝ)
    (epsilonNodeBundle : Bool → ℝ) (epsilonNodeBlock : Bool → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCoarse : H.blockOf false = coarseOf)
    (hFine : H.blockOf true = fineOf)
    (hBundleFalse : epsilonNodeBundle false = epsilonBundle)
    (hBundleTrue : epsilonNodeBundle true = epsilonBundle)
    (hBlockFalse : epsilonNodeBlock false = epsilonCoarse)
    (hBlockTrue : epsilonNodeBlock true = epsilonFine) :
    continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
        φ H q M epsilonCarrier epsilonNodeBundle epsilonNodeBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  unfold continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
  rw [continuousLinearMapJointRemainderFiniteMaximum_bool_eq_max]
  unfold continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
  simp [hCoarse, hFine, hBundleFalse, hBundleTrue, hBlockFalse, hBlockTrue]

end MathlibAnalytic
end MGAP4D
