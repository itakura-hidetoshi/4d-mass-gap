import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {V ι κ λ : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype κ] [Fintype λ]
variable [DecidableEq κ] [DecidableEq λ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- One hierarchy master simultaneously controls one coarse partition and one
fine partition of the same dependent finite response family. -/
noncomputable def continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  max
    (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
      epsilonCoordinate epsilonTrace)
    (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ fineOf q M epsilonCarrier epsilonBundle epsilonFine
      epsilonCoordinate epsilonTrace)

/-- Exact seven-channel threshold characterization of the hierarchy master. -/
theorem continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_le_iff
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace ≤ N ↔
      continuousLinearMapJointRemainderCarrierSharpOrder
          q M epsilonCarrier ≤ N ∧
      continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
            φ coarseOf) q M epsilonBundle ≤ N ∧
      continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
            φ fineOf) q M epsilonBundle ≤ N ∧
      (∀ c, continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockObservable
            φ coarseOf c) q M (epsilonCoarse c) ≤ N) ∧
      (∀ k, continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockObservable
            φ fineOf k) q M (epsilonFine k) ≤ N) ∧
      (∀ i, continuousLinearMapJointRemainderResponseSafeOrder
          (φ i) q M (epsilonCoordinate i) ≤ N) ∧
      continuousLinearMapJointRemainderTraceSafeOrder
          V q M epsilonTrace ≤ N := by
  unfold continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
  rw [max_le_iff]
  rw [continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff]
  rw [continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff]
  tauto

/-- The carrier order lies below the hierarchy master. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilonCarrier ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockToleranceMaster
    φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
    epsilonCoordinate epsilonTrace).trans (le_max_left _ _)

/-- The coarse bundle order lies below the hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coarseBundle_le_hierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ coarseOf) q M epsilonBundle ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
    φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
    epsilonCoordinate epsilonTrace).trans (le_max_left _ _)

/-- The fine bundle order lies below the hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_fineBundle_le_hierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ fineOf) q M epsilonBundle ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
    φ fineOf q M epsilonCarrier epsilonBundle epsilonFine
    epsilonCoordinate epsilonTrace).trans (le_max_right _ _)

/-- Every coarse block order lies below the hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coarseBlock_le_hierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (c : λ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ coarseOf c) q M (epsilonCoarse c) ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_block_le_toleranceMaster
    φ coarseOf c q M epsilonCarrier epsilonBundle epsilonCoarse
    epsilonCoordinate epsilonTrace).trans (le_max_left _ _)

/-- Every fine block order lies below the hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_hierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (k : κ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ fineOf k) q M (epsilonFine k) ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_block_le_toleranceMaster
    φ fineOf k q M epsilonCarrier epsilonBundle epsilonFine
    epsilonCoordinate epsilonTrace).trans (le_max_right _ _)

/-- Every coordinate order lies below the hierarchy master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (i : ι)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M (epsilonCoordinate i) ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
    φ coarseOf i q M epsilonCarrier epsilonBundle epsilonCoarse
    epsilonCoordinate epsilonTrace).trans (le_max_left _ _)

/-- The trace order lies below the hierarchy master. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockHierarchyToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockToleranceMaster
    φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
    epsilonCoordinate epsilonTrace).trans (le_max_left _ _)

/-- A fine block master is bounded by its compatible parent coarse block
master when every fine tolerance is inherited from or relaxed relative to its
parent coarse tolerance. -/
theorem continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_fine_le_coarse
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (parent : κ → λ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent)
    {q M epsilonCarrier epsilonBundle epsilonTrace : ℝ}
    {epsilonFine : κ → ℝ} {epsilonCoarse : λ → ℝ}
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax : ∀ k, epsilonCoarse (parent k) ≤ epsilonFine k) :
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ fineOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoordinate epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  apply (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff
    φ fineOf q M epsilonCarrier epsilonBundle epsilonFine
    epsilonCoordinate epsilonTrace _).2
  refine ⟨
    continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockToleranceMaster
      φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
      epsilonCoordinate epsilonTrace,
    ?_, ?_, ?_,
    continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockToleranceMaster
      φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
      epsilonCoordinate epsilonTrace⟩
  · rw [continuousLinearMapJointRemainderResponseSafeOrder_dependentPiBlockBundle_eq
      (W := W) φ fineOf q M epsilonBundle]
    rw [← continuousLinearMapJointRemainderResponseSafeOrder_dependentPiBlockBundle_eq
      (W := W) φ coarseOf q M epsilonBundle]
    exact continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
      φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
      epsilonCoordinate epsilonTrace
  · intro k
    exact (continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_coarseBlock_of_parentTolerance_le
      (W := W) φ fineOf coarseOf parent hrefines k
      hq0 hq1 hM hFine hCoarse hRelax).trans
      (continuousLinearMapJointRemainderResponseSafeOrder_block_le_toleranceMaster
        φ coarseOf (parent k) q M epsilonCarrier epsilonBundle epsilonCoarse
        epsilonCoordinate epsilonTrace)
  · intro i
    exact continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
      φ coarseOf i q M epsilonCarrier epsilonBundle epsilonCoarse
      epsilonCoordinate epsilonTrace

/-- Under inherited block tolerances, the hierarchy master collapses exactly
to the coarse block master. -/
theorem continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_eq_coarseMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (parent : κ → λ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent)
    {q M epsilonCarrier epsilonBundle epsilonTrace : ℝ}
    {epsilonFine : κ → ℝ} {epsilonCoarse : λ → ℝ}
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax : ∀ k, epsilonCoarse (parent k) ≤ epsilonFine k) :
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  unfold continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
  exact max_eq_left
    (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_fine_le_coarse
      (W := W) φ fineOf coarseOf parent hrefines epsilonCoordinate
      hq0 hq1 hM hFine hCoarse hRelax)

/-- The identity two-level hierarchy is definitionally the original block
master. -/
theorem continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_refl
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → κ) (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ blockOf blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonBlock epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  simp [continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder]

/-- Relaxing any hierarchy tolerance cannot increase the hierarchy master. -/
theorem continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_antitone
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    {q M epsilonCarrier₁ epsilonCarrier₂ epsilonBundle₁ epsilonBundle₂
      epsilonTrace₁ epsilonTrace₂ : ℝ}
    {epsilonFine₁ epsilonFine₂ : κ → ℝ}
    {epsilonCoarse₁ epsilonCoarse₂ : λ → ℝ}
    {epsilonCoordinate₁ epsilonCoordinate₂ : ι → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hCarrier₁ : 0 < epsilonCarrier₁) (hCarrier₂ : 0 < epsilonCarrier₂)
    (hBundle₁ : 0 < epsilonBundle₁) (hBundle₂ : 0 < epsilonBundle₂)
    (hFine₁ : ∀ k, 0 < epsilonFine₁ k)
    (hFine₂ : ∀ k, 0 < epsilonFine₂ k)
    (hCoarse₁ : ∀ c, 0 < epsilonCoarse₁ c)
    (hCoarse₂ : ∀ c, 0 < epsilonCoarse₂ c)
    (hCoordinate₁ : ∀ i, 0 < epsilonCoordinate₁ i)
    (hCoordinate₂ : ∀ i, 0 < epsilonCoordinate₂ i)
    (hTrace₁ : 0 < epsilonTrace₁) (hTrace₂ : 0 < epsilonTrace₂)
    (hCarrier : epsilonCarrier₁ ≤ epsilonCarrier₂)
    (hBundle : epsilonBundle₁ ≤ epsilonBundle₂)
    (hFine : ∀ k, epsilonFine₁ k ≤ epsilonFine₂ k)
    (hCoarse : ∀ c, epsilonCoarse₁ c ≤ epsilonCoarse₂ c)
    (hCoordinate : ∀ i, epsilonCoordinate₁ i ≤ epsilonCoordinate₂ i)
    (hTrace : epsilonTrace₁ ≤ epsilonTrace₂) :
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier₂ epsilonBundle₂ epsilonFine₂
        epsilonCoarse₂ epsilonCoordinate₂ epsilonTrace₂ ≤
      continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier₁ epsilonBundle₁ epsilonFine₁
        epsilonCoarse₁ epsilonCoordinate₁ epsilonTrace₁ := by
  unfold continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
  exact max_le_max
    (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_antitone
      φ coarseOf hq0 hq1 hM hCarrier₁ hCarrier₂ hBundle₁ hBundle₂
      hCoarse₁ hCoarse₂ hCoordinate₁ hCoordinate₂ hTrace₁ hTrace₂
      hCarrier hBundle hCoarse hCoordinate hTrace)
    (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_antitone
      φ fineOf hq0 hq1 hM hCarrier₁ hCarrier₂ hBundle₁ hBundle₂
      hFine₁ hFine₂ hCoordinate₁ hCoordinate₂ hTrace₁ hTrace₂
      hCarrier hBundle hFine hCoordinate hTrace)

/-- If both coarse and fine block tolerances are no stricter than the common
bundle tolerance, the hierarchy master is exactly the previous product master. -/
theorem continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder_eq_productMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    {q M epsilonCarrier epsilonBundle epsilonTrace : ℝ}
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hFineRelax : ∀ k, epsilonBundle ≤ epsilonFine k)
    (hCoarseRelax : ∀ c, epsilonBundle ≤ epsilonCoarse c) :
    continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
        φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoarse epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonBundle epsilonCoordinate epsilonTrace := by
  unfold continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
  rw [continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_eq_productMaster
    (W := W) φ coarseOf epsilonCoarse epsilonCoordinate
    hq0 hq1 hM hBundle hCoarse hCoarseRelax]
  rw [continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_eq_productMaster
    (W := W) φ fineOf epsilonFine epsilonCoordinate
    hq0 hq1 hM hBundle hFine hFineRelax]
  exact max_self _

/-- Hierarchical domination composes along a three-level refinement chain. -/
theorem continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_chain_le
    {μ : Type*} [Fintype μ] [DecidableEq μ]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (middleOf : ι → λ) (coarseOf : ι → μ)
    (parent₁ : κ → λ) (parent₂ : λ → μ)
    (hrefines₁ : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf middleOf parent₁)
    (hrefines₂ : ContinuousLinearMapJointDependentPiBlockRefines
      middleOf coarseOf parent₂)
    {q M epsilonCarrier epsilonBundle epsilonTrace : ℝ}
    {epsilonFine : κ → ℝ} {epsilonMiddle : λ → ℝ}
    {epsilonCoarse : μ → ℝ}
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hMiddle : ∀ m, 0 < epsilonMiddle m)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax₁ : ∀ k, epsilonMiddle (parent₁ k) ≤ epsilonFine k)
    (hRelax₂ : ∀ m, epsilonCoarse (parent₂ m) ≤ epsilonMiddle m) :
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ fineOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoordinate epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
        epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_fine_le_coarse
    (W := W) φ fineOf middleOf parent₁ hrefines₁ epsilonCoordinate
    hq0 hq1 hM hFine hMiddle hRelax₁).trans
    (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_fine_le_coarse
      (W := W) φ middleOf coarseOf parent₂ hrefines₂ epsilonCoordinate
      hq0 hq1 hM hMiddle hCoarse hRelax₂)

end MathlibAnalytic
end MGAP4D
