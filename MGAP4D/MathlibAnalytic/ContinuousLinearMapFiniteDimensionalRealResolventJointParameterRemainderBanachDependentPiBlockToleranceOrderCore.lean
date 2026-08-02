import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockDecompositionCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {V ι β : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype β] [DecidableEq β]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- A finite family of differently typed block observables with one tolerance
per block. -/
noncomputable def continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder
    {Z : β → Type*}
    [∀ b, NormedAddCommGroup (Z b)] [∀ b, NormedSpace ℝ (Z b)]
    (ψ : ∀ b, (V →L[ℝ] V) →L[ℝ] Z b)
    (q M : ℝ) (epsilonBlock : β → ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
    ψ q M epsilonBlock

/-- Exact threshold characterization of a finite block response family. -/
theorem continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder_le_iff
    {Z : β → Type*}
    [∀ b, NormedAddCommGroup (Z b)] [∀ b, NormedSpace ℝ (Z b)]
    (ψ : ∀ b, (V →L[ℝ] V) →L[ℝ] Z b)
    (q M : ℝ) (epsilonBlock : β → ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder
        ψ q M epsilonBlock ≤ N ↔
      ∀ b, continuousLinearMapJointRemainderResponseSafeOrder
        (ψ b) q M (epsilonBlock b) ≤ N := by
  exact continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_le_iff
    ψ q M epsilonBlock N

/-- Coordinatewise relaxation of block tolerances cannot increase the block
response order. -/
theorem continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder_antitone
    {Z : β → Type*}
    [∀ b, NormedAddCommGroup (Z b)] [∀ b, NormedSpace ℝ (Z b)]
    (ψ : ∀ b, (V →L[ℝ] V) →L[ℝ] Z b)
    {q M : ℝ} {epsilonBlock₁ epsilonBlock₂ : β → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hBlock₁ : ∀ b, 0 < epsilonBlock₁ b)
    (hBlock₂ : ∀ b, 0 < epsilonBlock₂ b)
    (hBlock : ∀ b, epsilonBlock₁ b ≤ epsilonBlock₂ b) :
    continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder
        ψ q M epsilonBlock₂ ≤
      continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder
        ψ q M epsilonBlock₁ := by
  exact continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_antitone
    ψ hq0 hq1 hM hBlock₁ hBlock₂ hBlock

/-- Homogeneous block families are invariant when block observables and their
block tolerances are reindexed together. -/
theorem continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder_reindex_eq
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n : ℕ} (ψ : Fin n → ((V →L[ℝ] V) →L[ℝ] U))
    (epsilonBlock : Fin n → ℝ) (e : Fin n ≃ Fin n) (q M : ℝ) :
    continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder
        (fun b => ψ (e b)) q M (fun b => epsilonBlock (e b)) =
      continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder
        ψ q M epsilonBlock := by
  exact continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_reindex_eq
    ψ epsilonBlock e q M

/-- The block response order induced by a concrete coordinate-to-block
assignment. -/
noncomputable def continuousLinearMapJointRemainderDependentPiBlockResponseToleranceSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) (q M : ℝ) (epsilonBlock : β → ℝ) : ℕ :=
  continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder
    (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf b) q M epsilonBlock

/-- One order controls carrier, the exact block bundle, every block at its own
tolerance, every original coordinate at its own tolerance, and trace. -/
noncomputable def continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) : ℕ :=
  max
    (continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
      (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
        φ blockOf b)
      q M epsilonCarrier epsilonBundle epsilonBlock epsilonTrace)
    (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
      φ q M epsilonCoordinate)

/-- Exact threshold characterization of the block-tolerance master. -/
theorem continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace ≤ N ↔
      continuousLinearMapJointRemainderCarrierSharpOrder
          q M epsilonCarrier ≤ N ∧
      continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
            φ blockOf) q M epsilonBundle ≤ N ∧
      (∀ b, continuousLinearMapJointRemainderResponseSafeOrder
          (continuousLinearMapJointRemainderDependentPiBlockObservable
            φ blockOf b) q M (epsilonBlock b) ≤ N) ∧
      (∀ i, continuousLinearMapJointRemainderResponseSafeOrder
          (φ i) q M (epsilonCoordinate i) ≤ N) ∧
      continuousLinearMapJointRemainderTraceSafeOrder
          V q M epsilonTrace ≤ N := by
  unfold continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
  rw [max_le_iff]
  rw [continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_le_iff]
  rw [continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_le_iff]
  tauto

/-- The carrier order lies below the block-tolerance master. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilonCarrier ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductToleranceMaster
    (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf b)
    q M epsilonCarrier epsilonBundle epsilonBlock epsilonTrace).trans
    (le_max_left _ _)

/-- The exact block-bundle response order lies below the block master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ blockOf) q M epsilonBundle ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
    (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf b)
    q M epsilonCarrier epsilonBundle epsilonBlock epsilonTrace).trans
    (le_max_left _ _)

/-- Every block response order lies below the block master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_block_le_toleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β) (b : β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ blockOf b) q M (epsilonBlock b) ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductToleranceMaster
    (fun c => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf c) b
    q M epsilonCarrier epsilonBundle epsilonBlock epsilonTrace).trans
    (le_max_left _ _)

/-- Every original coordinate order lies below the block master. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β) (i : ι)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M (epsilonCoordinate i) ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainder_le_finiteMaximum
    (fun j => continuousLinearMapJointRemainderResponseSafeOrder
      (φ j) q M (epsilonCoordinate j)) i).trans (le_max_right _ _)

/-- The trace order lies below the block master. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockToleranceMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace := by
  exact (continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductToleranceMaster
    (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf b)
    q M epsilonCarrier epsilonBundle epsilonBlock epsilonTrace).trans
    (le_max_left _ _)

/-- Every block order is bounded by the exact bundle order whenever each block
is assigned a tolerance no stricter than the bundle tolerance. -/
theorem continuousLinearMapJointRemainderDependentPiBlockResponseToleranceSafeOrder_le_bundle
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    {q M epsilonBundle : ℝ} {epsilonBlock : β → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hBundle : 0 < epsilonBundle) (hBlock : ∀ b, 0 < epsilonBlock b)
    (hRelax : ∀ b, epsilonBundle ≤ epsilonBlock b) :
    continuousLinearMapJointRemainderDependentPiBlockResponseToleranceSafeOrder
        φ blockOf q M epsilonBlock ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ blockOf) q M epsilonBundle := by
  apply (continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder_le_iff
    (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf b) q M epsilonBlock _).2
  intro b
  exact le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_antitone_epsilon
      (continuousLinearMapJointRemainderDependentPiBlockObservable
        φ blockOf b)
      hq0 hq1 hM hBundle (hBlock b) (hRelax b))
    (continuousLinearMapJointRemainderResponseSafeOrder_le_dependentPiProductObservable
      (fun c => continuousLinearMapJointRemainderDependentPiBlockObservable
        φ blockOf c) b hq0 hq1 hM hBundle)

/-- Relaxing any carrier, bundle, block, coordinate, or trace tolerance cannot
increase the block master. -/
theorem continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_antitone
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    {q M epsilonCarrier₁ epsilonCarrier₂ epsilonBundle₁ epsilonBundle₂
      epsilonTrace₁ epsilonTrace₂ : ℝ}
    {epsilonBlock₁ epsilonBlock₂ : β → ℝ}
    {epsilonCoordinate₁ epsilonCoordinate₂ : ι → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hCarrier₁ : 0 < epsilonCarrier₁) (hCarrier₂ : 0 < epsilonCarrier₂)
    (hBundle₁ : 0 < epsilonBundle₁) (hBundle₂ : 0 < epsilonBundle₂)
    (hBlock₁ : ∀ b, 0 < epsilonBlock₁ b)
    (hBlock₂ : ∀ b, 0 < epsilonBlock₂ b)
    (hCoordinate₁ : ∀ i, 0 < epsilonCoordinate₁ i)
    (hCoordinate₂ : ∀ i, 0 < epsilonCoordinate₂ i)
    (hTrace₁ : 0 < epsilonTrace₁) (hTrace₂ : 0 < epsilonTrace₂)
    (hCarrier : epsilonCarrier₁ ≤ epsilonCarrier₂)
    (hBundle : epsilonBundle₁ ≤ epsilonBundle₂)
    (hBlock : ∀ b, epsilonBlock₁ b ≤ epsilonBlock₂ b)
    (hCoordinate : ∀ i, epsilonCoordinate₁ i ≤ epsilonCoordinate₂ i)
    (hTrace : epsilonTrace₁ ≤ epsilonTrace₂) :
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier₂ epsilonBundle₂ epsilonBlock₂
        epsilonCoordinate₂ epsilonTrace₂ ≤
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier₁ epsilonBundle₁ epsilonBlock₁
        epsilonCoordinate₁ epsilonTrace₁ := by
  unfold continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
  exact max_le_max
    (continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_antitone
      (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
        φ blockOf b)
      hq0 hq1 hM hCarrier₁ hCarrier₂ hBundle₁ hBundle₂
      hBlock₁ hBlock₂ hTrace₁ hTrace₂ hCarrier hBundle hBlock hTrace)
    (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_antitone
      φ hq0 hq1 hM hCoordinate₁ hCoordinate₂ hCoordinate)

/-- The block master is exactly the previous vector-tolerance master whenever
all block tolerances are no stricter than the product tolerance. -/
theorem continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_eq_productMaster
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    {q M epsilonCarrier epsilonProduct epsilonTrace : ℝ}
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hProduct : 0 < epsilonProduct)
    (hBlock : ∀ b, 0 < epsilonBlock b)
    (hRelax : ∀ b, epsilonProduct ≤ epsilonBlock b) :
    continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ blockOf q M epsilonCarrier epsilonProduct epsilonBlock
        epsilonCoordinate epsilonTrace =
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  apply le_antisymm
  · apply (continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder_le_iff
      φ blockOf q M epsilonCarrier epsilonProduct epsilonBlock
      epsilonCoordinate epsilonTrace _).2
    refine ⟨
      continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductToleranceMaster
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace,
      ?_, ?_, ?_,
      continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductToleranceMaster
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace⟩
    · rw [continuousLinearMapJointRemainderResponseSafeOrder_dependentPiBlockBundle_eq
        (W := W) φ blockOf q M epsilonProduct]
      exact continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
    · intro b
      exact le_trans
        (continuousLinearMapJointRemainderResponseSafeOrder_antitone_epsilon
          (continuousLinearMapJointRemainderDependentPiBlockObservable
            φ blockOf b)
          hq0 hq1 hM hProduct (hBlock b) (hRelax b))
        (le_trans
          (continuousLinearMapJointRemainderResponseSafeOrder_le_dependentPiProductObservable
            (fun c => continuousLinearMapJointRemainderDependentPiBlockObservable
              φ blockOf c) b hq0 hq1 hM hProduct)
          (by
            change continuousLinearMapJointRemainderResponseSafeOrder
              (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
                φ blockOf) q M epsilonProduct ≤
              continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
                φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
            rw [continuousLinearMapJointRemainderResponseSafeOrder_dependentPiBlockBundle_eq
              (W := W) φ blockOf q M epsilonProduct]
            exact continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
              φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace))
    · intro i
      exact continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductToleranceMaster
        φ i q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
  · apply (continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_le_iff
      φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace _).2
    refine ⟨
      continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiBlockToleranceMaster
        φ blockOf q M epsilonCarrier epsilonProduct epsilonBlock
        epsilonCoordinate epsilonTrace,
      ?_, ?_,
      continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiBlockToleranceMaster
        φ blockOf q M epsilonCarrier epsilonProduct epsilonBlock
        epsilonCoordinate epsilonTrace⟩
    · rw [← continuousLinearMapJointRemainderResponseSafeOrder_dependentPiBlockBundle_eq
        (W := W) φ blockOf q M epsilonProduct]
      exact continuousLinearMapJointRemainderResponseSafeOrder_blockBundle_le_toleranceMaster
        φ blockOf q M epsilonCarrier epsilonProduct epsilonBlock
        epsilonCoordinate epsilonTrace
    · intro i
      exact continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
        φ blockOf i q M epsilonCarrier epsilonProduct epsilonBlock
        epsilonCoordinate epsilonTrace

end MathlibAnalytic
end MGAP4D