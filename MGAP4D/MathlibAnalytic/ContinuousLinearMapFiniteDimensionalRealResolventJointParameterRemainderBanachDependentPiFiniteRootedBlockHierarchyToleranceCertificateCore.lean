import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyToleranceOrderCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockToleranceCertificateCore

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

/-- Rectangular remainder control for carrier, every rooted-hierarchy node
bundle, every node block, every coordinate, and trace. -/
def ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchyToleranceCertificate
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : Prop :=
  ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCarrier ∧
  (∀ t, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
        φ (Htree.blockOf t))
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonBundle t) ∧
  (∀ t b, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockObservable
        φ (Htree.blockOf t) b)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonBlock t b) ∧
  (∀ i, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCoordinate i) ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
      V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonTrace

/-- Every order above the finite rooted hierarchy master satisfies all channels. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_le
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbase : continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
      φ Htree q M epsilonCarrier epsilonBundle epsilonBlock
      epsilonCoordinate epsilonTrace ≤ baseOrder)
    (hCarrier : 0 < epsilonCarrier)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchyToleranceCertificate
      φ Htree baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  have hnode : ∀ t,
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
          φ (Htree.blockOf t) q M epsilonCarrier (epsilonBundle t)
          (epsilonBlock t) epsilonCoordinate epsilonTrace ≤ baseOrder := by
    intro t
    exact (continuousLinearMapJointRemainder_le_finiteMaximum
      (fun s => continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ (Htree.blockOf s) q M epsilonCarrier (epsilonBundle s)
        (epsilonBlock s) epsilonCoordinate epsilonTrace) t).trans hbase
  have hcert : ∀ t,
      ContinuousLinearMapJointDependentPiBlockToleranceCertificate
        φ (Htree.blockOf t) baseOrder taylorOrder tailOrder m H ds h Rbase Rend
        epsilonCarrier (epsilonBundle t) (epsilonBlock t)
        epsilonCoordinate epsilonTrace := by
    intro t
    exact
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiBlockToleranceMasterSafeOrder_le
        φ (Htree.blockOf t) baseOrder taylorOrder tailOrder m H ds h Rbase Rend
        q M epsilonCarrier (epsilonBundle t) (epsilonBlock t)
        epsilonCoordinate epsilonTrace hq0 hq1 hM hperturb hend (hnode t)
        hCarrier (hBundle t) (hBlock t) hCoordinate hTrace
  refine ⟨(hcert Htree.root).1, ?_, ?_,
    (hcert Htree.root).2.2.2.1, (hcert Htree.root).2.2.2.2⟩
  · intro t
    exact (hcert t).2.1
  · intro t b
    exact (hcert t).2.2.1 b

/-- The explicit finite rooted hierarchy master satisfies the complete fixed
parameter certificate without a second order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_at_dependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hCarrier : 0 < epsilonCarrier)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := continuousLinearMapJointRemainderDependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder
      φ Htree q M epsilonCarrier epsilonBundle epsilonBlock
      epsilonCoordinate epsilonTrace
    ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchyToleranceCertificate
      φ Htree N taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  dsimp
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiFiniteRootedBlockHierarchyToleranceMasterSafeOrder_le
      φ Htree _ taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace
      hq0 hq1 hM hperturb hend le_rfl
      hCarrier hBundle hBlock hCoordinate hTrace

end MathlibAnalytic
end MGAP4D
