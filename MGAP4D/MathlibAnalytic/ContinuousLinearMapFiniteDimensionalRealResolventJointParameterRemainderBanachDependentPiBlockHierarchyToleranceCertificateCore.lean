import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyToleranceOrderCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockToleranceCertificateCore

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

/-- Seven-channel rectangular remainder control for one coarse and one fine
finite block assignment. -/
def ContinuousLinearMapJointDependentPiBlockHierarchyToleranceCertificate
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : Prop :=
  ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCarrier ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ coarseOf)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonBundle ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ fineOf)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonBundle ∧
  (∀ c, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockObservable φ coarseOf c)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCoarse c) ∧
  (∀ k, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonFine k) ∧
  (∀ i, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCoordinate i) ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
      V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonTrace

/-- Every order above the hierarchy master satisfies all seven channels. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiBlockHierarchyToleranceMasterSafeOrder_le
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbase : continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
      φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
      epsilonCoarse epsilonCoordinate epsilonTrace ≤ baseOrder)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    ContinuousLinearMapJointDependentPiBlockHierarchyToleranceCertificate
      φ fineOf coarseOf baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace := by
  have hcoarse :
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ coarseOf q M epsilonCarrier epsilonBundle epsilonCoarse
        epsilonCoordinate epsilonTrace ≤ baseOrder :=
    le_trans (le_max_left _ _) hbase
  have hfine :
      continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
        φ fineOf q M epsilonCarrier epsilonBundle epsilonFine
        epsilonCoordinate epsilonTrace ≤ baseOrder :=
    le_trans (le_max_right _ _) hbase
  have hc :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiBlockToleranceMasterSafeOrder_le
      φ coarseOf baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilonCarrier epsilonBundle epsilonCoarse epsilonCoordinate epsilonTrace
      hq0 hq1 hM hperturb hend hcoarse
      hCarrier hBundle hCoarse hCoordinate hTrace
  have hf :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiBlockToleranceMasterSafeOrder_le
      φ fineOf baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilonCarrier epsilonBundle epsilonFine epsilonCoordinate epsilonTrace
      hq0 hq1 hM hperturb hend hfine
      hCarrier hBundle hFine hCoordinate hTrace
  exact ⟨hc.1, hc.2.1, hf.2.1, hc.2.2.1, hf.2.2.1,
    hc.2.2.2.1, hc.2.2.2.2⟩

/-- The explicit hierarchy master satisfies all seven channels without a new
order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_at_dependentPiBlockHierarchyToleranceMasterSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := continuousLinearMapJointRemainderDependentPiBlockHierarchyToleranceMasterSafeOrder
      φ fineOf coarseOf q M epsilonCarrier epsilonBundle epsilonFine
      epsilonCoarse epsilonCoordinate epsilonTrace
    ContinuousLinearMapJointDependentPiBlockHierarchyToleranceCertificate
      φ fineOf coarseOf N taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
      epsilonCoordinate epsilonTrace := by
  dsimp
  exact continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiBlockHierarchyToleranceMasterSafeOrder_le
    φ fineOf coarseOf _ taylorOrder tailOrder m H ds h Rbase Rend
    q M epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
    epsilonCoordinate epsilonTrace hq0 hq1 hM hperturb hend le_rfl
    hCarrier hBundle hFine hCoarse hCoordinate hTrace

end MathlibAnalytic
end MGAP4D
