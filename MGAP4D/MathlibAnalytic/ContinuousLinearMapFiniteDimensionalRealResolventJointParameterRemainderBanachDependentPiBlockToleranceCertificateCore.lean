import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockToleranceOrderCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiProductToleranceCertificateCore

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

/-- Five-channel rectangular remainder control for a finite block assignment. -/
def ContinuousLinearMapJointDependentPiBlockToleranceCertificate
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) : Prop :=
  ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCarrier ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockBundleObservable φ blockOf)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonBundle ∧
  (∀ b, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiBlockObservable φ blockOf b)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonBlock b) ∧
  (∀ i, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCoordinate i) ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
      V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonTrace

/-- Every order above the block master satisfies all five tolerance channels. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiBlockToleranceMasterSafeOrder_le
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbase : continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
      epsilonCoordinate epsilonTrace ≤ baseOrder)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hBlock : ∀ b, 0 < epsilonBlock b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    ContinuousLinearMapJointDependentPiBlockToleranceCertificate
      φ blockOf baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  have hfamily :
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
          φ blockOf b)
        q M epsilonCarrier epsilonBundle epsilonBlock epsilonTrace ≤ baseOrder :=
    le_trans (le_max_left _ _) hbase
  have hb :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiProductToleranceMasterSafeOrder_le
      (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
        φ blockOf b)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilonCarrier epsilonBundle epsilonBlock epsilonTrace
      hq0 hq1 hM hperturb hend hfamily hCarrier hBundle hBlock hTrace
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_, hb.2.2.2⟩
  intro i
  exact continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
    (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend
    q M (epsilonCoordinate i) hq0 hq1 hM hperturb hend
    (le_trans
      (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiBlockToleranceMaster
        φ blockOf i q M epsilonCarrier epsilonBundle epsilonBlock
        epsilonCoordinate epsilonTrace)
      hbase)
    (hCoordinate i)

/-- The explicit block master order satisfies all five channels without a new
order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_at_dependentPiBlockToleranceMasterSafeOrder
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → β)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : β → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hBlock : ∀ b, 0 < epsilonBlock b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :
    let N := continuousLinearMapJointRemainderDependentPiBlockToleranceMasterSafeOrder
      φ blockOf q M epsilonCarrier epsilonBundle epsilonBlock
      epsilonCoordinate epsilonTrace
    ContinuousLinearMapJointDependentPiBlockToleranceCertificate
      φ blockOf N taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace := by
  dsimp
  exact continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiBlockToleranceMasterSafeOrder_le
    φ blockOf _ taylorOrder tailOrder m H ds h Rbase Rend
    q M epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace
    hq0 hq1 hM hperturb hend le_rfl
    hCarrier hBundle hBlock hCoordinate hTrace

end MathlibAnalytic
end MGAP4D