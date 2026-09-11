import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiProductToleranceCore

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The four-channel rectangular remainder assertion at a fixed base order. -/
def ContinuousLinearMapJointDependentPiProductToleranceCertificate
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (epsilonCarrier epsilonProduct : ℝ) (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : Prop :=
  ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCarrier ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapJointRemainderDependentPiProductObservable φ)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonProduct ∧
  (∀ i, ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonCoordinate i) ∧
  ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
      V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilonTrace

/-- Every order above the vector-tolerance master satisfies all four channels. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiProductToleranceMasterSafeOrder_le
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonProduct : ℝ) (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k * continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbase : continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
      φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace ≤ baseOrder)
    (hCarrier : 0 < epsilonCarrier) (hProduct : 0 < epsilonProduct)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i) (hTrace : 0 < epsilonTrace) :
    ContinuousLinearMapJointDependentPiProductToleranceCertificate
      φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  constructor
  · exact continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilonCarrier
      hq0 hq1 hM hperturb hend
      (le_trans (continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductToleranceMaster
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace) hbase) hCarrier
  constructor
  · exact continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
      (continuousLinearMapJointRemainderDependentPiProductObservable φ)
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilonProduct
      hq0 hq1 hM hperturb hend
      (le_trans (continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_toleranceMaster
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace) hbase) hProduct
  constructor
  · intro i
    exact continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
      (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M (epsilonCoordinate i)
      hq0 hq1 hM hperturb hend
      (le_trans (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductToleranceMaster
        φ i q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace) hbase) (hCoordinate i)
  · exact continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJet_norm_lt_of_safeOrder_le
      V baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilonTrace
      hq0 hq1 hM hperturb hend
      (le_trans (continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductToleranceMaster
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace) hbase) hTrace

/-- The explicit master order satisfies all four channels without a new order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_at_dependentPiProductToleranceMasterSafeOrder
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilonCarrier epsilonProduct : ℝ) (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k * continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hCarrier : 0 < epsilonCarrier) (hProduct : 0 < epsilonProduct)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i) (hTrace : 0 < epsilonTrace) :
    let N := continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
      φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
    ContinuousLinearMapJointDependentPiProductToleranceCertificate
      φ N taylorOrder tailOrder m H ds h Rbase Rend
      epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  dsimp
  exact continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_of_dependentPiProductToleranceMasterSafeOrder_le
    φ _ taylorOrder tailOrder m H ds h Rbase Rend
    q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
    hq0 hq1 hM hperturb hend le_rfl hCarrier hProduct hCoordinate hTrace

end MathlibAnalytic
end MGAP4D
