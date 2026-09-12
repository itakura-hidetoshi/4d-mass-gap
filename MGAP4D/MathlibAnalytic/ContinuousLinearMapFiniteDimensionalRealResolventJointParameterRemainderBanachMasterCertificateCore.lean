import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachSharpCertificateCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The universally available master order simultaneously controlling the
carrier, one arbitrary Banach-valued response, and the basis-independent trace. -/
noncomputable def continuousLinearMapJointRemainderMasterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (q M epsilon : ℝ) : ℕ :=
  max (continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon)
    (max (continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon)
      (continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon))

/-- The carrier sharp order is below the master safe order. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_masterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon ≤
      continuousLinearMapJointRemainderMasterSafeOrder φ q M epsilon := by
  exact le_max_left _ _

/-- The response safe order is below the master safe order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_le_masterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤
      continuousLinearMapJointRemainderMasterSafeOrder φ q M epsilon := by
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- The trace safe order is below the master safe order. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_masterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon ≤
      continuousLinearMapJointRemainderMasterSafeOrder φ q M epsilon := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The carrier sharp order exactly characterizes all geometric carrier
certificates. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_iff
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) (N : ℕ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon ≤ N ↔
      q ^ N * M < epsilon := by
  simpa [continuousLinearMapJointRemainderCarrierSharpOrder,
    geometricDecayAdmissible] using
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hM hepsilon N)

/-- The carrier sharp order is the least geometric carrier certificate. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_isLeast
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    IsLeast {N : ℕ | q ^ N * M < epsilon}
      (continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon) := by
  simpa [continuousLinearMapJointRemainderCarrierSharpOrder,
    geometricDecayAdmissible] using
    (geometricDecaySharpTruncationOrder_isLeast
      hq0 hq1 hM hepsilon)

/-- Every carrier order below the sharp threshold fails the strict geometric
tolerance test. -/
theorem continuousLinearMapJointRemainderCarrier_not_lt_before_sharpOrder
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) {N : ℕ}
    (hN : N < continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon) :
    epsilon ≤ q ^ N * M := by
  exact geometricDecay_not_lt_before_sharpTruncationOrder
    hq0 hq1 hM hepsilon hN

/-- Increasing tolerance cannot increase the carrier sharp order. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_antitone_epsilon
    {q M epsilon₁ epsilon₂ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₂ : 0 < epsilon₂)
    (heps : epsilon₁ ≤ epsilon₂) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon₂ ≤
      continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon₁ := by
  exact geometricDecaySharpTruncationOrder_antitone_epsilon
    hq0 hq1 hM hepsilon₁ hepsilon₂ heps

/-- Increasing the endpoint envelope cannot decrease the carrier sharp order. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_mono_endpoint
    {q M₁ M₂ epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM : M₁ ≤ M₂)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M₁ epsilon ≤
      continuousLinearMapJointRemainderCarrierSharpOrder q M₂ epsilon := by
  exact geometricDecaySharpTruncationOrder_mono_constant
    hq0 hq1 hM₁ hM₂ hM hepsilon

/-- Increasing the geometric rate in `[0,1)` cannot decrease the carrier sharp
order. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_mono_rate
    {q₁ q₂ M epsilon : ℝ}
    (hq₁0 : 0 ≤ q₁) (hq₂0 : 0 ≤ q₂)
    (hq₁₂ : q₁ ≤ q₂) (hq₂1 : q₂ < 1)
    (hM : 0 < M) (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderCarrierSharpOrder q₁ M epsilon ≤
      continuousLinearMapJointRemainderCarrierSharpOrder q₂ M epsilon := by
  exact geometricDecaySharpTruncationOrder_mono_rate
    hq₁0 hq₂0 hq₁₂ hq₂1 hM hepsilon

/-- Every order above the universally valid response safe threshold controls
the complete Banach-valued response rectangle. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder : continuousLinearMapJointRemainderResponseSafeOrder
      φ q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have hC : 0 < ‖φ‖ + 1 := by linarith [norm_nonneg φ]
  have hconstant : 0 < (‖φ‖ + 1) * M := mul_pos hC hM
  have henvelope : q ^ baseOrder * ((‖φ‖ + 1) * M) < epsilon :=
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hconstant hepsilon baseOrder).1 hbaseOrder
  exact
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_geometricEnvelope
      φ (‖φ‖ + 1) baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon hC.le (by linarith) hq0 hq1 hM hperturb hend
      henvelope hepsilon

/-- Every order above the trace safe threshold controls the complete
basis-independent trace rectangle. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJet_norm_lt_of_safeOrder_le
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder : continuousLinearMapJointRemainderTraceSafeOrder
      V q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  simpa [continuousLinearMapJointRemainderTraceSafeOrder,
    continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
      (continuousLinearMapTrace (V := V)) baseOrder taylorOrder tailOrder m
      H ds h Rbase Rend q M epsilon hq0 hq1 hM hperturb hend hbaseOrder hepsilon

/-- One master natural number simultaneously controls carrier, arbitrary
Banach-valued response, and basis-independent trace remainder rectangles. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_masterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    let N := continuousLinearMapJointRemainderMasterSafeOrder φ q M epsilon
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  dsimp
  constructor
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
        (continuousLinearMapJointRemainderMasterSafeOrder φ q M epsilon)
        taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
        hq0 hq1 hM hperturb hend
        (continuousLinearMapJointRemainderCarrierSharpOrder_le_masterSafeOrder
          φ q M epsilon) hepsilon
  constructor
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
        φ (continuousLinearMapJointRemainderMasterSafeOrder φ q M epsilon)
        taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
        hq0 hq1 hM hperturb hend
        (continuousLinearMapJointRemainderResponseSafeOrder_le_masterSafeOrder
          φ q M epsilon) hepsilon
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJet_norm_lt_of_safeOrder_le
        V (continuousLinearMapJointRemainderMasterSafeOrder φ q M epsilon)
        taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
        hq0 hq1 hM hperturb hend
        (continuousLinearMapJointRemainderTraceSafeOrder_le_masterSafeOrder
          φ q M epsilon) hepsilon

end MathlibAnalytic
end MGAP4D
