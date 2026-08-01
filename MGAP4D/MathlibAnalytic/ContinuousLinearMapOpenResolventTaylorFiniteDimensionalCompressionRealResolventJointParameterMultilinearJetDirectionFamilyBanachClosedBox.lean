import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetDirectionFamilyBanachCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetDirectionFamilyClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

set_option maxHeartbeats 5000000

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Complete closed-box convergence of the moving-direction carrier jet in the
actual finite dependent-product norm for an arbitrary joint net. -/
theorem taylorPartialSum_realResolventJointMultilinearCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (mixedOrder m : ℕ)
    {f : Filter β} (a : β → α) (degree : β → ℕ)
    (H : β → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (ha : Tendsto a f l) (hdegree : Tendsto degree f atTop)
    (hH : Tendsto H f (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) (H b)
          (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (F (a b)) p.center p.target (degree b) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) H0
          (continuousLinearMapCompressedRealResolventAt
            J Q (S.limitResolvent p.target) z)‖ < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.taylorPartialSum_realResolventJointMultilinearCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_sup
      B L hLgap hLresolvent J Q mixedOrder m a degree H H0 ha hdegree hH box Z
      margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  apply (continuousLinearMapJointMultilinearCarrierJet_norm_sub_lt_iff_supDistance_lt
    (V := V) (W := V →L[ℝ] V) _ _ hepsilon).2
  exact hb p hp z hz

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Complete closed-box convergence of every Banach-valued response jet in its
actual finite dependent-product norm for an arbitrary joint net. -/
theorem taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (mixedOrder m : ℕ) {f : Filter β} (a : β → α) (degree : β → ℕ)
    (H : β → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (ha : Tendsto a f l) (hdegree : Tendsto degree f atTop)
    (hH : Tendsto H f (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder (H b)
          (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (F (a b)) p.center p.target (degree b) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H0
          (continuousLinearMapCompressedRealResolventAt
            J Q (S.limitResolvent p.target) z)‖ < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_sup
      B L hLgap hLresolvent J Q φ mixedOrder m a degree H H0 ha hdegree hH box Z
      margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  apply (continuousLinearMapJointMultilinearCarrierJet_norm_sub_lt_iff_supDistance_lt
    (V := V) (W := W) _ _ hepsilon).2
  exact hb p hp z hz

/-- Complete closed-box convergence of the basis-independent trace jet in its
actual finite dependent-product norm for an arbitrary joint net. -/
theorem taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (mixedOrder m : ℕ)
    {f : Filter β} (a : β → α) (degree : β → ℕ)
    (H : β → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (ha : Tendsto a f l) (hdegree : Tendsto degree f atTop)
    (hH : Tendsto H f (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder (H b)
          (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (F (a b)) p.center p.target (degree b) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H0
          (continuousLinearMapCompressedRealResolventAt
            J Q (S.limitResolvent p.target) z)‖ < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_sup
      B L hLgap hLresolvent J Q mixedOrder m a degree H H0 ha hdegree hH box Z
      margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  apply (continuousLinearMapJointMultilinearCarrierJet_norm_sub_lt_iff_supDistance_lt
    (V := V) (W := ℝ) _ _ hepsilon).2
  exact hb p hp z hz

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
