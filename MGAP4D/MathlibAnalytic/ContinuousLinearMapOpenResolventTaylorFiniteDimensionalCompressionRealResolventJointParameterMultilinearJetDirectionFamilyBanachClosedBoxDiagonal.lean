import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetDirectionFamilyBanachClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Diagonal no-rate convergence of the complete carrier jet in its genuine
finite dependent-product norm. -/
theorem taylorPartialSum_realResolventJointMultilinearCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (mixedOrder m : ℕ)
    (degree : α → ℕ) (H : α → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V)) (hdegree : Tendsto degree l atTop)
    (hH : Tendsto H l (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) (H a)
          (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (F a) p.center p.target (degree a) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) H0
          (continuousLinearMapCompressedRealResolventAt
            J Q (S.limitResolvent p.target) z)‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointMultilinearCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_norm
      B L hLgap hLresolvent J Q mixedOrder m (fun a => a) degree H H0
      tendsto_id hdegree hH box Z margin hmargin hlimitMargin M hM hlimitNorm

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Diagonal no-rate convergence of the complete Banach-valued response jet in
its genuine finite dependent-product norm. -/
theorem taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (mixedOrder m : ℕ) (degree : α → ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hdegree : Tendsto degree l atTop) (hH : Tendsto H l (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder (H a)
          (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (F a) p.center p.target (degree a) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H0
          (continuousLinearMapCompressedRealResolventAt
            J Q (S.limitResolvent p.target) z)‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_norm
      B L hLgap hLresolvent J Q φ mixedOrder m (fun a => a) degree H H0
      tendsto_id hdegree hH box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the complete basis-independent trace jet in
its genuine finite dependent-product norm. -/
theorem taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (mixedOrder m : ℕ)
    (degree : α → ℕ) (H : α → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V)) (hdegree : Tendsto degree l atTop)
    (hH : Tendsto H l (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder (H a)
          (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (F a) p.center p.target (degree a) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H0
          (continuousLinearMapCompressedRealResolventAt
            J Q (S.limitResolvent p.target) z)‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_norm
      B L hLgap hLresolvent J Q mixedOrder m (fun a => a) degree H H0
      tendsto_id hdegree hH box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
