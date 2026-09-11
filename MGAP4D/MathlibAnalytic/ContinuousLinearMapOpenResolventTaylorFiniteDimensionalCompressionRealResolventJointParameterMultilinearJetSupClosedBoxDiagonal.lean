import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetSupClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Diagonal no-rate closed-box convergence of the entire finite joint Fréchet
carrier jet in one maximum component norm. -/
theorem taylorPartialSum_realResolventJointMultilinearCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_sup
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (mixedOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
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
      continuousLinearMapJointMultilinearCarrierJetSupDistance
        (V := V) (W := V →L[ℝ] V)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)) < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointMultilinearCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_sup
      B L hLgap hLresolvent J Q mixedOrder m H (fun a => a) degree tendsto_id hdegree
      box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate closed-box convergence of the entire finite Banach-valued
response jet in one maximum component norm. -/
theorem taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_sup
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
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
      continuousLinearMapJointMultilinearCarrierJetSupDistance
        (V := V) (W := W)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)) < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_sup
      B L hLgap hLresolvent J Q φ mixedOrder m H (fun a => a) degree tendsto_id hdegree
      box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate closed-box convergence of the entire basis-independent
trace jet in one maximum component norm. -/
theorem taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_sup
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (mixedOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
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
      continuousLinearMapJointMultilinearCarrierJetSupDistance
        (V := V) (W := ℝ)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)) < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_sup
      B L hLgap hLresolvent J Q mixedOrder m H (fun a => a) degree tendsto_id hdegree
      box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
