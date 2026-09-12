import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventSpectralJetClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Diagonal convergence of a fixed algebraic spectral jet on a complete
closed Taylor box, with no rate relation between time and Taylor degree. -/
theorem taylorPartialSum_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (spectralOrder : ℕ)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventSpectralJet spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F a) p.center p.target (degree a))) z) -
          continuousLinearMapRealResolventSpectralJet spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (S.limitResolvent p.target)) z)‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q spectralOrder (fun a => a) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal simultaneous convergence of every algebraic spectral jet through
a fixed finite order on the complete closed Taylor box. -/
theorem taylorPartialSum_realResolventSpectralJetVector_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (spectralOrder : ℕ)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventSpectralJetVector spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F a) p.center p.target (degree a))) z) -
          continuousLinearMapRealResolventSpectralJetVector spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (S.limitResolvent p.target)) z)‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventSpectralJetVector_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q spectralOrder (fun a => a) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal convergence of the true operator-norm spectral derivatives on an
open common real spectral region, with no rate relation. -/
theorem taylorPartialSum_realResolvent_iteratedSpectralDeriv_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (spectralOrder : ℕ)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (U : Set ℝ) (hU : IsOpen U)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ U,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ U,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ z ∈ U,
        ‖_root_.iteratedDeriv spectralOrder
            (fun w => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F a) p.center p.target (degree a))) w) z -
          _root_.iteratedDeriv spectralOrder
            (fun w => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (S.limitResolvent p.target)) w) z‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolvent_iteratedSpectralDeriv_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q spectralOrder (fun a => a) degree
      tendsto_id hdegree box U hU margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
