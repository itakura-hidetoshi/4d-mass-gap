import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventLinearResponseClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α κ E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Diagonal no-rate convergence for a finite family of continuous-linear
Newton-Hermite spectral responses on a complete closed Taylor box. -/
theorem taylorPartialSum_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (interpolationDegree : ℕ)
    {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (responseBound : ℝ) (hresponseBound : 0 ≤ responseBound)
    (hPhi : ∀ r, ‖Phi r‖ ≤ responseBound)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ)
    (T : Set κ) (Z : Set ℝ) (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z)
    (heval : ∀ q ∈ T, eval q ∈ Z) (D : ℝ) (hD : 0 ≤ D)
    (hdist : ∀ q ∈ T, ∀ j, |eval q - nodes q j| ≤ D)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ q ∈ T,
        ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F a) p.center p.target (degree a)))
              (nodes q) (eval q)) -
          continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
              (continuousLinearMapCompression J Q (S.limitResolvent p.target))
              (nodes q) (eval q))‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q interpolationDegree Phi
      responseBound hresponseBound hPhi (fun a => a) degree tendsto_id hdegree
      box nodes eval T Z hnodes heval D hD hdist margin hmargin
      hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
