import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventLinearResponseCompactRectangular
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventNewtonHermiteClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β κ E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Simultaneous convergence of every response in a finite continuous-linear
observable family, for Newton-Hermite interpolants and exact remainders on a
complete closed Taylor box and arbitrary joint time/degree nets. -/
theorem taylorPartialSum_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
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
    {m : Filter β} (a : β → α) (taylorDegree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto taylorDegree m atTop)
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
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ p, box.Contains p → ∀ q ∈ T,
        ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F (a b)) p.center p.target (taylorDegree b)))
              (nodes q) (eval q)) -
          continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
              (continuousLinearMapCompression J Q (S.limitResolvent p.target))
              (nodes q) (eval q))‖ < epsilon := by
  apply finiteDimensional_linearResponseFamilyPair_tendsto_uniformOn
    Phi
    (fun b q => continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
      (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) q.1.center q.1.target (taylorDegree b)))
      (nodes q.2) (eval q.2))
    (fun q => continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
      (continuousLinearMapCompression J Q (S.limitResolvent q.1.target))
      (nodes q.2) (eval q.2))
    responseBound hresponseBound hPhi
  intro eta heta
  have h :=
    S.taylorPartialSum_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q interpolationDegree a taylorDegree
      ha hdegree box nodes eval T Z hnodes heval D hD hdist
      margin hmargin hlimitMargin M hM hlimitNorm eta heta
  filter_upwards [h] with b hb
  intro q hq
  exact hb q.1 hq.1 q.2 hq.2

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
