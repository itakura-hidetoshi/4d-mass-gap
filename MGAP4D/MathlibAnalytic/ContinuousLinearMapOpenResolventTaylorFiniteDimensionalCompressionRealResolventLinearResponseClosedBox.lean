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
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (interpolationDegree : ℕ) {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (responseBound : ℝ) (hresponseBound : 0 ≤ responseBound) (hPhi : ∀ r, ‖Phi r‖ ≤ responseBound)
    {m : Filter β} (a : β → α) (taylorDegree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto taylorDegree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ T, eval q ∈ Z)
    (D : ℝ) (hD : 0 ≤ D) (hdist : ∀ q ∈ T, ∀ j, |eval q - nodes q j| ≤ D)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ q ∈ T,
      ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi
          (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (taylorDegree b))) (nodes q) (eval q)) -
        continuousLinearMapRealResolventLinearResponseFamilyPair Phi
          (continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
            (continuousLinearMapCompression J Q (S.limitResolvent p.target))
            (nodes q) (eval q))‖ < epsilon := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / (responseBound + 1)
  have hbound1 : 0 < responseBound + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hbound1
  have hpair :=
    S.taylorPartialSum_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q interpolationDegree a taylorDegree
      ha hdegree box nodes eval T Z hnodes heval D hD hdist
      margin hmargin hlimitMargin M hM hlimitNorm eta heta
  filter_upwards [hpair] with b hb
  intro p hp q hq
  let PA : Fin 2 → (V →L[ℝ] V) :=
    continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
      (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
        (F (a b)) p.center p.target (taylorDegree b))) (nodes q) (eval q)
  let P0 : Fin 2 → (V →L[ℝ] V) :=
    continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
      (continuousLinearMapCompression J Q (S.limitResolvent p.target))
      (nodes q) (eval q)
  have hpairAt : ‖PA - P0‖ < eta := by
    simpa [PA, P0] using hb p hp q hq
  rw [pi_norm_lt_iff hepsilon]
  intro r
  rw [pi_norm_lt_iff hepsilon]
  intro i
  have hi : ‖PA i - P0 i‖ < eta := by
    rw [pi_norm_lt_iff heta] at hpairAt
    simpa only [Pi.sub_apply] using hpairAt i
  have hdual := (Phi r).le_opNorm (PA i - P0 i)
  rw [Real.norm_eq_abs] at hdual
  calc
    ‖(continuousLinearMapRealResolventLinearResponseFamilyPair Phi PA -
        continuousLinearMapRealResolventLinearResponseFamilyPair Phi P0) r i‖ =
        |Phi r (PA i - P0 i)| := by
          simp [continuousLinearMapRealResolventLinearResponseFamilyPair,
            Real.norm_eq_abs]
    _ ≤ ‖Phi r‖ * ‖PA i - P0 i‖ := hdual
    _ ≤ responseBound * ‖PA i - P0 i‖ :=
      mul_le_mul_of_nonneg_right (hPhi r) (norm_nonneg _)
    _ ≤ (responseBound + 1) * ‖PA i - P0 i‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (responseBound + 1) * eta :=
      mul_lt_mul_of_pos_left hi hbound1
    _ = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hbound1]

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
