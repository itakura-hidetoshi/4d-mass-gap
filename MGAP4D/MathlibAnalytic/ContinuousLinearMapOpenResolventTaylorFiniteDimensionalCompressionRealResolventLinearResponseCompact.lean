import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventLinearResponseTransfer
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventNewtonHermiteCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α κ E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Compact-uniform simultaneous convergence of Newton-Hermite interpolant and
exact-remainder responses for every member of a finite continuous-linear
spectral-observable family. -/
theorem iteratedDeriv_realResolventNewtonHermiteLinearResponseFamilyPair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k degree : ℕ)
    {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (responseBound : ℝ) (hresponseBound : 0 ≤ responseBound)
    (hPhi : ∀ r, ‖Phi r‖ ≤ responseBound)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (nodes : κ → Fin (degree + 1) → ℝ) (eval : κ → ℝ)
    (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ T, eval q ∈ Z)
    (D : ℝ) (hD : 0 ≤ D) (hdist : ∀ q ∈ T, ∀ j, |eval q - nodes q j| ≤ D)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePair degree
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) (nodes q) (eval q)) -
          continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePair degree
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda))
              (nodes q) (eval q))‖ < epsilon := by
  apply finiteDimensional_linearResponseFamilyPair_tendsto_uniformOn
    Phi
    (fun a p => continuousLinearMapRealResolventNewtonHermitePair degree
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) p.1)) (nodes p.2) (eval p.2))
    (fun p => continuousLinearMapRealResolventNewtonHermitePair degree
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent p.1)) (nodes p.2) (eval p.2))
    responseBound hresponseBound hPhi
  intro eta heta
  have h :=
    S.iteratedDeriv_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k degree K hKcompact hKu hu
      nodes eval T Z hnodes heval D hD hdist margin hmargin
      hlimitMargin M hM hlimitNorm eta heta
  filter_upwards [h] with a ha
  intro p hp
  exact ha p.1 hp.1 p.2 hp.2

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
