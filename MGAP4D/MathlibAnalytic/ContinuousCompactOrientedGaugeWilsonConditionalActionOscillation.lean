import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonRemoteCancellation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOscillationTV

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Uniform target-local Wilson-action oscillation under every active physical
source-link perturbation. -/
def ContinuousCompactOrientedGaugeWilsonSystem.ActiveLocalActionDifferenceOscillationBound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (omega : ℝ) : Prop :=
  ∀ (target source : C.base.geometry.Edge)
    (A : C.base.Configuration) (g : C.base.Gauge),
    source ∈ C.base.activePlaquetteNeighbors target →
      ∀ u v : C.base.Gauge,
        ((C.base.targetLocalPlaquetteAction
              (C.base.replaceLink A target u) target -
            C.base.targetLocalPlaquetteAction
              (C.base.replaceLink (C.base.replaceLink A source g)
                target u) target) -
          (C.base.targetLocalPlaquetteAction
              (C.base.replaceLink A target v) target -
            C.base.targetLocalPlaquetteAction
              (C.base.replaceLink (C.base.replaceLink A source g)
                target v) target)) ≤ omega

/-- A target-local action oscillation bound gives the exact compact conditional
exponent-difference radius `beta * omega`. -/
theorem continuous_compact_oriented_singleLinkExponentDifferenceOscillationBound_of_localActionOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (omega : ℝ)
    (hOsc : C.ActiveLocalActionDifferenceOscillationBound omega)
    (target source : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (g : C.base.Gauge)
    (hActive : source ∈ C.base.activePlaquetteNeighbors target) :
    C.SingleLinkExponentDifferenceOscillationBound
      A (C.base.replaceLink A source g) target (C.base.beta * omega) := by
  intro u v
  have hAction := hOsc target source A g hActive v u
  have hMul := mul_le_mul_of_nonneg_left hAction C.base.beta_nonneg
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkGibbsExponent
    CompactOrientedGaugeWilsonSystem.gibbsExponent
  rw [compact_oriented_wilsonAction_replaceLink_eq_local_add_remote,
    compact_oriented_wilsonAction_replaceLink_eq_local_add_remote,
    compact_oriented_wilsonAction_replaceLink_eq_local_add_remote,
    compact_oriented_wilsonAction_replaceLink_eq_local_add_remote]
  nlinarith

/-- Uniform compact target-local action oscillation bounds every active exact
one-link conditional total variation by the sharp likelihood-ratio majorant. -/
theorem continuous_compact_oriented_active_singleLinkConditionalTotalVariation_le_of_localActionOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (omega : ℝ)
    (hOmega : 0 ≤ omega)
    (hOsc : C.ActiveLocalActionDifferenceOscillationBound omega)
    (target source : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (g : C.base.Gauge)
    (hActive : source ∈ C.base.activePlaquetteNeighbors target) :
    C.singleLinkConditionalTotalVariation
        A (C.base.replaceLink A source g) target ≤
      (Real.exp (C.base.beta * omega) - 1) /
        (Real.exp (C.base.beta * omega) + 1) := by
  exact continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_exponentDifferenceOscillation
    C A (C.base.replaceLink A source g) target
    (C.base.beta * omega)
    (mul_nonneg C.base.beta_nonneg hOmega)
    (continuous_compact_oriented_singleLinkExponentDifferenceOscillationBound_of_localActionOscillation
      C omega hOsc target source A g hActive)

end
end MathlibAnalytic
end MGAP4D
