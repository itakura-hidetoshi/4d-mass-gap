import MGAP4D.MathlibAnalytic.FinitePMFLikelihoodRatioTotalVariation
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalNormalizedExp

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Total variation between two exact oriented single-link conditional laws. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ g : L.Gauge,
    |(L.singleLinkConditionalPMF A target g).toReal -
      (L.singleLinkConditionalPMF B target g).toReal|

/-- Uniform exponential likelihood-ratio control for every active source-link
perturbation of an oriented target conditional law. -/
def FiniteOrientedLatticeWilsonSystem.ActiveConditionalExpRatioBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (R : ℝ) : Prop :=
  ∀ (target source : L.Edge) (A : L.Configuration) (g : L.Gauge),
    source ∈ L.activePlaquetteNeighbors target →
      ∀ u : L.Gauge,
        (L.singleLinkConditionalPMF A target u).toReal ≤
            Real.exp R *
              (L.singleLinkConditionalPMF
                (L.replaceLink A source g) target u).toReal ∧
          (L.singleLinkConditionalPMF
              (L.replaceLink A source g) target u).toReal ≤
            Real.exp R *
              (L.singleLinkConditionalPMF A target u).toReal

/-- Uniform oscillation control of the target-local action difference produced
by every active source-link perturbation. -/
def FiniteOrientedLatticeWilsonSystem.ActiveLocalActionDifferenceOscillationBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (omega : ℝ) : Prop :=
  ∀ (target source : L.Edge) (A : L.Configuration) (g : L.Gauge),
    source ∈ L.activePlaquetteNeighbors target →
      ∀ u v : L.Gauge,
        ((L.targetLocalPlaquetteAction
              (L.replaceLink A target u) target -
            L.targetLocalPlaquetteAction
              (L.replaceLink (L.replaceLink A source g) target u) target) -
          (L.targetLocalPlaquetteAction
              (L.replaceLink A target v) target -
            L.targetLocalPlaquetteAction
              (L.replaceLink (L.replaceLink A source g) target v) target)) ≤
        omega

end

end MathlibAnalytic
end MGAP4D
