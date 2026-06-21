import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalActionOscillationBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Local action oscillation bounds every realizable active conditional total
variation by the sharp exponential-ratio majorant. -/
theorem finite_oriented_activeSingleLinkConditionalTotalVariation_le_of_localActionOscillation
    (L : FiniteOrientedLatticeWilsonSystem)
    (omega : ℝ)
    (hOmega : 0 ≤ omega)
    (hOsc : L.ActiveLocalActionDifferenceOscillationBound omega)
    (target source : L.Edge)
    (A : L.Configuration)
    (g : L.Gauge)
    (hActive : source ∈ L.activePlaquetteNeighbors target) :
    L.singleLinkConditionalTotalVariation
        A (L.replaceLink A source g) target ≤
      (Real.exp (L.beta * omega) - 1) /
        (Real.exp (L.beta * omega) + 1) := by
  have hRatio :=
    finite_oriented_activeConditionalExpRatioBound_of_localActionOscillation
      L omega hOmega hOsc
  apply finite_oriented_singleLinkConditionalTotalVariation_le_of_mutual_exp_ratio
    L A (L.replaceLink A source g) target (L.beta * omega)
      (mul_nonneg L.beta_nonneg hOmega)
  · intro u
    exact (hRatio target source A g hActive u).1
  · intro u
    exact (hRatio target source A g hActive u).2

end

end MathlibAnalytic
end MGAP4D
