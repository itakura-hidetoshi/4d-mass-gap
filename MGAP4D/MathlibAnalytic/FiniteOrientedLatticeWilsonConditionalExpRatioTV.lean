import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalActionOscillation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pointwise mutual exponential likelihood-ratio control gives the sharp
finite total-variation bound for oriented conditionals. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_le_of_mutual_exp_ratio
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hAB : ∀ u : L.Gauge,
      (L.singleLinkConditionalPMF A target u).toReal ≤
        Real.exp R * (L.singleLinkConditionalPMF B target u).toReal)
    (hBA : ∀ u : L.Gauge,
      (L.singleLinkConditionalPMF B target u).toReal ≤
        Real.exp R * (L.singleLinkConditionalPMF A target u).toReal) :
    L.singleLinkConditionalTotalVariation A B target ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
  exact finite_pmf_totalVariation_le_of_mutual_le_exp_mul
    (L.singleLinkConditionalPMF A target)
    (L.singleLinkConditionalPMF B target)
    R hR hAB hBA

end

end MathlibAnalytic
end MGAP4D
