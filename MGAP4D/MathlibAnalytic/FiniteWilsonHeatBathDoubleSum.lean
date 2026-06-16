import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductReindexing

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Nested-sum form of finite single-link heat-bath reversibility. -/
theorem finite_lattice_singleLinkHeatBath_reversible_double_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ A : L.Configuration, ∑ h : L.Gauge,
      L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A e h).toReal *
        f (L.replaceLink A e h) * g A) =
      ∑ A : L.Configuration, ∑ h : L.Gauge,
        L.gibbsProbabilityReal A *
          (L.singleLinkConditionalPMF A e h).toReal *
          f A * g (L.replaceLink A e h) := by
  rw [← Fintype.sum_prod_type, ← Fintype.sum_prod_type]
  exact finite_lattice_singleLinkHeatBath_reversible_product_sum L e f g

end

end MathlibAnalytic
end MGAP4D
