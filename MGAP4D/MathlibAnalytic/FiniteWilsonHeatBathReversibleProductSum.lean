import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTransitionSum
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact detailed balance reindexes the complete finite configuration--gauge
transition sum through the involutive link exchange. -/
theorem finite_lattice_singleLinkHeatBath_reversible_product_sum_v2
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.singleLinkHeatBathForwardTerm e f g x) =
      ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g x := by
  classical
  apply Fintype.sum_equiv (L.singleLinkUpdateSwapEquiv e)
  intro x
  exact finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
    L e f g x

end

end MathlibAnalytic
end MGAP4D
