import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductReindexing
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The backward single-link transition sum is invariant under the involutive
exchange of the old and newly sampled link values. -/
theorem finite_lattice_singleLinkHeatBath_backwardTerm_sum_swap
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.singleLinkHeatBathBackwardTerm e f g
        (L.singleLinkUpdateSwapEquiv e x)) =
      ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g x := by
  classical
  exact finite_sum_comp_equiv
    (L.singleLinkUpdateSwapEquiv e)
    (L.singleLinkHeatBathBackwardTerm e f g)

end

end MathlibAnalytic
end MGAP4D
