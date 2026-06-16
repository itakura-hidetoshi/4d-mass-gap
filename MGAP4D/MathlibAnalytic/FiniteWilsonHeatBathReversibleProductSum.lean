import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTransitionSum
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact detailed balance reindexes the complete finite configuration--gauge
transition sum through the involutive link exchange. -/
theorem finite_lattice_singleLinkHeatBath_reversible_product_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.singleLinkHeatBathForwardTerm e f g x) =
      ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g x := by
  classical
  have hTerm :=
    finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_comp
      L e f g
  have hSum := congrArg
    (fun k : (L.Configuration × L.Gauge) → ℝ => ∑ x, k x)
    hTerm
  exact hSum.trans
    (finite_sum_comp_equiv
      (L.singleLinkUpdateSwapEquiv e)
      (L.singleLinkHeatBathBackwardTerm e f g))

end

end MathlibAnalytic
end MGAP4D
