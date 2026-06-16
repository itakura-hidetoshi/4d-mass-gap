import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductReindexing
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The forward transition term is the backward transition term composed with
the involutive link exchange. -/
theorem finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_comp
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.singleLinkHeatBathForwardTerm e f g =
      fun x => L.singleLinkHeatBathBackwardTerm e f g
        (L.singleLinkUpdateSwapEquiv e x) := by
  funext x
  exact finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
    L e f g x

/-- Exact detailed balance reindexes the complete finite configuration--gauge
transition sum through the involutive link exchange. -/
theorem finite_lattice_singleLinkHeatBath_reversible_product_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.singleLinkHeatBathForwardTerm e f g x) =
      ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g x := by
  rw [finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_comp]
  exact finite_sum_comp_equiv
    (L.singleLinkUpdateSwapEquiv e)
    (L.singleLinkHeatBathBackwardTerm e f g)

end

end MathlibAnalytic
end MGAP4D
