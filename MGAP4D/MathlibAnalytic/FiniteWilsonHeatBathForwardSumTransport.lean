import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTransitionSum
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathReversibleProductSum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem finite_lattice_singleLinkHeatBath_forward_sum_eq_swapped_backward_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration -> Real) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
      Finset.univ.sum
        (fun x : Prod L.Configuration L.Gauge =>
          L.singleLinkHeatBathBackwardTerm e f g
            (L.singleLinkUpdateSwapEquiv e x)) := by
  classical
  exact finite_sum_rewrite
    (finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_comp
      L e f g)

end

end MathlibAnalytic
end MGAP4D
