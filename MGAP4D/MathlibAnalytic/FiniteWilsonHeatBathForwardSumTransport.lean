import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTransitionSum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem finite_lattice_singleLinkHeatBath_forwardTerm_comp_alias
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration -> Real) :
    L.singleLinkHeatBathForwardTerm e f g =
      fun x => L.singleLinkHeatBathBackwardTerm e f g
        (L.singleLinkUpdateSwapEquiv e x) :=
  finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_comp
    L e f g

end

end MathlibAnalytic
end MGAP4D
