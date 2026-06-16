import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductReindexing

namespace MGAP4D
namespace MathlibAnalytic

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

end

end MathlibAnalytic
end MGAP4D
