import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathForwardSumTransport
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable local instance finiteLatticeWilsonConfigurationFintype
    (L : FiniteLatticeWilsonSystem) : Fintype L.Configuration := by
  classical
  exact Fintype.ofFinite L.Configuration

theorem finite_lattice_singleLinkHeatBath_forward_sum_eq_swapped_backward_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration -> Real) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
      Finset.univ.sum
        (fun x : L.Configuration × L.Gauge =>
          L.singleLinkHeatBathBackwardTerm e f g
            (L.singleLinkUpdateSwapEquiv e x)) := by
  classical
  exact congrArg
    (fun w : (L.Configuration × L.Gauge -> Real) =>
      Finset.univ.sum w)
    (finite_lattice_singleLinkHeatBath_forwardTerm_comp_alias L e f g)

theorem finite_lattice_singleLinkHeatBath_swapped_backward_sum_eq_backward_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration -> Real) :
    Finset.univ.sum
        (fun x : L.Configuration × L.Gauge =>
          L.singleLinkHeatBathBackwardTerm e f g
            (L.singleLinkUpdateSwapEquiv e x)) =
      Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) := by
  classical
  exact finite_sum_comp_equiv
    (L.singleLinkUpdateSwapEquiv e)
    (L.singleLinkHeatBathBackwardTerm e f g)

theorem finite_lattice_singleLinkHeatBath_reversible_product_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration -> Real) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
      Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) := by
  calc
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
        Finset.univ.sum
          (fun x : L.Configuration × L.Gauge =>
            L.singleLinkHeatBathBackwardTerm e f g
              (L.singleLinkUpdateSwapEquiv e x)) :=
      finite_lattice_singleLinkHeatBath_forward_sum_eq_swapped_backward_sum
        L e f g
    _ = Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) :=
      finite_lattice_singleLinkHeatBath_swapped_backward_sum_eq_backward_sum
        L e f g

end

end MathlibAnalytic
end MGAP4D
