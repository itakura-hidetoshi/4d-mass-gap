import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTransitionSum
import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Summing the pointwise transition identity gives the forward sum as the
backward sum composed with the involutive link exchange. -/
theorem finite_lattice_singleLinkHeatBath_forward_sum_eq_swapped_backward_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.singleLinkHeatBathForwardTerm e f g x) =
      ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g
          (L.singleLinkUpdateSwapEquiv e x) := by
  classical
  exact Fintype.sum_congr
    (fun x : L.Configuration × L.Gauge =>
      L.singleLinkHeatBathForwardTerm e f g x)
    (fun x : L.Configuration × L.Gauge =>
      L.singleLinkHeatBathBackwardTerm e f g
        (L.singleLinkUpdateSwapEquiv e x))
    (fun x =>
      finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
        L e f g x)

end

end MathlibAnalytic
end MGAP4D
