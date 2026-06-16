import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathTransitionSum
import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

theorem finite_sum_eq_of_function_eq
    {α M : Type*} [Fintype α] [AddCommMonoid M]
    {u v : α → M} (h : u = v) :
    (∑ x : α, u x) = ∑ x : α, v x := by
  cases h
  rfl

theorem finite_lattice_singleLinkHeatBath_forward_sum_eq_swapped_backward_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ x : L.Configuration × L.Gauge,
      L.singleLinkHeatBathForwardTerm e f g x) =
      ∑ x : L.Configuration × L.Gauge,
        L.singleLinkHeatBathBackwardTerm e f g
          (L.singleLinkUpdateSwapEquiv e x) := by
  classical
  exact finite_sum_eq_of_function_eq
    (finite_lattice_singleLinkHeatBath_forwardTerm_eq_backwardTerm_comp
      L e f g)

end

end MathlibAnalytic
end MGAP4D
