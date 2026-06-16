import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathForwardSumTransport
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathReversibleProductSum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite Wilson configuration space inherits a canonical noncomputable
`Fintype` structure from the finite edge set and finite gauge group.  Naming
this instance makes product sums available already while theorem statements
are elaborated, before a proof-local `classical` tactic can run. -/
noncomputable local instance finiteLatticeWilsonConfigurationFintype
    (L : FiniteLatticeWilsonSystem) : Fintype L.Configuration := by
  classical
  exact Fintype.ofFinite L.Configuration

/-- Summing the pointwise detailed-balance identity transports the forward
transition sum to the backward transition sum precomposed with the involutive
link-update swap. -/
theorem finite_lattice_singleLinkHeatBath_forward_sum_eq_swapped_backward_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
      Finset.univ.sum
        (fun x : L.Configuration × L.Gauge =>
          L.singleLinkHeatBathBackwardTerm e f g
            (L.singleLinkUpdateSwapEquiv e x)) := by
  classical
  exact congrArg
    (fun w : (L.Configuration × L.Gauge → ℝ) =>
      Finset.univ.sum w)
    (finite_lattice_singleLinkHeatBath_forwardTerm_comp_alias L e f g)

end

end MathlibAnalytic
end MGAP4D
