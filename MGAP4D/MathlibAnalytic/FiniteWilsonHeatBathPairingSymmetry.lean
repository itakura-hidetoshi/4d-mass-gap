import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathForwardSumExplicit
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact single-link heat-bath resampling is symmetric for the finite Wilson
Gibbs pairing. -/
theorem finite_lattice_singleLinkHeatBath_gibbsPairing_projection_symm
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g =
      L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) := by
  classical
  have hProduct :=
    finite_lattice_singleLinkHeatBath_reversible_product_sum L e f g
  simpa only [
    FiniteLatticeWilsonSystem.gibbsPairingReal,
    FiniteLatticeWilsonSystem.singleLinkHeatBathProjection,
    FiniteLatticeWilsonSystem.singleLinkConditionalExpectation,
    FiniteLatticeWilsonSystem.singleLinkHeatBathForwardTerm,
    FiniteLatticeWilsonSystem.singleLinkHeatBathBackwardTerm,
    Fintype.sum_prod_type,
    Finset.mul_sum,
    Finset.sum_mul,
    mul_assoc,
    mul_left_comm,
    mul_comm
  ] using hProduct

end

end MathlibAnalytic
end MGAP4D
