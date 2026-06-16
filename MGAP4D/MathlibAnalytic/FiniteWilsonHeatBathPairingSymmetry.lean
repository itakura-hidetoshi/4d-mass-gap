import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathForwardSumExplicit
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

attribute [local instance] finiteLatticeWilsonConfigurationFintype

/-- The total forward transition sum is the Gibbs pairing with the heat-bath
projection in the first slot. -/
theorem finite_lattice_singleLinkHeatBath_forward_sum_eq_gibbsPairing
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
      L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g := by
  classical
  rw [Fintype.sum_prod_type]
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathForwardTerm
    FiniteLatticeWilsonSystem.gibbsPairingReal
    FiniteLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr rfl
  intro A _hA
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _hh
  ring

/-- The total backward transition sum is the Gibbs pairing with the heat-bath
projection in the second slot. -/
theorem finite_lattice_singleLinkHeatBath_backward_sum_eq_gibbsPairing
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) =
      L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) := by
  classical
  rw [Fintype.sum_prod_type]
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathBackwardTerm
    FiniteLatticeWilsonSystem.gibbsPairingReal
    FiniteLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr rfl
  intro A _hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _hh
  ring

/-- Exact single-link heat-bath resampling is symmetric for the finite Wilson
Gibbs pairing. -/
theorem finite_lattice_singleLinkHeatBath_gibbsPairing_projection_symm
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g =
      L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) := by
  calc
    L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g =
        Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) :=
      (finite_lattice_singleLinkHeatBath_forward_sum_eq_gibbsPairing
        L e f g).symm
    _ = Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) :=
      finite_lattice_singleLinkHeatBath_reversible_product_sum L e f g
    _ = L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) :=
      finite_lattice_singleLinkHeatBath_backward_sum_eq_gibbsPairing
        L e f g

end

end MathlibAnalytic
end MGAP4D
