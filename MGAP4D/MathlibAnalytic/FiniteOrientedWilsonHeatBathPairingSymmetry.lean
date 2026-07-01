import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathProjection
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Forward Gibbs-weighted transition term for one native oriented update. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathForwardTerm
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) : ℝ :=
  L.gibbsProbabilityReal x.1 *
    (L.singleLinkConditionalPMF x.1 e x.2).toReal *
    f (L.replaceLink x.1 e x.2) * g x.1

/-- Backward Gibbs-weighted transition term for one native oriented update. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathBackwardTerm
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) : ℝ :=
  L.gibbsProbabilityReal x.1 *
    (L.singleLinkConditionalPMF x.1 e x.2).toReal *
    f x.1 * g (L.replaceLink x.1 e x.2)

/-- Pointwise reversibility of the native Gibbs-weighted transition term. -/
theorem finite_oriented_singleLinkHeatBath_reversible_term
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (h : L.Gauge)
    (f g : L.Configuration → ℝ) :
    L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A e h).toReal *
        f (L.replaceLink A e h) * g A =
      L.gibbsProbabilityReal (L.replaceLink A e h) *
        (L.singleLinkConditionalPMF
          (L.replaceLink A e h) e (A e)).toReal *
        f (L.replaceLink A e h) *
        g (L.replaceLink (L.replaceLink A e h) e (A e)) := by
  rw [finite_oriented_singleLinkHeatBath_detailedBalance_real]
  rw [finite_oriented_singleLinkUpdateSwap_first_roundTrip]

/-- Pointwise detailed balance identifies the forward term with the backward
term after the link-exchange involution. -/
theorem finite_oriented_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) :
    L.singleLinkHeatBathForwardTerm e f g x =
      L.singleLinkHeatBathBackwardTerm e f g
        (L.singleLinkUpdateSwapEquiv e x) := by
  rcases x with ⟨A, h⟩
  simpa
    [FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathForwardTerm,
      FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathBackwardTerm,
      FiniteOrientedLatticeWilsonSystem.singleLinkUpdateSwapEquiv]
    using finite_oriented_singleLinkHeatBath_reversible_term
      L A e h f g

/-- Finite enumeration used by the active oriented heat-bath carrier. -/
noncomputable instance finiteOrientedHeatBathConfigurationFintype
    (L : FiniteOrientedLatticeWilsonSystem) : Fintype L.Configuration := by
  classical
  exact Fintype.ofFinite L.Configuration

/-- Native forward and backward transition sums coincide. -/
theorem finite_oriented_singleLinkHeatBath_reversible_product_sum
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
      Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) := by
  classical
  calc
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
        Finset.univ.sum
          (fun x : L.Configuration × L.Gauge =>
            L.singleLinkHeatBathBackwardTerm e f g
              (L.singleLinkUpdateSwapEquiv e x)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact
        finite_oriented_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
          L e f g x
    _ = Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) :=
      finite_sum_comp_equiv
        (L.singleLinkUpdateSwapEquiv e)
        (L.singleLinkHeatBathBackwardTerm e f g)

/-- The forward transition sum is the Gibbs pairing with `P_e f`. -/
theorem finite_oriented_singleLinkHeatBath_forward_sum_eq_gibbsPairing
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) =
      L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g := by
  classical
  rw [Fintype.sum_prod_type]
  unfold
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathForwardTerm
    FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr
  · ext A
    simp
  · intro A _hA
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _hh
    ring

/-- The backward transition sum is the Gibbs pairing with `P_e g`. -/
theorem finite_oriented_singleLinkHeatBath_backward_sum_eq_gibbsPairing
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) =
      L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) := by
  classical
  rw [Fintype.sum_prod_type]
  unfold
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathBackwardTerm
    FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr
  · ext A
    simp
  · intro A _hA
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _hh
    ring

/-- Native oriented one-link resampling is symmetric for the Gibbs pairing. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g =
      L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) := by
  calc
    L.gibbsPairingReal (L.singleLinkHeatBathProjection e f) g =
        Finset.univ.sum (L.singleLinkHeatBathForwardTerm e f g) :=
      (finite_oriented_singleLinkHeatBath_forward_sum_eq_gibbsPairing
        L e f g).symm
    _ = Finset.univ.sum (L.singleLinkHeatBathBackwardTerm e f g) :=
      finite_oriented_singleLinkHeatBath_reversible_product_sum L e f g
    _ = L.gibbsPairingReal f (L.singleLinkHeatBathProjection e g) :=
      finite_oriented_singleLinkHeatBath_backward_sum_eq_gibbsPairing
        L e f g

end

end MathlibAnalytic
end MGAP4D
