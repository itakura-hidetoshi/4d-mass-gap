import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonLinkExchange
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathProjection
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsRealVariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Pointwise reversibility of the Gibbs-weighted oriented one-link transition
term. -/
theorem finite_oriented_singleLinkHeatBath_reversible_term
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (h : L.Gauge)
    (f g : L.Configuration → ℝ) :
    L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A target h).toReal *
        f (L.replaceLink A target h) * g A =
      L.gibbsProbabilityReal (L.replaceLink A target h) *
        (L.singleLinkConditionalPMF
          (L.replaceLink A target h) target (A target)).toReal *
        f (L.replaceLink A target h) *
        g (L.replaceLink (L.replaceLink A target h) target (A target)) := by
  rw [finite_oriented_singleLinkHeatBath_detailedBalance_real]
  rw [finite_oriented_singleLinkUpdateSwap_first_roundTrip]

/-- Forward Gibbs-weighted transition term for one exact physical-link
resampling. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathForwardTerm
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) : ℝ :=
  L.gibbsProbabilityReal x.1 *
    (L.singleLinkConditionalPMF x.1 target x.2).toReal *
    f (L.replaceLink x.1 target x.2) * g x.1

/-- Backward Gibbs-weighted transition term for one exact physical-link
resampling. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathBackwardTerm
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) : ℝ :=
  L.gibbsProbabilityReal x.1 *
    (L.singleLinkConditionalPMF x.1 target x.2).toReal *
    f x.1 * g (L.replaceLink x.1 target x.2)

/-- Detailed balance identifies a forward oriented transition term with the
backward term after the involutive old/new-value exchange. -/
theorem finite_oriented_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ)
    (x : L.Configuration × L.Gauge) :
    L.singleLinkHeatBathForwardTerm target f g x =
      L.singleLinkHeatBathBackwardTerm target f g
        (L.singleLinkUpdateSwapEquiv target x) := by
  rcases x with ⟨A, h⟩
  simpa [FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathForwardTerm,
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathBackwardTerm,
    FiniteOrientedLatticeWilsonSystem.singleLinkUpdateSwapEquiv] using
    finite_oriented_singleLinkHeatBath_reversible_term L A target h f g

noncomputable instance finiteOrientedLatticeWilsonConfigurationFintype
    (L : FiniteOrientedLatticeWilsonSystem) : Fintype L.Configuration := by
  classical
  exact Fintype.ofFinite L.Configuration

/-- Summed oriented forward and backward transition terms agree by finite
reindexing under the update-exchange equivalence. -/
theorem finite_oriented_singleLinkHeatBath_reversible_product_sum
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm target f g) =
      Finset.univ.sum (L.singleLinkHeatBathBackwardTerm target f g) := by
  calc
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm target f g) =
        Finset.univ.sum
          (fun x : L.Configuration × L.Gauge =>
            L.singleLinkHeatBathBackwardTerm target f g
              (L.singleLinkUpdateSwapEquiv target x)) := by
      exact congrArg
        (fun w : (L.Configuration × L.Gauge → ℝ) => Finset.univ.sum w)
        (by
          funext x
          exact finite_oriented_singleLinkHeatBath_forwardTerm_eq_backwardTerm_swap
            L target f g x)
    _ = Finset.univ.sum (L.singleLinkHeatBathBackwardTerm target f g) :=
      finite_sum_comp_equiv
        (L.singleLinkUpdateSwapEquiv target)
        (L.singleLinkHeatBathBackwardTerm target f g)

/-- The total forward transition sum is the oriented Gibbs pairing with the
one-link projection in its first slot. -/
theorem finite_oriented_singleLinkHeatBath_forward_sum_eq_gibbsPairing
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathForwardTerm target f g) =
      L.gibbsPairingReal (L.singleLinkHeatBathProjection target f) g := by
  classical
  rw [Fintype.sum_prod_type]
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathForwardTerm
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

/-- The total backward transition sum is the oriented Gibbs pairing with the
one-link projection in its second slot. -/
theorem finite_oriented_singleLinkHeatBath_backward_sum_eq_gibbsPairing
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    Finset.univ.sum (L.singleLinkHeatBathBackwardTerm target f g) =
      L.gibbsPairingReal f (L.singleLinkHeatBathProjection target g) := by
  classical
  rw [Fintype.sum_prod_type]
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathBackwardTerm
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

/-- Exact physical-link heat-bath resampling is symmetric for the
orientation-correct finite Wilson Gibbs pairing. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (L.singleLinkHeatBathProjection target f) g =
      L.gibbsPairingReal f (L.singleLinkHeatBathProjection target g) := by
  calc
    L.gibbsPairingReal (L.singleLinkHeatBathProjection target f) g =
        Finset.univ.sum (L.singleLinkHeatBathForwardTerm target f g) :=
      (finite_oriented_singleLinkHeatBath_forward_sum_eq_gibbsPairing
        L target f g).symm
    _ = Finset.univ.sum (L.singleLinkHeatBathBackwardTerm target f g) :=
      finite_oriented_singleLinkHeatBath_reversible_product_sum
        L target f g
    _ = L.gibbsPairingReal f (L.singleLinkHeatBathProjection target g) :=
      finite_oriented_singleLinkHeatBath_backward_sum_eq_gibbsPairing
        L target f g

end

end MathlibAnalytic
end MGAP4D