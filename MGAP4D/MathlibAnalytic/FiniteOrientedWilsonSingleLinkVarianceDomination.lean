import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathPythagorean
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathWeightedFluctuationNorm
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Lightweight centered observable used by the variance-domination layer. -/
def FiniteOrientedLatticeWilsonSystem.varianceCenteredObservable
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  fun A => f A - L.gibbsExpectationReal f

/-- Gibbs variance is the Gibbs squared norm of the centered observable. -/
theorem finite_oriented_gibbsVarianceReal_eq_gibbsPairing_varianceCentered
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsVarianceReal f =
      L.gibbsPairingReal (L.varianceCenteredObservable f)
        (L.varianceCenteredObservable f) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
    FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.varianceCenteredObservable
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- The one-link fluctuation projection is insensitive to subtracting a constant. -/
theorem finite_oriented_singleLinkHeatBathFluctuation_varianceCentered
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.singleLinkHeatBathFluctuationLinearMap e
        (L.varianceCenteredObservable f) =
      L.singleLinkHeatBathFluctuationLinearMap e f := by
  classical
  funext A
  have hMass :
      ∑ g : L.Gauge, (L.singleLinkConditionalPMF A e g).toReal = 1 :=
    finite_oriented_pmf_sum_toReal_eq_one (L.singleLinkConditionalPMF A e)
  have hConditionalCentered :
      L.singleLinkConditionalExpectation
          (L.varianceCenteredObservable f) A e =
        L.singleLinkConditionalExpectation f A e -
          L.gibbsExpectationReal f := by
    unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
      FiniteOrientedLatticeWilsonSystem.varianceCenteredObservable
    calc
      (∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A e g).toReal *
            (f (L.replaceLink A e g) - L.gibbsExpectationReal f)) =
          ∑ g : L.Gauge,
            ((L.singleLinkConditionalPMF A e g).toReal *
                f (L.replaceLink A e g) -
              (L.singleLinkConditionalPMF A e g).toReal *
                L.gibbsExpectationReal f) := by
            apply Finset.sum_congr rfl
            intro g _hg
            ring
      _ = (∑ g : L.Gauge,
            (L.singleLinkConditionalPMF A e g).toReal *
              f (L.replaceLink A e g)) -
          ∑ g : L.Gauge,
            (L.singleLinkConditionalPMF A e g).toReal *
              L.gibbsExpectationReal f := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ g : L.Gauge,
            (L.singleLinkConditionalPMF A e g).toReal *
              f (L.replaceLink A e g)) -
          L.gibbsExpectationReal f := by
            rw [← Finset.sum_mul, hMass, one_mul]
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  change
    L.varianceCenteredObservable f A -
        L.singleLinkConditionalExpectation
          (L.varianceCenteredObservable f) A e =
      f A - L.singleLinkConditionalExpectation f A e
  rw [hConditionalCentered]
  unfold FiniteOrientedLatticeWilsonSystem.varianceCenteredObservable
  ring

/-- The Gibbs squared norm of a one-link fluctuation is bounded by the full
Gibbs squared norm. -/
theorem finite_oriented_gibbsPairing_singleLinkFluctuation_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) ≤
      L.gibbsPairingReal f f := by
  have hPyth :=
    finite_oriented_singleLinkHeatBath_gibbsPairing_pythagorean L e f
  have hProjectionNonneg :
      0 ≤ L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f)
        (L.singleLinkHeatBathProjectionLinearMap e f) := by
    classical
    unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    apply Finset.sum_nonneg
    intro A _hA
    simpa [pow_two, mul_assoc] using
      mul_nonneg
        (finite_oriented_gibbsProbabilityReal_nonneg L A)
        (sq_nonneg ((L.singleLinkHeatBathProjectionLinearMap e f) A))
  linarith

/-- Law-of-total-variance inequality for one physical link: the Gibbs average
of its exact conditional variance is bounded by the full Gibbs variance. -/
theorem finite_oriented_averagedSingleLinkVariance_le_gibbsVarianceReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.averagedSingleLinkVariance f e ≤ L.gibbsVarianceReal f := by
  rw [finite_oriented_averagedSingleLinkVariance_eq_gibbsPairing_fluctuation]
  rw [finite_oriented_gibbsVarianceReal_eq_gibbsPairing_varianceCentered]
  rw [← finite_oriented_singleLinkHeatBathFluctuation_varianceCentered L f e]
  exact finite_oriented_gibbsPairing_singleLinkFluctuation_le
    L (L.varianceCenteredObservable f) e

end

end MathlibAnalytic
end MGAP4D
