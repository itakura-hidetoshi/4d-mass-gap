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
  funext A
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  unfold FiniteOrientedLatticeWilsonSystem.varianceCenteredObservable
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjectionLinearMap
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  classical
  have hMass :
      ∑ g : L.Gauge, (L.singleLinkConditionalPMF A e g).toReal = 1 :=
    finite_oriented_pmf_sum_toReal_eq_one (L.singleLinkConditionalPMF A e)
  rw [Finset.sum_sub_distrib]
  have hConst :
      ∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A e g).toReal *
            L.gibbsExpectationReal f = L.gibbsExpectationReal f := by
    rw [← Finset.sum_mul, hMass, one_mul]
  rw [hConst]
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
    exact Finset.sum_nonneg fun A _hA =>
      mul_nonneg
        (finite_oriented_gibbsProbabilityReal_nonneg L A)
        (mul_self_nonneg _)
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
