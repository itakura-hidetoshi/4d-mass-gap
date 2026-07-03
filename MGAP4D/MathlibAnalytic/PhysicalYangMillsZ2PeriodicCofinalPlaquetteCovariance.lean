import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCofinalExpectationPullback
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance (index : ℕ → ℕ) (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k)) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- Finite Gibbs covariance equals the connected correlation of the cofinally
indexed approximating measure. -/
theorem
    PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData.finiteCovariance_eq
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ} {hBeta : 0 < beta} {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData
        S beta hBeta distance)
    (k : ℕ) :
    FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
          beta hBeta.le)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
            beta hBeta.le)
          (B.sourcePlaquette k))
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
            beta hBeta.le)
          (B.targetPlaquette k)) =
      S.approximatingConnectedCorrelation
        k B.sourceObservable B.targetObservable := by
  let L :=
    z2PeriodicHypercubicOrientedWilsonSystem
      (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
      beta hBeta.le
  let sourceFinite : L.Configuration → ℝ :=
    FiniteOrientedLatticeWilsonSystem.plaquetteObservable
      L (B.sourcePlaquette k)
  let targetFinite : L.Configuration → ℝ :=
    FiniteOrientedLatticeWilsonSystem.plaquetteObservable
      L (B.targetPlaquette k)
  have hSource :=
    B.approximatingExpectation_eq_gibbs_of_pullback
      k B.sourceObservable sourceFinite (by
        intro U
        simpa [L, sourceFinite] using B.source_pullback k U)
  have hTarget :=
    B.approximatingExpectation_eq_gibbs_of_pullback
      k B.targetObservable targetFinite (by
        intro U
        simpa [L, targetFinite] using B.target_pullback k U)
  have hProduct :=
    B.approximatingExpectation_eq_gibbs_of_pullback
      k (B.sourceObservable * B.targetObservable)
      (fun U => sourceFinite U * targetFinite U) (by
        intro U
        simpa [L, sourceFinite, targetFinite] using
          congrArg₂ (fun x y : ℝ => x * y)
            (B.source_pullback k U) (B.target_pullback k U))
  change L.gibbsCovarianceReal sourceFinite targetFinite =
    S.approximatingConnectedCorrelation
      k B.sourceObservable B.targetObservable
  calc
    L.gibbsCovarianceReal sourceFinite targetFinite =
      (∫ U, sourceFinite U * targetFinite U ∂L.gibbsMeasure) -
        (∫ U, sourceFinite U ∂L.gibbsMeasure) *
          ∫ U, targetFinite U ∂L.gibbsMeasure :=
      Z2PeriodicPlaquetteInterpolationAux.gibbsCovarianceReal_eq_integral_sub_mul_integral
        L sourceFinite targetFinite
    _ = S.approximatingConnectedCorrelation
        k B.sourceObservable B.targetObservable := by
      unfold PhysicalFourDimensionalYangMillsWeakLimit.approximatingConnectedCorrelation
      rw [hProduct, hSource, hTarget]

end

end MathlibAnalytic
end MGAP4D
