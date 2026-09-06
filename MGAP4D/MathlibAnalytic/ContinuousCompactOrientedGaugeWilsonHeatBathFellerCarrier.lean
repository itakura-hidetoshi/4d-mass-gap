import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathCommutation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkFellerClosure

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The raw exact heat-bath transform introduced for commutation is definitionally
identical to the canonical pointwise one-link conditional expectation on bounded
continuous observables. -/
@[simp] theorem continuous_compact_oriented_singleLinkHeatBathTransform_eq_conditionalExpectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathTransform target O A =
      C.singleLinkConditionalExpectationBCF O A target := by
  rfl

/-- The canonical Feller-closed one-link conditional expectations commute on
distinct links in the same fixed eight-color class.  This is the bounded-
continuous carrier statement needed before forming an order-independent color
block. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkConditionalExpectationContinuousBCF_commute_of_sameColor
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
    C.singleLinkConditionalExpectationContinuousBCF source
        (C.singleLinkConditionalExpectationContinuousBCF target O) =
      C.singleLinkConditionalExpectationContinuousBCF target
        (C.singleLinkConditionalExpectationContinuousBCF source O) := by
  dsimp only
  ext A
  change
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
        source
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
            target O) A =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
          target
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
              source O) A
  exact congrFun
    (periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathTransform_commute_of_sameColor
      H N hN beta hBeta O O.continuous hNe hColor) A

end
end MathlibAnalytic
end MGAP4D
