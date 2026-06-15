import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticClusterLimitTransfer

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Sequential Schwinger values built from actual finite Wilson Gibbs
expectations, together with a volume-uniform regularity bound. -/
structure FiniteWilsonOSAutomaticRegularityLimitData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  TestDatum : Type
  scale : ℕ → W.index
  finiteObservable :
    (n : ℕ) → TestDatum → (W.system (scale n)).Configuration → ℝ
  continuumSchwingerValue : TestDatum → ℝ
  regularityBound : TestDatum → ℝ
  pointwiseConvergence :
    ∀ q : TestDatum,
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsExpectation (finiteObservable n q))
        atTop (nhds (continuumSchwingerValue q))
  uniformRegularityBound :
    ∀ (n : ℕ) (q : TestDatum),
      ‖(W.system (scale n)).gibbsExpectation (finiteObservable n q)‖ ≤
        regularityBound q

/-- Adapter from actual finite Wilson Schwinger expectations to the generic
regularity-limit record. -/
noncomputable def
    FiniteWilsonOSAutomaticRegularityLimitData.toRegularityLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticRegularityLimitData W) :
    EuclideanYangMillsRegularityLimitData :=
  { TestDatum := D.TestDatum
    finiteSchwingerValue := fun n q =>
      (W.system (D.scale n)).gibbsExpectation (D.finiteObservable n q)
    continuumSchwingerValue := D.continuumSchwingerValue
    regularityBound := D.regularityBound
    pointwiseConvergence := D.pointwiseConvergence
    uniformRegularityBound := D.uniformRegularityBound }

/-- Continuum regularity obtained from actual finite Wilson Schwinger
expectations and a volume-uniform bound. -/
theorem finite_wilson_os_automatic_regularity_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticRegularityLimitData W) :
    D.toRegularityLimitData.ContinuumRegularity :=
  euclidean_yang_mills_regularity_passes_to_limit D.toRegularityLimitData

end

end MathlibAnalytic
end MGAP4D
