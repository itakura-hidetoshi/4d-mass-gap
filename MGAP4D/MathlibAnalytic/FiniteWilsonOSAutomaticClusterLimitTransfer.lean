import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticEuclideanLimitTransfer

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Connected correlation of two real finite-lattice observables. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsConnectedCorrelation
    (L : FiniteLatticeWilsonSystem)
    (O₁ O₂ : L.Configuration → ℝ) : ℝ :=
  L.gibbsExpectation (fun A => O₁ A * O₂ A) -
    L.gibbsExpectation O₁ * L.gibbsExpectation O₂

/-- Sequential connected correlations built from actual finite Wilson Gibbs
expectations, together with a volume-uniform decaying envelope. -/
structure FiniteWilsonOSAutomaticClusterLimitData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  clusterEnvelope : Observable → ℕ → ℝ
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsConnectedCorrelation
            (leftObservable n O) (rightObservable n O r))
        atTop (nhds (continuumConnectedCorrelation O r))
  uniformEnvelope :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      ‖(W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r)‖ ≤
        clusterEnvelope O r
  envelopeTendstoZero :
    ∀ O : Observable, Tendsto (clusterEnvelope O) atTop (nhds 0)

/-- Adapter from actual finite Wilson connected correlations to the generic
cluster-limit record. -/
noncomputable def
    FiniteWilsonOSAutomaticClusterLimitData.toClusterLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticClusterLimitData W) :
    EuclideanYangMillsClusterLimitData :=
  { Observable := D.Observable
    finiteConnectedCorrelation := fun n O r =>
      (W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    clusterEnvelope := D.clusterEnvelope
    pointwiseConvergence := D.pointwiseConvergence
    uniformEnvelope := D.uniformEnvelope
    envelopeTendstoZero := D.envelopeTendstoZero }

/-- Continuum clustering obtained from actual finite Wilson connected
correlations and a decaying volume-uniform envelope. -/
theorem finite_wilson_os_automatic_cluster_property_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticClusterLimitData W) :
    D.toClusterLimitData.ContinuumClusterProperty :=
  euclidean_yang_mills_cluster_property_passes_to_limit D.toClusterLimitData

end

end MathlibAnalytic
end MGAP4D
