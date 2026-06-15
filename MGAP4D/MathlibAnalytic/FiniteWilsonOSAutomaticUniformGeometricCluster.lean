import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticClusterLimitTransfer
import Mathlib.Analysis.SpecificLimits.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A nonnegative geometric envelope with ratio strictly below one tends to
zero, uniformly in any fixed amplitude. -/
theorem geometric_cluster_envelope_tendsto_zero
    (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun r : ℕ => C * q ^ r) atTop (nhds 0) := by
  have hq : Tendsto (fun r : ℕ => q ^ r) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  simpa using (tendsto_const_nhds.mul hq)

/-- Finite Wilson connected correlations controlled by one volume-independent
geometric contraction ratio.

Compared with `FiniteWilsonOSAutomaticClusterLimitData`, this package no longer
asks for an arbitrary envelope or a separate proof that the envelope tends to
zero.  Both are generated from `decayAmplitude O * contractionRatio ^ r`. -/
structure FiniteWilsonOSAutomaticUniformGeometricClusterData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  decayAmplitude_nonneg : ∀ O : Observable, 0 ≤ decayAmplitude O
  contractionRatio : ℝ
  contractionRatio_nonneg : 0 ≤ contractionRatio
  contractionRatio_lt_one : contractionRatio < 1
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsConnectedCorrelation
            (leftObservable n O) (rightObservable n O r))
        atTop (nhds (continuumConnectedCorrelation O r))
  uniformGeometricBound :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      ‖(W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r)‖ ≤
        decayAmplitude O * contractionRatio ^ r

/-- The generated geometric envelope. -/
def FiniteWilsonOSAutomaticUniformGeometricClusterData.clusterEnvelope
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticUniformGeometricClusterData W) :
    D.Observable → ℕ → ℝ :=
  fun O r => D.decayAmplitude O * D.contractionRatio ^ r

/-- Convert a uniform geometric estimate into the general finite Wilson cluster
limit package.  The envelope convergence field is discharged automatically. -/
noncomputable def
    FiniteWilsonOSAutomaticUniformGeometricClusterData.toClusterLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticUniformGeometricClusterData W) :
    FiniteWilsonOSAutomaticClusterLimitData W :=
  { Observable := D.Observable
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    clusterEnvelope := D.clusterEnvelope
    pointwiseConvergence := D.pointwiseConvergence
    uniformEnvelope := D.uniformGeometricBound
    envelopeTendstoZero := fun O =>
      geometric_cluster_envelope_tendsto_zero
        (D.decayAmplitude O) D.contractionRatio
        D.contractionRatio_nonneg D.contractionRatio_lt_one }

/-- A volume-uniform geometric bound therefore gives continuum clustering after
pointwise convergence of the actual finite Wilson connected correlations. -/
theorem finite_wilson_uniform_geometric_cluster_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticUniformGeometricClusterData W) :
    D.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_os_automatic_cluster_property_passes_to_limit
    D.toClusterLimitData

/-- The limiting connected correlation inherits the same geometric envelope. -/
theorem finite_wilson_uniform_geometric_cluster_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticUniformGeometricClusterData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * D.contractionRatio ^ r := by
  exact le_of_tendsto'
    (D.pointwiseConvergence O r).norm
    (fun n => D.uniformGeometricBound n O r)

end

end MathlibAnalytic
end MGAP4D
