import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticUniformGeometricCluster
import MGAP4D.MathlibAnalytic.ExactGapClusterContractionRatio

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson connected correlations satisfying the public exact-gap geometric rate. -/
structure FiniteWilsonOSAutomaticExactGapClusterData
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
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsConnectedCorrelation
            (leftObservable n O) (rightObservable n O r))
        atTop (nhds (continuumConnectedCorrelation O r))
  uniformExactGapBound :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      ‖(W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r)‖ ≤
        decayAmplitude O * exactGapClusterContractionRatio ^ r

/-- Convert an exact-gap finite-volume estimate into the uniform geometric package. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapClusterData.toUniformGeometricClusterData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapClusterData W) :
    FiniteWilsonOSAutomaticUniformGeometricClusterData W :=
  { Observable := D.Observable
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    decayAmplitude_nonneg := D.decayAmplitude_nonneg
    contractionRatio := exactGapClusterContractionRatio
    contractionRatio_nonneg := exact_gap_cluster_contraction_ratio_nonneg
    contractionRatio_lt_one := exact_gap_cluster_contraction_ratio_lt_one
    pointwiseConvergence := D.pointwiseConvergence
    uniformGeometricBound := D.uniformExactGapBound }

/-- Exact-gap finite Wilson bounds imply continuum clustering. -/
theorem finite_wilson_exact_gap_cluster_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapClusterData W) :
    D.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.
      ContinuumClusterProperty :=
  finite_wilson_uniform_geometric_cluster_passes_to_limit
    D.toUniformGeometricClusterData

/-- The continuum connected correlation inherits the exact-gap geometric rate. -/
theorem finite_wilson_exact_gap_cluster_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapClusterData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_uniform_geometric_cluster_continuum_bound
    D.toUniformGeometricClusterData O r

end

end MathlibAnalytic
end MGAP4D
