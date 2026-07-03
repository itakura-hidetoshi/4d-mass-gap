import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakMeasureLimit
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteCovarianceLimitBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The connected correlation of two bounded continuous observables in one
approximating probability measure of a physical weak-limit carrier. -/
def PhysicalFourDimensionalYangMillsWeakLimit.approximatingConnectedCorrelation
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (n : ℕ)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) : ℝ :=
  (∫ A, O₁ A * O₂ A
    ∂(S.approximatingMeasure n : Measure S.Configuration)) -
    (∫ A, O₁ A
      ∂(S.approximatingMeasure n : Measure S.Configuration)) *
    (∫ A, O₂ A
      ∂(S.approximatingMeasure n : Measure S.Configuration))

/-- The connected correlation of two bounded continuous observables in the
continuum probability measure of a physical weak-limit carrier. -/
def PhysicalFourDimensionalYangMillsWeakLimit.continuumConnectedCorrelation
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) : ℝ :=
  (∫ A, O₁ A * O₂ A
    ∂(S.continuumMeasure : Measure S.Configuration)) -
    (∫ A, O₁ A
      ∂(S.continuumMeasure : Measure S.Configuration)) *
    (∫ A, O₂ A
      ∂(S.continuumMeasure : Measure S.Configuration))

/-- Weak convergence gives convergence of the two-point expectation because
the product of two bounded continuous real observables is again bounded and
continuous. -/
theorem physical_yang_mills_bounded_observable_twoPoint_expectation_converges
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, O₁ A * O₂ A
          ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, O₁ A * O₂ A
          ∂(S.continuumMeasure : Measure S.Configuration))) := by
  simpa using
    physical_yang_mills_bounded_observable_expectation_converges
      S (O₁ * O₂)

/-- Weak convergence of probability measures automatically gives convergence
of connected correlations for every pair of bounded continuous observables. -/
theorem physical_yang_mills_bounded_observable_connectedCorrelation_converges
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ => S.approximatingConnectedCorrelation n O₁ O₂)
      atTop
      (nhds (S.continuumConnectedCorrelation O₁ O₂)) := by
  have h₁₂ :=
    physical_yang_mills_bounded_observable_twoPoint_expectation_converges
      S O₁ O₂
  have h₁ :=
    physical_yang_mills_bounded_observable_expectation_converges S O₁
  have h₂ :=
    physical_yang_mills_bounded_observable_expectation_converges S O₂
  simpa
    [PhysicalFourDimensionalYangMillsWeakLimit.approximatingConnectedCorrelation,
      PhysicalFourDimensionalYangMillsWeakLimit.continuumConnectedCorrelation] using
    h₁₂.sub (h₁.mul h₂)

/-- Model-dependent identifications connecting a fixed pair of bounded
continuous observables in one common Polish weak-limit space to actual finite
periodic `Z₂` plaquette covariances.

Weak convergence supplies covariance convergence automatically once these
identifications and the fixed-distance plaquette family are provided.  This
bridge does not construct the common configuration space or the finite-volume
interpolation maps. -/
structure PhysicalYangMillsZ2PeriodicPlaquetteCovarianceWeakLimitBridge
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ) where
  sourceObservable : BoundedContinuousFunction S.Configuration ℝ
  targetObservable : BoundedContinuousFunction S.Configuration ℝ
  sourcePlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  targetPlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  distance_eq :
    ∀ k : ℕ,
      periodicHypercubicPlaquetteBaseL1Distance
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          (sourcePlaquette k)
          (targetPlaquette k) =
        distance
  finiteCovariance_eq :
    ∀ k : ℕ,
      FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
            (z2PeriodicHypercubicOrientedWilsonSystem
              (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
              beta hBeta.le)
            (sourcePlaquette k))
          (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
            (z2PeriodicHypercubicOrientedWilsonSystem
              (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
              beta hBeta.le)
            (targetPlaquette k)) =
        S.approximatingConnectedCorrelation
          k sourceObservable targetObservable

/-- Convert a common-space weak-limit identification into the scalar
covariance-limit bridge.  The limiting scalar is the connected correlation in
the weak-limit probability measure. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicPlaquetteCovarianceWeakLimitBridge.toCovarianceLimitBridge
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicPlaquetteCovarianceWeakLimitBridge
        S beta hBeta distance) :
    Z2PeriodicHypercubicOrientedPlaquetteCovarianceLimitBridge
      beta hBeta distance :=
  { sourcePlaquette := B.sourcePlaquette
    targetPlaquette := B.targetPlaquette
    distance_eq := B.distance_eq
    limitingCovariance :=
      S.continuumConnectedCorrelation
        B.sourceObservable B.targetObservable
    covariance_tendsto := by
      have h :=
        physical_yang_mills_bounded_observable_connectedCorrelation_converges
          S B.sourceObservable B.targetObservable
      simpa only [B.finiteCovariance_eq] using h }

/-- The volume-uniform finite-volume clustering estimate therefore passes to
the connected correlation in any common-space weak limit equipped with the
finite plaquette identification bridge. -/
theorem
    PhysicalYangMillsZ2PeriodicPlaquetteCovarianceWeakLimitBridge.continuumConnectedCorrelation_abs_le
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (B :
      PhysicalYangMillsZ2PeriodicPlaquetteCovarianceWeakLimitBridge
        S beta hBeta distance) :
    |S.continuumConnectedCorrelation
        B.sourceObservable B.targetObservable| ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  B.toCovarianceLimitBridge.limitingCovariance_abs_le K

end

end MathlibAnalytic
end MGAP4D
