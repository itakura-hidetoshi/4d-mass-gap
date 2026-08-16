import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryWilsonSectorGaugeInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryBoundaryGaugeTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenHalfSectorBoundaryFiberedDependence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialCrossingBoundaryDependence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance boundaryGramGaugeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- The completed positive Wilson Boltzmann amplitude on the full actual finite
configuration space is gauge invariant. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta A := by
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_gaugeInvariant
    H N hN beta hbeta]
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_gaugeInvariant
    H N hN beta hbeta]

/-- The boundary-only spatial crossing Boltzmann weight is invariant under the
actual boundary restriction of a finite lattice gauge transformation.

The proof reconstructs the transformed full configuration from its boundary
and two open-half coordinates.  Open-half choices disappear by the already
proved boundary dependence theorem. -/
theorem periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight H N beta
        (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b) =
      periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight H N beta b := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let A₀ : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
    P.boundaryFiberedAssemble b (fun _ => 1) (fun _ => 1)
  let A₁ : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform gamma A₀
  have hB :
      P.boundaryRestriction A₁ =
        periodicHypercubicEvenBoundaryGaugeTransform H N gamma b := by
    dsimp [A₁]
    simpa [P, A₀] using
      (periodicHypercubicEven_boundaryRestriction_gaugeTransform
        H N hN beta hbeta gamma A₀)
  have hcoords :
      P.boundaryFiberedAssemble
          (P.boundaryRestriction A₁)
          (P.positiveRestriction A₁)
          (P.negativeRestriction A₁) = A₁ := by
    exact (P.boundaryFiberedCoordinates
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).left_inv A₁
  change
    periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta
        (P.boundaryFiberedAssemble
          (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b)
          (fun _ => 1) (fun _ => 1)) =
      periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta A₀
  calc
    periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta
        (P.boundaryFiberedAssemble
          (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b)
          (fun _ => 1) (fun _ => 1)) =
      periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta
        (P.boundaryFiberedAssemble
          (P.boundaryRestriction A₁) (fun _ => 1) (fun _ => 1)) := by
      rw [hB]
    _ = periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta
        (P.boundaryFiberedAssemble
          (P.boundaryRestriction A₁)
          (P.positiveRestriction A₁)
          (P.negativeRestriction A₁)) :=
      periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight_boundaryFiberedAssemble_independent
        H N beta (P.boundaryRestriction A₁)
        (fun _ => 1) (fun _ => 1)
        (P.positiveRestriction A₁) (P.negativeRestriction A₁)
    _ = periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta A₁ := by
      rw [hcoords]
    _ = periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight H N beta A₀ := by
      simpa [A₁] using
        (periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight_gaugeInvariant
          H N hN beta hbeta gamma A₀)

/-- The boundary Gram coefficient is gauge invariant. -/
theorem periodicHypercubicEvenBoundaryGramCoefficient_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta
        (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b) =
      periodicHypercubicEvenBoundaryGramCoefficient H N hN beta hbeta b := by
  unfold periodicHypercubicEvenBoundaryGramCoefficient
  rw [periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_gaugeInvariant
    H N hN beta hbeta]

/-- The boundary-conditioned completed positive Wilson amplitude is invariant
under simultaneous gauge transformation of the shared boundary and positive
open-half coordinates.

The unused negative half is not assumed gauge stable.  Instead it is replaced
by the actual negative restriction of the transformed full configuration;
negative-half independence then reconstructs that full configuration exactly. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta
        (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b)
        (periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma x) =
      periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H N beta b x := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let A₀ : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
    P.boundaryFiberedAssemble b x (fun _ => 1)
  let A₁ : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform gamma A₀
  have hB :
      P.boundaryRestriction A₁ =
        periodicHypercubicEvenBoundaryGaugeTransform H N gamma b := by
    dsimp [A₁]
    simpa [P, A₀] using
      (periodicHypercubicEven_boundaryRestriction_gaugeTransform
        H N hN beta hbeta gamma A₀)
  have hX :
      P.positiveRestriction A₁ =
        periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma x := by
    dsimp [A₁]
    simpa [P, A₀] using
      (periodicHypercubicEven_positiveRestriction_gaugeTransform
        H N hN beta hbeta gamma A₀)
  have hcoords :
      P.boundaryFiberedAssemble
          (P.boundaryRestriction A₁)
          (P.positiveRestriction A₁)
          (P.negativeRestriction A₁) = A₁ := by
    exact (P.boundaryFiberedCoordinates
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).left_inv A₁
  change
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        (P.boundaryFiberedAssemble
          (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b)
          (periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma x)
          (fun _ => 1)) =
      periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta A₀
  calc
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        (P.boundaryFiberedAssemble
          (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b)
          (periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma x)
          (fun _ => 1)) =
      periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        (P.boundaryFiberedAssemble
          (P.boundaryRestriction A₁)
          (P.positiveRestriction A₁)
          (fun _ => 1)) := by
      rw [hB, hX]
    _ = periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        (P.boundaryFiberedAssemble
          (P.boundaryRestriction A₁)
          (P.positiveRestriction A₁)
          (P.negativeRestriction A₁)) :=
      periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_independent_y
        H N beta
        (P.boundaryRestriction A₁)
        (P.positiveRestriction A₁)
        (fun _ => 1)
        (P.negativeRestriction A₁)
    _ = periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta A₁ := by
      rw [hcoords]
    _ = periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta A₀ := by
      simpa [A₁] using
        (periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_gaugeInvariant
          H N hN beta hbeta gamma A₀)

/-- The completed positive boundary Gram feature is invariant under the
simultaneous actual finite gauge action on its boundary and open-half
coordinates. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature H N hN beta hbeta
        (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b)
        (periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma x) =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature H N hN beta hbeta b x := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  rw [periodicHypercubicEvenBoundaryGramCoefficient_gaugeInvariant
    H N hN beta hbeta]
  rw [periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_gaugeInvariant
    H N hN beta hbeta]

end

end MathlibAnalytic
end MGAP4D
