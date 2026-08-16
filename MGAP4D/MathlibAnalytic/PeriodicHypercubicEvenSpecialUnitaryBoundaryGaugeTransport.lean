import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNormalizedTraceFinitePolynomialGaugeInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedHaarFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance boundaryGaugeTransportNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

/-- The actual finite `SU(N)` gauge action restricted to the reflection-fixed
boundary-edge sector.

The action is kinematic: it depends only on the actual periodic source and
target vertices, not on `beta` or on any additional physical hypothesis. -/
def periodicHypercubicEvenBoundaryGaugeTransform
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e =>
    gamma (periodicHypercubicEdgeSource
        (PeriodicHypercubicEvenSideLength H) e.1) *
      b e *
      (gamma (periodicHypercubicEdgeTarget
        (PeriodicHypercubicEvenSideLength H) e.1))⁻¹

/-- The same actual finite `SU(N)` gauge action restricted to the selected
positive open-half links. -/
def periodicHypercubicEvenPositiveOpenHalfGaugeTransform
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e =>
    gamma (periodicHypercubicEdgeSource
        (PeriodicHypercubicEvenSideLength H) e.1) *
      x e *
      (gamma (periodicHypercubicEdgeTarget
        (PeriodicHypercubicEvenSideLength H) e.1))⁻¹

/-- Boundary restriction commutes exactly with the actual full finite gauge
transform.  This is a definitional restriction identity, not a gauge
invariance assumption. -/
theorem periodicHypercubicEven_boundaryRestriction_gaugeTransform
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenBoundaryGaugeTransform H N gamma
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A) := by
  funext e
  rfl

/-- Positive open-half restriction commutes exactly with the actual full finite
gauge transform.  This is the kinematic square needed to transport the raw
boundary-integral target through `positiveRestriction`. -/
theorem periodicHypercubicEven_positiveRestriction_gaugeTransform
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma
        ((periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) := by
  funext e
  rfl

end

end MathlibAnalytic
end MGAP4D
