import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNormalizedTraceFinitePolynomialGaugeInvariance
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private theorem boundaryGaugeTransportTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryGaugeTransportNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryGaugeTransportSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private abbrev periodicHypercubicEvenBoundaryGaugeTransportSystem
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :=
  periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2
    boundaryGaugeTransportTwoRankPositive beta hbeta

/-- The actual finite `SU(2)` gauge action restricted to the reflection-fixed
boundary-edge sector.

No new gauge datum is introduced: the same full-lattice vertex gauge
transformation acts on each retained boundary link through its actual source
and target vertices. -/
def periodicHypercubicEvenBoundaryGaugeTransform
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma :
      (periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.GaugeTransformation)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 :=
  fun e =>
    gamma
        ((periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.geometry.edgeSource
          e.1) *
      b e *
      (gamma
        ((periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.geometry.edgeTarget
          e.1))⁻¹

/-- The same actual finite `SU(2)` gauge action restricted to the selected
positive open-half links. -/
def periodicHypercubicEvenPositiveOpenHalfGaugeTransform
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma :
      (periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.GaugeTransformation)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 :=
  fun e =>
    gamma
        ((periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.geometry.edgeSource
          e.1) *
      x e *
      (gamma
        ((periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.geometry.edgeTarget
          e.1))⁻¹

/-- Boundary restriction commutes exactly with the actual full finite gauge
transform.  This is a definitional restriction identity, not a gauge
invariance assumption. -/
theorem periodicHypercubicEven_boundaryRestriction_gaugeTransform
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma :
      (periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.GaugeTransformation)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
        ((periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenBoundaryGaugeTransform H beta hbeta gamma
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A) := by
  funext e
  rfl

/-- Positive open-half restriction commutes exactly with the actual full finite
gauge transform.  This is the kinematic square needed to transport the raw
boundary-integral target through `positiveRestriction`. -/
theorem periodicHypercubicEven_positiveRestriction_gaugeTransform
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma :
      (periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.GaugeTransformation)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction
        ((periodicHypercubicEvenBoundaryGaugeTransportSystem H beta hbeta).base.gaugeTransform
          gamma A) =
      periodicHypercubicEvenPositiveOpenHalfGaugeTransform H beta hbeta gamma
        ((periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) := by
  funext e
  rfl

end

end MathlibAnalytic
end MGAP4D
