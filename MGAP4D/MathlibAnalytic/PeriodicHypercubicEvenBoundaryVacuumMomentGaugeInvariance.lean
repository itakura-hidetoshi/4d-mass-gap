import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeatureGaugeInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryBoundaryGaugeHaar
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMoment
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundaryVacuumGaugeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryVacuumGaugeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryVacuumGaugeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryVacuumGaugeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryVacuumGaugeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual boundary gauge action is a measurable equivalence.  Its inverse
is the same coordinate action for the pointwise inverse vertex gauge. -/
def periodicHypercubicEvenBoundaryGaugeMeasurableEquiv
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toEquiv :=
    { toFun := periodicHypercubicEvenBoundaryGaugeTransform H N gamma
      invFun := periodicHypercubicEvenBoundaryGaugeTransform H N (fun v => (gamma v)⁻¹)
      left_inv := by
        intro b
        funext e
        simp [periodicHypercubicEvenBoundaryGaugeTransform, mul_assoc]
      right_inv := by
        intro b
        funext e
        simp [periodicHypercubicEvenBoundaryGaugeTransform, mul_assoc] }
  measurable_toFun :=
    (periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving
      H N gamma).measurable
  measurable_invFun :=
    (periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving
      H N (fun v => (gamma v)⁻¹)).measurable

/-- The actual positive open-half gauge action is a measurable equivalence. -/
def periodicHypercubicEvenPositiveOpenHalfGaugeMeasurableEquiv
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toEquiv :=
    { toFun := periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma
      invFun := periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N (fun v => (gamma v)⁻¹)
      left_inv := by
        intro x
        funext e
        simp [periodicHypercubicEvenPositiveOpenHalfGaugeTransform, mul_assoc]
      right_inv := by
        intro x
        funext e
        simp [periodicHypercubicEvenPositiveOpenHalfGaugeTransform, mul_assoc] }
  measurable_toFun :=
    (periodicHypercubicEvenPositiveOpenHalfGaugeTransform_measurePreserving
      H N gamma).measurable
  measurable_invFun :=
    (periodicHypercubicEvenPositiveOpenHalfGaugeTransform_measurePreserving
      H N (fun v => (gamma v)⁻¹)).measurable

/-- The finite Wilson OS boundary vacuum wavefunction is gauge invariant.

This is derived constructively from simultaneous gauge invariance of the
completed positive Gram feature and measure preservation of the open-half
product Haar law.  No independent vacuum-invariance hypothesis is used. -/
theorem periodicHypercubicEvenBoundaryVacuumMoment_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta
        (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b) =
      periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b := by
  let T := periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ := fun x =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta
      (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b) x
  have hmp : MeasurePreserving T mu mu := by
    simpa [T, mu] using
      (periodicHypercubicEvenPositiveOpenHalfGaugeTransform_measurePreserving
        H N gamma)
  have hme : MeasurableEmbedding T := by
    simpa [T] using
      (periodicHypercubicEvenPositiveOpenHalfGaugeMeasurableEquiv
        H N gamma).measurableEmbedding
  unfold periodicHypercubicEvenBoundaryVacuumMoment
  change (∫ x, f x ∂mu) =
    ∫ x,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x ∂mu
  calc
    (∫ x, f x ∂mu) = ∫ x, f (T x) ∂mu :=
      (hmp.integral_comp hme f).symm
    _ = ∫ x,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaugeInvariant
        H N hN beta hbeta gamma b x

end

end MathlibAnalytic
end MGAP4D
