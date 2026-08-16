import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryBoundaryGaugeTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableGram
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonGaugeInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

private theorem periodicHypercubicEvenBoundaryGaugeCoordinate_measurePreserving
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (e : (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge) :
    MeasurePreserving
      (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        gamma (periodicHypercubicEdgeSource
            (PeriodicHypercubicEvenSideLength H) e.1) *
          u *
          (gamma (periodicHypercubicEdgeTarget
            (PeriodicHypercubicEvenSideLength H) e.1))⁻¹)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  normalizedCompactHaar_measurePreserving_mul_left_right
    (Matrix.specialUnitaryGroup (Fin N) ℂ)
    (gamma (periodicHypercubicEdgeSource
      (PeriodicHypercubicEvenSideLength H) e.1))
    (gamma (periodicHypercubicEdgeTarget
      (PeriodicHypercubicEvenSideLength H) e.1))⁻¹

private theorem periodicHypercubicEvenPositiveOpenHalfGaugeCoordinate_measurePreserving
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (e : (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge) :
    MeasurePreserving
      (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        gamma (periodicHypercubicEdgeSource
            (PeriodicHypercubicEvenSideLength H) e.1) *
          u *
          (gamma (periodicHypercubicEdgeTarget
            (PeriodicHypercubicEvenSideLength H) e.1))⁻¹)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  normalizedCompactHaar_measurePreserving_mul_left_right
    (Matrix.specialUnitaryGroup (Fin N) ℂ)
    (gamma (periodicHypercubicEdgeSource
      (PeriodicHypercubicEvenSideLength H) e.1))
    (gamma (periodicHypercubicEdgeTarget
      (PeriodicHypercubicEvenSideLength H) e.1))⁻¹

/-- The actual vertex gauge action on reflection-fixed boundary links preserves
the product normalized Haar probability law. -/
theorem periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasurePreserving
      (periodicHypercubicEvenBoundaryGaugeTransform H N gamma)
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  refine ⟨?_, ?_⟩
  · unfold periodicHypercubicEvenBoundaryGaugeTransform
    fun_prop
  · unfold periodicHypercubicEvenBoundaryHaarMeasure
    unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
    let f : (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge →
        Matrix.specialUnitaryGroup (Fin N) ℂ →
          Matrix.specialUnitaryGroup (Fin N) ℂ := fun e u =>
      gamma (periodicHypercubicEdgeSource
          (PeriodicHypercubicEvenSideLength H) e.1) *
        u *
        (gamma (periodicHypercubicEdgeTarget
          (PeriodicHypercubicEvenSideLength H) e.1))⁻¹
    have hf : ∀ e,
        AEMeasurable (f e)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
      fun e =>
        (periodicHypercubicEvenBoundaryGaugeCoordinate_measurePreserving
          H N gamma e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite
        ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).map
          (f e)) := fun e => by
      rw [(periodicHypercubicEvenBoundaryGaugeCoordinate_measurePreserving
        H N gamma e).map_eq]
      infer_instance
    rw [show periodicHypercubicEvenBoundaryGaugeTransform H N gamma =
      (fun b e => f e (b e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (periodicHypercubicEvenBoundaryGaugeCoordinate_measurePreserving
        H N gamma e).map_eq

/-- The actual vertex gauge action on the selected positive open half preserves
its product normalized Haar probability law. -/
theorem periodicHypercubicEvenPositiveOpenHalfGaugeTransform_measurePreserving
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasurePreserving
      (periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  refine ⟨?_, ?_⟩
  · unfold periodicHypercubicEvenPositiveOpenHalfGaugeTransform
    fun_prop
  · unfold periodicHypercubicEvenOpenHalfHaarMeasure
    unfold FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure
    let f : (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge →
        Matrix.specialUnitaryGroup (Fin N) ℂ →
          Matrix.specialUnitaryGroup (Fin N) ℂ := fun e u =>
      gamma (periodicHypercubicEdgeSource
          (PeriodicHypercubicEvenSideLength H) e.1) *
        u *
        (gamma (periodicHypercubicEdgeTarget
          (PeriodicHypercubicEvenSideLength H) e.1))⁻¹
    have hf : ∀ e,
        AEMeasurable (f e)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
      fun e =>
        (periodicHypercubicEvenPositiveOpenHalfGaugeCoordinate_measurePreserving
          H N gamma e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite
        ((normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)).map
          (f e)) := fun e => by
      rw [(periodicHypercubicEvenPositiveOpenHalfGaugeCoordinate_measurePreserving
        H N gamma e).map_eq]
      infer_instance
    rw [show periodicHypercubicEvenPositiveOpenHalfGaugeTransform H N gamma =
      (fun x e => f e (x e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (periodicHypercubicEvenPositiveOpenHalfGaugeCoordinate_measurePreserving
        H N gamma e).map_eq

end

end MathlibAnalytic
end MGAP4D
