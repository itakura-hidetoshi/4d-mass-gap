import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicTranslationInvariance
import Mathlib.MeasureTheory.Group.Measure

/-!
# Product-Haar invariance under physical time reflection

Physical reflection of a positive-link configuration has two independent pieces:

1. reindex links by the involutive geometric edge reflection;
2. invert exactly the time-link coordinates to correct their orientation.

The finite product of normalized compact Haar measures is invariant under both
operations.  Coordinate reindexing is handled by `Measure.pi_map_piCongrLeft`;
coordinatewise orientation correction is handled by `Measure.pi_map_pi` together
with Haar inversion invariance.

This file proves only the reference-measure statement.  Wilson-action and Gibbs
reflection invariance are deliberately left to the next layer.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance configurationHaarReflectionIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance configurationHaarReflectionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance configurationHaarReflectionSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance configurationHaarReflectionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance configurationHaarReflectionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The geometric positive-link reflection bundled as an equivalence. -/
def periodicHypercubicEvenEdgeReflectionEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenEdge H ≃ PeriodicHypercubicEvenEdge H where
  toFun := periodicHypercubicEvenEdgeReflection H
  invFun := periodicHypercubicEvenEdgeReflection H
  left_inv := periodicHypercubicEvenEdgeReflection_involutive H
  right_inv := periodicHypercubicEvenEdgeReflection_involutive H

/-- Pure coordinate reindexing of configurations by geometric edge reflection. -/
noncomputable def periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv
    (H N : ℕ) :
    (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : PeriodicHypercubicEvenEdge H =>
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (periodicHypercubicEvenEdgeReflectionEquiv H)

@[simp]
theorem periodicHypercubicEvenConfigurationEdgeReflection_apply_reflectedEdge
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv H N A
        (periodicHypercubicEvenEdgeReflection H e) =
      A e := by
  simpa [periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv,
    periodicHypercubicEvenEdgeReflectionEquiv] using
    (Equiv.piCongrLeft_apply_apply
      (fun _ : PeriodicHypercubicEvenEdge H =>
        Matrix.specialUnitaryGroup (Fin N) ℂ)
      (periodicHypercubicEvenEdgeReflectionEquiv H) A e)

@[simp]
theorem periodicHypercubicEvenConfigurationEdgeReflection_apply
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv H N A e =
      A (periodicHypercubicEvenEdgeReflection H e) := by
  have h :=
    periodicHypercubicEvenConfigurationEdgeReflection_apply_reflectedEdge
      H N A (periodicHypercubicEvenEdgeReflection H e)
  simpa [periodicHypercubicEvenEdgeReflection_involutive H e] using h

/-- Orientation correction: invert exactly the positive time-link coordinates. -/
def periodicHypercubicEvenConfigurationTimeOrientationCorrection
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ :=
  fun e => if e.2 = 0 then (A e)⁻¹ else A e

/-- The coordinatewise time-link orientation correction is measurable. -/
theorem periodicHypercubicEvenConfigurationTimeOrientationCorrection_measurable
    (H N : ℕ) :
    Measurable
      (periodicHypercubicEvenConfigurationTimeOrientationCorrection H N) := by
  exact measurable_pi_lambda _ (fun e => by
    by_cases htime : e.2 = 0
    · simpa [periodicHypercubicEvenConfigurationTimeOrientationCorrection, htime] using
        (measurable_inv.comp (measurable_pi_apply e))
    · simpa [periodicHypercubicEvenConfigurationTimeOrientationCorrection, htime] using
        (measurable_pi_apply e))

/-- The physical configuration reflection is exactly edge reindexing followed
by the time-link orientation correction. -/
theorem periodicHypercubicEvenConfigurationReflection_eq_orientationCorrection_comp_edgeReflection
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenConfigurationReflection H A =
      periodicHypercubicEvenConfigurationTimeOrientationCorrection H N
        (periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv H N A) := by
  funext e
  by_cases htime : e.2 = 0 <;>
    simp [periodicHypercubicEvenConfigurationReflection,
      periodicHypercubicEvenConfigurationTimeOrientationCorrection, htime]

/-- Product normalized Haar is invariant under pure geometric edge reindexing. -/
theorem periodicHypercubicEvenSpecialUnitary_configurationHaar_map_edgeReflection_eq_self
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
        (periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv H N)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure := by
  unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
  simpa [periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv,
    periodicHypercubicEvenEdgeReflectionEquiv] using
    (Measure.pi_map_piCongrLeft
      (periodicHypercubicEvenEdgeReflectionEquiv H)
      (fun _ : PeriodicHypercubicEvenEdge H =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- Product normalized Haar is invariant under coordinatewise orientation
correction of the time links. -/
theorem periodicHypercubicEvenSpecialUnitary_configurationHaar_map_timeOrientationCorrection_eq_self
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
        (periodicHypercubicEvenConfigurationTimeOrientationCorrection H N)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure := by
  unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
  rw [Measure.pi_map_pi]
  · congr 1
    funext e
    by_cases htime : e.2 = 0
    · simp [periodicHypercubicEvenConfigurationTimeOrientationCorrection, htime]
    · simp [periodicHypercubicEvenConfigurationTimeOrientationCorrection, htime]
  · intro e
    by_cases htime : e.2 = 0
    · simpa [periodicHypercubicEvenConfigurationTimeOrientationCorrection, htime] using
        (measurable_inv.aemeasurable :
          AEMeasurable Inv.inv
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    · simpa [periodicHypercubicEvenConfigurationTimeOrientationCorrection, htime] using
        (measurable_id.aemeasurable :
          AEMeasurable id
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- Product normalized Haar is invariant under the full physical positive-link
configuration reflection. -/
theorem periodicHypercubicEvenSpecialUnitary_configurationHaar_map_reflection_eq_self
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
        (periodicHypercubicEvenConfigurationReflection H)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure := by
  have hreflect :
      periodicHypercubicEvenConfigurationReflection H =
        (periodicHypercubicEvenConfigurationTimeOrientationCorrection H N) ∘
          (periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv H N) := by
    funext A
    exact
      periodicHypercubicEvenConfigurationReflection_eq_orientationCorrection_comp_edgeReflection
        H N A
  rw [hreflect]
  rw [← Measure.map_map
    (periodicHypercubicEvenConfigurationTimeOrientationCorrection_measurable H N)
    (periodicHypercubicEvenConfigurationEdgeReflectionMeasurableEquiv H N).measurable]
  rw [periodicHypercubicEvenSpecialUnitary_configurationHaar_map_edgeReflection_eq_self
    H N hN beta hbeta]
  exact
    periodicHypercubicEvenSpecialUnitary_configurationHaar_map_timeOrientationCorrection_eq_self
      H N hN beta hbeta

end
end MathlibAnalytic
end MGAP4D
