import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenAllSpatialPlanesZeroMomentum
import MGAP4D.MathlibAnalytic.SpecialUnitaryChargeConjugation
import Mathlib.Tactic

/-!
# Charge-conjugation invariance of the all-spatial zero-momentum plaquette operator

The canonical `SU(N)` charge-conjugation involution is now available as
`C(U) = (U⁻¹)ᵀ`.  This file applies it pointwise to the actual positive-link configuration and proves
that it commutes with every signed boundary incidence, hence with the ordered four-edge plaquette
holonomy.  The already-canonical normalized-real-trace `C`-even theorem then lifts directly to each
translated spatial plaquette, each fixed-plane zero-momentum sum, and finally the equal-weight sum
over all three spatial coordinate planes.

No geometric reindexing is required: charge conjugation changes only the `SU(N)` link value and
leaves every lattice edge and plaquette label fixed.  This is the concrete finite-lattice `C = +`
receipt for the all-spatial zero-momentum Wilson observable.  A final discrete-channel package,
continuum-spin identification, and spectral mass claims remain downstream.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Pointwise charge conjugation of an actual finite periodic `SU(N)` positive-link configuration. -/
def periodicHypercubicEvenConfigurationChargeConjugation
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
  fun e => specialUnitaryChargeConjugation (A e)

@[simp]
theorem periodicHypercubicEvenConfigurationChargeConjugation_apply
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenConfigurationChargeConjugation H N A e =
      specialUnitaryChargeConjugation (A e) :=
  rfl

/-- Pointwise charge conjugation is involutive on the finite configuration carrier. -/
@[simp]
theorem periodicHypercubicEvenConfigurationChargeConjugation_involutive
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenConfigurationChargeConjugation H N
        (periodicHypercubicEvenConfigurationChargeConjugation H N A) = A := by
  funext e
  simp [periodicHypercubicEvenConfigurationChargeConjugation]

/-- Charge conjugation commutes with the value of every signed plaquette-boundary incidence.
The backward case uses compatibility of `C` with group inversion. -/
theorem periodicHypercubicStepValue_configurationChargeConjugation
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (s : PeriodicHypercubicBoundaryStep (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicStepValue
        (periodicHypercubicEvenConfigurationChargeConjugation H N A) s =
      specialUnitaryChargeConjugation (periodicHypercubicStepValue A s) := by
  cases s with
  | mk edge orientation =>
      cases orientation <;>
        simp [periodicHypercubicStepValue,
          periodicHypercubicEvenConfigurationChargeConjugation]

/-- The actual ordered four-edge plaquette holonomy commutes exactly with charge conjugation. -/
theorem periodicHypercubicPlaquetteHolonomy_configurationChargeConjugation
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationChargeConjugation H N A) p =
      specialUnitaryChargeConjugation
        (periodicHypercubicPlaquetteHolonomy A p) := by
  unfold periodicHypercubicPlaquetteHolonomy
  rw [periodicHypercubicStepValue_configurationChargeConjugation,
    periodicHypercubicStepValue_configurationChargeConjugation,
    periodicHypercubicStepValue_configurationChargeConjugation,
    periodicHypercubicStepValue_configurationChargeConjugation]
  simp only [specialUnitaryChargeConjugation_mul]

/-- One translated purely spatial normalized-real-trace plaquette is charge-conjugation even. -/
theorem periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_chargeConjugation
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a
        (periodicHypercubicEvenConfigurationChargeConjugation H N A) =
      periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a A := by
  unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
  rw [periodicHypercubicPlaquetteHolonomy_configurationChargeConjugation]
  exact normalizedSpecialUnitaryRealTrace_chargeConjugation
    (periodicHypercubicPlaquetteHolonomy A
      (periodicHypercubicEvenSpatialPlanePlaquette H a plane))

/-- Every fixed spatial-plane zero-momentum component is charge-conjugation even. -/
theorem periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_chargeConjugationInvariant
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane
        (periodicHypercubicEvenConfigurationChargeConjugation H N A) =
      periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane A := by
  classical
  unfold periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
  apply Finset.sum_congr rfl
  intro a _ha
  exact periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_chargeConjugation
    H N plane a A

/-- The equal-weight all-spatial zero-momentum normalized-real-trace observable has `C = +`. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_chargeConjugationInvariant
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicEvenConfigurationChargeConjugation H N A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace
  apply Finset.sum_congr rfl
  intro plane _hplane
  exact periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_chargeConjugationInvariant
    H N plane A

end

end MathlibAnalytic
end MGAP4D
