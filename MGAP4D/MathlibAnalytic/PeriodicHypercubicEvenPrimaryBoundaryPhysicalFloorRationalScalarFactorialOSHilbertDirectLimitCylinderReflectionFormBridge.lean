import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonalSmoothedAlgebraicCore
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumOS
import Mathlib.Tactic

/-!
# Same-root cylinder states and continuum reflection forms

The canonical factorial-Wilson / primary-scalar OS route already contains both sides needed for a
model-dependent quantitative estimate:

* literal bounded-continuous fixed-slot cylinder observables and their finite-Wilson reflection
  forms, converging weakly to the same Prokhorov continuum law; and
* the completed algebraic direct-limit Hilbert carrier with its rational OS semigroup.

This file exposes their exact identification on literal fixed-slot cylinder states.  A wrapped
fixed-slot carrier is packaged as the corresponding positive cylinder, its OS quadratic form is
identified definitionally with the continuum path `realReflectionForm`, and the canonical chain

`fixed-slot carrier -> fixed-slot Hilbert -> algebraic direct limit -> completion`

is proved to preserve that value exactly.  Rational time translation is then threaded through the
same chain.  Consequently the direct-limit double-time self-correlation of a literal cylinder state
is exactly the continuum reflection form of its half-time translated cylinder.  The existing
Prokhorov weak convergence theorem finally identifies that same number as the limit of the actual
finite Wilson reflection forms along the selected subsequence.

This is only an exact carrier/weak-limit bridge.  It introduces no non-collapse assumption, no
positive variance floor, no uniform decay or coercive constant, and no claim that the canonical
same-root infrared mass is strictly positive.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory UniformSpace
open scoped InnerProductSpace

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The positive bounded-continuous path cylinder canonically represented by a wrapped fixed-slot
OS carrier. -/
noncomputable def fixedSlotCarrierPositiveCylinder
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) :
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder where
  slots := P.slots
  slots_nonneg := P.slots_nonneg
  observable := F.observable

@[simp]
theorem fixedSlotCarrierPositiveCylinder_slots
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) :
    (P.fixedSlotCarrierPositiveCylinder F).slots = P.slots :=
  rfl

@[simp]
theorem fixedSlotCarrierPositiveCylinder_observable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) :
    (P.fixedSlotCarrierPositiveCylinder F).observable = F.observable :=
  rfl

/-- The diagonal fixed-slot OS bilinear form is literally the intrinsic continuum path reflection
form of the corresponding positive cylinder. -/
theorem fixedSlotOSBilinForm_self_eq_carrierPositiveCylinder_realReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) :
    L.fixedSlotOSBilinForm H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        P.slots F.observable F.observable =
      (P.fixedSlotCarrierPositiveCylinder F).realReflectionForm
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
  rw [L.fixedSlotOSBilinForm_apply]
  simp [
    fixedSlotCarrierPositiveCylinder,
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionForm,
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.realReflectionIntegrand_apply,
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.pathObservable_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply,
    mul_comm]

/-- Along the actual Prokhorov subsequence, finite Wilson reflection forms of a literal fixed-slot
carrier converge to exactly the continuum reflection form used by the OS Hilbert reconstruction. -/
theorem fixedSlotCarrierPositiveCylinder_reflectionForm_tendsto_continuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) :
    Tendsto
      (fun n =>
        (P.fixedSlotCarrierPositiveCylinder F).realReflectionForm
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            (fun k =>
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence k))
            n : Measure (ℚ → ℝ)))
      atTop
      (nhds
        ((P.fixedSlotCarrierPositiveCylinder F).realReflectionForm
          (L.continuumMeasure : Measure (ℚ → ℝ)))) := by
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_reflectionForm_tendsto_of_weakConvergence
      (fun n =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          (fun k =>
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (L.subsequence k))
          n)
      L.continuumMeasure
      (L.weakConvergence_reindexed H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
      (P.fixedSlotCarrierPositiveCylinder F)

/-- A literal fixed-slot cylinder state inserted canonically all the way into the completed
algebraic direct-limit Hilbert carrier. -/
noncomputable def fixedSlotHilbertDirectLimitCarrierState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitCompletion :=
  ((P.fixedSlotHilbertAlgebraicLinearIsometry J
      ((P.fixedSlotDataOfIndex J).hilbertState F) :
      P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertDirectLimitCompletion)

/-- The completed direct-limit norm/inner product of a literal cylinder state is exactly its same
continuum path reflection form. -/
theorem fixedSlotHilbertDirectLimitCarrierState_inner_self_eq_realReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitCarrierState J F)
        (P.fixedSlotHilbertDirectLimitCarrierState J F) =
      ((P.fixedSlotDataOfIndex J).fixedSlotCarrierPositiveCylinder F).realReflectionForm
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
  change
    inner ℝ
        ((P.fixedSlotHilbertAlgebraicLinearIsometry J
            ((P.fixedSlotDataOfIndex J).hilbertState F) :
          P.fixedSlotHilbertAlgebraicDirectLimit) :
          P.fixedSlotHilbertDirectLimitCompletion)
        ((P.fixedSlotHilbertAlgebraicLinearIsometry J
            ((P.fixedSlotDataOfIndex J).hilbertState F) :
          P.fixedSlotHilbertAlgebraicDirectLimit) :
          P.fixedSlotHilbertDirectLimitCompletion) = _
  rw [Completion.inner_coe]
  rw [P.fixedSlotHilbertAlgebraicLinearIsometry_inner]
  rw [(P.fixedSlotDataOfIndex J).inner_hilbertState_hilbertState]
  rw [(P.fixedSlotDataOfIndex J).inner_eq_fixedSlotOSBilinForm]
  exact
    (P.fixedSlotDataOfIndex J).fixedSlotOSBilinForm_self_eq_carrierPositiveCylinder_realReflectionForm F

/-- Equivalently, the same completed direct-limit self-inner-product is the weak limit of the
actual finite Wilson reflection forms along the selected Prokhorov subsequence. -/
theorem fixedSlotHilbertDirectLimitCarrierState_reflectionForm_tendsto_inner_self
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n =>
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierPositiveCylinder F).realReflectionForm
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            (fun k =>
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence k))
            n : Measure (ℚ → ℝ)))
      atTop
      (nhds
        (inner ℝ
          (P.fixedSlotHilbertDirectLimitCarrierState J F)
          (P.fixedSlotHilbertDirectLimitCarrierState J F))) := by
  rw [P.fixedSlotHilbertDirectLimitCarrierState_inner_self_eq_realReflectionForm J F]
  exact
    (P.fixedSlotDataOfIndex J).fixedSlotCarrierPositiveCylinder_reflectionForm_tendsto_continuum F

/-- Rational time translation of a literal completed direct-limit cylinder state is exactly the
literal cylinder state obtained by translating the fixed-slot observable first. -/
@[simp]
theorem fixedSlotHilbertDirectLimitTimeTranslateCLM_carrierState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (t : ℚ) (ht : 0 ≤ t)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht
        (P.fixedSlotHilbertDirectLimitCarrierState J F) =
      P.fixedSlotHilbertDirectLimitCarrierState
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate t ht F) := by
  unfold fixedSlotHilbertDirectLimitCarrierState
  rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_coe]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslateCLM_apply]
  rw [P.fixedSlotHilbertAlgebraicLinearIsometry_apply]
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  rw [(P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM_hilbertState]
  rfl

/-- The direct-limit double-time self-correlation of a literal cylinder state is exactly the
continuum reflection form of the half-time translated cylinder. -/
theorem fixedSlotHilbertDirectLimitCarrierState_correlation_double_eq_realReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitCarrierState J F)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (h + h) (add_nonneg hh hh)
          (P.fixedSlotHilbertDirectLimitCarrierState J F)) =
      ((P.fixedSlotDataOfIndex
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierPositiveCylinder
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)).realReflectionForm
          (L.continuumMeasure : Measure (ℚ → ℝ)) := by
  rw [← P.fixedSlotHilbertDirectLimitTimeTranslate_inner_factorization h hh
    (P.fixedSlotHilbertDirectLimitCarrierState J F)
    (P.fixedSlotHilbertDirectLimitCarrierState J F)]
  rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_carrierState J h hh F]
  exact
    P.fixedSlotHilbertDirectLimitCarrierState_inner_self_eq_realReflectionForm
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)
      ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)

/-- Therefore the direct-limit double-time self-correlation is itself the weak limit of finite
Wilson reflection forms of the half-time translated literal cylinder.  This is the exact insertion
point for a future scale-uniform model-derived quantitative inequality. -/
theorem fixedSlotHilbertDirectLimitCarrierState_translatedReflectionForm_tendsto_correlation_double
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n =>
        ((P.fixedSlotDataOfIndex
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierPositiveCylinder
          ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)).realReflectionForm
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
              (H (L.subsequence n)) N hN
              (beta (L.subsequence n)) (hbeta (L.subsequence n))
              (fun k =>
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                  (L.subsequence k))
              n : Measure (ℚ → ℝ)))
      atTop
      (nhds
        (inner ℝ
          (P.fixedSlotHilbertDirectLimitCarrierState J F)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh)
            (P.fixedSlotHilbertDirectLimitCarrierState J F)))) := by
  rw [P.fixedSlotHilbertDirectLimitCarrierState_correlation_double_eq_realReflectionForm J h hh F]
  exact
    (P.fixedSlotDataOfIndex
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierPositiveCylinder_reflectionForm_tendsto_continuum
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
