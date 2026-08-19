import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSHilbertIsometry
import Mathlib.Tactic

/-!
# Factorial OS Hilbert time translation is natural under finite-slot inclusion

The preceding layer extends nonnegative rational-time translation to a contraction between each
fixed-slot OS Hilbert sector and its translated-slot sector.  Independently, the canonical
finite-slot inclusions are already real linear isometries and form a directed system.

This file proves the compatibility needed before descending time translation to the algebraic
direct limit: enlarging the finite slot set and then translating gives exactly the same vector as
translating first and then enlarging the translated slot set.

The proof is entirely same-root and proceeds through the existing layers:

* fixed-slot bounded-continuous observables;
* wrapped OS seminormed carriers;
* separated OS quotients; and
* Hilbert completions by density and continuity.

No direct-limit operator, global rational-time contraction, semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

noncomputable section

/-- Fixed-slot observable time translation commutes exactly with enlarging the finite slot set. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate_inclusion
    (J K : Finset ℚ)
    (hJK : J ⊆ K)
    (t : ℚ)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
        K t
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J K hJK F) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t K)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_mono
          t hJK)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t F) := by
  ext v
  rfl

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Translating finite slots by a nonnegative rational time preserves every slot inclusion. -/
theorem fixedSlotTimeTranslateData_mono
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (t : ℚ) (ht : 0 ≤ t) :
    (P.fixedSlotTimeTranslateData t ht).slots ⊆
      (Q.fixedSlotTimeTranslateData t ht).slots := by
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t P.slots ⊆
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t Q.slots
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate_mono
      t hPQ

/-- Wrapped OS carrier translation is natural under finite-slot inclusion. -/
theorem fixedSlotCarrierTimeTranslate_inclusion
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    (P.fixedSlotTimeTranslateData t ht).fixedSlotCarrierInclusion
        (Q.fixedSlotTimeTranslateData t ht)
        (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)
        (P.fixedSlotCarrierTimeTranslate t ht F) =
      Q.fixedSlotCarrierTimeTranslate t ht
        (P.fixedSlotCarrierInclusion Q hPQ F) := by
  apply FixedSlotCarrier.observable_injective (Q.fixedSlotTimeTranslateData t ht)
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          t P.slots)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
          t Q.slots)
        (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          P.slots t F.observable) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
        Q.slots t
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          P.slots Q.slots hPQ F.observable)
  exact
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate_inclusion
      P.slots Q.slots hPQ t F.observable).symm

/-- Separated OS time translation is natural under finite-slot inclusion. -/
theorem fixedSlotSeparatedTimeTranslate_inclusion
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.Separated) :
    (P.fixedSlotTimeTranslateData t ht).fixedSlotSeparatedInclusion
        (Q.fixedSlotTimeTranslateData t ht)
        (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)
        (P.fixedSlotSeparatedTimeTranslate t ht x) =
      Q.fixedSlotSeparatedTimeTranslate t ht
        (P.fixedSlotSeparatedInclusion Q hPQ x) := by
  obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
  change
    (P.fixedSlotTimeTranslateData t ht).fixedSlotSeparatedInclusion
        (Q.fixedSlotTimeTranslateData t ht)
        (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)
        (P.fixedSlotSeparatedTimeTranslate t ht (P.osClass F)) =
      Q.fixedSlotSeparatedTimeTranslate t ht
        (P.fixedSlotSeparatedInclusion Q hPQ (P.osClass F))
  rw [P.fixedSlotSeparatedTimeTranslate_osClass]
  rw [(P.fixedSlotTimeTranslateData t ht).fixedSlotSeparatedInclusion_osClass]
  rw [P.fixedSlotSeparatedInclusion_osClass]
  rw [Q.fixedSlotSeparatedTimeTranslate_osClass]
  rw [P.fixedSlotCarrierTimeTranslate_inclusion Q hPQ t ht F]

/-- The fixed-slot Hilbert contraction commutes exactly with the canonical isometric inclusion into
any larger finite-slot sector. -/
theorem fixedSlotHilbertTimeTranslateCLM_inclusion
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.Hilbert) :
    (P.fixedSlotTimeTranslateData t ht).fixedSlotHilbertInclusion
        (Q.fixedSlotTimeTranslateData t ht)
        (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)
        (P.fixedSlotHilbertTimeTranslateCLM t ht x) =
      Q.fixedSlotHilbertTimeTranslateCLM t ht
        (P.fixedSlotHilbertInclusion Q hPQ x) := by
  change
    (P.fixedSlotTimeTranslateData t ht).fixedSlotHilbertLinearIsometry
        (Q.fixedSlotTimeTranslateData t ht)
        (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)
        (P.fixedSlotHilbertTimeTranslateCLM t ht x) =
      Q.fixedSlotHilbertTimeTranslateCLM t ht
        (P.fixedSlotHilbertLinearIsometry Q hPQ x)
  induction x using Completion.induction_on with
  | hp =>
      exact
        isClosed_eq
          ((P.fixedSlotTimeTranslateData t ht).fixedSlotHilbertLinearIsometry
              (Q.fixedSlotTimeTranslateData t ht)
              (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)).continuous.comp
            (P.fixedSlotHilbertTimeTranslateCLM t ht).continuous
          ((Q.fixedSlotHilbertTimeTranslateCLM t ht).continuous.comp
            (P.fixedSlotHilbertLinearIsometry Q hPQ).continuous)
  | ih x =>
      rw [P.fixedSlotHilbertTimeTranslateCLM_coe]
      rw [(P.fixedSlotTimeTranslateData t ht).fixedSlotHilbertLinearIsometry_coe]
      rw [P.fixedSlotHilbertLinearIsometry_coe]
      rw [Q.fixedSlotHilbertTimeTranslateCLM_coe]
      rw [P.fixedSlotSeparatedTimeTranslateCLM_apply]
      rw [Q.fixedSlotSeparatedTimeTranslateCLM_apply]
      change
        ((P.fixedSlotTimeTranslateData t ht).fixedSlotSeparatedInclusion
            (Q.fixedSlotTimeTranslateData t ht)
            (P.fixedSlotTimeTranslateData_mono Q hPQ t ht)
            (P.fixedSlotSeparatedTimeTranslate t ht x) :
          Completion (Q.fixedSlotTimeTranslateData t ht).Separated) =
          (Q.fixedSlotSeparatedTimeTranslate t ht
            (P.fixedSlotSeparatedInclusion Q hPQ x) :
          Completion (Q.fixedSlotTimeTranslateData t ht).Separated)
      exact
        congrArg
          (fun y : (Q.fixedSlotTimeTranslateData t ht).Separated =>
            (y : Completion (Q.fixedSlotTimeTranslateData t ht).Separated))
          (P.fixedSlotSeparatedTimeTranslate_inclusion Q hPQ t ht x)

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
