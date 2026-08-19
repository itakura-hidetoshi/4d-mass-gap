import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSSeparatedContraction
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Tactic

/-!
# Factorial OS contraction on fixed-slot Hilbert completions

The preceding layer packages nonnegative rational time translation on each separated fixed-slot OS
sector as a continuous linear contraction.  Mathlib's canonical
`ContinuousLinearMap.completion` therefore extends it uniquely to the corresponding Hilbert
completions.

This file records that extension, its exact agreement with the separated map on the dense canonical
embedding, and the inherited contraction estimate

`‖T_t x‖ ≤ ‖x‖`

on the completed fixed-slot Hilbert sectors.  The proof of the completed norm inequality uses
`UniformSpace.Completion.induction_on`: the inequality is closed by continuity of the norm, and it
holds on the dense separated carrier by the already-canonical separated contraction.

No direct-limit operator, global positive-time carrier, semigroup, Hamiltonian, spectral statement,
or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

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

/-- Canonical Hilbert-completion extension of separated rational-time translation. -/
noncomputable def fixedSlotHilbertTimeTranslateCLM
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.Hilbert →L[ℝ] (P.fixedSlotTimeTranslateData t ht).Hilbert := by
  change
    Completion P.Separated →L[ℝ]
      Completion (P.fixedSlotTimeTranslateData t ht).Separated
  exact (P.fixedSlotSeparatedTimeTranslateCLM t ht).completion

/-- On the dense separated carrier, the Hilbert extension is exactly the separated translation. -/
@[simp]
theorem fixedSlotHilbertTimeTranslateCLM_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.Separated) :
    P.fixedSlotHilbertTimeTranslateCLM t ht
        (x : Completion P.Separated) =
      (P.fixedSlotSeparatedTimeTranslateCLM t ht x :
        Completion (P.fixedSlotTimeTranslateData t ht).Separated) := by
  change
    (P.fixedSlotSeparatedTimeTranslateCLM t ht).completion
        (x : Completion P.Separated) =
      (P.fixedSlotSeparatedTimeTranslateCLM t ht x :
        Completion (P.fixedSlotTimeTranslateData t ht).Separated)
  exact ContinuousLinearMap.completion_apply_coe _ _

/-- The completed fixed-slot rational-time translation remains a contraction. -/
theorem fixedSlotHilbertTimeTranslate_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.Hilbert) :
    ‖P.fixedSlotHilbertTimeTranslateCLM t ht x‖ ≤ ‖x‖ := by
  change
    ‖P.fixedSlotHilbertTimeTranslateCLM t ht x‖ ≤ ‖x‖
  induction x using Completion.induction_on with
  | hp =>
      exact
        isClosed_le
          (continuous_norm.comp (P.fixedSlotHilbertTimeTranslateCLM t ht).continuous)
          continuous_norm
  | ih x =>
      rw [P.fixedSlotHilbertTimeTranslateCLM_coe]
      rw [P.fixedSlotSeparatedTimeTranslateCLM_apply]
      simpa [Hilbert, hilbertNormedAddCommGroup] using
        P.fixedSlotSeparatedTimeTranslate_norm_le t ht x

/-- The Hilbert-completion translation has operator norm at most one. -/
theorem fixedSlotHilbertTimeTranslateCLM_norm_le_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    ‖P.fixedSlotHilbertTimeTranslateCLM t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using P.fixedSlotHilbertTimeTranslate_norm_le t ht x

/-- On dense vectors represented by fixed-slot observables, the completed translation is exactly the
Hilbert state represented by the translated observable. -/
@[simp]
theorem fixedSlotHilbertTimeTranslateCLM_hilbertState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotHilbertTimeTranslateCLM t ht (P.hilbertState F) =
      (P.fixedSlotTimeTranslateData t ht).hilbertState
        (P.fixedSlotCarrierTimeTranslate t ht F) := by
  change
    P.fixedSlotHilbertTimeTranslateCLM t ht
        (P.osClass F : Completion P.Separated) =
      ((P.fixedSlotTimeTranslateData t ht).osClass
          (P.fixedSlotCarrierTimeTranslate t ht F) :
        Completion (P.fixedSlotTimeTranslateData t ht).Separated)
  rw [P.fixedSlotHilbertTimeTranslateCLM_coe]
  rw [P.fixedSlotSeparatedTimeTranslateCLM_apply]
  rw [P.fixedSlotSeparatedTimeTranslate_osClass]

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
