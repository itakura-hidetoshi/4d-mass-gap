import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointKernelSectionDensityFactorization
import Mathlib.Tactic

/-!
# Fixed-left orientation of the ground-state joint kernel-section factor

PR #4741 identifies the genuine normalized joint density with the canonical
continuous fixed-right kernel-section presentation.  For the next
disintegration step we want the first boundary to be the retained boundary and
the second boundary to be sampled from the corresponding kernel section.

This file rewrites the same density in the orientation

  rho_joint(C,A) = lambda^{-1} Omega(C) w(C,A),

where

  w(C,A) = Omega(A) K(A,C).

The only exchange of the two boundary arguments is the already-proved symmetry
of the one-slab Wilson kernel.  No source/target index is exchanged.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointFixedLeftKernelSectionFactorTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointFixedLeftKernelSectionFactorCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointFixedLeftKernelSectionFactorSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointFixedLeftKernelSectionFactorMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointFixedLeftKernelSectionFactorBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointFixedLeftKernelSectionFactorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Continuous normalized joint-density factor with the first boundary retained
and the second boundary sampled from its fixed-right kernel section. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta z.1 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta z.1 z.2

/-- The fixed-right and fixed-left continuous presentations are pointwise
identical.  The proof uses only symmetry of the one-slab Wilson kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor_eq_fixedLeft
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
        H N hN beta hbeta z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
        H N hN beta hbeta z := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
      H N hN beta hbeta z.2 z.1]
  ring

/-- The fixed-left factor is strictly positive pointwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
        H N hN beta hbeta z := by
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor_eq_fixedLeft
      H N hN beta hbeta z]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor_pos
      H N hN beta hbeta z

/-- The genuine historical normalized joint density agrees pair-Haar almost
everywhere with the fixed-left kernel-section factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_fixedLeftKernelSectionFactor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
        H N hN beta hbeta := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuousKernelSectionFactor
      H N hN beta hbeta] with z hz
  rw [hz]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor_eq_fixedLeft
      H N hN beta hbeta z

/-- ENNReal density form of the fixed-left factorization, ready for the
Markov/Tonelli disintegration step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedENNRealWeight_ae_eq_fixedLeftKernelSectionFactor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (fun z =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta z)) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      (fun z =>
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
            H N hN beta hbeta z)) := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_fixedLeftKernelSectionFactor
      H N hN beta hbeta] with z hz
  rw [hz]

end

end MathlibAnalytic
end MGAP4D
