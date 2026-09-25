import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateKernelSectionMarkovFubini
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import Mathlib.Tactic

/-!
# Ground-state joint density through fixed-right kernel sections

PR #4740 exposes the continuous fixed-right kernel-section weight

  w(C,A) = Ω_cont(A) K(A,C)

together with its exact section mass and measurable Markov-kernel realization.

This file identifies the genuine normalized two-boundary ground-state density
with the same section weight, keeping the retained right-boundary vacuum factor
explicit:

  ρ_joint(A,C)
    = λ⁻¹ Ω_cont(C) w(C,A)

almost everywhere under pair Haar measure.

The equality is only almost everywhere because the historical joint density is
written using the original L² vacuum representative, whereas the section
weight uses the canonical continuous representative.  No fixed-section norm is
compared pointwise with a global L² norm, and no source/target index exchange is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointKernelSectionDensityFactorizationTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointKernelSectionDensityFactorizationCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointKernelSectionDensityFactorizationSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointKernelSectionDensityFactorizationMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointKernelSectionDensityFactorizationBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointKernelSectionDensityFactorizationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Continuous presentation of the normalized ground-state joint density in
fixed-right kernel-section coordinates.  The pair is ordered as
`(sampledLeft, retainedRight)`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
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
      H N hN beta hbeta z.2 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta z.2 z.1

/-- The continuous kernel-section factor is strictly positive pointwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
        H N hN beta hbeta z := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
  exact mul_pos
    (mul_pos
      (inv_pos.mpr
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
          H N hN beta hbeta))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta z.2))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_pos
      H N hN beta hbeta z.2 z.1)

/-- The historical genuine joint normalized density and the canonical
continuous fixed-right kernel-section factor agree pair-Haar almost everywhere.

Only the already-proved a.e. identification of the continuous vacuum with the
original L² representative is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuousKernelSectionFactor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
        H N hN beta hbeta := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hOmegaFst :
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 z.1) =ᵐ[μ.prod μ]
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta z.1) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
          H N hN beta hbeta).symm
  have hOmegaSnd :
      (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 z.2) =ᵐ[μ.prod μ]
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta z.2) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
          H N hN beta hbeta).symm
  have hPair :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta =ᵐ[μ.prod μ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
          H N hN beta hbeta := by
    filter_upwards [hOmegaFst, hOmegaSnd] with z hFst hSnd
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
    rw [hFst, hSnd]
    ring
  simpa [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using hPair

/-- ENNReal density form of the same a.e. factorization, ready for
`withDensity` and Tonelli/Fubini calculations. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedENNRealWeight_ae_eq_continuousKernelSectionFactor
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
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointContinuousKernelSectionFactor
            H N hN beta hbeta z)) := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuousKernelSectionFactor
      H N hN beta hbeta] with z hz
  rw [hz]

end

end MathlibAnalytic
end MGAP4D
