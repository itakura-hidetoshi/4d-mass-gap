import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSourceUpdateDiagonalKernelSectionL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFullKernelSectionBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkConditionalIntegral
import Mathlib.Tactic

/-!
# Diagonal section conditional-variance energy

PR #4748 constructs, for one outer boundary `C`, the canonical local-mean
section vector in the literal fixed-right kernel-section space

  L2(kappa_C).

The remote one-link fluctuation representing that vector is

  q_C(A) = F(C,A) - P_link F_C(A),

where `P_link` is the actual one-link heat-bath / conditional-expectation
projection inside the same section law.

This file proves the exact conditional-energy identity

  int_A [ int_D q_C(D)^2 K_link(A,dD) ] kappa_C(dA)
    = ||r_C^KS||^2.

The proof uses only:

1. exact identification of the remote reference probability with the
   fixed-right kernel-section law;
2. the existing one-link conditional-integral stationarity theorem on the
   reference law;
3. the canonical `toLp` representative from PR #4748.

No comparison constant and no source/target exchange is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointDiagonalSectionConditionalVarianceTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointDiagonalSectionConditionalVarianceCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointDiagonalSectionConditionalVarianceSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointDiagonalSectionConditionalVarianceMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointDiagonalSectionConditionalVarianceBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointDiagonalSectionConditionalVarianceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The section fluctuation square, averaged once through the actual one-link
heat-bath kernel and then over the section law, is exactly the squared norm of
the canonical diagonal local-mean section vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuter_conditionalSquareEnergy_eq_localMeanKernelSectionL2_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫ A,
      (∫ D,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta C link distinguishedSource link
          (C distinguishedSource) (C link)
          (fun X => F (C, X)) D) ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta C link distinguishedSource link
          (C distinguishedSource) (C link) A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound‖ ^ 2 := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
      H N hN beta hbeta C link distinguishedSource link
      (C distinguishedSource) (C link)
      (fun X => F (C, X))
  let qsq : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A => q A ^ 2
  let r :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      F hF bound hbound

  have hRetained :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq
      H N C link distinguishedSource

  have hReference :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
      H N hN beta hbeta C hRefNe hNoShare
      (C distinguishedSource) (C link)
  rw [hRetained] at hReference

  have hq :
      MemLp q 2 μ := by
    simpa [q, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterKernelSectionFluctuation_memLp_two
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound

  have hqsq :
      Integrable qsq μ := by
    simpa only [qsq, Pi.pow_apply] using hq.integrable_sq

  have hqsqReference :
      Integrable qsq
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C link distinguishedSource
          (C distinguishedSource) (C link)) := by
    rw [hReference]
    exact hqsq

  have hstationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_setIntegral_integral_eq
      H N hN beta hbeta C link distinguishedSource link
      (C distinguishedSource) (C link)
      qsq hqsqReference Set.univ MeasurableSet.univ

  have hstationary' :
      (∫ A,
        (∫ D, qsq D
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
            H N hN beta hbeta C link distinguishedSource link
            (C distinguishedSource) (C link) A)
        ∂μ) =
        ∫ A, qsq A ∂μ := by
    simpa [μ, hReference] using hstationary

  have hRep :
      (fun A => r A) =ᵐ[μ] q := by
    simpa [r, q, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterKernelSectionFluctuation_memLp_two
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound).coeFn_toLp

  calc
    (∫ A,
      (∫ D,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta C link distinguishedSource link
          (C distinguishedSource) (C link)
          (fun X => F (C, X)) D) ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta C link distinguishedSource link
          (C distinguishedSource) (C link) A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
        ∫ A, qsq A ∂μ := by
      simpa [q, qsq, μ] using hstationary'
    _ = ∫ A, ‖r A‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hRep] with A hA
      rw [hA]
      simp [qsq, Real.norm_eq_abs, sq_abs]
    _ = ‖r‖ ^ 2 := by
      exact (realL2_norm_sq_eq_integral_norm_sq r).symm
    _ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound‖ ^ 2 := by
      rfl

end

end MathlibAnalytic
end MGAP4D
