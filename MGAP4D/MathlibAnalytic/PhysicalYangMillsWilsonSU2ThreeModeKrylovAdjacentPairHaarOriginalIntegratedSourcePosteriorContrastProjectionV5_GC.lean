import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedSourcePosteriorContrastProjectionV5_GB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSSpatialSupportV5_FH
import Mathlib.Tactic

/-!
# P4-Q2-GC: integrated true-Wilson source/contrast projection floor

GB proves pointwise in every PHYSICAL pair-Haar context that the original
signed FF/FG source response conditional RMS dominates the source overlap
with GA's genuine normalized-Wilson posterior contrast.

This file integrates that exact inequality over the original pair-Haar
outer reference (without altering the true Wilson INNER posterior), then
sums an arbitrary finite physical-link patch, preserving the original
transfer norm normalization:

  D_S(f) >= (1/2)||T_beta||^(-2) beta^2 exp(-48 beta) V_SU2
                    * sum_{e in S} integral_pairHaar alpha(e,f,z)^2 dz.

The single outstanding local integrability of alpha^2 is an EXPLICIT
hypothesis. It is NOT disguised as an established theorem. This is a
conditional analytic certificate for the genuinely source-dependent
physical Wilson energies. Later work must discharge integrability,
establish whether a physical source frame lower bound exists, and
control scale/volume normalization. It does NOT prove H1-C3 or any
continuum Yang--Mills spectral gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Pair-Haar integrated squared actual signed physical-source overlap
with the two-row TRUE Wilson posterior contrast at a selected link.
This is a nonnegative diagnostic when its integrability is certified. -/
noncomputable def p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ z, (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H beta hbeta f e z) ^ 2
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- Spatially resolved sum of the same actual source projection
coefficients across a finite set of original physical links. -/
noncomputable def p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  S.sum (p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
    H beta hbeta f)

/-- Pointwise GB inequality integrated over the authentic OUTER pair-Haar
reference; the INNER conditional probability is the original Wilson law.
No artificial per-link lower frame coefficient is assumed. -/
theorem p4Q2GC_originalWilsonLinkRMS_ge_integratedSourceProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (hAlpha : Integrable
      (fun z => (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z) ^ 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) :
    (Real.exp (-16 * beta) *
      (Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
        H beta (le_of_lt hbeta) f e ≤
      p4Q2FH_originalWilsonConditionalRMSLinkMean
        H 2 (by norm_num) beta (le_of_lt hbeta) f e := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let A := fun z => (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
    H beta (le_of_lt hbeta) f e z) ^ 2
  let M := p4Q2FG_originalWilsonRelativeResponseConditionalSquare
    H 2 (by norm_num) beta (le_of_lt hbeta) f e
  let k : ℝ := Real.exp (-16 * beta) *
    (Real.exp (-32 * beta) *
      (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))
  have hA : Integrable A μ := hAlpha
  have hM : Integrable M μ :=
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_pairHaar_integrable
      H 2 (by norm_num) beta (le_of_lt hbeta) f e
  have hPoint (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
      k * A z ≤ M z := by
    simpa only [k, A, M, mul_assoc] using
      (p4Q2GB_originalWilsonConditionalSourceRMS_projection_floor
        H beta hbeta f e z)
  change k * (∫ z, A z ∂μ) ≤ ∫ z, M z ∂μ
  calc
    k * (∫ z, A z ∂μ) =
        ∫ z, k * A z ∂μ := by rw [integral_const_mul]
    _ ≤ ∫ z, M z ∂μ := by
      apply integral_mono (hA.const_mul _) hM
      intro z
      exact hPoint z

/-- Exact transfer-norm-rescaled ORIGINAL physical link defect receives
the source projection lower certificate from genuine Wilson RMS. -/
theorem p4Q2GC_originalPhysicalLinkDefect_ge_sourceProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (hAlpha : Integrable
      (fun z => (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z) ^ 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta) *
        (Real.exp (-32 * beta) *
          (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
          H beta (le_of_lt hbeta) f e) ≤
      p4Q2FD_originalPhysicalLinkDefect
        H 2 (by norm_num) beta (le_of_lt hbeta) f e := by
  have hBound :=
    p4Q2GC_originalWilsonLinkRMS_ge_integratedSourceProjection
      H beta hbeta f e hAlpha
  have hScale : 0 ≤
      (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  calc
    (1 / 2 : ℝ) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
        ((Real.exp (-16 * beta) *
          (Real.exp (-32 * beta) *
            (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
          p4Q2GC_originalWilsonSourcePosteriorContrastProjectedLinkMean
            H beta (le_of_lt hbeta) f e) ≤
      (1 / 2 : ℝ) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
        p4Q2FH_originalWilsonConditionalRMSLinkMean
          H 2 (by norm_num) beta (le_of_lt hbeta) f e :=
      mul_le_mul_of_nonneg_left hBound hScale
    _ = p4Q2FD_originalPhysicalLinkDefect
          H 2 (by norm_num) beta (le_of_lt hbeta) f e := by
      simpa only [p4Q2FH_originalWilsonConditionalRMSLinkMean] using
        (p4Q2FG_originalPhysicalLinkDefect_eq_half_pairHaarConditionalRMS
          H 2 (by norm_num) beta (le_of_lt hbeta) f e).symm

/-- Finite physical-link patch: no unproved large-volume or summability
hypothesis, just the exact sum of source-overlap lower certificates. -/
theorem p4Q2GC_originalWilsonSpatialRMSMass_ge_sourceProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (hAlpha : ∀ e ∈ S, Integrable
      (fun z => (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z) ^ 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) :
    (Real.exp (-16 * beta) *
      (Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
      p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
        H beta (le_of_lt hbeta) f S ≤
      p4Q2FH_originalWilsonSpatialRMSMass
        H 2 (by norm_num) beta (le_of_lt hbeta) f S := by
  unfold p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
    p4Q2FH_originalWilsonSpatialRMSMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun e he =>
    p4Q2GC_originalWilsonLinkRMS_ge_integratedSourceProjection
      H beta hbeta f e (hAlpha e he))

/-- The original finite-patch physical Wilson energy (including the
mandatory squared inverse-transfer normalization) dominates the finite
pair-Haar source-overlap certificate for the SAME genuine physical f. -/
theorem p4Q2GC_originalPhysicalPatchEnergy_ge_sourceProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (hAlpha : ∀ e ∈ S, Integrable
      (fun z => (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z) ^ 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) :
    (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
      ((Real.exp (-16 * beta) *
        (Real.exp (-32 * beta) *
          (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
        p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
          H beta (le_of_lt hbeta) f S) ≤
      p4Q2FD_originalPhysicalRestrictedLinkEnergy
        H 2 (by norm_num) beta (le_of_lt hbeta) f S := by
  have hBound :=
    p4Q2GC_originalWilsonSpatialRMSMass_ge_sourceProjection
      H beta hbeta f S hAlpha
  have hScale : 0 ≤
      (1 / 2 : ℝ) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  calc
    (1 / 2 : ℝ) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
        ((Real.exp (-16 * beta) *
          (Real.exp (-32 * beta) *
            (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))) *
          p4Q2GC_originalWilsonSourcePosteriorContrastProjectedSpatialMass
            H beta (le_of_lt hbeta) f S) ≤
      (1 / 2 : ℝ) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta (le_of_lt hbeta)‖⁻¹) ^ 2 *
        p4Q2FH_originalWilsonSpatialRMSMass
          H 2 (by norm_num) beta (le_of_lt hbeta) f S :=
      mul_le_mul_of_nonneg_left hBound hScale
    _ = p4Q2FD_originalPhysicalRestrictedLinkEnergy
          H 2 (by norm_num) beta (le_of_lt hbeta) f S :=
      (p4Q2FH_originalPhysicalPatchEnergy_eq_spatialRMSMass
        H 2 (by norm_num) beta (le_of_lt hbeta) f S).symm

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GC_originalWilsonLinkRMS_ge_integratedSourceProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GC_originalPhysicalLinkDefect_ge_sourceProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GC_originalWilsonSpatialRMSMass_ge_sourceProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GC_originalPhysicalPatchEnergy_ge_sourceProjection
