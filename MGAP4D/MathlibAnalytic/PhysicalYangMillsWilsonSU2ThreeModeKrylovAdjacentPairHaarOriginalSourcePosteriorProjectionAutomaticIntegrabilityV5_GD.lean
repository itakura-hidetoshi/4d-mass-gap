import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalIntegratedSourcePosteriorContrastProjectionV5_GC
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberCrossRatio
import Mathlib.Tactic

/-!
# P4-Q2-GD: eliminate GC's projection integrability hypothesis

This is the next genuine original-Wilson source-dependent step:
1. prove continuous right-link replacement JOINTLY in (right,g);
2. prove original complete Wilson kernel times physical vacuum jointly continuous;
3. deduce joint measurability of the TRUE normalized posterior density by
   integrating the complete weight to obtain its physical partition function;
4. deduce measurable genuine GA posterior contrast and GB physical signed
   source projection coefficients;
5. dominate the squared source coefficient by FG's integrable physical
   conditional RMS, using the strictly positive GA variance floor.
   Consequently the GC conditional integrability hypothesis is discharged
   for all finite volumes, links and physical sources whenever beta>0.

No independent Haar conditional posterior, synthetic physical frame floor,
scale-uniform summability, H1-C3 closure or continuum mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2GD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

private theorem p4Q2GD_originalWilsonUpdateRight_joint_continuous
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun t :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      Function.update t.1 e t.2) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i = e
  · subst i
    simpa using
      (continuous_snd : Continuous (fun t :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          Matrix.specialUnitaryGroup (Fin 2) ℂ => t.2))
  · simpa [hi] using
      ((continuous_apply i).comp
        (continuous_fst : Continuous (fun t :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            Matrix.specialUnitaryGroup (Fin 2) ℂ => t.1)))

/-- The EXACT original Wilson one-link complete physical weight is
jointly continuous in its physical right background and candidate SU2
link. The genuine positive continuous physical vacuum is retained. -/
theorem p4Q2GD_originalWilsonCompleteFiberWeight_joint_continuous
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun t :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H 2 (by norm_num) beta hbeta left t.1 e t.2) := by
  let Update := fun t :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      Matrix.specialUnitaryGroup (Fin 2) ℂ =>
    Function.update t.1 e t.2
  have hUpdate : Continuous Update :=
    p4Q2GD_originalWilsonUpdateRight_joint_continuous H e
  have hK : Continuous (fun t =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta left (Update t)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp₂ continuous_const hUpdate
  have hV : Continuous (fun t =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta (Update t)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) beta hbeta).comp hUpdate
  simpa only [Update,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      hK.mul hV

/-- Genuine normalized one-link posterior density is jointly MEASURABLE
in its right physical environment and inserted SU2 link, because its
complete ORIGINAL Wilson physical weight is jointly continuous and its
Haar normalizer is the actual integral of that SAME weight. -/
theorem p4Q2GD_originalWilsonConditionalDensity_joint_measurable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable (fun t :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta left t.1 e t.2) := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let W := fun t :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      Matrix.specialUnitaryGroup (Fin 2) ℂ =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
      H 2 (by norm_num) beta hbeta left t.1 e t.2
  have hW : Continuous W :=
    p4Q2GD_originalWilsonCompleteFiberWeight_joint_continuous H beta hbeta left e
  have hZ : Measurable (fun right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      ∫ g, W (right,g) ∂μ) :=
    hW.stronglyMeasurable.integral_prod_right.measurable
  have hRatio : Measurable (fun t :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      W t / (∫ g, W (t.1,g) ∂μ)) :=
    hW.measurable.div (hZ.comp measurable_fst)
  convert hRatio using 1
  funext t
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_eq_groundStateNormalizedDensity,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_eq]

/-- Joint measurability of the exact density difference of GA, with
physical left identity versus pi rotation at the selected left link. -/
theorem p4Q2GD_originalWilsonPosteriorContrast_joint_measurable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable (fun t :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H beta hbeta t.1 e t.2) := by
  simpa only [p4Q2GB_originalWilsonPosteriorLeftDensityContrast] using
    ((p4Q2GD_originalWilsonConditionalDensity_joint_measurable H beta hbeta
      (originalWilsonExplicitIdentityBoundary H) e).sub
    (p4Q2GD_originalWilsonConditionalDensity_joint_measurable H beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) e))

/-- The GA squared posterior density-row distance is measurable as
a function of the actual right physical boundary context. -/
theorem p4Q2GD_originalWilsonPosteriorContrastHaarSq_measurable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable (fun right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta hbeta right e) := by
  let D := fun t :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      Matrix.specialUnitaryGroup (Fin 2) ℂ =>
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast H beta hbeta t.1 e t.2
  have hD : Measurable D :=
    p4Q2GD_originalWilsonPosteriorContrast_joint_measurable H beta hbeta e
  have hIntegral : Measurable (fun right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
    ∫ g, (D (right,g)) ^ 2
      ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
    by
      simpa only [pow_two] using
        ((hD.mul hD).stronglyMeasurable.integral_prod_right.measurable)
  simpa only [D, p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq,
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast] using hIntegral

/-- The genuine source-dependent GB projection coefficient is
measurable in the original pair-Haar physical context, retaining
the full signed FF receiver response and GA's real normalized posterior. -/
theorem p4Q2GD_originalPhysicalSourceContrastProjection_measurable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H beta hbeta f e) := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) beta hbeta f e
  let D := fun t :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      Matrix.specialUnitaryGroup (Fin 2) ℂ =>
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast H beta hbeta t.1 e t.2
  have hD : Measurable D :=
    p4Q2GD_originalWilsonPosteriorContrast_joint_measurable H beta hbeta e
  have hNumJoint : Measurable (fun t :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      B t * D (t.1.2,t.2)) := by
    exact B.continuous.measurable.mul
      (hD.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hNum : Measurable (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      ∫ g, B (z,g) * D (z.2,g) ∂μ) :=
    hNumJoint.stronglyMeasurable.integral_prod_right.measurable
  have hDen : Measurable (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta hbeta z.2 e) :=
    (p4Q2GD_originalWilsonPosteriorContrastHaarSq_measurable
      H beta hbeta e).comp measurable_snd
  change Measurable (fun z =>
    (∫ g, B (z,g) * D (z.2,g) ∂μ) /
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta hbeta z.2 e)
  exact hNum.div hDen

/-- At beta>0, the true GA variance floor bounds the squared actual
source-projection coefficient by the already integrable genuine
FG response RMS. It follows that all GC projection integrals exist
WITHOUT any additional hypotheses on physical sources or volume. -/
theorem p4Q2GD_originalPhysicalSourceProjection_sq_integrable
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Integrable
      (fun z => (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
        H beta (le_of_lt hbeta) f e z) ^ 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let A := fun z =>
    (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H beta (le_of_lt hbeta) f e z) ^ 2
  let M := p4Q2FG_originalWilsonRelativeResponseConditionalSquare
    H 2 (by norm_num) beta (le_of_lt hbeta) f e
  let c : ℝ := Real.exp (-16 * beta) *
    (Real.exp (-32 * beta) *
      (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))
  have hc : 0 < c :=
    mul_pos (Real.exp_pos _) (mul_pos (Real.exp_pos _)
      (mul_pos (pow_pos hbeta 2)
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos))
  have hAMeas : AEStronglyMeasurable A μ := by
    have hAlpha :
        Measurable (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
          H beta (le_of_lt hbeta) f e) :=
      p4Q2GD_originalPhysicalSourceContrastProjection_measurable
        H beta (le_of_lt hbeta) f e
    simpa only [A, pow_two] using (hAlpha.mul hAlpha).aestronglyMeasurable
  have hMInt : Integrable M μ :=
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_pairHaar_integrable
      H 2 (by norm_num) beta (le_of_lt hbeta) f e
  have hBoundInt : Integrable (fun z => M z / c) μ :=
    hMInt.div_const c
  change Integrable A μ
  apply Integrable.mono' hBoundInt hAMeas
  filter_upwards with z
  have hPoint : c * A z ≤ M z := by
    simpa only [c, A, M, mul_assoc] using
      (p4Q2GB_originalWilsonConditionalSourceRMS_projection_floor
        H beta hbeta f e z)
  have hBound : A z ≤ M z / c := by
    apply (le_div_iff₀ hc).2
    calc
      A z * c = c * A z := mul_comm _ _
      _ ≤ M z := hPoint
  have hMnonneg : 0 ≤ M z :=
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare_nonneg
      H 2 (by norm_num) beta (le_of_lt hbeta) f e z
  have hNonneg : 0 ≤ M z / c := div_nonneg hMnonneg hc.le
  change ‖A z‖ ≤ M z / c
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hBound

/-- GC's ORIGINAL Wilson finite-patch physical energy lower bound now
holds for EVERY physical gauge-invariant input and finite link patch,
with NO integrability assumption. The projected mass may still vanish. -/
theorem p4Q2GD_originalPhysicalPatchEnergy_ge_sourceProjection
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
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
  exact p4Q2GC_originalPhysicalPatchEnergy_ge_sourceProjection
    H beta hbeta f S
    (fun e _he => p4Q2GD_originalPhysicalSourceProjection_sq_integrable
      H beta hbeta f e)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GD_originalWilsonCompleteFiberWeight_joint_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GD_originalWilsonConditionalDensity_joint_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GD_originalWilsonPosteriorContrast_joint_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GD_originalWilsonPosteriorContrastHaarSq_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GD_originalPhysicalSourceContrastProjection_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GD_originalPhysicalSourceProjection_sq_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GD_originalPhysicalPatchEnergy_ge_sourceProjection
