import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOneSlabSpatialTranslationCovarianceV5_PZ37AAR
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorLocalFactor
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAS — true Wilson Perron-vacuum spatial transport

Exact AAR kernel covariance plus exact AAQ ORIGINAL spatial Haar transport imply
covariance of the true (not proxy) kernel integral on continuous functions.

In particular, the translated canonical strictly positive continuous physical
Wilson Perron representative solves the SAME original one-slab top-eigenvalue
integral equation. It remains strictly positive. These are unconditional
original-model facts, not a claimed posterior invariance.

The remaining Gauss-law physical-subspace and Perron-line descent must be
proved before asserting that the *selected* positive vacuum is fixed by every
spatial translation. Consequently this module does not claim unconditional
AAP response covariance, the 1/3 participation lower bound, uniform
coercivity, a common fine interval, E/F, H1--H4, or continuum mass gap.
Append-only; no existing theorem carrier is changed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAS_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAS_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAS_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAS_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAS_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section TruePositiveVacuumSpatialTransport
variable (H : ℕ)

local notation "Disp" => PeriodicHypercubicEvenSpatialDisplacement H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" =>
  p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative H 2

/-- The ORIGINAL link-coordinate permutation is continuous on the full SU(2)
boundary product space, not merely measurable. -/
theorem p4Q2PZ37AAS_originalSpatialConfigurationTranslation_continuous
    (a : Disp) : Continuous (T a : Cfg → Cfg) := by
  let E := p4Q2PZ37AAP_actualSpatialLinkTranslation H a
  apply continuous_pi
  intro e
  obtain ⟨j, rfl⟩ := E.surjective e
  have he :
      (fun A : Cfg => (T a A) (E j)) = (fun A : Cfg => A j) := by
    funext A
    exact p4Q2PZ37AAQ_configurationTranslation_apply_translatedLink H a A j
  rw [he]
  exact continuous_apply j

/-- Haar integration of ANY integrable scalar function is invariant under
the actual coordinate relabeling from AAQ. No replacement law is used. -/
theorem p4Q2PZ37AAS_originalSpatialHaar_integralTranslation
    (a : Disp) (f : Cfg → ℝ) (hf : Integrable f haar) :
    (∫ A : Cfg, f (T a A) ∂haar) = ∫ A : Cfg, f A ∂haar := by
  have hp := p4Q2PZ37AAQ_originalSpatialHaar_measurePreserving H a
  have hMeas :
      AEStronglyMeasurable f (Measure.map (T a) haar) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  calc
    (∫ A : Cfg, f (T a A) ∂haar) =
        (∫ A : Cfg, f A ∂Measure.map (T a) haar) :=
      (MeasureTheory.integral_map hp.measurable.aemeasurable hMeas).symm
    _ = ∫ A : Cfg, f A ∂haar := by rw [hp.map_eq]

/-- The true original one-slab Wilson kernel integral intertwines spatial
translation on the input with spatial translation of the output boundary.
This is an unconditional integral-operator statement for continuous test
functions and the original full Haar measure. -/
theorem p4Q2PZ37AAS_originalOneSlabIntegral_spatialTranslation
    (a : Disp) (beta : ℝ) (f : Cfg → ℝ) (hf : Continuous f) (B : Cfg) :
    (∫ A : Cfg, f (T a A) * K beta A B ∂haar) =
      ∫ A : Cfg, f A * K beta A (T a B) ∂haar := by
  have hK :
      Continuous (fun A : Cfg => K beta A (T a B)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp₂ continuous_id continuous_const
  have hInt :
      Integrable (fun A : Cfg => f A * K beta A (T a B)) haar :=
    (hf.mul hK).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, f (T a A) * K beta A B ∂haar) =
        (∫ A : Cfg, f (T a A) * K beta (T a A) (T a B) ∂haar) := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AAR_originalCompleteOneSlabKernel_translation H a beta A B]
    _ = ∫ A : Cfg, f A * K beta A (T a B) ∂haar := by
      simpa using
        (p4Q2PZ37AAS_originalSpatialHaar_integralTranslation H a
          (fun A : Cfg => f A * K beta A (T a B)) hInt)

/-- Transported TRUE canonical continuous Perron vacuum solves the SAME
positive original Wilson eigenfunction equation with eigenvalue equal to
the norm of the physical Gauss-law transfer, at every actual boundary. -/
theorem p4Q2PZ37AAS_originalTranslatedPerronVacuum_eigenIntegral
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖ * Omega (by norm_num) beta hbeta (T a B) =
      ∫ A : Cfg,
        Omega (by norm_num) beta hbeta (T a A) * K beta A B ∂haar := by
  have hOmega :
      Continuous (Omega (by norm_num) beta hbeta : Cfg → ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) beta hbeta
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
        Omega (by norm_num) beta hbeta (T a B) =
        ∫ A : Cfg, Omega (by norm_num) beta hbeta A *
          K beta A (T a B) ∂haar :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_continuousVacuum_kernel
        H 2 (by norm_num) beta hbeta (T a B)
    _ = ∫ A : Cfg, Omega (by norm_num) beta hbeta (T a A) *
          K beta A B ∂haar :=
      (p4Q2PZ37AAS_originalOneSlabIntegral_spatialTranslation H a beta
        (Omega (by norm_num) beta hbeta) hOmega B).symm

/-- Spatial reindexing preserves pointwise strict positivity of the
canonical physical Perron representative. -/
theorem p4Q2PZ37AAS_originalTranslatedPerronVacuum_pos
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    0 < Omega (by norm_num) beta hbeta (T a B) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
    H 2 (by norm_num) beta hbeta (T a B)

/-- The translated selected positive Perron representative remains
continuous on the original full spatial configuration carrier. -/
theorem p4Q2PZ37AAS_originalTranslatedPerronVacuum_continuous
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous (fun A : Cfg => Omega (by norm_num) beta hbeta (T a A)) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
    H 2 (by norm_num) beta hbeta).comp
      (p4Q2PZ37AAS_originalSpatialConfigurationTranslation_continuous H a)

end TruePositiveVacuumSpatialTransport
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalSpatialConfigurationTranslation_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalSpatialHaar_integralTranslation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalOneSlabIntegral_spatialTranslation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalTranslatedPerronVacuum_eigenIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalTranslatedPerronVacuum_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAS_originalTranslatedPerronVacuum_continuous
