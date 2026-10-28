import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOneLinkPosteriorSpatialTransportV5_PZ37AAT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonFiberRieszDerivativeV5_JH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAU — original GI joint and source-integral translation

AAS established pointwise spatial translation invariance of the ORIGINAL
positive physical Perron vacuum. AAR established the genuine interacting
one-slab SU(2) Wilson kernel symmetry; AAT transported BOTH original
conditional one-link Wilson densities and the FX contrast variance.

This layer combines them without replacing the original model. We prove:
* the original full physical Wilson joint continuous probability weight
  and its positive square root are invariant under original spatial shifts;
* the genuine two-interacting-posterior density contrast is invariant;
* the ORIGINAL Wilson kernel Haar integral of any translation-invariant
  continuous source is invariant at the translated right boundary.

Those are the precise independent inputs of JH's real original Wilson
physical Gauss-law receiver. The next dependent theorem carrier will use
JH to prove GI's signed expectation-gap covariance, then use AAQ/AAP to
remove the original conditional nonconcentration assumption.

No new axiom/sorry/admit/native_decide, substitute posterior, volume-uniform
coercivity, common positive fine interval, endpoint E/F, H1–H4, or continuum
mass-gap assertion. Strictly append-only.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAU_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAU_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAU_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAU_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAU_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AAU_probability : IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G
private noncomputable instance p4Q2PZ37AAU_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AAU_spatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section OriginalGIJointCovariance
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Disp" => PeriodicHypercubicEvenSpatialDisplacement H
local notation "Pair" => Cfg × Cfg
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" =>
  p4Q2PZ37AAQ_originalSpatialConfigurationTranslation H
local notation "TP" =>
  p4Q2PZ37AAQ_originalSpatialPairTranslation H
local notation "L" =>
  p4Q2PZ37AAP_actualSpatialLinkTranslation H
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2

/-- The ORIGINAL full Wilson joint weight, with both genuine physical
positive Perron vacuum factors and the actual one-slab Wilson kernel,
is pointwise invariant under simultaneous spatial translation. -/
theorem p4Q2PZ37AAU_originalJointWeight_translation
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta) (z : Pair) :
    continuousJointWeight H 2 (by norm_num) beta hbeta (TP a z) =
      continuousJointWeight H 2 (by norm_num) beta hbeta z := by
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta (T a z.1) *
      K beta (T a z.1) (T a z.2) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta (T a z.2)) =
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta z.1 *
      K beta z.1 z.2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta z.2)
  rw [p4Q2PZ37AAS_originalPositivePerronVacuum_spatialTranslation H a beta hbeta z.1,
    p4Q2PZ37AAR_originalCompleteOneSlabKernel_translation H a beta z.1 z.2,
    p4Q2PZ37AAS_originalPositivePerronVacuum_spatialTranslation H a beta hbeta z.2]

/-- Spatial covariance of the SAME strictly positive physical Wilson joint
square-root density (not an unrelated square-root law). -/
theorem p4Q2PZ37AAU_originalJointSqrtDensity_translation
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta) (z : Pair) :
    continuousJointSqrtDensity H 2 (by norm_num) beta hbeta (TP a z) =
      continuousJointSqrtDensity H 2 (by norm_num) beta hbeta z := by
  unfold continuousJointSqrtDensity
  rw [p4Q2PZ37AAU_originalJointWeight_translation H a beta hbeta z]

/-- The exact ORIGINAL contrast of the two fully normalized interacting
conditional Wilson posterior densities transports pointwise. -/
theorem p4Q2PZ37AAU_originalPosteriorDensityContrast_translation
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : Cfg) (e : Link) (g : G) :
    p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H beta hbeta (T a A) (L a e) g =
      p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H beta hbeta A e g := by
  unfold p4Q2GB_originalWilsonPosteriorLeftDensityContrast
  rw [p4Q2PZ37AAT_originalIdentityLeftConditionalDensity_translation H a beta hbeta A e g,
    p4Q2PZ37AAT_originalPiRotatedLeftConditionalDensity_translation H a beta hbeta A e g]

/-- Original Wilson Haar transfer of any continuous, spatially invariant
Gauss-law source representative is covariant. Uses only the ACTUAL one-slab
kernel and original Haar law, without a function-space proxy. -/
theorem p4Q2PZ37AAU_originalKernelIntegral_invariantSource
    (a : Disp) (beta : ℝ)
    (f : C(Cfg, ℝ)) (hf : ∀ A : Cfg, f (T a A) = f A)
    (B : Cfg) :
    (∫ A : Cfg, K beta A (T a B) * f A ∂haar) =
      ∫ A : Cfg, K beta A B * f A ∂haar := by
  calc
    (∫ A : Cfg, K beta A (T a B) * f A ∂haar) =
        ∫ A : Cfg, f A * K beta A (T a B) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = ∫ A : Cfg, f (T a A) * K beta A B ∂haar :=
      (p4Q2PZ37AAS_originalOneSlabIntegral_spatialTranslation
        H a beta f f.continuous B).symm
    _ = ∫ A : Cfg, K beta A B * f A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [hf A]
      ring

end OriginalGIJointCovariance
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalJointWeight_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalJointSqrtDensity_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalPosteriorDensityContrast_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalKernelIntegral_invariantSource
