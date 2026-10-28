import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredGIJointTransportV5_PZ37AAU
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalCenteredGLRayleighLimitV5_PZ37ZW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAU2 — original centered Gauss-law GI receiver covariance

Connect AAU's true SU(2) posterior density contrast and physical joint
sqrt-density transport to JH's ORIGINAL Wilson fiber-moment Riesz detector.
Transport the true Wilson source kernel integral using the original Haar
measure, without an artificial receiver or a substitute posterior.

The canonical continuous source is exactly the original center-subtracted
spatial Wilson action with the SAME physical Haar inner-product coefficient.
Its Haar-L² class is the unchanged physical centered Gauss-law vector from
PZ37ZW. Pointwise spatial symmetry therefore descends through JH's actual
physical/GI equality into the two genuine interacting Wilson conditional
posterior expectation-gap response.

This establishes the previously missing ORIGINAL GI numerator covariance;
AAU3 can now combine it with AAT FX covariance and AAQ/AAP nonconcentration.

No new axioms, sorry/admit/native_decide, Haar-posterior substitution,
volume-uniform coercivity, common fine interval, E/F, H1--H4, or continuum
Yang-Mills mass gap. Append-only.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAU2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAU2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAU2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAU2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAU2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AAU2_probability : IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G
private noncomputable instance p4Q2PZ37AAU2_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AAU2_spatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section TrueCenteredGITranslation
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Disp" => PeriodicHypercubicEvenSpatialDisplacement H
local notation "Pair" => Cfg × Cfg
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
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
local notation "s" =>
  continuousJointSqrtDensity H 2
local notation "delta" =>
  p4Q2GB_originalWilsonPosteriorLeftDensityContrast H

/-- The SAME genuine JH original Wilson Haar-L² fiber moment is invariant
under simultaneous translation of the genuine link and two boundaries,
when evaluated on any original spatially invariant continuous source. -/
theorem p4Q2PZ37AAU_originalFiberMoment_invariantSource
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : C(Cfg, ℝ)) (hf : ∀ A : Cfg, f (T a A) = f A)
    (e : Link) (z : Pair) :
    p4Q2JH_originalFiberMomentCLM H beta hbeta (L a e) (TP a z)
        (ContinuousMap.toLp 2 haar ℝ f) =
      p4Q2JH_originalFiberMomentCLM H beta hbeta e z
        (ContinuousMap.toLp 2 haar ℝ f) := by
  rw [p4Q2JH_originalFiberMomentCLM_eq_iteratedIntegral
      H beta hbeta (L a e) (TP a z) f,
      p4Q2JH_originalFiberMomentCLM_eq_iteratedIntegral
      H beta hbeta e z f]
  apply integral_congr_ae
  filter_upwards with g
  let Bu : Cfg := Function.update z.2 e g
  have hUpdate :
      Function.update (T a z.2) (L a e) g = T a Bu := by
    exact (p4Q2PZ37AAQ_configurationTranslation_update H a z.2 e g).symm
  have hTransfer :
      (∫ A : Cfg,
        K beta A (Function.update (T a z.2) (L a e) g) * f A ∂haar) =
      (∫ A : Cfg, K beta A Bu * f A ∂haar) := by
    rw [hUpdate]
    exact p4Q2PZ37AAU_originalKernelIntegral_invariantSource
      H a beta f hf Bu
  have hs :
      s (by norm_num) beta hbeta
        (T a z.1, Function.update (T a z.2) (L a e) g) =
      s (by norm_num) beta hbeta (z.1, Bu) := by
    rw [hUpdate]
    exact p4Q2PZ37AAU_originalJointSqrtDensity_translation
      H a beta hbeta (z.1, Bu)
  have hd :
      delta beta hbeta (T a z.2) (L a e) g =
        delta beta hbeta z.2 e g :=
    p4Q2PZ37AAU_originalPosteriorDensityContrast_translation
      H a beta hbeta z.2 e g
  change
    ((∫ A : Cfg, K beta A (Function.update (T a z.2) (L a e) g) *
        f A ∂haar) /
        s (by norm_num) beta hbeta
          (T a z.1, Function.update (T a z.2) (L a e) g)) *
      delta beta hbeta (T a z.2) (L a e) g =
    ((∫ A : Cfg, K beta A Bu * f A ∂haar) /
        s (by norm_num) beta hbeta (z.1, Bu)) *
      delta beta hbeta z.2 e g
  rw [hTransfer, hs, hd]

/-- The ORIGINAL (not newly chosen) real JH GI Riesz detector inherits
the same spatial equivariance on every genuinely invariant continuous
source, including the physical spatial Wilson action and constant one. -/
theorem p4Q2PZ37AAU_originalGIResponseCLM_invariantSource
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : C(Cfg, ℝ)) (hf : ∀ A : Cfg, f (T a A) = f A)
    (e : Link) (z : Pair) :
    p4Q2JH_originalGIResponseCLM H beta hbeta (L a e) (TP a z)
        (ContinuousMap.toLp 2 haar ℝ f) =
      p4Q2JH_originalGIResponseCLM H beta hbeta e z
        (ContinuousMap.toLp 2 haar ℝ f) := by
  change
    (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ *
        s (by norm_num) beta hbeta (TP a z)) *
      p4Q2JH_originalFiberMomentCLM H beta hbeta (L a e) (TP a z)
        (ContinuousMap.toLp 2 haar ℝ f) =
    (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ *
        s (by norm_num) beta hbeta z) *
      p4Q2JH_originalFiberMomentCLM H beta hbeta e z
        (ContinuousMap.toLp 2 haar ℝ f)
  rw [p4Q2PZ37AAU_originalJointSqrtDensity_translation H a beta hbeta z,
    p4Q2PZ37AAU_originalFiberMoment_invariantSource
      H a beta hbeta f hf e z]

/-- The canonical REAL source is literally one-half of the original
spatial Wilson action minus its original physical Haar average. -/
noncomputable def p4Q2PZ37AAU_originalCenteredWilsonContinuous : C(Cfg, ℝ) :=
  (1 / 2 : ℝ) •
    (p4Q2JI_actualSpatialWilsonContinuous H -
      (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) •
          (1 : C(Cfg, ℝ)))

/-- The actual centered Wilson continuous source is strictly spatially
translation invariant, with no change to its original centering scalar. -/
theorem p4Q2PZ37AAU_originalCenteredWilsonContinuous_translation
    (a : Disp) (A : Cfg) :
    p4Q2PZ37AAU_originalCenteredWilsonContinuous H (T a A) =
      p4Q2PZ37AAU_originalCenteredWilsonContinuous H A := by
  change (1 / 2 : ℝ) *
      (p4Q2JI_actualSpatialWilsonContinuous H (T a A) -
        (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) * 1) =
    (1 / 2 : ℝ) *
      (p4Q2JI_actualSpatialWilsonContinuous H A -
        (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) * 1)
  rw [p4Q2PZ37AAR_originalPhysicalSpatialWilsonSource_translation H a A]

/-- The ORIGINAL centered physical Gauss-law Hilbert vector (the ZW
strong fine tangent) is EXACTLY this same continuous centered source
as a Haar-L² class. -/
theorem p4Q2PZ37AAU_originalCenteredWilsonPhysical_eq_continuousLp :
    ((p4Q2PZ37ZW_originalCenteredPhysicalDirection H : Phys) :
        Lp ℝ 2 haar) =
      ContinuousMap.toLp 2 haar ℝ
        (p4Q2PZ37AAU_originalCenteredWilsonContinuous H) := by
  unfold p4Q2PZ37ZW_originalCenteredPhysicalDirection
    p4Q2PZ37AAU_originalCenteredWilsonContinuous
  rw [Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_smul,
    p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H,
    map_smul, map_sub, map_smul]

/-- UNCONDITIONAL pointwise covariance of the original centered
physical Gauss-law GI signed TWO-interacting-Wilson-posterior
expectation gap. This is the precise AAP numerator obstruction.
It comes from the SAME original JH real Riesz receiver. -/
theorem p4Q2PZ37AAU_originalCenteredPhysicalGIGap_translation
    (a : Disp) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Link) (z : Pair) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta hbeta (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
        (L a e) (TP a z) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta hbeta (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
        e z := by
  let f : C(Cfg, ℝ) := p4Q2PZ37AAU_originalCenteredWilsonContinuous H
  let u : Phys := p4Q2PZ37ZW_originalCenteredPhysicalDirection H
  have hLp : (u : Lp ℝ 2 haar) = ContinuousMap.toLp 2 haar ℝ f :=
    p4Q2PZ37AAU_originalCenteredWilsonPhysical_eq_continuousLp H
  have hAE : (fun A : Cfg => (u : Lp ℝ 2 haar) A) =ᵐ[haar] f := by
    rw [hLp]
    exact f.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hInv : ∀ A : Cfg, f (T a A) = f A :=
    p4Q2PZ37AAU_originalCenteredWilsonContinuous_translation H a
  have hLeft :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
      H beta hbeta (L a e) (TP a z) u f hAE
  have hRight :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
      H beta hbeta e z u f hAE
  rw [hLp] at hLeft hRight
  calc
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta hbeta u (L a e) (TP a z) =
      p4Q2JH_originalGIResponseCLM H beta hbeta (L a e) (TP a z)
        (ContinuousMap.toLp 2 haar ℝ f) := hLeft.symm
    _ = p4Q2JH_originalGIResponseCLM H beta hbeta e z
        (ContinuousMap.toLp 2 haar ℝ f) :=
      p4Q2PZ37AAU_originalGIResponseCLM_invariantSource
        H a beta hbeta f hInv e z
    _ = p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta hbeta u e z := hRight

end TrueCenteredGITranslation
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalFiberMoment_invariantSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalGIResponseCLM_invariantSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalCenteredWilsonContinuous_translation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalCenteredWilsonPhysical_eq_continuousLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalCenteredPhysicalGIGap_translation
