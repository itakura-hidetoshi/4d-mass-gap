import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonSingleLinkIntegralInjectiveV5_KV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorCoordinatePolynomialDetectionV5_KM
import Mathlib.Tactic

/-!
# P4-Q2-KW — the two ORIGINAL interacting Wilson posteriors are detected
# by an ACTUAL Wilson single-link kernel section, not merely a polynomial test

KV establishes injectivity of the literal positive-beta Wilson
SU(2) one-link Haar integral transform for every real continuous
signed source. KM and KF prove that the *actual* two interacting
conditional Wilson posterior densities differ by a continuous
nonzero function at every finite volume, right background, link and b>0.

Consequently, the true posterior difference is detected by an
ORIGINAL Wilson kernel section (not a synthetic coordinate polynomial).
More generally, if a real continuous receiver F is nonzero at
the actual SU(2) identity, the original Wilson convolution detects
the product of F and the genuine two-posterior density contrast.
This conditional multiplication result is proved from KF and KV,
not posited as an artificial rank/frame assumption.

We do NOT identify this single-link kernel-section test with the
unresolved physical GI receiver. Establishing the exact joint
square-root/transfer-weight bridge and full finite-volume transfer
nondegeneracy remains necessary for a genuine spatial Wilson
second-context Gauss-law response. No H1-C3, continuum mass-gap
claim, independent-Haar posterior substitution, sorry or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "Delta" => p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous H

/-- TRUE interacting Wilson posterior density difference has a
nonzero Wilson one-link Haar transform section at every positive b,
for every physical link and right background. No replacement
conditional posterior, and no assumed detector rank. -/
theorem p4Q2KW_originalInteractingPosterior_detected_by_trueWilsonSection
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link) :
    ∃ g : Gauge,
      (∫ h : Gauge,
        specialUnitaryWilsonRelativeKernel 2 b g h *
        p4Q2GB_originalWilsonPosteriorLeftDensityContrast
          H b hb.le right e h ∂nu) ≠ 0 := by
  let ψ : C(Gauge, ℝ) := Delta b hb.le right e
  have hψ : ψ ≠ 0 :=
    p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_ne_zero
      H b hb right e
  obtain ⟨g, hg⟩ :=
    p4Q2KV_originalWilsonSingleLinkHaarTransform_exists_nonzero_receiver
      b hb ψ hψ
  refine ⟨g, ?_⟩
  simpa only [ψ,
    p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_apply]
    using hg

/-- Multiplying the ORIGINAL two-Wilson-posterior contrast by any
continuous real receiver that is nonzero at the physical identity
cannot annihilate the resulting signed source. The strict identity
contrast is already theorem-proved in KF. -/
theorem p4Q2KW_originalPosteriorWeightedContinuous_ne_zero
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) (hF : F (1 : Gauge) ≠ 0) :
    Delta b hb.le right e * F ≠ 0 := by
  let δ : C(Gauge, ℝ) := Delta b hb.le right e
  have hδ : 0 < δ (1 : Gauge) := by
    simpa [δ] using
      (p4Q2KF_originalPosteriorDensityContrast_identity_pos H b hb right e)
  intro hz
  have hAt := congrArg (fun f : C(Gauge, ℝ) => f (1 : Gauge)) hz
  have hProduct : δ (1 : Gauge) * F (1 : Gauge) = 0 := by
    simpa only [δ, ContinuousMap.mul_apply, ContinuousMap.zero_apply] using hAt
  exact (mul_ne_zero (ne_of_gt hδ) hF) hProduct

/-- A genuine original Wilson kernel section detects the actual
two-interacting-posterior contrast multiplied by ANY continuous
real receiver that does not vanish at identity. This is an
analytic interface; the ORIGINAL physical spatial Wilson GI
receiver must still be shown to satisfy its hypotheses and
the exact half-density crossing factorization. -/
theorem p4Q2KW_originalWeightedPosterior_detected_by_trueWilsonSection
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) (hF : F (1 : Gauge) ≠ 0) :
    ∃ g : Gauge,
      (∫ h : Gauge,
        specialUnitaryWilsonRelativeKernel 2 b g h *
        (p4Q2GB_originalWilsonPosteriorLeftDensityContrast
          H b hb.le right e h * F h) ∂nu) ≠ 0 := by
  let ψ : C(Gauge, ℝ) := Delta b hb.le right e * F
  have hψ : ψ ≠ 0 :=
    p4Q2KW_originalPosteriorWeightedContinuous_ne_zero H b hb right e F hF
  obtain ⟨g, hg⟩ :=
    p4Q2KV_originalWilsonSingleLinkHaarTransform_exists_nonzero_receiver
      b hb ψ hψ
  refine ⟨g, ?_⟩
  simpa only [ψ, ContinuousMap.mul_apply,
    p4Q2KM_originalInteractingWilsonPosteriorContrastContinuous_apply]
    using hg

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KW_originalInteractingPosterior_detected_by_trueWilsonSection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KW_originalPosteriorWeightedContinuous_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KW_originalWeightedPosterior_detected_by_trueWilsonSection
