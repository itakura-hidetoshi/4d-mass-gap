import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourLinkThirdProjectionV5_PZ35D9C
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D9D — TRUE four-link SU(2) Schur eigenlaw for original J_p

Complete the fourth actual inverse-oriented physical plaquette-link
Haar contraction from PZ35D9A/B/C, using the PZ35D8 original full
product Haar projector and the ORIGINAL SU(2) Wilson energy.

For every finite even periodic spatial H (including H=0), every
original plaquette p and original spatial boundary B, prove WITHOUT
a premise J_p(B) = chi_p(B)/256. Thus the existing PZ35 conditional
conclusions can be specialized unconditionally inside the ORIGINAL
Wilson model. This does NOT establish nonzero sixth Ward obstruction,
physical rank three, mass gap, or any continuum theorem.

No alternate Haar, finite-subgroup integration, new axiom, sorry,
admit, native_decide or replacement physical posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance p4Q2PZ35D9D_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ35D9D_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ35D9D_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ35D9D_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ35D9D_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ35D9D_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ35D9D_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
local instance p4Q2PZ35D9D_spatialProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalFourEdgeExactSchur
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- FOURTH physical spatial-link Schur contraction, against the true
whole original finite-volume spatial product Haar probability measure.
All group ordering is retained, including both inverse links. -/
theorem p4Q2PZ35D9D_originalOneLinkHaar_fourthEdgeProjection
    (p : Plaq) (B : Cfg) :
    p4Q2PZ35D9C_originalOneLinkResidual H p B =
      -(1 / 4 : ℝ) *
        χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (B (e3 p))⁻¹) := by
  let c : Cfg → G := fun _ =>
    B (e0 p) * B (e1 p) * (B (e2 p))⁻¹
  have hc : Continuous c := continuous_const
  have hcInv : ∀ (a : G) (A : Cfg), c (T (e3 p) a A) = c A := by
    intro a A
    rfl
  have hFInv : ∀ (a : G) (A : Cfg),
      (fun _ : Cfg => (1 : ℝ)) (T (e3 p) a A) = 1 := by
    intro a A
    rfl
  have hCyc (A : Cfg) :
      χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (A (e3 p))⁻¹) =
        χ ((A (e3 p))⁻¹ * c A) := by
    dsimp [c]
    calc
      χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (A (e3 p))⁻¹) =
        χ ((B (e0 p) * B (e1 p) * (B (e2 p))⁻¹) *
            (A (e3 p))⁻¹) := rfl
      _ = χ ((A (e3 p))⁻¹ *
          (B (e0 p) * B (e1 p) * (B (e2 p))⁻¹)) :=
        p4Q2PZ35D5_originalCharacter_mul_comm _ _
  have hOut (A : Cfg) :
      χ ((B (e3 p))⁻¹ * c A) =
        χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (B (e3 p))⁻¹) := by
    dsimp [c]
    calc
      χ ((B (e3 p))⁻¹ * (B (e0 p) * B (e1 p) * (B (e2 p))⁻¹)) =
        χ ((B (e0 p) * B (e1 p) * (B (e2 p))⁻¹) *
            (B (e3 p))⁻¹) :=
          p4Q2PZ35D5_originalCharacter_mul_comm _ _
      _ = χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (B (e3 p))⁻¹) := rfl
  have hProj :=
    p4Q2PZ35D8_originalSpatialHaar_inverseProject
      H (e3 p) (B (e3 p)) c (fun _ : Cfg => (1 : ℝ))
      hc continuous_const hcInv hFInv
  have hConst :
      (∫ A : Cfg, χ ((B (e3 p))⁻¹ * c A) * (1 : ℝ) ∂haar) =
        χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (B (e3 p))⁻¹) := by
    calc
      (∫ A : Cfg, χ ((B (e3 p))⁻¹ * c A) * (1 : ℝ) ∂haar) =
        (∫ _A : Cfg,
          χ (B (e0 p) * B (e1 p) *
            (B (e2 p))⁻¹ * (B (e3 p))⁻¹) ∂haar) := by
          apply integral_congr_ae
          filter_upwards with A
          simpa only [mul_one] using hOut A
      _ = χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (B (e3 p))⁻¹) := by simp
  calc
    p4Q2PZ35D9C_originalOneLinkResidual H p B =
      (∫ A : Cfg,
        (χ ((A (e3 p))⁻¹ * c A) *
          E ((A (e3 p))⁻¹ * B (e3 p))) * (1 : ℝ) ∂haar) := by
        unfold p4Q2PZ35D9C_originalOneLinkResidual
        apply integral_congr_ae
        filter_upwards with A
        rw [hCyc A]
        ring
    _ = -(1 / 4 : ℝ) *
        (∫ A : Cfg, χ ((B (e3 p))⁻¹ * c A) * (1 : ℝ) ∂haar) := hProj
    _ = -(1 / 4 : ℝ) *
        χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (B (e3 p))⁻¹) := by rw [hConst]

/-- The previously OPEN original four-link compact SU(2) Schur
Haar-eigenlaw, now proved pointwise with no premise, for ALL original
finite even spatial periods and all ORIGINAL Wilson boundaries. -/
theorem p4Q2PZ35D9D_originalCanonicalFourHaar_exactSchur
    (p : Plaq) (B : Cfg) :
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
      (1 / 256 : ℝ) * p4Q2PV_originalPlaquetteRealCharacter H p B := by
  have hChar : p4Q2PV_originalPlaquetteRealCharacter H p B =
      χ (B (e0 p) * B (e1 p) *
        (B (e2 p))⁻¹ * (B (e3 p))⁻¹) := by
    rfl
  calc
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
      -(1 / 64 : ℝ) * p4Q2PZ35D9C_originalOneLinkResidual H p B :=
      p4Q2PZ35D9C_originalCanonicalHaar_threeEdgeProjection H p B
    _ = -(1 / 64 : ℝ) *
        (-(1 / 4 : ℝ) *
          χ (B (e0 p) * B (e1 p) *
            (B (e2 p))⁻¹ * (B (e3 p))⁻¹)) := by
      rw [p4Q2PZ35D9D_originalOneLinkHaar_fourthEdgeProjection H p B]
    _ = (1 / 256 : ℝ) * p4Q2PV_originalPlaquetteRealCharacter H p B := by
      rw [hChar]
      ring

/-- Unlike the earlier PZ35 interface, this theorem requires NO
Schur predicate, additional analytic axiom, or assumed eigenvalue. -/
theorem p4Q2PZ35D9D_originalFourHaarSchurEigenlaw :
    p4Q2PZ35_originalFourHaarSchurEigenlaw H (1 / 256 : ℝ) := by
  intro p B
  exact p4Q2PZ35D9D_originalCanonicalFourHaar_exactSchur H p B

/-- Original PZ34 fourth Haar survivor, now exactly AFFINE with the
physical spatial Wilson half-action, without any Schur premise. -/
theorem p4Q2PZ35D9D_originalS4_unconditional (B : Cfg) :
    p4Q2PZ32_originalCoveredFourthSupportSum H B =
      (3 / 32 : ℝ) *
        ((Fintype.card Plaq : ℝ) -
          2 * p4Q2PS_originalHalfSpatialAction H B) :=
  p4Q2PZ35_originalS4_threeOverThirtyTwo_of_SchurQuarter H
    (p4Q2PZ35D9D_originalFourHaarSchurEigenlaw H) B

/-- Original centered physical first/fourth Ward defect, with NO
Schur hypothesis, is exactly linear in the ORIGINAL half-action. -/
theorem p4Q2PZ35D9D_originalD14_unconditional (B : Cfg) :
    p4Q2PZ24_originalCenteredFirstFourthDefect H B =
      -(3 / 32 : ℝ) * p4Q2PS_originalHalfSpatialAction H B :=
  p4Q2PZ35_originalD14_threeOverThirtyTwo_of_SchurQuarter H
    (p4Q2PZ35D9D_originalFourHaarSchurEigenlaw H) B

/-- The exact fourth-supported correction to the original sixth Ward
identity disappears, leaving the original previously proved LOW-sector
baseline; no nonzero physical sixth Ward residual is asserted. -/
theorem p4Q2PZ35D9D_originalSixthWard_lowOnly_unconditional
    (A B C : Cfg) :
    p4Q2PZ8_originalSixthWardObstruction H A B C =
      p4Q2PZ32_originalSixthWardLowBaseline H A B C :=
  p4Q2PZ35_originalSixthWard_eq_lowBaseline_of_SchurQuarter H
    (p4Q2PZ35D9D_originalFourHaarSchurEigenlaw H) A B C

end OriginalFourEdgeExactSchur
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9D_originalOneLinkHaar_fourthEdgeProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9D_originalCanonicalFourHaar_exactSchur
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9D_originalFourHaarSchurEigenlaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9D_originalS4_unconditional
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9D_originalD14_unconditional
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9D_originalSixthWard_lowOnly_unconditional
