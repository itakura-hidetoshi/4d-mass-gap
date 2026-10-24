import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoCrossingHaarReductionV5_PT3
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryTwoStapleOscillationSeparationBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationHaarReflection
import Mathlib.Tactic

/-!
# P4-Q2-PU — true SU(2) single spatial-link center flip preserves Haar

On the original finite-volume spatial SU(2) slice, multiply ONE link by
the genuine central negative identity z=-I. Every coordinate's normalized
compact Haar is preserved (right multiplication by z on the selected link,
identity elsewhere), hence so is the ORIGINAL complete product Haar.

The integral of any continuous observable that changes sign under this
ONE-LINK center flip is exactly zero. This lemma is the foundational
selection rule for the remaining PT3 two-crossing quartic Ward moment.
Nothing is assumed about the sign of the actual Wilson plaquette trace
or the existence of a free plaquette link here: the geometric and
pointwise sign conditions require separate physical proofs.

No alternative posterior, surrogate spectral measure, Dobrushin,
new axiom, sorry, admit, or assumed physical rank.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PU_spatialLinksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section OriginalSpatialCenterFlip
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "z" => specialUnitaryTwoNegativeIdentity
local notation "μ" => normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- The actual one-link central SU(2) flip acts on the unchanged
spatial lattice configuration; all other link values stay intact. -/
def p4Q2PU_originalSpatialSingleLinkCenterFlip
    (target : Link) (A : Cfg) : Cfg :=
  fun e => if e = target then A e * z else A e

local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H

@[simp] theorem p4Q2PU_originalSingleLinkCenterFlip_at
    (target : Link) (A : Cfg) :
    Flip target A target = A target * z := by
  simp [p4Q2PU_originalSpatialSingleLinkCenterFlip]

theorem p4Q2PU_originalSingleLinkCenterFlip_other
    (target e : Link) (he : e ≠ target) (A : Cfg) :
    Flip target A e = A e := by
  simp [p4Q2PU_originalSpatialSingleLinkCenterFlip, he]

/-- A Haar-probability-preserving operation on each genuine SU(2) link:
right multiplication by -I at the target, identity elsewhere. -/
theorem p4Q2PU_originalCenterFlip_coordinate_measurePreserving
    (target e : Link) :
    MeasurePreserving
      (fun x : G => if e = target then x * z else x)
      μ μ := by
  classical
  by_cases he : e = target
  · have h :=
      normalizedCompactHaar_measurePreserving_mul_left_right
        G (1 : G) z
    simpa [he] using h
  · simpa [he] using (MeasurePreserving.id μ)

/-- The original, unchanged product spatial-Haar probability is preserved
by an ACTUAL one-link SU(2) central flip at any finite spatial H. -/
theorem p4Q2PU_originalCenterFlip_Haar_measurePreserving (target : Link) :
    MeasurePreserving (Flip target) haar haar := by
  refine ⟨?_, ?_⟩
  · unfold p4Q2PU_originalSpatialSingleLinkCenterFlip
    refine measurable_pi_lambda _ ?_
    intro e
    exact
      (p4Q2PU_originalCenterFlip_coordinate_measurePreserving H target e).measurable.comp
        (measurable_pi_apply e)
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    let f : Link → G → G := fun e x => if e = target then x * z else x
    have hf : ∀ e, AEMeasurable (f e) μ :=
      fun e =>
        (p4Q2PU_originalCenterFlip_coordinate_measurePreserving H target e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite (Measure.map (f e) μ) := fun e => by
      rw [(p4Q2PU_originalCenterFlip_coordinate_measurePreserving H target e).map_eq]
      infer_instance
    rw [show Flip target = (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (p4Q2PU_originalCenterFlip_coordinate_measurePreserving H target e).map_eq

/-- Exact Haar oddness cancellation, requiring an independently proven
pointwise sign reversal under the genuine SU(2) center flip.
No physical sign-reversal premise is silently assumed. -/
theorem p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    (target : Link) (f : Cfg → ℝ)
    (hf : Continuous f)
    (hOdd : ∀ A : Cfg, f (Flip target A) = -f A) :
    (∫ A : Cfg, f A ∂haar) = 0 := by
  let T : Cfg → Cfg := Flip target
  have hPres := p4Q2PU_originalCenterFlip_Haar_measurePreserving H target
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf.measurable.aestronglyMeasurable
  have hSymm :
      (∫ A : Cfg, f A ∂haar) =
        (∫ A : Cfg, f (T A) ∂haar) := by
    calc
      (∫ A : Cfg, f A ∂haar) =
        (∫ A : Cfg, f A ∂Measure.map T haar) := by rw [hmap]
      _ = (∫ A : Cfg, f (T A) ∂haar) :=
        MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
  have hNeg :
      (∫ A : Cfg, f (T A) ∂haar) =
        -(∫ A : Cfg, f A ∂haar) := by
    calc
      (∫ A : Cfg, f (T A) ∂haar) =
        (∫ A : Cfg, -f A ∂haar) := by
          apply integral_congr_ae
          filter_upwards with A
          exact hOdd A
      _ = -(∫ A : Cfg, f A ∂haar) := by rw [integral_neg]
  linarith

end OriginalSpatialCenterFlip
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU_originalSingleLinkCenterFlip_at
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU_originalSingleLinkCenterFlip_other
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU_originalCenterFlip_coordinate_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU_originalCenterFlip_Haar_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
