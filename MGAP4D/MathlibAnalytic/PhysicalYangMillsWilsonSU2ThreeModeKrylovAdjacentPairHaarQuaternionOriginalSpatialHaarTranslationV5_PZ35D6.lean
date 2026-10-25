import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarOrientationsV5_PZ35D5
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenterFlipHaarV5_PU
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D6 — coordinate SU(2) translations of ORIGINAL spatial product Haar

PZ35D4/D5 prove the exact one-link Wilson Schur contraction. To
transport this into the genuine four-link plaquette moment, this module
generalizes the established PZ25/PU central single-link flip to LEFT
translation by an ARBITRARY genuine SU(2) element on precisely one
original finite spatial link.

Each original normalized SU(2) link Haar is preserved, so the original
full spatial-slice product Haar measure is also preserved. The exact
integral invariance for any continuous real observable follows from
mathlib's Measure.pi_map_pi and integral_map. No finite-subgroup Haar
measure or altered lattice appears.

This is the measure-transport input for the still-open genuine
four-link Schur/Fubini theorem; no J_p=chi_p/256 is asserted yet.
No new axioms, sorry, admit, native_decide or substitute posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G

local instance p4Q2PZ35D6_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance p4Q2PZ35D6_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2

local instance p4Q2PZ35D6_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2

local instance p4Q2PZ35D6_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2

local instance p4Q2PZ35D6_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ35D6_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

local instance p4Q2PZ35D6_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section OriginalSpatialHaarTranslation
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2

/-- Change exactly ONE physical spatial-link variable by genuine
left multiplication in the original SU(2) group. -/
def p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate
    (target : Link) (a : G) (A : Cfg) : Cfg :=
  fun e => if e = target then a * A e else A e

local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H

@[simp] theorem p4Q2PZ35D6_originalLinkTranslate_at
    (target : Link) (a : G) (A : Cfg) :
    T target a A target = a * A target := by
  simp [p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate]

theorem p4Q2PZ35D6_originalLinkTranslate_other
    (target e : Link) (a : G) (he : e ≠ target) (A : Cfg) :
    T target a A e = A e := by
  simp [p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate, he]

/-- The true normalized Haar law on each SU(2) spatial link is
preserved, for ANY left multiplier in SU(2). -/
theorem p4Q2PZ35D6_originalLinkTranslate_coordinate_measurePreserving
    (target e : Link) (a : G) :
    MeasurePreserving (fun x : G => if e = target then a * x else x) μ μ := by
  classical
  by_cases he : e = target
  · have h :=
      normalizedCompactHaar_measurePreserving_mul_left_right G a (1 : G)
    simpa [he] using h
  · simpa [he] using (MeasurePreserving.id μ)

/-- The ORIGINAL unmodified finite spatial-slice product Haar
measure is preserved under left translation at any one original link. -/
theorem p4Q2PZ35D6_originalSpatialHaar_oneLinkMeasurePreserving
    (target : Link) (a : G) :
    MeasurePreserving (T target a) haar haar := by
  refine ⟨?_, ?_⟩
  · unfold p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate
    refine measurable_pi_lambda _ ?_
    intro e
    exact
      (p4Q2PZ35D6_originalLinkTranslate_coordinate_measurePreserving
        H target e a).measurable.comp (measurable_pi_apply e)
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    let f : Link → G → G := fun e x => if e = target then a * x else x
    have hf : ∀ e, AEMeasurable (f e) μ :=
      fun e =>
        (p4Q2PZ35D6_originalLinkTranslate_coordinate_measurePreserving
          H target e a).measurable.aemeasurable
    letI : ∀ e, SigmaFinite (Measure.map (f e) μ) := fun e => by
      rw [(p4Q2PZ35D6_originalLinkTranslate_coordinate_measurePreserving
        H target e a).map_eq]
      infer_instance
    rw [show T target a = (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (p4Q2PZ35D6_originalLinkTranslate_coordinate_measurePreserving
        H target e a).map_eq

/-- An arbitrary continuous observable's integral over the SAME
original full spatial Haar law is invariant under any one-link
genuine SU(2) left translation. This is a finite product-Haar theorem,
not a four-point counting-Haar approximation. -/
theorem p4Q2PZ35D6_originalSpatialHaar_oneLinkIntegralLeftTranslate
    (target : Link) (a : G) (f : Cfg → ℝ) (hf : Continuous f) :
    (∫ A : Cfg, f (T target a A) ∂haar) =
      (∫ A : Cfg, f A ∂haar) := by
  have hPres :=
    p4Q2PZ35D6_originalSpatialHaar_oneLinkMeasurePreserving H target a
  have hMeas :
      AEStronglyMeasurable f (Measure.map (T target a) haar) := by
    rw [hPres.map_eq]
    exact hf.measurable.aestronglyMeasurable
  calc
    (∫ A : Cfg, f (T target a A) ∂haar) =
        (∫ A : Cfg, f A ∂Measure.map (T target a) haar) :=
      (MeasureTheory.integral_map hPres.measurable.aemeasurable hMeas).symm
    _ = (∫ A : Cfg, f A ∂haar) := by
      rw [hPres.map_eq]

end OriginalSpatialHaarTranslation
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D6_originalLinkTranslate_at
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D6_originalLinkTranslate_other
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D6_originalLinkTranslate_coordinate_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D6_originalSpatialHaar_oneLinkMeasurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D6_originalSpatialHaar_oneLinkIntegralLeftTranslate
