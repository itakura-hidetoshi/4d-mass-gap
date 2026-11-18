import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NativeTopFirstSlopeV5_PZ37ANU
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteHaarCharacterBridgeV5_PZ37AMB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANV — native first Wilson Haar action moment evaluation

This is the additive research leaf for the ORIGINAL SU(2) one-slab first
Haar-action moment defined in ANU.  The starting step transfers the exact
SU(2) fundamental-character first and second Haar moments to the unchanged
physical time-zero spatial-slice measure, without replacing it with the
reflection-fixed OS boundary or postulating independent plaquettes.

The intended next steps use the actual finite spatial plaquette sum and
temporal crossing action to compute ANU's original first Haar moment.
Unfinished steps are not presented as certified Lean theorems.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "nu" => normalizedCompactHaar G
local notation "Chi" =>
  GroundStatePosteriorJoint.p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37ANV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANV_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The genuinely physical time-zero PRIMARY spatial plaquette holonomy
has exactly normalized compact SU(2) Haar as its pushforward law.
This is the original four-link spatial-slice Haar, not an assumed OS
measure or a new independent group variable. -/
theorem p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport
    (H : ℕ) (f : G → ℝ) (hf : AEStronglyMeasurable f nu) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      f (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      (∫ g : G, f g ∂nu) := by
  let phi := p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  have hmp : MeasurePreserving phi mu nu :=
    p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2
  have hfmap : AEStronglyMeasurable f (Measure.map phi mu) := by
    rw [hmp.map_eq]
    exact hf
  calc
    _ = ∫ g : G, f g ∂Measure.map phi mu :=
      (MeasureTheory.integral_map hmp.measurable.aemeasurable hfmap).symm
    _ = ∫ g : G, f g ∂nu := by rw [hmp.map_eq]

/-- First moment of the ACTUAL primary spatial plaquette's real normalized
fundamental SU(2) character is exactly zero at every finite physical H. -/
theorem p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero (H : ℕ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  have hf : AEStronglyMeasurable Chi nu :=
    GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.measurable.aestronglyMeasurable
  calc
    _ = ∫ g : G, Chi g ∂nu :=
      p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport H Chi hf
    _ = 0 :=
      GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero

/-- Genuine native four-link SU(2) spatial-slice character has exact
Haar variance 1/4, not an assumed unit variance. -/
theorem p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarSecondMoment (H : ℕ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      (Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) ^ 2
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      (1 / 4 : ℝ) := by
  have hf : AEStronglyMeasurable (fun g : G => (Chi g) ^ 2) nu :=
    (GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.pow 2).measurable.aestronglyMeasurable
  calc
    _ = ∫ g : G, (Chi g) ^ 2 ∂nu :=
      p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport
        H (fun g : G => (Chi g) ^ 2) hf
    _ = (1 / 4 : ℝ) :=
      GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarSecondMoment
