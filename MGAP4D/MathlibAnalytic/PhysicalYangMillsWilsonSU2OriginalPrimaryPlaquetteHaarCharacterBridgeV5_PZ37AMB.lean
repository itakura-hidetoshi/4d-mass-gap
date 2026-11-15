import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH21SmallCouplingThirdTaylorAJANoGoV5_PZ37AKW
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMB — actual primary SU(2) plaquette free-Haar character moments

The original fundamental SU(2) character chi has exactly zero *true
normalized-Haar* mean and one-quarter second moment (AIQ/ACK/AKW).
The canonical primary spatial plaquette is NOT an abstract fresh group
variable: its four actual distinct boundary edges define the cyclic word
c^{-1} d^{-1} a b in the genuine product Haar boundary configuration.
The existing measure-preserving theorem identifies the pushforward of that
actual plaquette holonomy with normalized SU(2) Haar.

This append-only leaf composes these TWO existing typed structures and
establishes exact first/second Haar moments of the genuine canonical primary
plaquette character. It also transports AKW's variance-sensitive exponential
character estimate and specializes it to the original fixed beta0.

The cyclic holonomy is conjugate to the originally oriented plaquette
holonomy, as proved in the imported Wilson class-function geometry.
We do not infer anything about multiple dependent plaquettes or the
interacting Gibbs/transfer law; no cross-H Gauss embedding or uniform gap
is claimed. Existing true Wilson SU(2), Haar, AJA, beta0, roots and pins
are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ

local instance p4Q2PZ37AMB_group : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMB_compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMB_countable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMB_measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMB_borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "nuK" => normalizedCompactHaar GK
local notation "chiK" => p4Q2PZ35C_originalOneLinkCharacter
local notation "PhiK" =>
  periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
local notation "muK" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

/-- Exact **physical-edge** primary plaquette expectation transport.
The measure-preserving premise is ALREADY THEOREM-GENERATED for the
actual four distinct spatial boundary links; we do not assume
plaquette independence or a fictitious Gaussian law. -/
theorem p4Q2PZ37AMB_primaryPlaquetteHaar_integral_transport
    (H : ℕ) (f : GK → ℝ)
    (hf : AEStronglyMeasurable f nuK) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      f (PhiK H 2 b) ∂muK H 2) =
    (∫ g : GK, f g ∂nuK) := by
  let phi := PhiK H 2
  let mu := muK H 2
  have hmp : MeasurePreserving phi mu nuK :=
    measurePreserving_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
      H 2
  have hfmap : AEStronglyMeasurable f (Measure.map phi mu) := by
    rw [hmp.map_eq]
    exact hf
  calc
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      f (PhiK H 2 b) ∂muK H 2) =
        ∫ g : GK, f g ∂Measure.map phi mu :=
          (MeasureTheory.integral_map hmp.measurable.aemeasurable hfmap).symm
    _ = ∫ g : GK, f g ∂nuK := by rw [hmp.map_eq]

/-- Genuine canonical primary spatial SU(2) plaquette character has
exact zero Haar mean at every finite physical spatial extent. -/
theorem p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_mean_zero
    (H : ℕ) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      chiK (PhiK H 2 b) ∂muK H 2) = 0 := by
  have hf : AEStronglyMeasurable chiK nuK :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.measurable.aestronglyMeasurable
  calc
    _ = (∫ g : GK, chiK g ∂nuK) :=
      p4Q2PZ37AMB_primaryPlaquetteHaar_integral_transport H chiK hf
    _ = 0 := p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero

/-- The same ACTUAL primary spatial SU(2) plaquette (not a synthetic
single-link replacement) has exactly one-quarter Haar second moment. -/
theorem p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_secondMoment
    (H : ℕ) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      (chiK (PhiK H 2 b)) ^ 2 ∂muK H 2) = (1 / 4 : ℝ) := by
  have hf : AEStronglyMeasurable (fun g : GK => (chiK g) ^ 2) nuK :=
    (p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.pow 2).measurable.aestronglyMeasurable
  calc
    _ = (∫ g : GK, (chiK g) ^ 2 ∂nuK) :=
      p4Q2PZ37AMB_primaryPlaquetteHaar_integral_transport
        H (fun g : GK => (chiK g) ^ 2) hf
    _ = (1 / 4 : ℝ) :=
      p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment

/-- Exact transport of the true SU(2) one-link exponential moment
to the real four-link primary-plaquette holonomy; the small-beta
bound comes from actual Haar moments, not independent plaquettes. -/
theorem p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_mgf_le
    (H : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) (hsmall : beta ≤ (1 / 156 : ℝ)) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      Real.exp (beta * chiK (PhiK H 2 b)) ∂muK H 2) ≤
    1 + 44 * beta ^ 2 / 351 := by
  have hcontinuous : Continuous (fun g : GK => Real.exp (beta * chiK g)) := by
    fun_prop
  have hf : AEStronglyMeasurable (fun g : GK => Real.exp (beta * chiK g)) nuK :=
    hcontinuous.measurable.aestronglyMeasurable
  have htransport :=
    p4Q2PZ37AMB_primaryPlaquetteHaar_integral_transport
      H (fun g : GK => Real.exp (beta * chiK g)) hf
  have hbound :=
    p4Q2PZ37AKW_originalSingleLinkCharacter_mgf_le_fortyFourThreeFiftyOne
      beta hbeta hsmall
  change (∫ g : GK, Real.exp (beta * chiK g) ∂nuK) ≤
    1 + 44 * beta ^ 2 / 351 at hbound
  exact htransport.trans_le hbound

/-- At the prescribed original beta0, the physical-edge *free-Haar*
primary plaquette moment-generating function obeys the same exact
certified bound for every H. Interacting Wilson Gibbs correlations are
NOT controlled by this result. -/
theorem p4Q2PZ37AMB_originalFixedBeta0_primaryPlaquetteHaar_mgf_le
    (H : ℕ) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      Real.exp (beta0 * chiK (PhiK H 2 b)) ∂muK H 2) ≤
    1 + 44 * beta0 ^ 2 / 351 := by
  exact p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_mgf_le
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMB_primaryPlaquetteHaar_integral_transport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_mgf_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMB_originalFixedBeta0_primaryPlaquetteHaar_mgf_le
