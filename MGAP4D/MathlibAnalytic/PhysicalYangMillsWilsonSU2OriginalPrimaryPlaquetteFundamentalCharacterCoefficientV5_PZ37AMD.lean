import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteWilsonBoltzmannCoefficientV5_PZ37AMC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTemporalCharacterTransmissionV5_PZ37ABN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMD — true primary SU(2) plaquette nontrivial Wilson character coefficient

ABN proves a nontrivial genuine SU(2) Wilson one-link fundamental character
coefficient is positive, with an explicit nonnegative-coupling lower bound.
AMB/AMC independently certify the *actual four physical links* of the
canonical primary spatial plaquette, their Haar pushforward, and exact Wilson
Boltzmann partition integral under the true boundary PRODUCT-HAAR reference
law. We connect them WITHOUT any new physical axiom or model replacement.

In particular the Haar-centered Wilson plaquette-character/weight covariance
is quantitatively positive at every beta>0; at the ORIGINAL fixed beta0
the corresponding normalized local character coefficient is in (0,1].
This is a local nontrivial plaquette character coefficient, NOT a proof of
factorization for plaquettes with shared links, not a genuine interacting
full Gibbs transfer norm comparison and not a mass-gap theorem.

Preserves original SU(2) Wilson operator and Haar/Gauss/AJA, beta0,
Lean v4.30.0-rc2 and pinned mathlib, append-only/same-root.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "Energy" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Phi" => periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
local notation "Mu" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "nu" => normalizedCompactHaar G

local instance p4Q2PZ37AMD_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMD_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMD_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMD_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMD_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

/-- Local normalized fundamental-character coefficient on the ACTUAL
four-edge SU(2) primary-plaquette boundary Haar reference measure. -/
noncomputable def p4Q2PZ37AMD_originalPrimaryPlaquetteWilsonCharacterCoefficient
    (H : ℕ) (beta : ℝ) : ℝ :=
  (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration G,
    Real.exp (-beta * Energy (Phi H 2 b)) * Chi (Phi H 2 b) ∂Mu H 2) /
  (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration G,
    Real.exp (-beta * Energy (Phi H 2 b)) ∂Mu H 2)

/-- The nontrivial weighted character moment of the actual four-link
primary plaquette equals the already VERIFIED original ABN Wilson
temporal Haar character moment. No independent plaquettes are assumed. -/
theorem p4Q2PZ37AMD_primaryPlaquetteWilsonCharacterMoment_eq_originalABN
    (H : ℕ) (beta : ℝ) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration G,
      Real.exp (-beta * Energy (Phi H 2 b)) * Chi (Phi H 2 b) ∂Mu H 2) =
      p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment beta := by
  have hcontinuous :
      Continuous (fun g : G => Real.exp (-beta * Energy g) * Chi g) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))).mul
      p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous
  have htransport :=
    p4Q2PZ37AMB_primaryPlaquetteHaar_integral_transport
      H (fun g : G => Real.exp (-beta * Energy g) * Chi g)
      hcontinuous.measurable.aestronglyMeasurable
  simpa only [p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment,
    specialUnitaryWilsonBoltzmannCentralFunction] using htransport

/-- The exact positive mass of the same four-link Haar plaquette equals
the original ABN denominator. It is an identity of the unchanged
normalized SU(2) Wilson Boltzmann integral, not a Gibbs factorization. -/
theorem p4Q2PZ37AMD_primaryPlaquetteWilsonMass_eq_originalABN
    (H : ℕ) (beta : ℝ) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration G,
      Real.exp (-beta * Energy (Phi H 2 b)) ∂Mu H 2) =
      p4Q2PZ37ABN_originalTemporalWilsonMass beta := by
  calc
    _ = p4Q2PZ37AIF_originalSingleLinkPartition beta :=
      p4Q2PZ37AMC_primaryPlaquetteWilsonHaar_partition_eq_original H beta
    _ = p4Q2PZ37ABN_originalTemporalWilsonMass beta := by
      rfl

/-- Exact typed equality of the ACTUAL local primary-plaquette Wilson
fundamental coefficient with the ORIGINAL temporal coefficient ABN.
No cross-volume Hilbert space identification occurs. -/
theorem p4Q2PZ37AMD_originalPrimaryPlaquetteCoefficient_eq_originalABN
    (H : ℕ) (beta : ℝ) :
    p4Q2PZ37AMD_originalPrimaryPlaquetteWilsonCharacterCoefficient H beta =
      p4Q2PZ37ABN_originalTemporalWilsonCoefficient beta := by
  unfold p4Q2PZ37AMD_originalPrimaryPlaquetteWilsonCharacterCoefficient
    p4Q2PZ37ABN_originalTemporalWilsonCoefficient
  rw [p4Q2PZ37AMD_primaryPlaquetteWilsonCharacterMoment_eq_originalABN,
    p4Q2PZ37AMD_primaryPlaquetteWilsonMass_eq_originalABN]

/-- The true free-product-Haar connected covariance of the original
primary-plaquette Wilson Boltzmann weight with its fundamental
character has an explicit nonnegative-coupling physical floor.
This is a ONE-plaquette connected observable, not interacting
two-plaquette clustering. -/
theorem p4Q2PZ37AMD_primaryPlaquetteWilsonCharacter_connectedHaar_ge
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    beta * Real.exp (-2 * beta) / 4 ≤
      (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration G,
        Real.exp (-beta * Energy (Phi H 2 b)) * Chi (Phi H 2 b) ∂Mu H 2) -
      (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration G,
        Real.exp (-beta * Energy (Phi H 2 b)) ∂Mu H 2) *
      (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration G,
        Chi (Phi H 2 b) ∂Mu H 2) := by
  rw [p4Q2PZ37AMB_primaryPlaquetteCharacter_Haar_mean_zero H, mul_zero, sub_zero,
    p4Q2PZ37AMD_primaryPlaquetteWilsonCharacterMoment_eq_originalABN]
  exact p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment_ge_explicit beta hb

/-- H-uniform TRUE one-plaquette normalized fundamental-character
lower bound, inherited from genuine SU(2) ABN with no new input. -/
theorem p4Q2PZ37AMD_originalPrimaryPlaquetteCoefficient_ge
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    beta * Real.exp (-2 * beta) / 4 ≤
      p4Q2PZ37AMD_originalPrimaryPlaquetteWilsonCharacterCoefficient H beta := by
  rw [p4Q2PZ37AMD_originalPrimaryPlaquetteCoefficient_eq_originalABN]
  exact p4Q2PZ37ABN_originalTemporalWilsonCoefficient_ge_explicit beta hb

/-- At the prescribed unchanged original SU(2) beta0 the actual
primary spatial plaquette's normalized fundamental coefficient is
strictly positive with explicit H-uniform local lower bound and
at most one. This is not a full transfer operator gap. -/
theorem p4Q2PZ37AMD_originalFixedBeta0_primaryPlaquetteCoefficient_certificate
    (H : ℕ) :
    0 < beta0 * Real.exp (-2 * beta0) / 4 ∧
    beta0 * Real.exp (-2 * beta0) / 4 ≤
      p4Q2PZ37AMD_originalPrimaryPlaquetteWilsonCharacterCoefficient H beta0 ∧
    p4Q2PZ37AMD_originalPrimaryPlaquetteWilsonCharacterCoefficient H beta0 ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact div_pos
      (mul_pos p4Q2PZ37ADC_fixedCoupling_pos (Real.exp_pos _))
      (by norm_num : (0 : ℝ) < 4)
  · exact p4Q2PZ37AMD_originalPrimaryPlaquetteCoefficient_ge
      H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  · rw [p4Q2PZ37AMD_originalPrimaryPlaquetteCoefficient_eq_originalABN]
    exact p4Q2PZ37ABN_originalTemporalWilsonCoefficient_le_one beta0

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMD_originalPrimaryPlaquetteWilsonCharacterCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMD_primaryPlaquetteWilsonCharacterMoment_eq_originalABN
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMD_primaryPlaquetteWilsonMass_eq_originalABN
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMD_originalPrimaryPlaquetteCoefficient_eq_originalABN
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMD_primaryPlaquetteWilsonCharacter_connectedHaar_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMD_originalPrimaryPlaquetteCoefficient_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMD_originalFixedBeta0_primaryPlaquetteCoefficient_certificate
