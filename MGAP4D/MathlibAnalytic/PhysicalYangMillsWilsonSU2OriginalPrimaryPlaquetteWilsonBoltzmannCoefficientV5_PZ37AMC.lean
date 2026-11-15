import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteHaarCharacterBridgeV5_PZ37AMB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMC — genuine primary SU(2) plaquette Wilson Haar coefficient

AMB certified the true normalized-Haar pushforward of the original
four-edge cyclic primary spatial plaquette and its character moments.
The cyclic holonomy is conjugate to the actual oriented primary spatial
plaquette. Since the ORIGINAL Wilson plaquette energy is conjugation
invariant, its Boltzmann factor has the same Haar distribution.

Here the actual primary-plaquette Wilson Boltzmann Haar integral is
identified EXACTLY with the original AIF single-link partition integral,
not an invented Gaussian model or an independent-plaquette assumption.

At the unchanged prescribed original beta0, the exact coefficient is
strictly positive and obeys the existing AKW genuine SU(2) Haar estimate.
No interaction between different plaquettes or gauge-constrained
cross-volume Hilbert transport is asserted; no Hamiltonian or continuum
mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AMC_group : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMC_compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMC_countable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMC_measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMC_borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "chiK" => p4Q2PZ35C_originalOneLinkCharacter
local notation "PhiK" =>
  periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
local notation "muK" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "EK" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "zK" => p4Q2PZ37AIF_originalSingleLinkPartition
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

/-- The physically ORIENTED four-edge primary spatial plaquette has the
exact same ORIGINAL SU(2) character as its canonical cyclic boundary
holonomy, for every actual full lattice link configuration. -/
theorem p4Q2PZ37AMC_originalOrientedPrimaryPlaquetteCharacter_eq_cyclic
    (H : ℕ) (A : PeriodicHypercubicEvenEdge H → GK) :
    chiK (periodicHypercubicPlaquetteHolonomy A
      (periodicHypercubicEvenPrimarySpatialPlaquette H)) =
    chiK (PhiK H 2
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)) := by
  have henergy :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergy_eq_boundaryCyclicHolonomy
      H 2 A
  simpa only [p4Q2PZ35C_originalOneLinkCharacter] using
    congrArg (fun e : ℝ => (1 : ℝ) - e) henergy

/-- Exact Haar coefficient for the actual FOUR physical primary
spatial plaquette edges; no surrogate group law, no four-link
independence assumption across *different* plaquettes. The group
Haar pushforward and Wilson energy are the genuine original ones. -/
theorem p4Q2PZ37AMC_primaryPlaquetteWilsonHaar_partition_eq_original
    (H : ℕ) (beta : ℝ) :
    (∫ b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      Real.exp (-beta * EK (PhiK H 2 b)) ∂muK H 2) = zK beta := by
  have hcontinuous :
      Continuous (fun g : GK => Real.exp (-beta * EK g)) :=
    Real.continuous_exp.comp
      (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))
  have htransport :=
    p4Q2PZ37AMB_primaryPlaquetteHaar_integral_transport
      H (fun g : GK => Real.exp (-beta * EK g))
      hcontinuous.measurable.aestronglyMeasurable
  simpa only [p4Q2PZ37AIF_originalSingleLinkPartition] using htransport

/-- The original fixed-beta0 PRIMARY physical Wilson plaquette
Boltzmann Haar coefficient is strictly positive at every H. -/
theorem p4Q2PZ37AMC_originalFixedBeta0_primaryPlaquetteWilsonHaar_pos
    (H : ℕ) :
    0 < (∫ b :
      (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      Real.exp (-beta0 * EK (PhiK H 2 b)) ∂muK H 2) := by
  rw [p4Q2PZ37AMC_primaryPlaquetteWilsonHaar_partition_eq_original]
  exact p4Q2PZ37AIF_originalSingleLinkPartition_pos beta0

/-- An unconditional, H-independent coefficient estimate for ONE
actual primary SU(2) plaquette under the true product-Haar reference
law at the prescribed original beta0. This does NOT control interacting
Wilson plaquette clusters or the full beta0 transfer operator. -/
theorem p4Q2PZ37AMC_originalFixedBeta0_primaryPlaquetteWilsonHaar_le
    (H : ℕ) :
    (∫ b :
      (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration GK,
      Real.exp (-beta0 * EK (PhiK H 2 b)) ∂muK H 2) ≤
    Real.exp (-beta0 + 44 * beta0 ^ 2 / 351) := by
  rw [p4Q2PZ37AMC_primaryPlaquetteWilsonHaar_partition_eq_original]
  exact p4Q2PZ37AKW_originalSingleLinkPartition_le_fortyFourThreeFiftyOneGaussian
    beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMC_originalOrientedPrimaryPlaquetteCharacter_eq_cyclic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMC_primaryPlaquetteWilsonHaar_partition_eq_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMC_originalFixedBeta0_primaryPlaquetteWilsonHaar_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMC_originalFixedBeta0_primaryPlaquetteWilsonHaar_le
