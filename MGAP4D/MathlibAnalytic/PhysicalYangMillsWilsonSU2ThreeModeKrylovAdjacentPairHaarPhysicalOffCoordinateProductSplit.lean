import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarProductFiberMeanCondExpIdentification
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# P4-Q2-CX: actual physical pair-Haar off-coordinate measurable product split

CV proved that the true Hilbert-L² conditional expectation onto the first
factor of a two-factor product probability equals the literal Haar fiber mean
on bounded strongly measurable real L² representatives. CU proved literal
two-link Haar mean commutation. CW reduces the remaining physical operator
commutation to bounded-core identification.

This file connects those generic product facts to the EXACT physical original
left/right SU(N) spatial pair-Haar law without changing that law:

* For every ACTUAL physical joint link i, construct an explicit measurable
  equivalence from the original left/right configuration to the retained
  off-i coordinates times its complementary coordinate block.
* Prove that equivalence takes the ORIGINAL physical pair-Haar law exactly
  to the product of its two genuine finite-coordinate Haar product measures.
* Prove that CR's exact retained-coordinate sigma algebra is literally the
  first-factor pullback through this measurable equivalence.

This is the measure/sigma part of the CV-to-physical transport. The
complement-to-single-Haar coordinate identification, consequent fiber
integral equality and unconditional full-L² CR commutation remain the
next theorem obligations. No invented Wilson law, positive-beta
commutation assumption, uniform Wilson gap, or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muH" => normalizedCompactHaar G

/-- The genuine measurable two-factor presentation, separating the retained
physical left/right links from the unique complementary link. The second
factor is kept as an honest finite Pi, not postulated as an independent
synthetic one-link conditional measure. -/
noncomputable def p4Q2CX_actualPairHaarOffCoordinateSplit
    (i : I) :
    Joint ≃ᵐ
      (({j : I // j ≠ i} → G) ×
       ({j : I // ¬(j ≠ i)} → G)) := by
  classical
  exact
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N).trans
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : I => G) (fun j : I => j ≠ i))

/-- THE ORIGINAL physical pair-Haar law splits as the honest retained
finite Haar Pi measure times the honest singleton-complement Haar Pi law.
This is an exact measure-preserving identification, not an auxiliary
approximate or interacting positive-beta Wilson product. -/
theorem p4Q2CX_actualPairHaarOffCoordinateSplit_measurePreserving
    (i : I) :
    MeasurePreserving
      (p4Q2CX_actualPairHaarOffCoordinateSplit H N i)
      muPair
      ((Measure.pi (fun _ : {j : I // j ≠ i} => muH)).prod
       (Measure.pi (fun _ : {j : I // ¬(j ≠ i)} => muH))) := by
  classical
  let he :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_pairHaar_measurePreserving
      H N
  let hs :=
    measurePreserving_piEquivPiSubtypeProd
      (fun _ : I => muH) (fun j : I => j ≠ i)
  exact hs.comp he

/-- CR's exact off-i sigma algebra on ORIGINAL physical joint
configurations is nothing other than the pullback of the FIRST factor
of the genuine Haar split constructed above. This aligns the sigma
algebra needed by CV with the actual Hilbert projection in CR. -/
theorem p4Q2CX_actualPairHaarOffCoordinateSigma_eq_splitFirst
    (i : I) :
    p4Q2CR_actualPairHaarOffCoordinateSigma H N i =
      MeasurableSpace.comap
        (Prod.fst ∘ p4Q2CX_actualPairHaarOffCoordinateSplit H N i)
        (inferInstance : MeasurableSpace ({j : I // j ≠ i} → G)) := by
  rfl

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
