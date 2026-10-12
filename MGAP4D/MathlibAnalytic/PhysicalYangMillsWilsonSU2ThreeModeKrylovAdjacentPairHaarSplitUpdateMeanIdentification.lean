import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCondExpMeasureEquivTransport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-DA: literal Function.update Haar mean equals true CR L² projection

CZ proved the genuine physical CR Hilbert-L² conditional expectation equals
the CY off-link × one SU(N) Haar fiber mean on every globally bounded
strongly measurable representative. CU already proved that literal
independent coordinate-Haar means, defined using Function.update on the
actual physical left/right spatial coordinates, commute by Fubini.

The exact pointwise missing link is now discharged: the inverse of CY's
off-link/single-link measurable equivalence at (retained z, u) is the
canonical physical configuration with precisely coordinate i updated to u.
Consequently the true CR Hilbert-L² coordinate projection agrees a.e.
with CU's LITERAL original spatial link Haar mean on bounded representatives.

No point evaluation of arbitrary L² quotient functions, no new law and
no positive-beta conditional commutation or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000
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
local notation "JH" => Lp ℝ 2 muPair

/-- Updating exactly one coordinate i in the original physical joint
configuration is literally inverse to CY's one-Haar coordinate split,
with the original retained coordinates unchanged. -/
theorem p4Q2DA_actualPairHaarSplit_update_eq
    (i : I) (z : Joint) (u : G) :
    (p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm
      (((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i) z).1, u) =
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N).symm
        (Function.update
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H N z) i u) := by
  classical
  let E := p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i
  let e := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
    H N
  apply E.injective
  rw [E.apply_symm_apply]
  apply Prod.ext
  · funext j
    simp [E, p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv,
      p4Q2CX_actualPairHaarOffCoordinateSplit,
      MeasurableEquiv.prodCongr, MeasurableEquiv.piUnique,
      Equiv.piEquivPiSubtypeProd, Function.update, j.property]
  · simp [E, p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv,
      p4Q2CX_actualPairHaarOffCoordinateSplit,
      MeasurableEquiv.prodCongr, MeasurableEquiv.piUnique,
      Equiv.piEquivPiSubtypeProd, Function.update]

/-- Exact equality of the two ORIGINAL physical Haar mean constructions:
CY's measurable off-link/single-coordinate fiber integral and CU's
canonical Function.update integral. This identity is pointwise on every
concrete observable, before forming any L² quotient. -/
theorem p4Q2DA_actualPairHaar_splitFiberMean_eq_CU
    (i : I) (F : Joint → ℝ) (z : Joint) :
    (∫ u : G,
      F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm
        (((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i) z).1, u))
      ∂muH) =
      p4Q2CU_actualPairHaarCoordinateMean H N i F z := by
  classical
  unfold p4Q2CU_actualPairHaarCoordinateMean
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u =>
    congrArg F (p4Q2DA_actualPairHaarSplit_update_eq H N i z u)

/-- The ACTUAL Hilbert-L² CR coordinate orthogonal projection, on any
bounded strongly measurable original physical representative, equals
CU's literal one-link Haar integral a.e.  Neither conclusion nor proof
uses an assumed projection-commutation oracle. -/
theorem p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
    (i : I) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    ((p4Q2CR_actualPairHaarCoordinateProjection H N i f : JH) :
      Joint → ℝ) =ᵐ[muPair]
      p4Q2CU_actualPairHaarCoordinateMean H N i F := by
  have h := p4Q2CZ_actualPairHaarProjection_ae_eq_splitFiberMean
    H N i f F hF M hM hEq
  exact h.trans <| Filter.Eventually.of_forall
    (p4Q2DA_actualPairHaar_splitFiberMean_eq_CU H N i F)

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
