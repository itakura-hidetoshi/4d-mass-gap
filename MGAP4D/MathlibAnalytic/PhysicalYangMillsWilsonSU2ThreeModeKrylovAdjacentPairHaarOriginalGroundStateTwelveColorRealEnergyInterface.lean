import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwoSidedTwelveColorDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointTwoBoundaryOrderedSchur
import Mathlib.Tactic

/-!
# P4-Q2-BC: exact interface between original Wilson reference Dirichlet and
# real physical twelve-color Hilbert residual energy

BB's positive original Wilson reference side is expressed in ENNReal
because actual physical fibers are integrated using lintegral. The physically
meaningful twelve-color frame and transfer estimates use the real squared
Hilbert residual sum. BC establishes this interface without discarding the
original fiber mass or changing the direction of any inequality.

An explicit, distinct follow-up obligation is still a POSITIVE lower bound
on the twelve-color physical residual relative to the top-orthogonal norm.
The already existing two-boundary ordered Schur constant is less than one
only under an explicit beta cutoff; that condition by itself does NOT
immediately imply the missing physical frame inequality.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1300000

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

section
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "C" => PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor

/-- Squared projection defects on the genuine joint Hilbert carrier are real,
nonnegative, and form the physical twelve-spatial Dirichlet energy. -/
noncomputable def p4Q2BC_twelvePhysicalResidualSum (f : J) : ℝ :=
  ∑ c : C,
    ‖f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta c f‖ ^ 2

/-- Exact finite sum embedding into ENNReal, without relying on a
measurability or integrability of an abstract conditional-law representative. -/
theorem p4Q2BC_ofReal_twelvePhysicalResidualSum
    (f : J) :
    ENNReal.ofReal (p4Q2BC_twelvePhysicalResidualSum H N hN beta hbeta f) =
      ∑ c : C, ENNReal.ofReal
        (‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
            H N hN beta hbeta c f‖ ^ 2) := by
  classical
  let a : C → ℝ := fun c =>
    ‖f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta c f‖ ^ 2
  have ha : ∀ c : C, 0 ≤ a c := fun c => sq_nonneg _
  have hsum : ∀ s : Finset C,
      ENNReal.ofReal (∑ c ∈ s, a c) =
        ∑ c ∈ s, ENNReal.ofReal (a c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
        simp only [Finset.sum_insert hc]
        rw [ENNReal.ofReal_add (ha c) (Finset.sum_nonneg (fun x hx => ha x))]
        exact congrArg (fun t : ENNReal => ENNReal.ofReal (a c) + t) ih
  change ENNReal.ofReal (∑ c : C, a c) = ∑ c : C, ENNReal.ofReal (a c)
  simpa only [Finset.sum_attach] using (hsum Finset.univ)

/-- On every bounded strongly measurable physical joint observable, the
UNNORMALIZED original Wilson 12-color mass-weighted Haar reference sum is
bounded by the exact real Hilbert twelve-color projection energy embedded
into ENNReal. This is the same inequality as BB, without the 1/12 factor. -/
theorem p4Q2BC_originalTwelveReferenceSum_le_realPhysicalResidualSum
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ c : C,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F) ≤
      ENNReal.ofReal
        (p4Q2BC_twelvePhysicalResidualSum H N hN beta hbeta
          (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)) := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  have hBound :
      (∑ c : C,
        p4Q2BB_twelveColorOriginalHaarReferenceAverage
          H N hN beta hbeta c F) ≤
        ∑ c : C,
          ENNReal.ofReal
            (‖f -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
                H N hN beta hbeta c f‖ ^ 2) := by
    classical
    apply Finset.sum_le_sum
    intro c _hc
    exact p4Q2BB_twelveColorOriginalHaarReferenceAverage_le_physicalBlock
      H N hN beta hbeta c F hF bound hbound
  rw [p4Q2BC_ofReal_twelvePhysicalResidualSum]
  exact hBound

/-- The real residual sum is twelve times the already canonical physical
twelve-spatial normalized Hilbert Dirichlet energy, with NO new estimates. -/
theorem p4Q2BC_realPhysicalResidualSum_eq_twelve_mul_normalized
    (f : J) :
    p4Q2BC_twelvePhysicalResidualSum H N hN beta hbeta f =
      (12 : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta f := by
  change
    (∑ c : C, ‖f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta c f‖ ^ 2) =
      (12 : ℝ) *
        ((Fintype.card C : ℝ)⁻¹ *
          ∑ c : C, ‖f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
              H N hN beta hbeta c f‖ ^ 2)
  rw [periodicHypercubicEvenGroundStateTwoSidedSpatialColor_card]
  norm_num

/-- BC main: explicit real twelve-color Dirichlet expression for the actual
original Wilson reference. The inequality points from original Haar
reference into the physical residual, NOT in the reverse Poincare direction. -/
theorem p4Q2BC_originalReference_le_realTwelveNormalizedHilbertEnergy
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ c : C,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F) ≤
      ENNReal.ofReal
        ((12 : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
            H N hN beta hbeta
            (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)) := by
  simpa only [p4Q2BC_realPhysicalResidualSum_eq_twelve_mul_normalized] using
    (p4Q2BC_originalTwelveReferenceSum_le_realPhysicalResidualSum
      H N hN beta hbeta F hF bound hbound)

end
end
end MathlibAnalytic
end MGAP4D
