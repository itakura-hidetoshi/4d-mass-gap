import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwoSidedTwelveColorDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialUniformGap
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# P4-Q2-BC: ORIGINAL physical Wilson twelve-color reference versus real relative frame

BB proves, for EVERY bounded strongly measurable concrete joint observable F,
the all-link actual mass-weighted Wilson Haar reference energy averaged over
both twelve physical spatial colors is BELOW the corresponding joint-L²
physical twelve-color sum of squared conditional-expectation defects.

The right side is ENNReal-valued in BB, while the earlier G1 ordered-dependence
twelve-color relative Poincare theorem uses the SAME joint physical projections
and a REAL Hilbert-space residual. We prove the EXACT conversion between these
two expressions, not an unproved comparison. In particular the full original
Wilson Haar reference energy is finite on the bounded joint core.

G1 already provides the POSITIVE physical twelve-color relative frame at
explicit restricted beta: beta <= twoSidedTwelveSpatialFrameCutoff(s), s>8.
G4 already supplies a more restrictive interval with the rank- and
volume-independent finite-volume coefficient 1/2304. We integrate both existing
verified results with BB as TWO genuine inequalities against the SAME physical
joint-L² residual. The local Wilson factor exp(-32 beta) is unchanged.

CRUCIAL DIRECTION: Haar reference <= physical residual and
kappa * physical constant-centered squared norm <= physical residual.
These DO NOT imply Haar reference >= kappa * variance. There is NO claim of a
global mass gap from this reference alone, and no uniform continuum scaling
from the positive finite-volume high-temperature conditional frame.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2600000
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

section ConcreteOriginalPhysicalTwelveFrame

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta
local notation "Bconst" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

/-- The actual original Wilson Haar reference, averaged over all links
inside their color and then over the twelve genuine right/left colors. -/
noncomputable def p4Q2BC_originalPhysicalTwelveColorHaarReference
    (F : Joint → ℝ) : ENNReal :=
  (12 : ENNReal)⁻¹ *
    ∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage H N hN beta hbeta c F

/-- The exact same real joint-L² twelve-color residual already used by the
verified G1/G4 ordered link-dependence frame theorems. -/
noncomputable def p4Q2BC_originalPhysicalTwelveColorResidual
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
    (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)

/-- The genuinely physical twelve-color residual is nonnegative. -/
theorem p4Q2BC_originalPhysicalTwelveColorResidual_nonneg
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    0 ≤ p4Q2BC_originalPhysicalTwelveColorResidual
      H N hN beta hbeta F hF bound hbound := by
  change 0 ≤
    groundStateJointColorNormalizedResidualEnergy P12
      (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)
  exact groundStateJointColorNormalizedResidualEnergy_nonneg P12 _

/-- FINITE sum of ENNReal.ofReal physical squared residuals is exactly the
ofReal of the finite real sum. This is not a measure-theoretic shortcut. -/
theorem p4Q2BC_originalTwelveColorResidualSum_eq_ofReal
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      p4Q2BB_twelveColorPhysicalBlockResidual
        H N hN beta hbeta c F hF bound hbound) =
    ENNReal.ofReal
      (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          P12 c (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  change (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      ENNReal.ofReal (‖f - P12 c f‖ ^ 2)) =
    ENNReal.ofReal
      (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
        ‖f - P12 c f‖ ^ 2)
  exact (ENNReal.ofReal_sum_of_nonneg
    (s := (Finset.univ : Finset PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor))
    (f := fun c => ‖f - P12 c f‖ ^ 2)
    (by intro c hc; positivity)).symm

/-- Exact identification of BB's ENNReal-valued 12-color squared-defect
average with the genuine REAL normalized E12 physical Hilbert residual.
The only coefficient conversion is 1/12 and is mathematically exact. -/
theorem p4Q2BC_originalTwelveColorENNRealResidual_eq_ofReal
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (12 : ENNReal)⁻¹ *
      (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
        p4Q2BB_twelveColorPhysicalBlockResidual
          H N hN beta hbeta c F hF bound hbound) =
      ENNReal.ofReal
        (p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound) := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  have hSum :=
    p4Q2BC_originalTwelveColorResidualSum_eq_ofReal
      H N hN beta hbeta F hF bound hbound
  have hCoeff :
      ENNReal.ofReal ((12 : ℝ)⁻¹) = (12 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 12)]
    norm_num
  have hReal :
      p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound =
        (12 : ℝ)⁻¹ *
          (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
            ‖f - P12 c f‖ ^ 2) := by
    simp only [p4Q2BC_originalPhysicalTwelveColorResidual,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy,
      groundStateJointColorNormalizedResidualEnergy,
      periodicHypercubicEvenGroundStateTwoSidedSpatialColor_card]
    norm_num
    rfl
  calc
    (12 : ENNReal)⁻¹ *
        (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
          p4Q2BB_twelveColorPhysicalBlockResidual
            H N hN beta hbeta c F hF bound hbound) =
      (12 : ENNReal)⁻¹ *
        ENNReal.ofReal
          (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
            ‖f - P12 c f‖ ^ 2) := by rw [hSum]
    _ =
      ENNReal.ofReal
        ((12 : ℝ)⁻¹ *
          (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
            ‖f - P12 c f‖ ^ 2)) := by
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (12 : ℝ)⁻¹), hCoeff]
    _ = ENNReal.ofReal
          (p4Q2BC_originalPhysicalTwelveColorResidual
            H N hN beta hbeta F hF bound hbound) := by rw [hReal]

/-- BB as a REAL-Hilbert-carrier inequality: the mass-weighted original
Wilson two-sided all-link reference is <= the exact physical E12 residual,
not a different auxiliary joint-measure or decoupled frame. -/
theorem p4Q2BC_originalWilsonHaarReference_le_physicalTwelveResidual
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BC_originalPhysicalTwelveColorHaarReference H N hN beta hbeta F ≤
      ENNReal.ofReal
        (p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound) := by
  calc
    p4Q2BC_originalPhysicalTwelveColorHaarReference H N hN beta hbeta F ≤
      (12 : ENNReal)⁻¹ *
        (∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
          p4Q2BB_twelveColorPhysicalBlockResidual
            H N hN beta hbeta c F hF bound hbound) :=
      p4Q2BB_originalTwoSidedAllLinkTwelveColorDirichlet_le_physicalResidual
        H N hN beta hbeta F hF bound hbound
    _ = ENNReal.ofReal
          (p4Q2BC_originalPhysicalTwelveColorResidual
            H N hN beta hbeta F hF bound hbound) :=
      p4Q2BC_originalTwelveColorENNRealResidual_eq_ofReal
        H N hN beta hbeta F hF bound hbound

/-- Genuine finiteness of the ORIGINAL mass-weighted Wilson all-link
reference on the bounded joint core, inherited from the actual physical
joint-L² conditional projection defects, not an auxiliary mass floor. -/
theorem p4Q2BC_originalWilsonHaarReference_lt_top
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BC_originalPhysicalTwelveColorHaarReference
      H N hN beta hbeta F < ∞ := by
  exact lt_of_le_of_lt
    (p4Q2BC_originalWilsonHaarReference_le_physicalTwelveResidual
      H N hN beta hbeta F hF bound hbound)
    ENNReal.ofReal_lt_top

/-- The finite mass-weighted original physical Haar reference is a well-defined
REAL number and is bounded by the same genuine joint-Hilbert E12 residual. -/
theorem p4Q2BC_originalWilsonHaarReference_toReal_le_physicalTwelveResidual
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (p4Q2BC_originalPhysicalTwelveColorHaarReference
      H N hN beta hbeta F).toReal ≤
      p4Q2BC_originalPhysicalTwelveColorResidual
        H N hN beta hbeta F hF bound hbound := by
  have hle :=
    p4Q2BC_originalWilsonHaarReference_le_physicalTwelveResidual
      H N hN beta hbeta F hF bound hbound
  have hnonneg :=
    p4Q2BC_originalPhysicalTwelveColorResidual_nonneg
      H N hN beta hbeta F hF bound hbound
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle)

/-- BC: G1's ALREADY-PROVED dependence-controlled ordered two-sided
sweep frame and BB's ORIGINAL Wilson all-link reference comparison
hold SIMULTANEOUSLY, against the SAME true joint-L² E12 energy.

There are no added link independence or Dobrushin assumptions. The strictly
positive relative-frame coefficient holds only on the stated beta cutoff.
The two lower quantities cannot be ordered from these inequalities alone. -/
theorem p4Q2BC_originalWilsonReference_and_orderedRelativeFrame
    (s : ℝ) (hs : 8 < s)
    (hcut :
      beta ≤ GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (p4Q2BC_originalPhysicalTwelveColorHaarReference
        H N hN beta hbeta F).toReal ≤
        p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound ∧
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
          s beta *
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          Bconst (p4Q2AZ_originalJointL2
            H N hN beta hbeta F hF bound hbound)‖ ^ 2 ≤
        p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound := by
  constructor
  · exact p4Q2BC_originalWilsonHaarReference_toReal_le_physicalTwelveResidual
      H N hN beta hbeta F hF bound hbound
  · exact GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatial_ordered_relativePoincare
      H N hN beta hbeta s hs hcut
      (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)

/-- BC quantitative G4 bridge. On the stricter existing uniform beta cutoff,
the SAME original Wilson physical joint-twelve-color residual controls both
the finite real original mass-weighted Haar reference and the intrinsic
constant-centered physical L² variance with coefficient >= 1/2304.

This is a finite-volume frame uniform in H/N within the given beta interval;
it does not prove the continuum mass gap after lattice-spacing scaling. -/
theorem p4Q2BC_originalWilsonReference_and_uniformPhysicalTwelveFrame
    (s : ℝ) (hs : 8 < s)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff s hs)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (p4Q2BC_originalPhysicalTwelveColorHaarReference
        H N hN beta hbeta F).toReal ≤
        p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound ∧
      (1 / 2304 : ℝ) *
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          Bconst (p4Q2AZ_originalJointL2
            H N hN beta hbeta F hF bound hbound)‖ ^ 2 ≤
        p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  have hframeCut :
      beta ≤ GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs :=
    hcut.trans
      (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
        s hs)
  have hk :
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
          s beta :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient_le_relativeFrameCoefficient
      s hs beta hbeta hcut
  have hOrdered :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatial_ordered_relativePoincare
      H N hN beta hbeta s hs hframeCut f
  constructor
  · exact p4Q2BC_originalWilsonHaarReference_toReal_le_physicalTwelveResidual
      H N hN beta hbeta F hF bound hbound
  · calc
      (1 / 2304 : ℝ) * ‖f - Bconst f‖ ^ 2 ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
            s beta * ‖f - Bconst f‖ ^ 2 := by
          change GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient *
              ‖f - Bconst f‖ ^ 2 ≤
            GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
              s beta * ‖f - Bconst f‖ ^ 2
          exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)
      _ ≤ p4Q2BC_originalPhysicalTwelveColorResidual
          H N hN beta hbeta F hF bound hbound := hOrdered

end ConcreteOriginalPhysicalTwelveFrame
end
end MathlibAnalytic
end MGAP4D
