import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwelveColorCenteredVarianceBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorRelativeFrameBridge
import Mathlib.Tactic

/-!
# P4-Q2-BG: genuine physical joint-L² twelve-color symmetric bilinear carrier

BF establishes an all-beta upper comparison for the mass-weighted ORIGINAL
Wilson twelve-color Haar reference on bounded concrete observables.
This file formalizes the symmetric bilinear (quadratic) carrier already
determined by the twelve genuine conditional-expectation projections on
the SAME physical Wilson ground-state joint L².

The bilinear pairing is the normalized sum of real inner products of the
linear residuals (id - P_c). Its diagonal is EXACTLY the earlier conventional
physical twelve-color Dirichlet energy; it is positive semidefinite and
invariant under removal of the intrinsic joint constant-line projection.
The pairing is additive and real homogeneous in BOTH variables, and the
diagonal scales quadratically.

The original mass-weighted Haar reference is bounded ABOVE by twelve times
the diagonal, as in BC/BD/BF; this does NOT identify the original reference
with this bilinear form. Constructing a separately justified bilinear
polarization and L² quotient extension of the literal original Haar reference
remains a distinct mathematical obligation. No new measure is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace InnerProduct ENNReal

noncomputable section

set_option maxHeartbeats 1500000

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
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

/-- Each residual map is an actual continuous real-linear operator on the
physical joint L², not a surrogate conditional law or auxiliary measure. -/
noncomputable def p4Q2BG_physicalTwelveResidualOperator
    (c : C12) : J →L[ℝ] J :=
  ContinuousLinearMap.id ℝ J - P12 c

@[simp] theorem p4Q2BG_physicalTwelveResidualOperator_apply
    (c : C12) (f : J) :
    p4Q2BG_physicalTwelveResidualOperator H N hN beta hbeta c f =
      f - P12 c f := by
  simp [p4Q2BG_physicalTwelveResidualOperator]

/-- Genuine finite, symmetric physical twelve-color residual pairing on
the complete original Wilson ground-state joint Hilbert space. -/
noncomputable def p4Q2BG_physicalTwelveResidualPair
    (f g : J) : ℝ :=
  ((Fintype.card C12 : ℝ)⁻¹) *
    ∑ c : C12,
      inner ℝ
        (p4Q2BG_physicalTwelveResidualOperator H N hN beta hbeta c f)
        (p4Q2BG_physicalTwelveResidualOperator H N hN beta hbeta c g)

/-- Exact identification with the existing physical twelve-color energy. -/
theorem p4Q2BG_physicalTwelveResidualPair_self_eq_energy
    (f : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f f =
      E12 f := by
  simp only [
    p4Q2BG_physicalTwelveResidualPair,
    p4Q2BG_physicalTwelveResidualOperator_apply,
    real_inner_self_eq_norm_sq,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy,
    groundStateJointColorNormalizedResidualEnergy]

theorem p4Q2BG_physicalTwelveResidualPair_symmetric
    (f g : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g =
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta g f := by
  unfold p4Q2BG_physicalTwelveResidualPair
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  exact real_inner_comm _ _

theorem p4Q2BG_physicalTwelveResidualPair_add_left
    (f g h : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta (f + g) h =
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f h +
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta g h := by
  simp only [
    p4Q2BG_physicalTwelveResidualPair,
    map_add, inner_add_left, Finset.sum_add_distrib, mul_add]

theorem p4Q2BG_physicalTwelveResidualPair_smul_left
    (a : ℝ) (f g : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta (a • f) g =
      a * p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g := by
  unfold p4Q2BG_physicalTwelveResidualPair
  simp_rw [map_smul, real_inner_smul_left]
  rw [← Finset.mul_sum]
  ring

theorem p4Q2BG_physicalTwelveResidualPair_add_right
    (f g h : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f (g + h) =
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g +
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f h := by
  calc
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f (g + h) =
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta (g + h) f :=
      p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta f (g + h)
    _ = p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta g f +
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta h f :=
      p4Q2BG_physicalTwelveResidualPair_add_left H N hN beta hbeta g h f
    _ = p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g +
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f h := by
      rw [
        p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta g f,
        p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta h f]

theorem p4Q2BG_physicalTwelveResidualPair_smul_right
    (a : ℝ) (f g : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f (a • g) =
      a * p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g := by
  calc
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f (a • g) =
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta (a • g) f :=
      p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta f (a • g)
    _ = a * p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta g f :=
      p4Q2BG_physicalTwelveResidualPair_smul_left H N hN beta hbeta a g f
    _ = a * p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g := by
      rw [p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta g f]

/-- The genuine physical twelve-color Dirichlet energy is quadratic on the
FULL joint L² (not merely on bounded concrete representatives). -/
theorem p4Q2BG_physicalTwelveResidualEnergy_smul
    (a : ℝ) (f : J) :
    E12 (a • f) = a ^ 2 * E12 f := by
  calc
    E12 (a • f) =
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta (a • f) (a • f) :=
      (p4Q2BG_physicalTwelveResidualPair_self_eq_energy
        H N hN beta hbeta (a • f)).symm
    _ = a * p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f (a • f) :=
      p4Q2BG_physicalTwelveResidualPair_smul_left
        H N hN beta hbeta a f (a • f)
    _ = a * (a * p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f f) := by
      rw [p4Q2BG_physicalTwelveResidualPair_smul_right
        H N hN beta hbeta a f f]
    _ = a ^ 2 * E12 f := by
      rw [p4Q2BG_physicalTwelveResidualPair_self_eq_energy]
      ring

/-- The bilinear pairing itself ignores the intrinsic constant component
in the first variable, with NO beta cutoff. -/
theorem p4Q2BG_physicalTwelveResidualPair_centered_left
    (f g : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta (f - B f) g =
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g := by
  have hzero (c : C12) :
      p4Q2BG_physicalTwelveResidualOperator H N hN beta hbeta c (B f) = 0 := by
    rw [p4Q2BG_physicalTwelveResidualOperator_apply]
    rw [p4Q2BF_twelveSpatialCondExp_fixes_jointConstantProjection
      H N hN beta hbeta f c]
    exact sub_self _
  unfold p4Q2BG_physicalTwelveResidualPair
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  rw [map_sub, hzero, sub_zero]

theorem p4Q2BG_physicalTwelveResidualPair_centered_right
    (f g : J) :
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f (g - B g) =
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g := by
  calc
    p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f (g - B g) =
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta (g - B g) f :=
      p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta f (g - B g)
    _ = p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta g f :=
      p4Q2BG_physicalTwelveResidualPair_centered_left H N hN beta hbeta g f
    _ = p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g :=
      (p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta f g).symm

/-- The original Wilson Haar reference is only UPPER dominated by the diagonal
of this genuine physical quadratic carrier; their equality is NOT asserted. -/
theorem p4Q2BG_originalWilsonReferenceReal_le_twelve_physicalBilinearDiagonal
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal H N hN beta hbeta F ≤
      (12 : ℝ) *
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta
          (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)
          (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound) := by
  rw [p4Q2BG_physicalTwelveResidualPair_self_eq_energy]
  exact p4Q2BD_originalWilsonTwelveColorHaarReferenceReal_le_realEnergy
    H N hN beta hbeta F hF bound hbound

end
end

end MathlibAnalytic
end MGAP4D
