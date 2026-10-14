import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundarySignedResponseHaarPositiveV5_GT
import Mathlib.Tactic

/-!
# P4-Q2-GU: exact original signed physical transfer nonzero detection

GT lifted GS's genuinely signed, two-original-Wilson-left-boundary
physical receiver contrast to a strictly positive Haar reference
squared mass, provided the authentic Wilson source transfer at the
concrete right SU(2) pi insertion is positive.

This module removes the one-sided sign restriction. The true posterior
square-root minor is strictly positive at positive beta irrespective
of the source. GS factors the two-boundary response difference into
a POSITIVE original transfer normalization, the source-dependent
original Wilson one-slab transfer, and a strictly NEGATIVE,
source-independent original posterior square-root ratio contrast.

Thus a NONZERO (possibly negative) physical source transfer at the
actual SU2 insertion yields strictly positive Haar squared mass.
Equivalently, zero Haar response mass NECESSARILY implies the true
Wilson transfer vanishes at that concrete insertion. This exact
source-kernel obstruction is specialized to the actual fine right
Krylov and three left source families.

Haar is solely the reference for the continuous response norm. This
does not claim GI's distinct two-Wilson-posterior integrated expectation
gap is nonzero, or arbitrary signed Krylov injectivity, a uniform frame
constant, H1-C3 closure or continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "L" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta‖⁻¹
local notation "P" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta

/-- The source-independent genuine posterior ratio contrast is strictly
negative at the TWO exact SU(2) right insertions and true left rows. -/
private theorem p4Q2GU_originalRatioBracket_neg
    (hpos : 0 < beta) (right : Cfg) (e : Link) :
    (Real.sqrt (P (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e (1 : Gauge)) /
      Real.sqrt (P (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
        (specialUnitaryTwoRotation Real.pi)) -
     Real.sqrt (P (originalWilsonExplicitIdentityBoundary H) right e (1 : Gauge)) /
      Real.sqrt (P (originalWilsonExplicitIdentityBoundary H) right e
        (specialUnitaryTwoRotation Real.pi))) < 0 := by
  exact sub_neg.mpr
    (p4Q2GS_originalTwoWilsonBoundary_posteriorSqrtRatio_strict
      H beta hbeta hpos right e)

/-- The actual signed physical two-left-boundary point witness is NONZERO
whenever the original source-smoothed Wilson transfer is NONZERO, with
no assumed positivity of the signed physical input. -/
theorem p4Q2GU_originalPhysicalSignedTwoBoundaryWitness_ne_of_transfer_ne
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hTransfer :
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) ≠ 0) :
    p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
      H beta hbeta f right e (specialUnitaryTwoRotation Real.pi) ≠ 0 := by
  have hL : L ≠ 0 :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) beta hbeta)).ne'
  have hBracket := p4Q2GU_originalRatioBracket_neg H beta hbeta hpos right e
  have hB : (Real.sqrt
      (P (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e (1 : Gauge)) /
      Real.sqrt (P (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
        (specialUnitaryTwoRotation Real.pi)) -
    Real.sqrt (P (originalWilsonExplicitIdentityBoundary H) right e (1 : Gauge)) /
      Real.sqrt (P (originalWilsonExplicitIdentityBoundary H) right e
        (specialUnitaryTwoRotation Real.pi))) ≠ 0 := ne_of_lt hBracket
  unfold p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
  rw [p4Q2GS_originalTwoBoundarySignedResponse_eq_transfer_mul_posteriorRootContrast]
  exact mul_ne_zero (mul_ne_zero hL hTransfer) hB

/-- The true signed Wilson two-boundary continuous Haar mass is positive
for ALL physically nonzero transfer outputs at the actual SU(2) point,
including negative outputs. The latter is an important extension of GT. -/
theorem p4Q2GU_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer_ne
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hTransfer :
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) ≠ 0) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      H beta hbeta f right e := by
  exact p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass_pos_of_witness
    H beta hbeta f right e (specialUnitaryTwoRotation Real.pi)
    (p4Q2GU_originalPhysicalSignedTwoBoundaryWitness_ne_of_transfer_ne
      H beta hbeta hpos f right e hTransfer)

/-- No arbitrary source injectivity is postulated: zero genuine
two-boundary Haar response mass requires that the original Wilson
transfer output at the actual pi insertion is ZERO. -/
theorem p4Q2GU_originalHaarMass_zero_implies_originalTransfer_zero
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hZero : p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      H beta hbeta f right e = 0) :
    decomposableOneSliceTransferIntegral H 2 beta f
      (Function.update right e (specialUnitaryTwoRotation Real.pi)) = 0 := by
  by_contra hNonzero
  have hPositive := p4Q2GU_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer_ne
    H beta hbeta hpos f right e hNonzero
  exact (ne_of_gt hPositive) hZero

end Frozen

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" => physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Source-kernel obstruction for ACTUAL signed fine-right Krylov
combinations (beta(n+1) orbit, frozen beta(n) transfer/posterior). -/
theorem p4Q2GU_actualRightKrylov_HaarMass_zero_implies_transfer_zero
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (right : Cfg) (e : Link)
    (hZero : p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) right e = 0) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Function.update right e (specialUnitaryTwoRotation Real.pi)) = 0 := by
  have h := p4Q2GU_originalHaarMass_zero_implies_originalTransfer_zero
    Hn (beta n) (hbeta n) hFrozen
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) right e hZero
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

/-- Identical genuine signed source obstruction for original fine
left-three-mode inputs; no invented 3-dimensional Hilbert carrier. -/
theorem p4Q2GU_actualLeftThreeMode_HaarMass_zero_implies_transfer_zero
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ)
    (right : Cfg) (e : Link)
    (hZero : p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      Hn (beta n) (hbeta n)
      (∑ k : Fin 3, a k • LeftFactor n r k) right e = 0) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ k : Fin 3, a k • LeftFactor n r k)
      (Function.update right e (specialUnitaryTwoRotation Real.pi)) = 0 := by
  have h := p4Q2GU_originalHaarMass_zero_implies_originalTransfer_zero
    Hn (beta n) (hbeta n) hFrozen
    (∑ k : Fin 3, a k • LeftFactor n r k) right e hZero
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalPhysicalSignedTwoBoundaryWitness_ne_of_transfer_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_originalHaarMass_zero_implies_originalTransfer_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_actualRightKrylov_HaarMass_zero_implies_transfer_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GU_actualLeftThreeMode_HaarMass_zero_implies_transfer_zero
