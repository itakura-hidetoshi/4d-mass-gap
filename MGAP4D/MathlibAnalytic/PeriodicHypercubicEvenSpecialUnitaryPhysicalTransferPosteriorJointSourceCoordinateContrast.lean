import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDefectSplit
import Mathlib.Tactic

/-!
# Drift-free centered source-coordinate contrast

The original signed one-link defect contains a scalar output/half-density drift.
PR #5224/#5225 already showed that a two-input cross-multiplied contrast cancels
the common output drift exactly.

This file pushes that cancellation through the centered source-coordinate
decomposition.  The scalar source-tilt mean cancels as well:

  O_v D_x - O_x D_v
    = Out * (O_x <C_v,Tilt> - O_v <C_x,Tilt>).

Thus the cross contrast sees only centered one-source-coordinate information.
This is stronger structurally than separately bounding the two terms of the
original defect, because it preserves the signed cancellation needed for P3.

A direct absolute bound then follows from the existing local tilt L2 estimate:

  |contrast|
    <= Out * (exp(2 beta)-1)
       * (|O_x| ||C_v|| + |O_v| ||C_x||).

No division by an observable is introduced, so zeros of O_x or O_v cause no
problem.  No covariance identification or spatial-decay claim is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStatePosteriorJoint

section GeneralCarrier

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Out" => outputRightLinkTilt H N hN beta hbeta
local notation "Center" => sourceCenteredCoordinate H N hN beta hbeta
local notation "Tilt" => sourceTiltL2 H N hN beta hbeta
local notation "Rate" => (Real.exp (2 * beta) - 1)

/-- Cross multiplication cancels BOTH the retained scalar output drift and the
common source-tilt mean, leaving only centered source-coordinate pairings. -/
theorem jointTransferSourceContrast_eq_centeredCoordinate
    (x v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Obs v z * jointTransferLinkDifference H N hN beta hbeta x e z g -
      Obs x z * jointTransferLinkDifference H N hN beta hbeta v e z g =
    Out z e g *
      (Obs x z * inner ℝ (Center v e z) (Tilt e z g) -
        Obs v z * inner ℝ (Center x e z) (Tilt e z g)) := by
  rw [jointTransferSourceContrast_eq]
  rw [
    sourceLinkResponse_eq_centeredCoordinate H N hN beta hbeta v e z g,
    sourceLinkResponse_eq_centeredCoordinate H N hN beta hbeta x e z g
  ]
  ring

/-- Absolute drift-free contrast bound in terms of the two centered
source-coordinate norms. -/
theorem jointTransferSourceContrast_abs_le_centeredCoordinate
    (x v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |Obs v z * jointTransferLinkDifference H N hN beta hbeta x e z g -
        Obs x z * jointTransferLinkDifference H N hN beta hbeta v e z g| ≤
      Out z e g * Rate *
        (|Obs x z| * ‖Center v e z‖ + |Obs v z| * ‖Center x e z‖) := by
  rw [jointTransferSourceContrast_eq_centeredCoordinate]
  rw [abs_mul, abs_of_pos (outputRightLinkTilt_pos H N hN beta hbeta z e g)]
  have hv :
      |inner ℝ (Center v e z) (Tilt e z g)| ≤
        Rate * ‖Center v e z‖ :=
    sourceTilt_inner_abs_le H N hN beta hbeta (Center v e z) e z g
  have hx :
      |inner ℝ (Center x e z) (Tilt e z g)| ≤
        Rate * ‖Center x e z‖ :=
    sourceTilt_inner_abs_le H N hN beta hbeta (Center x e z) e z g
  have hTri :
      |Obs x z * inner ℝ (Center v e z) (Tilt e z g) -
          Obs v z * inner ℝ (Center x e z) (Tilt e z g)| ≤
        |Obs x z| * |inner ℝ (Center v e z) (Tilt e z g)| +
          |Obs v z| * |inner ℝ (Center x e z) (Tilt e z g)| := by
    calc
      _ ≤ |Obs x z * inner ℝ (Center v e z) (Tilt e z g)| +
          |Obs v z * inner ℝ (Center x e z) (Tilt e z g)| :=
        abs_sub _ _
      _ = _ := by rw [abs_mul, abs_mul]
  have hCentered :
      |Obs x z| * |inner ℝ (Center v e z) (Tilt e z g)| +
          |Obs v z| * |inner ℝ (Center x e z) (Tilt e z g)| ≤
        |Obs x z| * (Rate * ‖Center v e z‖) +
          |Obs v z| * (Rate * ‖Center x e z‖) :=
    add_le_add
      (mul_le_mul_of_nonneg_left hv (abs_nonneg (Obs x z)))
      (mul_le_mul_of_nonneg_left hx (abs_nonneg (Obs v z)))
  have hOut :
      0 ≤ Out z e g :=
    (outputRightLinkTilt_pos H N hN beta hbeta z e g).le
  calc
    Out z e g *
        |Obs x z * inner ℝ (Center v e z) (Tilt e z g) -
          Obs v z * inner ℝ (Center x e z) (Tilt e z g)| ≤
      Out z e g *
        (|Obs x z| * |inner ℝ (Center v e z) (Tilt e z g)| +
          |Obs v z| * |inner ℝ (Center x e z) (Tilt e z g)|) :=
      mul_le_mul_of_nonneg_left hTri hOut
    _ ≤ Out z e g *
        (|Obs x z| * (Rate * ‖Center v e z‖) +
          |Obs v z| * (Rate * ‖Center x e z‖)) :=
      mul_le_mul_of_nonneg_left hCentered hOut
    _ = Out z e g * Rate *
        (|Obs x z| * ‖Center v e z‖ + |Obs v z| * ‖Center x e z‖) := by
      ring

end GeneralCarrier

section FrozenFamily

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Joint" => Cfg × Cfg
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 Hn 2
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "Obs" => jointTransferBCF Hn 2 Pos (beta n) (hbeta n)
local notation "Out" => outputRightLinkTilt Hn 2 Pos (beta n) (hbeta n)
local notation "Center" => sourceCenteredCoordinate Hn 2 Pos (beta n) (hbeta n)
local notation "Rate" => (Real.exp (2 * beta n) - 1)

/-- Frozen-orbit specialization against an arbitrary signed reference vector.
The common output drift and source-tilt mean remain exactly canceled. -/
theorem fineFrozenSourceContrast_abs_le_centeredCoordinate
    (v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |Obs v z * jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n) Orbit e z g -
        Obs Orbit z * jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n) v e z g| ≤
      Out z e g * Rate *
        (|Obs Orbit z| * ‖Center v e z‖ + |Obs v z| * ‖Center Orbit e z‖) :=
  jointTransferSourceContrast_abs_le_centeredCoordinate
    Hn 2 Pos (beta n) (hbeta n) Orbit v e z g

end FrozenFamily

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic
