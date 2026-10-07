import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateContrast
import Mathlib.Tactic

/-!
# Output-deweighted centered source-coordinate contrast

PR #5232 proves the exact cross-multiplied cancellation

  O_v D_x - O_x D_v
    = Out * (O_x <C_v,Tilt> - O_v <C_x,Tilt>).

The multiplicative output/half-density factor Out is strictly positive.
Therefore it can be removed exactly by multiplying the contrast by Out⁻¹,
without dividing by either observable:

  Out⁻¹ (O_v D_x - O_x D_v)
    = O_x <C_v,Tilt> - O_v <C_x,Tilt>.

This removes the output/half-density factor completely from the drift-free
contrast.  The resulting absolute estimate depends only on the local source
tilt rate and the two centered source-coordinate norms.

No claim is made that this deweighted contrast equals the original one-link
Dirichlet defect, and no covariance-to-norm identification is introduced.
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

/-- Cross-multiplied signed defect with the positive output factor removed. -/
def jointTransferSourceDeweightedContrast
    (x v : PairL2) (e : Link) (z : Joint) (g : GaugeT) : ℝ :=
  (Out z e g)⁻¹ *
    (Obs v z * jointTransferLinkDifference H N hN beta hbeta x e z g -
      Obs x z * jointTransferLinkDifference H N hN beta hbeta v e z g)

/-- Exact elimination of the output/half-density factor from the drift-free
contrast.  No observable is divided by. -/
theorem jointTransferSourceDeweightedContrast_eq_centeredCoordinate
    (x v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    jointTransferSourceDeweightedContrast H N hN beta hbeta x v e z g =
      Obs x z * inner ℝ (Center v e z) (Tilt e z g) -
        Obs v z * inner ℝ (Center x e z) (Tilt e z g) := by
  unfold jointTransferSourceDeweightedContrast
  rw [jointTransferSourceContrast_eq_centeredCoordinate]
  have hOut : Out z e g ≠ 0 :=
    (outputRightLinkTilt_pos H N hN beta hbeta z e g).ne'
  field_simp [hOut]

/-- Output-free absolute bound for the exact deweighted contrast. -/
theorem jointTransferSourceDeweightedContrast_abs_le_centeredCoordinate
    (x v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |jointTransferSourceDeweightedContrast H N hN beta hbeta x v e z g| ≤
      Rate *
        (|Obs x z| * ‖Center v e z‖ + |Obs v z| * ‖Center x e z‖) := by
  rw [jointTransferSourceDeweightedContrast_eq_centeredCoordinate]
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
  exact hTri.trans (hCentered.trans_eq (by ring))

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
local notation "Center" => sourceCenteredCoordinate Hn 2 Pos (beta n) (hbeta n)
local notation "Rate" => (Real.exp (2 * beta n) - 1)

/-- Frozen-orbit specialization of the output-deweighted drift-free contrast. -/
theorem fineFrozenSourceDeweightedContrast_abs_le_centeredCoordinate
    (v : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |jointTransferSourceDeweightedContrast
        Hn 2 Pos (beta n) (hbeta n) Orbit v e z g| ≤
      Rate *
        (|Obs Orbit z| * ‖Center v e z‖ +
          |Obs v z| * ‖Center Orbit e z‖) :=
  jointTransferSourceDeweightedContrast_abs_le_centeredCoordinate
    Hn 2 Pos (beta n) (hbeta n) Orbit v e z g

end FrozenFamily

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic
