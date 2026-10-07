import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateL2
import Mathlib.Tactic

/-!
# Pointwise separation of the retained output drift and centered source term

The exact source-coordinate formula from the preceding layer is

  D_e = A_e - B_e

with

  A_e = [1 - Out_e (1 + AvgTilt_e)] O_x

and

  B_e = Out_e <C_e^src, Tilt_e>.

This file performs the quantitative separation that P3 needs without discarding
either term.  The elementary inequality

  (A - B)^2 <= 2 A^2 + 2 B^2

isolates the output/half-density drift from the centered source-coordinate
piece.  Cauchy--Schwarz together with the already-proved local source-tilt L2
bound gives

  B_e^2 <= Out_e^2 (exp(2 beta)-1)^2 ||C_e^src||_2^2.

No covariance identification, spatial decay, volume-uniform output bound, or
frozen-orbit support claim is added here.  In particular the output drift is
retained as an independent nonnegative envelope for P3-C.
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
local notation "Avg" => sourceTiltMean H N beta
local notation "Center" => sourceCenteredCoordinate H N hN beta hbeta
local notation "Tilt" => sourceTiltL2 H N hN beta hbeta
local notation "Rate" => (Real.exp (2 * beta) - 1)

/-- The scalar output/half-density drift retained by the exact defect. -/
def sourceOutputDriftSq
    (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) : ℝ :=
  ((1 - Out z e g * (1 + Avg e z g)) * Obs x z) ^ 2

/-- The centered source-coordinate square envelope after using the local tilt
L2 bound. -/
def sourceCenteredCoordinateSqEnvelope
    (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) : ℝ :=
  (Out z e g) ^ 2 * Rate ^ 2 * ‖Center x e z‖ ^ 2

theorem sourceOutputDriftSq_nonneg
    (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    0 ≤ sourceOutputDriftSq H N hN beta hbeta x e z g := by
  unfold sourceOutputDriftSq
  positivity

theorem sourceCenteredCoordinateSqEnvelope_nonneg
    (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    0 ≤ sourceCenteredCoordinateSqEnvelope H N hN beta hbeta x e z g := by
  unfold sourceCenteredCoordinateSqEnvelope
  positivity

/-- The squared centered response is bounded by the source-coordinate norm
times only the exact output factor and the local source-tilt rate. -/
theorem sourceCenteredCoordinateResponse_sq_le_envelope
    (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    (Out z e g * inner ℝ (Center x e z) (Tilt e z g)) ^ 2 ≤
      sourceCenteredCoordinateSqEnvelope H N hN beta hbeta x e z g := by
  have hOut : 0 ≤ Out z e g :=
    (outputRightLinkTilt_pos H N hN beta hbeta z e g).le
  have hInner :
      |inner ℝ (Center x e z) (Tilt e z g)| ≤
        Rate * ‖Center x e z‖ :=
    sourceTilt_inner_abs_le H N hN beta hbeta (Center x e z) e z g
  have hProd :
      |Out z e g * inner ℝ (Center x e z) (Tilt e z g)| ≤
        Out z e g * (Rate * ‖Center x e z‖) := by
    rw [abs_mul, abs_of_nonneg hOut]
    exact mul_le_mul_of_nonneg_left hInner hOut
  have hSq :=
    pow_le_pow_left₀
      (abs_nonneg (Out z e g * inner ℝ (Center x e z) (Tilt e z g)))
      hProd 2
  unfold sourceCenteredCoordinateSqEnvelope
  calc
    (Out z e g * inner ℝ (Center x e z) (Tilt e z g)) ^ 2 =
        |Out z e g * inner ℝ (Center x e z) (Tilt e z g)| ^ 2 := by
          symm
          exact sq_abs _
    _ ≤ (Out z e g * (Rate * ‖Center x e z‖)) ^ 2 := hSq
    _ = (Out z e g) ^ 2 * Rate ^ 2 * ‖Center x e z‖ ^ 2 := by ring

/-- Pointwise P3 split of the ORIGINAL signed defect.  The output drift and
centered source-coordinate contribution are kept as separate nonnegative
quantities. -/
theorem jointTransferLinkDifference_sq_le_outputDrift_add_centeredEnvelope
    (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    (jointTransferLinkDifference H N hN beta hbeta x e z g) ^ 2 ≤
      2 * sourceOutputDriftSq H N hN beta hbeta x e z g +
        2 * sourceCenteredCoordinateSqEnvelope H N hN beta hbeta x e z g := by
  rw [jointTransferLinkDifference_eq_centeredCoordinate]
  let A : ℝ := (1 - Out z e g * (1 + Avg e z g)) * Obs x z
  let B : ℝ := Out z e g * inner ℝ (Center x e z) (Tilt e z g)
  have hB :
      B ^ 2 ≤ sourceCenteredCoordinateSqEnvelope H N hN beta hbeta x e z g := by
    dsimp [B]
    exact sourceCenteredCoordinateResponse_sq_le_envelope
      H N hN beta hbeta x e z g
  change
    (A - B) ^ 2 ≤
      2 * sourceOutputDriftSq H N hN beta hbeta x e z g +
        2 * sourceCenteredCoordinateSqEnvelope H N hN beta hbeta x e z g
  have hA :
      A ^ 2 = sourceOutputDriftSq H N hN beta hbeta x e z g := by
    rfl
  rw [← hA]
  nlinarith [sq_nonneg (A + B)]

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
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k

/-- Frozen-orbit specialization of the pointwise P3 split.  This leaves both
the P3-B centered norm and the P3-C output drift visible. -/
theorem fineFrozenLinkDifference_sq_le_outputDrift_add_centeredEnvelope
    (e : Link) (z : Joint) (g : GaugeT) :
    (jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n) Orbit e z g) ^ 2 ≤
      2 * sourceOutputDriftSq Hn 2 Pos (beta n) (hbeta n) Orbit e z g +
        2 * sourceCenteredCoordinateSqEnvelope
          Hn 2 Pos (beta n) (hbeta n) Orbit e z g :=
  jointTransferLinkDifference_sq_le_outputDrift_add_centeredEnvelope
    Hn 2 Pos (beta n) (hbeta n) Orbit e z g

end FrozenFamily

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic
