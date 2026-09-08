import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialFrameGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- Mean squared norm retained by a finite family of projections.  For
orthogonal projections this is the complementary Rayleigh quantity to the
normalized residual energy. -/
def groundStateJointColorMeanProjectedNormSq
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (x : E) : ℝ :=
  ((Fintype.card C : ℝ)⁻¹) * ∑ c : C, ‖P c x‖ ^ 2

/-- For a finite family of orthogonal projections, normalized residual energy
is exactly total squared norm minus the mean squared projected norm. -/
theorem groundStateJointColorNormalizedResidualEnergy_eq_norm_sq_sub_meanProjectedNormSq
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) :
    groundStateJointColorNormalizedResidualEnergy P x =
      ‖x‖ ^ 2 - groundStateJointColorMeanProjectedNormSq P x := by
  have hres : ∀ c : C,
      ‖x - P c x‖ ^ 2 = ‖x‖ ^ 2 - ‖P c x‖ ^ 2 := by
    intro c
    exact realHilbert_groundStateJoint_projection_residual_sq_eq_defect
      (P c) (hPid c) (hPsymm c) x
  have hsum :
      (∑ c : C, ‖x - P c x‖ ^ 2) =
        (Fintype.card C : ℝ) * ‖x‖ ^ 2 - ∑ c : C, ‖P c x‖ ^ 2 := by
    calc
      (∑ c : C, ‖x - P c x‖ ^ 2) =
          ∑ c : C, (‖x‖ ^ 2 - ‖P c x‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hres c
      _ = (∑ _c : C, ‖x‖ ^ 2) - ∑ c : C, ‖P c x‖ ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = (Fintype.card C : ℝ) * ‖x‖ ^ 2 - ∑ c : C, ‖P c x‖ ^ 2 := by
        simp
  have hcard : 0 < (Fintype.card C : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold groundStateJointColorNormalizedResidualEnergy
  unfold groundStateJointColorMeanProjectedNormSq
  rw [hsum, mul_sub, ← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

/-- Exact algebraic form of a finite-color frame inequality: a residual frame
coefficient `κ` is equivalent to contraction of the mean projected squared norm
by the complementary coefficient `1 - κ`. -/
theorem groundStateJointColorFrame_iff_meanProjectedNormSq_le
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (κ : ℝ)
    (x : E) :
    κ * ‖x‖ ^ 2 ≤ groundStateJointColorNormalizedResidualEnergy P x ↔
      groundStateJointColorMeanProjectedNormSq P x ≤ (1 - κ) * ‖x‖ ^ 2 := by
  rw [groundStateJointColorNormalizedResidualEnergy_eq_norm_sq_sub_meanProjectedNormSq
    P hPid hPsymm x]
  constructor <;> intro h <;> nlinarith

section FiniteVolume

variable (H N : ℕ)
variable (hN : 0 < N)
variable (beta : ℝ)
variable (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "V" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta
local notation "P6" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
    H N hN beta hbeta

/-- Mean squared norm retained by the six genuine spatial conditional
expectations on the ground-state joint law, evaluated on a right-boundary
vacuum vector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
    (u : V) : ℝ :=
  groundStateJointColorMeanProjectedNormSq P6 (R u)

/-- Exact six-spatial Dirichlet identity.  No comparison constant is used: the
six-spatial residual is the vacuum norm squared minus the mean squared norm
retained by the six actual conditional expectations. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy_eq_norm_sq_sub_meanProjectedNormSq
    (u : V) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
        H N hN beta hbeta u =
      ‖u‖ ^ 2 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
          H N hN beta hbeta u := by
  change
    groundStateJointColorNormalizedResidualEnergy P6 (R u) =
      ‖u‖ ^ 2 - groundStateJointColorMeanProjectedNormSq P6 (R u)
  calc
    groundStateJointColorNormalizedResidualEnergy P6 (R u) =
        ‖R u‖ ^ 2 - groundStateJointColorMeanProjectedNormSq P6 (R u) :=
      groundStateJointColorNormalizedResidualEnergy_eq_norm_sq_sub_meanProjectedNormSq
        P6
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_idempotent
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_symmetric
          H N hN beta hbeta)
        (R u)
    _ = ‖u‖ ^ 2 - groundStateJointColorMeanProjectedNormSq P6 (R u) := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_norm_sq]

/-- On the physical top-orthogonal sector, the six-spatial frame inequality is
exactly equivalent to contraction of the mean squared projected norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_iff_meanProjectionContraction
    (κ : ℝ)
    (x : K) :
    κ * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          H N hN beta hbeta (U ((x : G) : HaarL2)) ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
          H N hN beta hbeta (U ((x : G) : HaarL2)) ≤
        (1 - κ) * ‖(x : G)‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy_eq_norm_sq_sub_meanProjectedNormSq]
  have hnorm : ‖U ((x : G) : HaarL2)‖ = ‖(x : G)‖ := by
    simpa using (U.norm_map ((x : G) : HaarL2))
  rw [hnorm]
  constructor <;> intro h <;> nlinarith

/-- A contraction factor `q ≤ 1` for the actual six-spatial mean projected
squared norm yields the explicit physical transfer-gap lower bound
`3 * (1 - q) / 8`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectionContraction_implies_transferGap
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hcontract : ∀ x : K,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
          H N hN beta hbeta (U ((x : G) : HaarL2)) ≤
        q * ‖(x : G)‖ ^ 2) :
    3 * (1 - q) / 8 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_implies_transferGap
      H N hN beta hbeta (1 - q) (by linarith) (by linarith)
  intro x
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_iff_meanProjectionContraction
      H N hN beta hbeta (1 - q) x).2 (by simpa using hcontract x)

/-- Strict contraction of the actual six-spatial mean projected squared norm
implies a positive finite-volume physical transfer gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectionContraction_positive_transferGap
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hcontract : ∀ x : K,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
          H N hN beta hbeta (U ((x : G) : HaarL2)) ≤
        q * ‖(x : G)‖ ^ 2) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectionContraction_implies_transferGap
      H N hN beta hbeta q hq0 hq1.le hcontract
  have hdiff : 0 < 1 - q := by linarith
  have hpos : 0 < 3 * (1 - q) / 8 :=
    div_pos (mul_pos (by norm_num) hdiff) (by norm_num)
  exact lt_of_lt_of_le hpos hgap

end FiniteVolume

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- Sharpened scale-uniform target: one strict contraction factor for the mean
squared norm retained by the six genuine ground-state spatial conditional
expectations on the physical top-orthogonal sector. -/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateSixSpatialMeanProjectionContraction : Prop :=
  ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
    ∀ (n : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            (halfExtent n) N hN (beta n) (hbeta n)
            ((x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N) :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  (halfExtent n) N))) ≤
        q *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2

/-- One scale-independent strict contraction factor for the concrete six-color
mean projection gives a uniform positive physical top-eigenspace transfer gap.
The explicit lower bound is `3 * (1 - q) / 8`. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformGroundStateSixSpatialMeanProjectionContraction_implies_uniformTransferGap
    (hcontract :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateSixSpatialMeanProjectionContraction
        halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  rcases hcontract with ⟨q, hq0, hq1, hcontract⟩
  have hdiff : 0 < 1 - q := by linarith
  have hpos : 0 < 3 * (1 - q) / 8 :=
    div_pos (mul_pos (by norm_num) hdiff) (by norm_num)
  refine ⟨3 * (1 - q) / 8, hpos, ?_⟩
  intro n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectionContraction_implies_transferGap
      (halfExtent n) N hN (beta n) (hbeta n)
      q hq0 hq1.le (fun x => hcontract n x)

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D
