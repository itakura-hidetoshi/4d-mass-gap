import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapCouplingKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ENNRealAnchoredOverlap

/-- Diagonal branch probability for a left-anchored overlap coupling, written
only in terms of its common and left-residual densities.  Exceptional zero or
infinite total densities are assigned an explicit deterministic fallback. -/
def diagonalWeight (common residual : ℝ≥0∞) : ℝ≥0∞ :=
  if common + residual = 0 ∨ common + residual = ∞ then 1
  else common * (common + residual)⁻¹

/-- Residual branch probability for the same left-anchored overlap coupling. -/
def residualWeight (common residual : ℝ≥0∞) : ℝ≥0∞ :=
  if common + residual = 0 ∨ common + residual = ∞ then 0
  else residual * (common + residual)⁻¹

/-- The two anchored branch probabilities sum to one at every input, including
the explicitly assigned exceptional fallback. -/
theorem diagonalWeight_add_residualWeight (common residual : ℝ≥0∞) :
    diagonalWeight common residual + residualWeight common residual = 1 := by
  by_cases hExceptional : common + residual = 0 ∨ common + residual = ∞
  · simp [diagonalWeight, residualWeight, hExceptional]
  · have h0 : common + residual ≠ 0 :=
      fun h => hExceptional (Or.inl h)
    have hTop : common + residual ≠ ∞ :=
      fun h => hExceptional (Or.inr h)
    rw [diagonalWeight, residualWeight, if_neg hExceptional,
      if_neg hExceptional, ← add_mul]
    calc
      (common + residual) * (common + residual)⁻¹ =
          (common + residual)⁻¹ * (common + residual) := mul_comm _ _
      _ = 1 := ENNReal.inv_mul_cancel h0 hTop

/-- The diagonal branch probability is at most one. -/
theorem diagonalWeight_le_one (common residual : ℝ≥0∞) :
    diagonalWeight common residual ≤ 1 := by
  rw [← diagonalWeight_add_residualWeight common residual]
  exact le_add_right le_rfl

/-- The residual branch probability is at most one. -/
theorem residualWeight_le_one (common residual : ℝ≥0∞) :
    residualWeight common residual ≤ 1 := by
  rw [← diagonalWeight_add_residualWeight common residual]
  exact le_add_left le_rfl

/-- Away from the explicit exceptional fallback, multiplying the diagonal branch
probability by the total left density recovers the common density exactly. -/
theorem total_mul_diagonalWeight
    (common residual : ℝ≥0∞)
    (h0 : common + residual ≠ 0)
    (hTop : common + residual ≠ ∞) :
    (common + residual) * diagonalWeight common residual = common := by
  have hExceptional :
      ¬ (common + residual = 0 ∨ common + residual = ∞) := by
    exact fun h => h.elim h0 hTop
  rw [diagonalWeight, if_neg hExceptional]
  calc
    (common + residual) * (common * (common + residual)⁻¹) =
        common * ((common + residual)⁻¹ * (common + residual)) := by ac_rfl
    _ = common := by rw [ENNReal.inv_mul_cancel h0 hTop, mul_one]

/-- Away from the explicit exceptional fallback, multiplying the residual branch
probability by the total left density recovers the left residual density exactly. -/
theorem total_mul_residualWeight
    (common residual : ℝ≥0∞)
    (h0 : common + residual ≠ 0)
    (hTop : common + residual ≠ ∞) :
    (common + residual) * residualWeight common residual = residual := by
  have hExceptional :
      ¬ (common + residual = 0 ∨ common + residual = ∞) := by
    exact fun h => h.elim h0 hTop
  rw [residualWeight, if_neg hExceptional]
  calc
    (common + residual) * (residual * (common + residual)⁻¹) =
        residual * ((common + residual)⁻¹ * (common + residual)) := by ac_rfl
    _ = residual := by rw [ENNReal.inv_mul_cancel h0 hTop, mul_one]

/-- Measurability of the diagonal branch probability under measurable common
and residual density inputs. -/
theorem diagonalWeight_measurable
    {α : Type*}
    [MeasurableSpace α]
    {common residual : α → ℝ≥0∞}
    (hCommon : Measurable common)
    (hResidual : Measurable residual) :
    Measurable (fun x => diagonalWeight (common x) (residual x)) := by
  let total := fun x => common x + residual x
  have hTotal : Measurable total := hCommon.add hResidual
  have hZero : MeasurableSet {x | total x = 0} :=
    hTotal (measurableSet_singleton 0)
  have hTop : MeasurableSet {x | total x = ∞} :=
    hTotal (measurableSet_singleton ∞)
  have hExceptional : MeasurableSet {x | total x = 0 ∨ total x = ∞} := by
    change MeasurableSet ({x | total x = 0} ∪ {x | total x = ∞})
    exact hZero.union hTop
  unfold diagonalWeight
  change Measurable
    (fun x => if total x = 0 ∨ total x = ∞ then 1
      else common x * (total x)⁻¹)
  exact Measurable.ite hExceptional measurable_const
    (hCommon.mul hTotal.inv)

/-- Measurability of the residual branch probability under measurable common
and residual density inputs. -/
theorem residualWeight_measurable
    {α : Type*}
    [MeasurableSpace α]
    {common residual : α → ℝ≥0∞}
    (hCommon : Measurable common)
    (hResidual : Measurable residual) :
    Measurable (fun x => residualWeight (common x) (residual x)) := by
  let total := fun x => common x + residual x
  have hTotal : Measurable total := hCommon.add hResidual
  have hZero : MeasurableSet {x | total x = 0} :=
    hTotal (measurableSet_singleton 0)
  have hTop : MeasurableSet {x | total x = ∞} :=
    hTotal (measurableSet_singleton ∞)
  have hExceptional : MeasurableSet {x | total x = 0 ∨ total x = ∞} := by
    change MeasurableSet ({x | total x = 0} ∪ {x | total x = ∞})
    exact hZero.union hTop
  unfold residualWeight
  change Measurable
    (fun x => if total x = 0 ∨ total x = ∞ then 0
      else residual x * (total x)⁻¹)
  exact Measurable.ite hExceptional measurable_const
    (hResidual.mul hTotal.inv)

end ENNRealAnchoredOverlap

/-- Measurable diagonal-branch probability of the explicit left-anchored overlap
transition, indexed jointly by a background pair and an anchoring target value. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) : ℝ≥0∞ :=
  ENNRealAnchoredOverlap.diagonalWeight
    (C.configurationPairConditionalOverlapDensity target w.1 w.2)
    (C.configurationPairConditionalLeftResidualDensity target w.1 w.2)

/-- Measurable residual-branch probability of the explicit left-anchored overlap
transition. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) : ℝ≥0∞ :=
  ENNRealAnchoredOverlap.residualWeight
    (C.configurationPairConditionalOverlapDensity target w.1 w.2)
    (C.configurationPairConditionalLeftResidualDensity target w.1 w.2)

/-- The anchored diagonal branch probability is jointly measurable. -/
theorem measurable_compact_oriented_configurationPairConditionalAnchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalAnchoredDiagonalWeight target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
  exact ENNRealAnchoredOverlap.diagonalWeight_measurable
    (by simpa [Function.uncurry] using
      measurable_compact_oriented_configurationPairConditionalOverlapDensity_uncurry
        C target)
    (by simpa [Function.uncurry] using
      measurable_compact_oriented_configurationPairConditionalLeftResidualDensity_uncurry
        C target)

/-- The anchored residual branch probability is jointly measurable. -/
theorem measurable_compact_oriented_configurationPairConditionalAnchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalAnchoredResidualWeight target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
  exact ENNRealAnchoredOverlap.residualWeight_measurable
    (by simpa [Function.uncurry] using
      measurable_compact_oriented_configurationPairConditionalOverlapDensity_uncurry
        C target)
    (by simpa [Function.uncurry] using
      measurable_compact_oriented_configurationPairConditionalLeftResidualDensity_uncurry
        C target)

/-- The two explicit anchored branch probabilities sum to one pointwise. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredWeights_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    C.configurationPairConditionalAnchoredDiagonalWeight target w +
        C.configurationPairConditionalAnchoredResidualWeight target w = 1 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
  exact ENNRealAnchoredOverlap.diagonalWeight_add_residualWeight _ _

/-- The anchored diagonal branch probability is bounded by one. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalWeight_le_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    C.configurationPairConditionalAnchoredDiagonalWeight target w ≤ 1 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
  exact ENNRealAnchoredOverlap.diagonalWeight_le_one _ _

/-- The anchored residual branch probability is bounded by one. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredResidualWeight_le_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    C.configurationPairConditionalAnchoredResidualWeight target w ≤ 1 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
  exact ENNRealAnchoredOverlap.residualWeight_le_one _ _

/-- At every nonexceptional anchoring value, total left density times the
diagonal branch probability is exactly the common overlap density. -/
theorem continuous_compact_oriented_totalLeftDensity_mul_anchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge)
    (h0 : C.configurationPairConditionalOverlapDensity target w.1 w.2 +
      C.configurationPairConditionalLeftResidualDensity target w.1 w.2 ≠ 0)
    (hTop : C.configurationPairConditionalOverlapDensity target w.1 w.2 +
      C.configurationPairConditionalLeftResidualDensity target w.1 w.2 ≠ ∞) :
    (C.configurationPairConditionalOverlapDensity target w.1 w.2 +
        C.configurationPairConditionalLeftResidualDensity target w.1 w.2) *
        C.configurationPairConditionalAnchoredDiagonalWeight target w =
      C.configurationPairConditionalOverlapDensity target w.1 w.2 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
  exact ENNRealAnchoredOverlap.total_mul_diagonalWeight _ _ h0 hTop

/-- At every nonexceptional anchoring value, total left density times the
residual branch probability is exactly the left residual density. -/
theorem continuous_compact_oriented_totalLeftDensity_mul_anchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge)
    (h0 : C.configurationPairConditionalOverlapDensity target w.1 w.2 +
      C.configurationPairConditionalLeftResidualDensity target w.1 w.2 ≠ 0)
    (hTop : C.configurationPairConditionalOverlapDensity target w.1 w.2 +
      C.configurationPairConditionalLeftResidualDensity target w.1 w.2 ≠ ∞) :
    (C.configurationPairConditionalOverlapDensity target w.1 w.2 +
        C.configurationPairConditionalLeftResidualDensity target w.1 w.2) *
        C.configurationPairConditionalAnchoredResidualWeight target w =
      C.configurationPairConditionalLeftResidualDensity target w.1 w.2 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
  exact ENNRealAnchoredOverlap.total_mul_residualWeight _ _ h0 hTop

end

end MathlibAnalytic
end MGAP4D
