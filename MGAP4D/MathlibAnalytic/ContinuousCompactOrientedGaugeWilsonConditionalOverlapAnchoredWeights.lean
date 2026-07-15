import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapCouplingKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ENNRealAnchoredOverlap

/-- Diagonal branch probability for an overlap coupling anchored at a left
sample of density `p`.  Exceptional zero or infinite left densities are assigned
an explicit deterministic fallback. -/
def diagonalWeight (p q : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 ∨ p = ∞ then 1 else min p q * p⁻¹

/-- Residual branch probability for an overlap coupling anchored at a left
sample of density `p`. -/
def residualWeight (p q : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 ∨ p = ∞ then 0 else (p - min p q) * p⁻¹

/-- The two anchored branch probabilities sum to one at every input, including
the explicitly assigned exceptional fallback. -/
theorem diagonalWeight_add_residualWeight (p q : ℝ≥0∞) :
    diagonalWeight p q + residualWeight p q = 1 := by
  by_cases hExceptional : p = 0 ∨ p = ∞
  · simp [diagonalWeight, residualWeight, hExceptional]
  · have hp0 : p ≠ 0 := fun hp => hExceptional (Or.inl hp)
    have hpTop : p ≠ ∞ := fun hp => hExceptional (Or.inr hp)
    rw [diagonalWeight, residualWeight, if_neg hExceptional,
      if_neg hExceptional, ← add_mul,
      add_tsub_cancel_of_le (min_le_left p q)]
    calc
      p * p⁻¹ = p⁻¹ * p := mul_comm _ _
      _ = 1 := ENNReal.inv_mul_cancel hp0 hpTop

/-- The diagonal branch probability is at most one. -/
theorem diagonalWeight_le_one (p q : ℝ≥0∞) :
    diagonalWeight p q ≤ 1 := by
  rw [← diagonalWeight_add_residualWeight p q]
  exact le_add_right le_rfl

/-- The residual branch probability is at most one. -/
theorem residualWeight_le_one (p q : ℝ≥0∞) :
    residualWeight p q ≤ 1 := by
  rw [← diagonalWeight_add_residualWeight p q]
  exact le_add_left le_rfl

/-- Away from the explicit exceptional fallback, multiplying the diagonal branch
probability by the left density recovers the common overlap density exactly. -/
theorem mul_diagonalWeight
    (p q : ℝ≥0∞)
    (hp0 : p ≠ 0)
    (hpTop : p ≠ ∞) :
    p * diagonalWeight p q = min p q := by
  have hExceptional : ¬ (p = 0 ∨ p = ∞) := by
    exact fun h => h.elim hp0 hpTop
  rw [diagonalWeight, if_neg hExceptional]
  calc
    p * (min p q * p⁻¹) = min p q * (p⁻¹ * p) := by ac_rfl
    _ = min p q := by rw [ENNReal.inv_mul_cancel hp0 hpTop, mul_one]

/-- Away from the explicit exceptional fallback, multiplying the residual branch
probability by the left density recovers the left residual density exactly. -/
theorem mul_residualWeight
    (p q : ℝ≥0∞)
    (hp0 : p ≠ 0)
    (hpTop : p ≠ ∞) :
    p * residualWeight p q = p - min p q := by
  have hExceptional : ¬ (p = 0 ∨ p = ∞) := by
    exact fun h => h.elim hp0 hpTop
  rw [residualWeight, if_neg hExceptional]
  calc
    p * ((p - min p q) * p⁻¹) =
        (p - min p q) * (p⁻¹ * p) := by ac_rfl
    _ = p - min p q := by
      rw [ENNReal.inv_mul_cancel hp0 hpTop, mul_one]

/-- Measurability of the diagonal branch probability under measurable density
inputs. -/
theorem diagonalWeight_measurable
    {α : Type*}
    [MeasurableSpace α]
    {p q : α → ℝ≥0∞}
    (hp : Measurable p)
    (hq : Measurable q) :
    Measurable (fun x => diagonalWeight (p x) (q x)) := by
  have hZero : MeasurableSet {x | p x = 0} :=
    hp (measurableSet_singleton 0)
  have hTop : MeasurableSet {x | p x = ∞} :=
    hp (measurableSet_singleton ∞)
  have hExceptional : MeasurableSet {x | p x = 0 ∨ p x = ∞} := by
    change MeasurableSet ({x | p x = 0} ∪ {x | p x = ∞})
    exact hZero.union hTop
  unfold diagonalWeight
  exact Measurable.ite hExceptional measurable_const
    ((hp.min hq).mul hp.inv)

/-- Measurability of the residual branch probability under measurable density
inputs. -/
theorem residualWeight_measurable
    {α : Type*}
    [MeasurableSpace α]
    {p q : α → ℝ≥0∞}
    (hp : Measurable p)
    (hq : Measurable q) :
    Measurable (fun x => residualWeight (p x) (q x)) := by
  have hZero : MeasurableSet {x | p x = 0} :=
    hp (measurableSet_singleton 0)
  have hTop : MeasurableSet {x | p x = ∞} :=
    hp (measurableSet_singleton ∞)
  have hExceptional : MeasurableSet {x | p x = 0 ∨ p x = ∞} := by
    change MeasurableSet ({x | p x = 0} ∪ {x | p x = ∞})
    exact hZero.union hTop
  unfold residualWeight
  exact Measurable.ite hExceptional measurable_const
    ((hp.sub (hp.min hq)).mul hp.inv)

end ENNRealAnchoredOverlap

/-- Left conditional Haar density evaluated jointly at a background pair and an
anchoring target-link value. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredLeftDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) : ℝ≥0∞ :=
  C.singleLinkConditionalDensity target w.1.1 w.2

/-- Right conditional Haar density evaluated at the same anchoring value. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredRightDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) : ℝ≥0∞ :=
  C.singleLinkConditionalDensity target w.1.2 w.2

/-- Joint measurability of the anchored left conditional density. -/
theorem measurable_compact_oriented_configurationPairConditionalAnchoredLeftDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalAnchoredLeftDensity target) := by
  have hInput : Measurable
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        (w.1.1, w.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredLeftDensity
  exact
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry C target).comp
      hInput

/-- Joint measurability of the anchored right conditional density. -/
theorem measurable_compact_oriented_configurationPairConditionalAnchoredRightDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalAnchoredRightDensity target) := by
  have hInput : Measurable
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        (w.1.2, w.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredRightDensity
  exact
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry C target).comp
      hInput

/-- Measurable diagonal-branch probability of the explicit left-anchored overlap
transition. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) : ℝ≥0∞ :=
  ENNRealAnchoredOverlap.diagonalWeight
    (C.configurationPairConditionalAnchoredLeftDensity target w)
    (C.configurationPairConditionalAnchoredRightDensity target w)

/-- Measurable residual-branch probability of the explicit left-anchored overlap
transition. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) : ℝ≥0∞ :=
  ENNRealAnchoredOverlap.residualWeight
    (C.configurationPairConditionalAnchoredLeftDensity target w)
    (C.configurationPairConditionalAnchoredRightDensity target w)

/-- The anchored diagonal branch probability is jointly measurable. -/
theorem measurable_compact_oriented_configurationPairConditionalAnchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalAnchoredDiagonalWeight target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
  exact ENNRealAnchoredOverlap.diagonalWeight_measurable
    (measurable_compact_oriented_configurationPairConditionalAnchoredLeftDensity
      C target)
    (measurable_compact_oriented_configurationPairConditionalAnchoredRightDensity
      C target)

/-- The anchored residual branch probability is jointly measurable. -/
theorem measurable_compact_oriented_configurationPairConditionalAnchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalAnchoredResidualWeight target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
  exact ENNRealAnchoredOverlap.residualWeight_measurable
    (measurable_compact_oriented_configurationPairConditionalAnchoredLeftDensity
      C target)
    (measurable_compact_oriented_configurationPairConditionalAnchoredRightDensity
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

/-- At every nonexceptional anchoring value, left density times the diagonal
branch probability is exactly the common overlap density. -/
theorem continuous_compact_oriented_leftDensity_mul_anchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge)
    (h0 : C.configurationPairConditionalAnchoredLeftDensity target w ≠ 0)
    (hTop : C.configurationPairConditionalAnchoredLeftDensity target w ≠ ∞) :
    C.configurationPairConditionalAnchoredLeftDensity target w *
        C.configurationPairConditionalAnchoredDiagonalWeight target w =
      C.configurationPairConditionalOverlapDensity target w.1 w.2 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalWeight
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapDensity
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredLeftDensity
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredRightDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
  exact ENNRealAnchoredOverlap.mul_diagonalWeight _ _ h0 hTop

/-- At every nonexceptional anchoring value, left density times the residual
branch probability is exactly the left residual density. -/
theorem continuous_compact_oriented_leftDensity_mul_anchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge)
    (h0 : C.configurationPairConditionalAnchoredLeftDensity target w ≠ 0)
    (hTop : C.configurationPairConditionalAnchoredLeftDensity target w ≠ ∞) :
    C.configurationPairConditionalAnchoredLeftDensity target w *
        C.configurationPairConditionalAnchoredResidualWeight target w =
      C.configurationPairConditionalLeftResidualDensity target w.1 w.2 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualWeight
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalLeftResidualDensity
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredLeftDensity
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredRightDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
  exact ENNRealAnchoredOverlap.mul_residualWeight _ _ h0 hTop

end

end MathlibAnalytic
end MGAP4D
