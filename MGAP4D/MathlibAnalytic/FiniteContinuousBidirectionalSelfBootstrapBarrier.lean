import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Continuous two-sided self-bootstrap continuation data.  The two
coefficients begin strictly inside a common barrier and, at every positive
parameter, each is bounded by a monotone scalar map applied to the other.
Sending the barrier strictly inside itself rules out a first exit. -/
structure FiniteContinuousBidirectionalSelfBootstrapBarrierData where
  upperParameter : ℝ
  upperParameter_pos : 0 < upperParameter
  barrier : ℝ
  barrier_nonneg : 0 ≤ barrier
  rowCoefficient : ℝ → ℝ
  columnCoefficient : ℝ → ℝ
  rowCoefficient_continuousOn :
    ContinuousOn rowCoefficient (Set.Icc 0 upperParameter)
  columnCoefficient_continuousOn :
    ContinuousOn columnCoefficient (Set.Icc 0 upperParameter)
  rowCoefficient_zero_lt : rowCoefficient 0 < barrier
  columnCoefficient_zero_lt : columnCoefficient 0 < barrier
  stepMap : ℝ → ℝ → ℝ
  rowCoefficient_nonneg :
    ∀ parameter ∈ Set.Ioc 0 upperParameter,
      0 ≤ rowCoefficient parameter
  columnCoefficient_nonneg :
    ∀ parameter ∈ Set.Ioc 0 upperParameter,
      0 ≤ columnCoefficient parameter
  stepMap_mono_on_nonneg :
    ∀ parameter ∈ Set.Ioc 0 upperParameter,
      ∀ {left right : ℝ},
        0 ≤ left → left ≤ right →
          stepMap parameter left ≤ stepMap parameter right
  stepMap_barrier_lt :
    ∀ parameter ∈ Set.Ioc 0 upperParameter,
      stepMap parameter barrier < barrier
  row_self_le :
    ∀ parameter ∈ Set.Ioc 0 upperParameter,
      rowCoefficient parameter ≤
        stepMap parameter (columnCoefficient parameter)
  column_self_le :
    ∀ parameter ∈ Set.Ioc 0 upperParameter,
      columnCoefficient parameter ≤
        stepMap parameter (rowCoefficient parameter)

namespace FiniteContinuousBidirectionalSelfBootstrapBarrierData

/-- Maximum of the two continuation coefficients. -/
def maximumCoefficient
    (C : FiniteContinuousBidirectionalSelfBootstrapBarrierData)
    (parameter : ℝ) : ℝ :=
  max (C.rowCoefficient parameter) (C.columnCoefficient parameter)

/-- The maximum coefficient is continuous on the continuation interval. -/
theorem maximumCoefficient_continuousOn
    (C : FiniteContinuousBidirectionalSelfBootstrapBarrierData) :
    ContinuousOn C.maximumCoefficient
      (Set.Icc 0 C.upperParameter) := by
  intro parameter hParameter
  unfold maximumCoefficient
  exact
    (C.rowCoefficient_continuousOn parameter hParameter).max
      (C.columnCoefficient_continuousOn parameter hParameter)

/-- The maximum coefficient starts strictly inside the barrier. -/
theorem maximumCoefficient_zero_lt
    (C : FiniteContinuousBidirectionalSelfBootstrapBarrierData) :
    C.maximumCoefficient 0 < C.barrier := by
  unfold maximumCoefficient
  exact max_lt C.rowCoefficient_zero_lt C.columnCoefficient_zero_lt

/-- At any positive parameter where both coefficients lie in the barrier, the
self-bootstrap inequalities improve both coefficients strictly into the
interior. -/
theorem coefficients_lt_of_le_barrier
    (C : FiniteContinuousBidirectionalSelfBootstrapBarrierData)
    (parameter : ℝ)
    (hParameter : parameter ∈ Set.Ioc 0 C.upperParameter)
    (hRow : C.rowCoefficient parameter ≤ C.barrier)
    (hColumn : C.columnCoefficient parameter ≤ C.barrier) :
    C.rowCoefficient parameter < C.barrier ∧
      C.columnCoefficient parameter < C.barrier := by
  have hRowMap :
      C.stepMap parameter (C.rowCoefficient parameter) ≤
        C.stepMap parameter C.barrier :=
    C.stepMap_mono_on_nonneg parameter hParameter
      (C.rowCoefficient_nonneg parameter hParameter) hRow
  have hColumnMap :
      C.stepMap parameter (C.columnCoefficient parameter) ≤
        C.stepMap parameter C.barrier :=
    C.stepMap_mono_on_nonneg parameter hParameter
      (C.columnCoefficient_nonneg parameter hParameter) hColumn
  constructor
  · exact lt_of_le_of_lt
      (C.row_self_le parameter hParameter)
      (lt_of_le_of_lt hColumnMap
        (C.stepMap_barrier_lt parameter hParameter))
  · exact lt_of_le_of_lt
      (C.column_self_le parameter hParameter)
      (lt_of_le_of_lt hRowMap
        (C.stepMap_barrier_lt parameter hParameter))

/-- Continuous first-exit contradiction: both coefficients remain strictly
inside the common barrier throughout the closed continuation interval. -/
theorem coefficients_lt_barrier
    (C : FiniteContinuousBidirectionalSelfBootstrapBarrierData)
    (parameter : ℝ)
    (hParameter : parameter ∈ Set.Icc 0 C.upperParameter) :
    C.rowCoefficient parameter < C.barrier ∧
      C.columnCoefficient parameter < C.barrier := by
  have hMaxParameter :
      C.maximumCoefficient parameter < C.barrier := by
    by_contra hNot
    have hBarrierLe : C.barrier ≤ C.maximumCoefficient parameter :=
      le_of_not_gt hNot
    have hInterval :
        C.barrier ∈ Set.Icc
          (C.maximumCoefficient 0)
          (C.maximumCoefficient parameter) :=
      ⟨le_of_lt C.maximumCoefficient_zero_lt, hBarrierLe⟩
    have hZeroParameter : 0 ≤ parameter := hParameter.1
    have hContinuousOn :
        ContinuousOn C.maximumCoefficient (Set.Icc 0 parameter) :=
      C.maximumCoefficient_continuousOn.mono (by
        intro x hx
        exact ⟨hx.1, hx.2.trans hParameter.2⟩)
    have hImage :=
      intermediate_value_Icc hZeroParameter hContinuousOn hInterval
    rcases hImage with ⟨crossing, hCrossingInterval, hCrossingEq⟩
    have hCrossingNeZero : crossing ≠ 0 := by
      intro hZero
      subst crossing
      have : C.maximumCoefficient 0 = C.barrier := hCrossingEq
      linarith [C.maximumCoefficient_zero_lt]
    have hCrossingPos : 0 < crossing :=
      lt_of_le_of_ne hCrossingInterval.1 (Ne.symm hCrossingNeZero)
    have hCrossingParameter :
        crossing ∈ Set.Ioc 0 C.upperParameter :=
      ⟨hCrossingPos, hCrossingInterval.2.trans hParameter.2⟩
    have hRowLeMax :
        C.rowCoefficient crossing ≤ C.maximumCoefficient crossing :=
      le_max_left _ _
    have hColumnLeMax :
        C.columnCoefficient crossing ≤ C.maximumCoefficient crossing :=
      le_max_right _ _
    have hStrict :=
      C.coefficients_lt_of_le_barrier crossing hCrossingParameter
        (hRowLeMax.trans_eq hCrossingEq)
        (hColumnLeMax.trans_eq hCrossingEq)
    have hMaximumStrict :
        C.maximumCoefficient crossing < C.barrier := by
      unfold maximumCoefficient
      exact max_lt hStrict.1 hStrict.2
    linarith
  exact ⟨
    lt_of_le_of_lt (le_max_left _ _) hMaxParameter,
    lt_of_le_of_lt (le_max_right _ _) hMaxParameter⟩

/-- Endpoint specialization of the first-exit theorem. -/
theorem endpoint_coefficients_lt_barrier
    (C : FiniteContinuousBidirectionalSelfBootstrapBarrierData) :
    C.rowCoefficient C.upperParameter < C.barrier ∧
      C.columnCoefficient C.upperParameter < C.barrier :=
  C.coefficients_lt_barrier C.upperParameter
    ⟨le_of_lt C.upperParameter_pos, le_rfl⟩

end FiniteContinuousBidirectionalSelfBootstrapBarrierData

end

end MathlibAnalytic
end MGAP4D