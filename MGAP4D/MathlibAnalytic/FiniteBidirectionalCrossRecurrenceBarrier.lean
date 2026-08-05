import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract proof-relevant forward barrier for a pair of nonnegative scalar
sequences whose successor estimates cross through one monotone scalar map. -/
structure FiniteBidirectionalCrossRecurrenceBarrierData
    (rowCoefficient columnCoefficient : ℕ → ℝ)
    (stepMap : ℝ → ℝ) where
  startStage : ℕ
  barrier : ℝ
  barrier_nonneg : 0 ≤ barrier
  barrier_lt_one : barrier < 1
  rowCoefficient_nonneg : ∀ stage : ℕ, 0 ≤ rowCoefficient stage
  columnCoefficient_nonneg : ∀ stage : ℕ, 0 ≤ columnCoefficient stage
  row_start_le : rowCoefficient startStage ≤ barrier
  column_start_le : columnCoefficient startStage ≤ barrier
  stepMap_mono_on_nonneg :
    ∀ {left right : ℝ},
      0 ≤ left → left ≤ right → stepMap left ≤ stepMap right
  stepMap_barrier_le : stepMap barrier ≤ barrier
  row_succ_le :
    ∀ stage : ℕ,
      rowCoefficient (stage + 1) ≤ stepMap (columnCoefficient stage)
  column_succ_le :
    ∀ stage : ℕ,
      columnCoefficient (stage + 1) ≤ stepMap (rowCoefficient stage)

namespace FiniteBidirectionalCrossRecurrenceBarrierData

variable
    {rowCoefficient columnCoefficient : ℕ → ℝ}
    {stepMap : ℝ → ℝ}
    (C : FiniteBidirectionalCrossRecurrenceBarrierData
      rowCoefficient columnCoefficient stepMap)

/-- Both scalar coefficients remain in the barrier at every later stage. -/
theorem coefficients_add_le
    (offset : ℕ) :
    rowCoefficient (C.startStage + offset) ≤ C.barrier ∧
      columnCoefficient (C.startStage + offset) ≤ C.barrier := by
  induction offset with
  | zero =>
      simpa using And.intro C.row_start_le C.column_start_le
  | succ offset ih =>
      have hRowMap :
          stepMap (columnCoefficient (C.startStage + offset)) ≤
            stepMap C.barrier :=
        C.stepMap_mono_on_nonneg
          (C.columnCoefficient_nonneg (C.startStage + offset)) ih.2
      have hColumnMap :
          stepMap (rowCoefficient (C.startStage + offset)) ≤
            stepMap C.barrier :=
        C.stepMap_mono_on_nonneg
          (C.rowCoefficient_nonneg (C.startStage + offset)) ih.1
      have hRow :
          rowCoefficient ((C.startStage + offset) + 1) ≤ C.barrier :=
        (C.row_succ_le (C.startStage + offset)).trans
          (hRowMap.trans C.stepMap_barrier_le)
      have hColumn :
          columnCoefficient ((C.startStage + offset) + 1) ≤ C.barrier :=
        (C.column_succ_le (C.startStage + offset)).trans
          (hColumnMap.trans C.stepMap_barrier_le)
      constructor
      · rw [Nat.add_succ]
        exact hRow
      · rw [Nat.add_succ]
        exact hColumn

/-- The row coefficient remains below the barrier. -/
theorem rowCoefficient_add_le
    (offset : ℕ) :
    rowCoefficient (C.startStage + offset) ≤ C.barrier :=
  (C.coefficients_add_le offset).1

/-- The column coefficient remains below the barrier. -/
theorem columnCoefficient_add_le
    (offset : ℕ) :
    columnCoefficient (C.startStage + offset) ≤ C.barrier :=
  (C.coefficients_add_le offset).2

/-- Every later row coefficient is strict. -/
theorem rowCoefficient_add_lt_one
    (offset : ℕ) :
    rowCoefficient (C.startStage + offset) < 1 :=
  lt_of_le_of_lt (C.rowCoefficient_add_le offset) C.barrier_lt_one

/-- Every later column coefficient is strict. -/
theorem columnCoefficient_add_lt_one
    (offset : ℕ) :
    columnCoefficient (C.startStage + offset) < 1 :=
  lt_of_le_of_lt (C.columnCoefficient_add_le offset) C.barrier_lt_one

/-- The cross recurrence remains simultaneously strict at every later stage. -/
theorem coefficients_add_lt_one
    (offset : ℕ) :
    rowCoefficient (C.startStage + offset) < 1 ∧
      columnCoefficient (C.startStage + offset) < 1 :=
  ⟨C.rowCoefficient_add_lt_one offset,
    C.columnCoefficient_add_lt_one offset⟩

end FiniteBidirectionalCrossRecurrenceBarrierData

end

end MathlibAnalytic
end MGAP4D